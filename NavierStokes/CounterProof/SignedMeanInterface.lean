import NavierStokes.CounterProof.Certificates.TerminalCertificate
import NavierStokes.CounterProof.Adapter.ExactCovariance
import NavierStokes.CounterProof.Adapter.ReconstructedResponse
import NavierStokes.CounterProof.Adapter.ReducedCross
import NavierStokes.CounterProof.Adapter.ResidualLedger

/-!
# Signed-mean source interface

This module is the public root and concluding layer of the source-adapter
subsystem prescribed by the companion note.  Focused modules under `Adapter/`
import completed proofs for the literal signed update, cross defect, iteration
ledger, and physical residual machinery from `NavierStokes/` rather than
reproving them or introducing a surrogate covariance model.

The exports below retain direct access to upstream identities.  The concluding
theorems derive exact consequences through the adapters, but do not assert that
a concrete compatibility obstruction already exists.  Such an instance must
still identify the active and hidden tangent spaces, construct the observation
and constraint maps, and discharge quantitative tail or residual hypotheses.

The `CounterProof/Adapter/` subsystem begins the source integration in this
order:

1. anchor the exact reconstructed state and covariance response;
2. identify the native two-coordinate reduced cross response;
3. retain the covariance and physical cross defects explicitly;
4. expose the actual fixed physical-jet loss and finite residual rates;
5. next differentiate the request-to-reconstruction path and propagate its
   inverse losses through the complete future tail;
6. instantiate a dual or relative-contraction certificate; and
7. expose a surviving mismatch in the physical residual.
-/

namespace NavierStokes.CounterProof.SignedMeanInterface

/-- Upstream source revision audited by the downstream companion note.  This
constant is documentation metadata, not a proof assumption. -/
def pinnedUpstreamCommit : String :=
  "f9e8bc5b38b6e212696e8a30e3e91517af887bbd"

export NavierStokes.SignedMeanGain
  (incrementTensor_split waveStage_mean waveStage_covariance waveStage_theta_change
    waveStage_gr_change waveStage_axial_change signed_tensor_bounds
    native_physical_cross)

export NavierStokes.CrossBasedMeanComposition
  (cross_cancels_with_defect signed_mean_gain_of_cross_defects)

open NavierStokes.SignedMeanGain

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {s : NavierStokes.WeightedClasses.StripData D} {P : ι → ℕ → D → ℝ}
variable {α δ β η : ℝ}

/-- A nonzero retained source remainder forces the literal covariance increment
to differ from the reduced primary–tangent cross tensor. -/
theorem retained_remainder_forces_covariance_mismatch
    (f : NavierStokes.LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f)
    (hremainder : remainderTensor f a ≠ 0) :
    incrementTensor f a ≠ crossTensor f a := by
  intro heq
  exact hremainder
    ((Adapter.incrementTensor_eq_crossTensor_iff_remainderTensor_eq_zero f a).mp heq)

/-- On an assembled source stage, a nonzero retained remainder rules out
identifying the actual recomputed covariance with a reduced cross-only update. -/
theorem retained_remainder_forces_waveStage_covariance_mismatch
    {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {U : Set (NavierStokes.PressureStream.Lift S)}
    {g : NavierStokes.VariableGaugeMean.GaugeData S}
    {c : NavierStokes.CorrectionState.Context (NavierStokes.PressureStream.Lift S)}
    {u : NavierStokes.CorrectionState.State (NavierStokes.PressureStream.Lift S)}
    {w : NavierStokes.CorrectionState.Oscillation (NavierStokes.PressureStream.Lift S)}
    {q : NavierStokes.CorrectionState.OscillatoryScalar (NavierStokes.PressureStream.Lift S)}
    {gaussian : NavierStokes.CorrectionState.Oscillation (NavierStokes.PressureStream.Lift S)}
    (R : Adapter.ReconstructedWaveStageResponse (U := U) g c u w q gaussian)
    {s : NavierStokes.WeightedClasses.StripData (NavierStokes.PressureStream.Lift S)}
    {P : ι → ℕ → NavierStokes.PressureStream.Lift S → ℝ} {α δ β η : ℝ}
    (f : NavierStokes.LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f)
    (hold : u.oscillation = oldField f a)
    (hwave : w = tangentField f a + curlField f a)
    (hremainder : remainderTensor f a ≠ 0) :
    (waveStage g c u w q gaussian).covariance ≠
      u.covariance + crossTensor f a := by
  intro hreduced
  have hfull := R.covariance_eq_cross_add_remainder f a hold hwave
  have hsum :
      u.covariance + (crossTensor f a + remainderTensor f a) =
        u.covariance + crossTensor f a := hfull.symm.trans hreduced
  have hcross : crossTensor f a + remainderTensor f a = crossTensor f a :=
    add_left_cancel hsum
  apply hremainder
  simpa only [add_eq_left] using hcross

/-- Pressure reconstruction is an indispensable part of the axial response:
if its axial derivative is nonzero at a source point, the actual axial change
cannot equal the covariance-only response there. -/
theorem pressure_feedback_forces_axial_response_mismatch
    {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {U : Set (NavierStokes.PressureStream.Lift S)}
    {g : NavierStokes.VariableGaugeMean.GaugeData S}
    {c : NavierStokes.CorrectionState.Context (NavierStokes.PressureStream.Lift S)}
    {u : NavierStokes.CorrectionState.State (NavierStokes.PressureStream.Lift S)}
    {w : NavierStokes.CorrectionState.Oscillation (NavierStokes.PressureStream.Lift S)}
    {q : NavierStokes.CorrectionState.OscillatoryScalar (NavierStokes.PressureStream.Lift S)}
    {gaussian : NavierStokes.CorrectionState.Oscillation (NavierStokes.PressureStream.Lift S)}
    (R : Adapter.ReconstructedWaveStageResponse (U := U) g c u w q gaussian)
    (n : ℕ) {x : NavierStokes.PressureStream.Lift S} (hx : x ∈ U)
    (hpressure : c.operators.dz (pressureChange g c u w q gaussian) n x ≠ 0) :
    ((waveStage g c u w q gaussian).axialResidual c - u.axialResidual c) n x ≠
      axialCovarianceChange c.operators (covarianceIncrement u.oscillation w) n x := by
  intro hcovarianceOnly
  have hfull := R.axial_change n hx
  simp only [Pi.sub_apply, Pi.add_apply] at hfull hcovarianceOnly
  apply hpressure
  linarith

end NavierStokes.CounterProof.SignedMeanInterface
