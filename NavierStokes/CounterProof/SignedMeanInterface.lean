import NavierStokes.CounterProof.Certificates.TerminalCertificate
import NavierStokes.CounterProof.Adapter.ExactCovariance
import NavierStokes.CounterProof.Adapter.ReconstructedResponse
import NavierStokes.CounterProof.Adapter.NativeDataObstruction
import NavierStokes.CounterProof.Adapter.ReducedCross
import NavierStokes.CounterProof.Adapter.ResidualLedger
import NavierStokes.CounterProof.Adapter.RequestDifferential
import NavierStokes.CounterProof.Adapter.FullCompatibility
import NavierStokes.CounterProof.Adapter.ConditionedResponse
import NavierStokes.CounterProof.Adapter.FiniteJetWitness
import NavierStokes.CounterProof.Adapter.DiagonalTail
import NavierStokes.CounterProof.Adapter.PhysicalResidualExposure

/-!
# Signed-mean source interface

This module is the public root and concluding layer of the source-adapter
subsystem prescribed by the companion note.  Focused modules under `Adapter/`
import completed proofs for the literal signed update, cross defect, iteration
ledger, and physical residual machinery from `NavierStokes/` rather than
reproving them or introducing a surrogate covariance model.

The exports below retain direct access to upstream identities.  They include
one concrete obstruction already established at the source interface: the
complete normalized `NativeData` package cannot exist on the actual geometry.
That exact incompatibility is a new Lean source audit derived by following the
manuscript instantiation program; it is not asserted in either manuscript.

The implementation follows §3.2–§7 and Lean-instantiation Phases I–VII of
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`.
In particular, source-level lower bounds exported from `FiniteJetWitness` are
inputs to—not substitutes for—the finite-jet dual certificate and actual-tail
coverage required by Theorem 6.1, Proposition 6.2, and Corollary 6.3.  Either
branch can close independently under Theorem 7.1, while Corollary 6.3's
same-witness `JointCokernelCertificate` is the primary project endpoint.  The
§15 interface checklist supplies the concrete Lean audit obligations.

`NativeDataObstruction` proves that the generic normalized-tail
`SignedMeanGain.NativeData` package is uninhabited on the actual geometry,
including after label-only reindexing.  Any claimed endpoint shown to require
that package is therefore false without invoking either dual branch.  This
direct closure, the reduced branch, and the full-compatible branch are each
independently usable counter-proofs.

NativeData is not logically necessary to instantiate either branch or the
primary joint certificate.  It is nevertheless the preferred robust
source-instantiation strategy for the pinned source.  The actual cycle’s
narrower partition-factor response exposes an exact finite-prefix defect and
the compatible repair it omits, giving both branches and a candidate common
finite-jet functional one structural provenance.  A non-NativeData source
argument could reach the same endpoint, but it would need to supply independently
the complete observed defect, repair target, common functional,
inverse/reconstruction losses, and complete-tail control prescribed by §8
Phases II–VI.  The physical cross identity alone recreates none of the missing
native package or quantitative joint hypotheses.

For a surviving reduced mismatch, physical residual exposure follows the
range/lift-cost and residual-leakage framework of
`docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex`, especially
Proposition 8.2 and Corollary 8.3.

The preferred `CounterProof/Adapter/` source integration is:

1. establish direct NativeData closure where an endpoint entails the package,
   and expose the forced physical-scale replacement used upstream;
2. anchor the exact reconstructed state and covariance response;
3. identify the native two-coordinate reduced cross response;
4. use the exact missing component as a common defect/repair obligation;
5. expose the actual fixed physical-jet loss and finite residual rates;
6. differentiate the request-to-reconstruction path and propagate its inverse
   losses through the complete future tail;
7. encode independently usable finite-jet witnesses for both branches and
   prefer one common functional; and
8. instantiate the primary `JointCokernelCertificate` when that functional
   proves both estimates, while preserving either completed branch as a valid
   terminal counter-proof.
-/

namespace NavierStokes.CounterProof.SignedMeanInterface

export Adapter
  (remainderLinearPart remainderQuadraticPart
    signedRemainder_eq_linear_add_quadratic signedRemainder_scaled_exact
    hasDerivAt_signedRemainder_component_zero signedIncrementCLM
    hasFDerivAt_signedIncrement derivative_split derivative_hidden_eq_remainder
    TangentialObservation averagedTangentialObservation reducedTangentialTarget
    hiddenTangentialRemainder source_averaged_response_eq_reduced_add_hidden
    source_averaged_response_sub_reduced_eq_hidden
    source_averaged_response_ne_reduced_of_hidden_ne_zero
    compatibilityBlocks compatibility_hidden_exact compatibility_full_apply
    reduced_branch_defect_eq_reconstructed ResponseLossLedger
    EvaluatedSignedJetState ConstraintKind EvaluatedConstraintBlocks
    source_target_amplitude_lower source_pressure_root_lower
    ReducedDefectWitness FullCapacityWitness IndependentFiniteJetWitnesses
    tailCapacityOfSeparateBounds complete_tail_fraction_bound
    IndependentBranchCertificates independent_counterproof_branches)

export Adapter.NativeDataObstruction
  (ActualNativeData NativeRouteAvailable native_route_unavailable
    tail_bound_contradiction ClaimRequiresNativeData
    refute_claim_of_native_data_requirement
    actualCrossComponent actualRequestedComponent actualMissingComponent actualCrossDefect
    actual_cross_eq_partition_factor actual_cross_defect_eq_neg_missing
    actual_cross_cancels_iff_missing_eq_zero actual_cross_ne_request_of_missing
    actual_cross_defect_ne_zero_of_missing actual_cross_tail_exact
    actual_cross_tail_jets FinitePrefixObstruction)

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

export NavierStokes.ActualSignedMeanBinding
  (no_legacy_nativeData family_defects_all_exponents)

open NavierStokes.SignedMeanGain

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {s : NavierStokes.WeightedClasses.StripData D} {P : ι → ℕ → D → ℝ}
variable {α δ β η : ℝ}

/-- Algebraic projection of companion-note Theorem 4.1 (`thm:covsplit`): a
nonzero retained source remainder forces the literal covariance increment to
differ from the reduced primary–tangent cross tensor.  This is a source-audit
helper, not a terminal obstruction without a tail-stable physical witness. -/
theorem retained_remainder_forces_covariance_mismatch
    (f : NavierStokes.LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f)
    (hremainder : remainderTensor f a ≠ 0) :
    incrementTensor f a ≠ crossTensor f a := by
  intro heq
  exact hremainder
    ((Adapter.incrementTensor_eq_crossTensor_iff_remainderTensor_eq_zero f a).mp heq)

/-- Source-state projection of companion-note Theorem 4.1: on an assembled
stage, a nonzero retained remainder rules out identifying actual recomputed
covariance with a cross-only update.  Proposition 4.2 and the tail estimates
are still required to turn it into an observed counter-proof certificate. -/
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

/-- Concrete consequence of companion-note Proposition 4.2
(`prop:fullresponse`): pressure reconstruction is indispensable in the axial
response.  If its axial derivative is nonzero at a source point, the actual
axial change cannot equal the covariance-only response there. -/
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
