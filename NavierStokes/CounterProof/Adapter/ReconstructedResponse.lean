import NavierStokes.CounterProof.Adapter.ExactCovariance

/-!
# Reconstructed wave-stage response adapter

The actual signed wave stage preserves the mean, recomputes covariance, and
reconstructs pressure before evaluating the axial residual.  This module
packages those imported identities as one proof object on the common slow
domain.  In particular, pressure feedback is a field of the package rather
than an optional later correction.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

open SignedMeanGain MeanIncrementBounds CorrectionState

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Exact source response of one reconstructed signed wave stage. -/
structure ReconstructedWaveStageResponse
    {U : Set (PressureStream.Lift S)}
    (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S))
    (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S))
    (gaussian : Oscillation (PressureStream.Lift S)) : Prop where
  /-- The active signed update does not directly change the mean field. -/
  mean_eq : (waveStage g c u w q gaussian).mean = u.mean
  /-- Covariance is recomputed from the actual updated oscillation. -/
  covariance_eq :
    (waveStage g c u w q gaussian).covariance =
      u.covariance + covarianceIncrement u.oscillation w
  /-- The theta residual sees the complete covariance increment. -/
  theta_change :
    Agree U ((waveStage g c u w q gaussian).thetaResidual c - u.thetaResidual c)
      (thetaCovarianceChange c.operators (covarianceIncrement u.oscillation w))
  /-- The radial source used by pressure reconstruction sees the same complete
  covariance increment. -/
  radial_source_change :
    Agree U ((waveStage g c u w q gaussian).gr c - u.gr c)
      (radialCovarianceChange c.operators (covarianceIncrement u.oscillation w))
  /-- The reconstructed pressure change is the literal pressure difference. -/
  pressure_eq :
    (waveStage g c u w q gaussian).pressure =
      u.pressure + pressureChange g c u w q gaussian
  /-- The axial response contains both the covariance response and the axial
  derivative of the reconstructed pressure change. -/
  axial_change :
    Agree U ((waveStage g c u w q gaussian).axialResidual c - u.axialResidual c)
      (axialCovarianceChange c.operators (covarianceIncrement u.oscillation w) +
        c.operators.dz (pressureChange g c u w q gaussian))

/-- Assemble the exact reconstructed response from completed upstream proofs.
The hypotheses are precisely the regularity assumptions required by those
source theorems. -/
theorem reconstructedWaveStageResponse_of_source
    {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S))
    (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S))
    (gaussian : Oscillation (PressureStream.Lift S))
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hX : ∀ i j, SmoothOn U (covarianceIncrement u.oscillation w i j))
    (hp : SmoothOn U u.pressure)
    (hδp : SmoothOn U (pressureChange g c u w q gaussian)) :
    ReconstructedWaveStageResponse (U := U) g c u w q gaussian where
  mean_eq := waveStage_mean g c u w q gaussian
  covariance_eq := waveStage_covariance g c u w q gaussian
  theta_change := waveStage_theta_change hU g c u w q gaussian hb hm hW hX
  radial_source_change := waveStage_gr_change hU g c u w q gaussian hb hm hW hX
  pressure_eq := by
    unfold pressureChange
    abel
  axial_change := waveStage_axial_change hU g c u w q gaussian hb hm hW hX hp hδp

namespace ReconstructedWaveStageResponse

/-- When the source state and wave are the fields assembled by a signed family,
the package's covariance identity contains the exact cross tensor and retained
remainder from `ExactCovariance`. -/
theorem covariance_eq_cross_add_remainder
    {U : Set (PressureStream.Lift S)}
    {g : VariableGaugeMean.GaugeData S}
    {c : Context (PressureStream.Lift S)}
    {u : State (PressureStream.Lift S)}
    {w : Oscillation (PressureStream.Lift S)}
    {q : OscillatoryScalar (PressureStream.Lift S)}
    {gaussian : Oscillation (PressureStream.Lift S)}
    (R : ReconstructedWaveStageResponse (U := U) g c u w q gaussian)
    {s : WeightedClasses.StripData (PressureStream.Lift S)}
    {P : ι → ℕ → PressureStream.Lift S → ℝ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f)
    (hold : u.oscillation = oldField f a)
    (hwave : w = tangentField f a + curlField f a) :
    (waveStage g c u w q gaussian).covariance =
      u.covariance + (crossTensor f a + remainderTensor f a) := by
  rw [R.covariance_eq, hold, hwave]
  change u.covariance + incrementTensor f a =
    u.covariance + (crossTensor f a + remainderTensor f a)
  rw [exact_covariance_split]

end ReconstructedWaveStageResponse

/- TODO(request differentiation): Implement
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`,
section "Lean instantiation and formalization strategy," Phases I–III.  Differentiate the
actual request-to-wave-to-reconstruction path built from
`SignedMeanGain.incrementTensor_split`, `SignedMeanGain.waveStage_gr_change`,
`SignedMeanGain.waveStage_axial_change`, and
`SignedMeanGain.native_physical_cross`; then instantiate the continuous-linear
maps `fullCompatibility`, `reducedResponse`, and
`hiddenResponse := fullCompatibility - reducedResponse`
without replacing the source state or pressure reconstruction. -/

end NavierStokes.CounterProof.Adapter
