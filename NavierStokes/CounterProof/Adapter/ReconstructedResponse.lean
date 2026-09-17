import NavierStokes.CounterProof.Adapter.ExactCovariance

/-!
# Reconstructed wave-stage response adapter

The actual signed wave stage preserves the mean, recomputes covariance, and
reconstructs pressure before evaluating the axial residual.  This module
packages those imported identities as one proof object on the common slow
domain.  In particular, pressure feedback is a field of the package rather
than an optional later correction.

## Manuscript correspondence

The fields mirror §3.2 "Evaluated finite-jet constrained state" and §3.4
"Physical tangential observation" of
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`.
Their joint mathematical target is Proposition 4.2 (`prop:fullresponse`), especially
the radial-source chain `R₀(ΔW) → pressureChange → dz pressureChange`.
The constructor imports the exact source results `waveStage_mean`,
`waveStage_covariance`, `waveStage_theta_change`, `waveStage_gr_change`, and
`waveStage_axial_change`, as required by Lean-instantiation Phases I and III.
`covariance_eq_cross_add_remainder` is a composition helper connecting those
identities to Theorem 4.1; it is not an additional manuscript assumption.
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

/- TODO(source request differentiation; companion note §8, Phase I, lines
"differentiate the actual reconstruction path" and the §15 interface-checklist
rows "Hidden reconstruction" and "Radial source / pressure"):
`RequestDifferential` bundles the literal inverse solve and
`FullCompatibility` supplies the exact block algebra.  Differentiate the
complete request-to-`actualSignedBlock`-to-`waveStage`-to-`pressureChange` path
on the physical-scale data in `ActualSignedMeanBinding.lean`, then construct
its concrete `CompatibilityBlocks`.  Do not use either generic theorem that
requires `SignedMeanGain.NativeData`: `NativeDataObstruction` proves that the
required package cannot exist on `ActualInitialization.geometry`.  This is a
complete counter-proof of the pinned native route, not an obligation awaiting
further instantiation; endpoint dependency only transports it to another claim.
NativeData is not logically necessary for the compatibility branches or their
primary joint synthesis.  For the preferred pinned-source instantiation, use
the precisely scoped partition-factor/tail replacement inserted into
`CorrectionAnalyticStep.StepData.cross_tail`, then prove all remaining
reconstruction and mean-gain obligations directly.  This realizes
companion-note §8 Phases III–IV and supplies the complete response needed by
Theorem 6.1, Proposition 6.2, and Corollary 6.3. -/

end NavierStokes.CounterProof.Adapter
