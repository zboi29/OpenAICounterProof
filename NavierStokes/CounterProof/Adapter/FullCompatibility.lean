import NavierStokes.CounterProof.Adapter.RequestDifferential
import NavierStokes.CounterProof.Reconstruction.BranchDefect

/-!
# Full reconstructed compatibility adapter

This module constructs compatibility blocks from an already differentiated
source reconstruction and proves that defining the hidden channel by
subtraction recovers every reconstructed hidden observation.  Source adapters
use the product hidden space for covariance, theta, radial-source, pressure,
and axial-response tangents.

## Manuscript correspondence

The abstract block construction is Theorem 5.1 (`thm:schur`) and
Lean-instantiation Phase I of
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`.
The source-specific definitions below implement §3.4 "Physical tangential
observation", equations `eq:A=B+H`--`eq:Hdef`, and Proposition 4.2
(`prop:fullresponse`): the reduced pair is the requested removed bump, while
the hidden pair is the exact theta remainder and the exact axial remainder
including `dz pressureChange`.  The pointwise subtraction lemma is the
finite-stage nonlinear precursor of `Hidden := Comp - Red` in Phase III;
later differentiation may reuse it without reconstructing the observation
split from scratch.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

open NavierStokes.CounterProof
open SignedMeanGain CorrectionState MeanIncrementBounds

variable {Active Hidden Obs Constraint : Type*}
  [NormedAddCommGroup Active] [NormedSpace ℝ Active]
  [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]

/-- Two-component θ/axial observation `Obs` from companion-note §3.4. -/
abbrev TangentialObservation := SignedWaveUpdate.Vec2

/-- Literal averaged θ/axial residual pair of a reconstructed source state;
this is the nonlinear source object differentiated in Proposition 4.2. -/
noncomputable def averagedTangentialObservation
    (c : Context SignedMeanGain.Point) (v : State SignedMeanGain.Point)
    (n : ℕ) (x : SignedMeanGain.Point) : TangentialObservation :=
  ![StateMomentBalances.meanBar (v.thetaResidual c) n x,
    StateMomentBalances.meanBar (v.axialResidual c) n x]

/-- The two reduced targets canceled by the native signed cross request,
before the explicit derivative-level identification with `Red` in `eq:Bdef`. -/
noncomputable def reducedTangentialTarget
    (G : Geometry) (c : Context SignedMeanGain.Point)
    (u : State SignedMeanGain.Point) (n : ℕ) (x : SignedMeanGain.Point) :
    TangentialObservation :=
  ![removedBump G 2 (u.thetaResidual c) n x,
    removedBump G 1 (u.axialResidual c) n x]

/-- Complete retained θ/axial response after reduced cross cancellation.  It
is the nonlinear precursor of `Hidden` in `eq:Hdef`; the axial coordinate
contains the reconstructed pressure change literally. -/
noncomputable def hiddenTangentialRemainder
    (G : Geometry) (S E : SignedMeanGain.Tensor SignedMeanGain.Point)
    (pressure : SignedMeanGain.ScalarField SignedMeanGain.Point)
    (n : ℕ) (x : SignedMeanGain.Point) : TangentialObservation :=
  ![StateMomentBalances.meanBar (thetaRemainderField G S E) n x,
    StateMomentBalances.meanBar (axialRemainderField G S E pressure) n x]

/-- Source-grounded full response decomposition at an actual band and point.
This is a direct adapter of `SignedMeanGain.averaged_residual_decomposition`,
the Lean identity cited in Proposition 4.2 of the companion note. -/
theorem source_averaged_response_eq_reduced_add_hidden
    (G : Geometry) (c : Context SignedMeanGain.Point)
    (u : State SignedMeanGain.Point) (w : Oscillation SignedMeanGain.Point)
    (q : OscillatoryScalar SignedMeanGain.Point)
    (gaussian : Oscillation SignedMeanGain.Point)
    (H : LocalData G c u w q gaussian)
    (S E : SignedMeanGain.Tensor SignedMeanGain.Point)
    (hS : ∀ i j, MovingField G (S i j))
    (hE : ∀ i j, MovingField G (E i j))
    (hX : covarianceIncrement u.oscillation w = S + E)
    (hcrossθ : Agree G.strip.domain (StateMomentBalances.meanBar (S 0 1))
      (physicalSigma G 2 (u.thetaResidual c)))
    (hcrossz : Agree G.strip.domain (StateMomentBalances.meanBar (S 0 2))
      (physicalSigma G 1 (u.axialResidual c)))
    (n : ℕ) {x : SignedMeanGain.Point} (hx : x ∈ G.strip.domain) :
    averagedTangentialObservation c (waveStage G.gauge c u w q gaussian) n x =
      reducedTangentialTarget G c u n x +
        hiddenTangentialRemainder G S E
          (pressureChange G.gauge c u w q gaussian) n x := by
  obtain ⟨hθ, hz⟩ := averaged_residual_decomposition
    G c u w q gaussian H S E hS hE hX hcrossθ hcrossz
  funext i
  fin_cases i
  · simpa [averagedTangentialObservation, reducedTangentialTarget,
      hiddenTangentialRemainder] using hθ n hx
  · simpa [averagedTangentialObservation, reducedTangentialTarget,
      hiddenTangentialRemainder] using hz n hx

/-- Exact source defect after subtracting the reduced target.  This helper is
the pointwise bridge used to instantiate Proposition 5.2 (`prop:defect`); its
proof is only additive cancellation after the preceding source theorem. -/
theorem source_averaged_response_sub_reduced_eq_hidden
    (G : Geometry) (c : Context SignedMeanGain.Point)
    (u : State SignedMeanGain.Point) (w : Oscillation SignedMeanGain.Point)
    (q : OscillatoryScalar SignedMeanGain.Point)
    (gaussian : Oscillation SignedMeanGain.Point)
    (H : LocalData G c u w q gaussian)
    (S E : SignedMeanGain.Tensor SignedMeanGain.Point)
    (hS : ∀ i j, MovingField G (S i j))
    (hE : ∀ i j, MovingField G (E i j))
    (hX : covarianceIncrement u.oscillation w = S + E)
    (hcrossθ : Agree G.strip.domain (StateMomentBalances.meanBar (S 0 1))
      (physicalSigma G 2 (u.thetaResidual c)))
    (hcrossz : Agree G.strip.domain (StateMomentBalances.meanBar (S 0 2))
      (physicalSigma G 1 (u.axialResidual c)))
    (n : ℕ) {x : SignedMeanGain.Point} (hx : x ∈ G.strip.domain) :
    averagedTangentialObservation c (waveStage G.gauge c u w q gaussian) n x -
        reducedTangentialTarget G c u n x =
      hiddenTangentialRemainder G S E
        (pressureChange G.gauge c u w q gaussian) n x := by
  rw [source_averaged_response_eq_reduced_add_hidden
    G c u w q gaussian H S E hS hE hX hcrossθ hcrossz n hx]
  abel

/-- Pointwise source consequence of Proposition 5.2 (`prop:defect`): a
nonzero complete θ/axial remainder rules out identifying the actual averaged
response with the reduced target.  This helper is conditional; it does not
assert nonvanishing until a concrete finite-jet witness supplies it. -/
theorem source_averaged_response_ne_reduced_of_hidden_ne_zero
    (G : Geometry) (c : Context SignedMeanGain.Point)
    (u : State SignedMeanGain.Point) (w : Oscillation SignedMeanGain.Point)
    (q : OscillatoryScalar SignedMeanGain.Point)
    (gaussian : Oscillation SignedMeanGain.Point)
    (H : LocalData G c u w q gaussian)
    (S E : SignedMeanGain.Tensor SignedMeanGain.Point)
    (hS : ∀ i j, MovingField G (S i j))
    (hE : ∀ i j, MovingField G (E i j))
    (hX : covarianceIncrement u.oscillation w = S + E)
    (hcrossθ : Agree G.strip.domain (StateMomentBalances.meanBar (S 0 1))
      (physicalSigma G 2 (u.thetaResidual c)))
    (hcrossz : Agree G.strip.domain (StateMomentBalances.meanBar (S 0 2))
      (physicalSigma G 1 (u.axialResidual c)))
    (n : ℕ) {x : SignedMeanGain.Point} (hx : x ∈ G.strip.domain)
    (hhidden : hiddenTangentialRemainder G S E
      (pressureChange G.gauge c u w q gaussian) n x ≠ 0) :
    averagedTangentialObservation c (waveStage G.gauge c u w q gaussian) n x ≠
      reducedTangentialTarget G c u n x := by
  intro heq
  have hdefect := source_averaged_response_sub_reduced_eq_hidden
    G c u w q gaussian H S E hS hE hX hcrossθ hcrossz n hx
  rw [heq, sub_self] at hdefect
  exact hhidden hdefect.symm

/-- Construct the concrete compatibility package after differentiating the
source constraint and observation maps. -/
def compatibilityBlocks
    (constraintActive : Active →L[ℝ] Constraint)
    (constraintHidden : Hidden →L[ℝ] Constraint)
    (reducedResponse : Active →L[ℝ] Obs)
    (hiddenObservation : Hidden →L[ℝ] Obs)
    (reconstructDeriv : Active →L[ℝ] Hidden)
    (constraint_lift : constraintHidden.comp reconstructDeriv = -constraintActive) :
    CompatibilityBlocks Active Hidden Obs Constraint where
  constraintActive := constraintActive
  constraintHidden := constraintHidden
  reducedResponse := reducedResponse
  hiddenObservation := hiddenObservation
  reconstructDeriv := reconstructDeriv
  constraint_lift := constraint_lift

/-- The subtraction-defined hidden response contains exactly the reconstructed
hidden observation, so pressure and residual channels cannot be omitted after
they are included in `Hidden`. -/
theorem compatibility_hidden_exact
    (K : CompatibilityBlocks Active Hidden Obs Constraint) :
    K.fullCompatibility - K.reducedResponse =
      K.hiddenObservation.comp K.reconstructDeriv := by
  simpa only [CompatibilityBlocks.hiddenResponse] using
    K.hiddenResponse_eq_reconstructed

/-- Pointwise full-response decomposition used by both counter-proof branches. -/
theorem compatibility_full_apply
    (K : CompatibilityBlocks Active Hidden Obs Constraint) (a : Active) :
    K.fullCompatibility a =
      K.reducedResponse a + K.hiddenObservation (K.reconstructDeriv a) :=
  K.fullCompatibility_apply a

/-- A reduced solution has exactly the reconstructed hidden observation as its
full primitive defect. -/
theorem reduced_branch_defect_eq_reconstructed
    (K : CompatibilityBlocks Active Hidden Obs Constraint) (target : Obs)
    (B : ReducedBranch K target) :
    B.defect = K.hiddenObservation (K.reconstructDeriv B.active) := by
  exact K.hiddenResponse_apply B.active

end NavierStokes.CounterProof.Adapter
