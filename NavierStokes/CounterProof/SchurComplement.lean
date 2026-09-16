import NavierStokes.CounterProof.Compatibility

/-!
# Constrained reconstruction and Schur complement

This module derives the compatibility operator from the derivative of the
actual reconstruction.  When the hidden constraint block is continuously
invertible, the derivative and full response reduce to their exact Schur
forms.  Separate representative-independence results expose the kernel
condition needed before using a generalized inverse or another gauge.

The equivalence `hiddenConstraint` is evidence that the concrete hidden block
is invertible; `hhidden` identifies it with the block stored in
`CompatibilityBlocks`.  No Moore–Penrose inverse is introduced here.  A
source-specific pseudoinverse adapter must separately establish its gauge and
the kernel-annihilation condition proved below.
-/

noncomputable section

namespace NavierStokes.CounterProof

variable {Active Hidden Obs Constraint : Type*}
  [NormedAddCommGroup Active] [NormedSpace ℝ Active]
  [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]

namespace CompatibilityBlocks

/-- Invertibility of the hidden constraint block uniquely determines the
derivative of the source reconstruction as `−D⁻¹ ∘ G`. -/
theorem reconstructDeriv_eq_schur
    (K : CompatibilityBlocks Active Hidden Obs Constraint)
    (hiddenConstraint : Hidden ≃L[ℝ] Constraint)
    (hhidden : hiddenConstraint.toContinuousLinearMap = K.constraintHidden) :
    K.reconstructDeriv =
      -(hiddenConstraint.symm.toContinuousLinearMap.comp K.constraintActive) := by
  ext active
  apply hiddenConstraint.injective
  have hconstraint := K.reconstructed_tangent_is_constrained active
  rw [← hhidden] at hconstraint
  simpa using hconstraint

/-- Exact Schur-complement formula for the full reconstructed observation
response: `Comp = Red − P ∘ D⁻¹ ∘ G`. -/
theorem fullCompatibility_eq_schur
    (K : CompatibilityBlocks Active Hidden Obs Constraint)
    (hiddenConstraint : Hidden ≃L[ℝ] Constraint)
    (hhidden : hiddenConstraint.toContinuousLinearMap = K.constraintHidden) :
    K.fullCompatibility = K.reducedResponse -
      (K.hiddenObservation.comp hiddenConstraint.symm.toContinuousLinearMap).comp
        K.constraintActive := by
  rw [fullCompatibility, K.reconstructDeriv_eq_schur hiddenConstraint hhidden]
  ext active
  simp [sub_eq_add_neg]

/-- The hidden response itself is the negative Schur correction. -/
theorem hiddenResponse_eq_schur_correction
    (K : CompatibilityBlocks Active Hidden Obs Constraint)
    (hiddenConstraint : Hidden ≃L[ℝ] Constraint)
    (hhidden : hiddenConstraint.toContinuousLinearMap = K.constraintHidden) :
    K.hiddenResponse =
      -(K.hiddenObservation.comp hiddenConstraint.symm.toContinuousLinearMap).comp
        K.constraintActive := by
  rw [K.hiddenResponse_eq_reconstructed,
    K.reconstructDeriv_eq_schur hiddenConstraint hhidden]
  ext active
  simp

/-- Hidden representatives with the same constraint value have the same
observation exactly when the observation kills homogeneous hidden directions.
This is the precise `P(ker D) = {0}` criterion required for gauge-independent
use of a generalized inverse. -/
theorem hidden_observation_rep_independent_iff
    (K : CompatibilityBlocks Active Hidden Obs Constraint) :
    (∀ hidden₁ hidden₂,
        K.constraintHidden hidden₁ = K.constraintHidden hidden₂ →
          K.hiddenObservation hidden₁ = K.hiddenObservation hidden₂) ↔
      ∀ hidden, K.constraintHidden hidden = 0 → K.hiddenObservation hidden = 0 := by
  constructor
  · intro hindependent hidden hconstraint
    have hsame : K.constraintHidden hidden = K.constraintHidden 0 := by
      simpa using hconstraint
    simpa using hindependent hidden 0 hsame
  · intro hkernel hidden₁ hidden₂ hconstraint
    have hconstraint_sub : K.constraintHidden (hidden₁ - hidden₂) = 0 := by
      rw [map_sub, hconstraint, sub_self]
    have hobservation_sub := hkernel (hidden₁ - hidden₂) hconstraint_sub
    rw [map_sub, sub_eq_zero] at hobservation_sub
    exact hobservation_sub

end CompatibilityBlocks

end NavierStokes.CounterProof
