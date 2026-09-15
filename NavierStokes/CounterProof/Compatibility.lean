import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Primitive compatibility blocks

This module formalizes the full constrained linear response from Phase I of the
signed-mean companion note.  The hidden response is defined by subtraction from
the full response, so later source-specific expansions cannot omit a state
channel by construction.
-/

noncomputable section

namespace NavierStokes.CounterProof

variable {Active Hidden Obs Constraint : Type*}
  [NormedAddCommGroup Active] [NormedSpace ℝ Active]
  [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]

/-- Linearized active, hidden, observational, and constraint blocks for an
actual reconstructed state. -/
structure CompatibilityBlocks
    (Active Hidden Obs Constraint : Type*)
    [NormedAddCommGroup Active] [NormedSpace ℝ Active]
    [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
    [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
    [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint] where
  constraintActive : Active →L[ℝ] Constraint
  constraintHidden : Hidden →L[ℝ] Constraint
  reducedResponse : Active →L[ℝ] Obs
  hiddenObservation : Hidden →L[ℝ] Obs
  reconstructDeriv : Active →L[ℝ] Hidden
  constraint_lift : constraintHidden.comp reconstructDeriv = -constraintActive

namespace CompatibilityBlocks

/-- The observation derivative along the source's constrained reconstruction. -/
def fullCompatibility
    (K : CompatibilityBlocks Active Hidden Obs Constraint) : Active →L[ℝ] Obs :=
  K.reducedResponse + K.hiddenObservation.comp K.reconstructDeriv

/-- Everything in the full response not visible to the selected reduced block. -/
def hiddenResponse
    (K : CompatibilityBlocks Active Hidden Obs Constraint) : Active →L[ℝ] Obs :=
  K.fullCompatibility - K.reducedResponse

@[simp]
theorem fullCompatibility_apply (K : CompatibilityBlocks Active Hidden Obs Constraint)
    (a : Active) :
    K.fullCompatibility a =
      K.reducedResponse a + K.hiddenObservation (K.reconstructDeriv a) := by
  rfl

theorem hiddenResponse_eq_reconstructed
    (K : CompatibilityBlocks Active Hidden Obs Constraint) :
    K.hiddenResponse = K.hiddenObservation.comp K.reconstructDeriv := by
  ext a
  simp [hiddenResponse, fullCompatibility]

@[simp]
theorem hiddenResponse_apply (K : CompatibilityBlocks Active Hidden Obs Constraint)
    (a : Active) :
    K.hiddenResponse a = K.hiddenObservation (K.reconstructDeriv a) := by
  rw [K.hiddenResponse_eq_reconstructed]
  rfl

theorem fullCompatibility_eq_reduced_add_hidden
    (K : CompatibilityBlocks Active Hidden Obs Constraint) :
    K.fullCompatibility = K.reducedResponse + K.hiddenResponse := by
  ext a
  simp

theorem reconstructed_tangent_is_constrained
    (K : CompatibilityBlocks Active Hidden Obs Constraint) (a : Active) :
    K.constraintHidden (K.reconstructDeriv a) = -K.constraintActive a := by
  have h := congrArg (fun L : Active →L[ℝ] Constraint => L a) K.constraint_lift
  simpa using h

end CompatibilityBlocks

end NavierStokes.CounterProof
