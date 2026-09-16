import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Primitive compatibility blocks

This module formalizes the full constrained linear response from Phase I of the
signed-mean companion note.  The hidden response is defined by subtraction from
the full response, so later source-specific expansions cannot omit a state
channel by construction.

`Active` contains the coordinates selected by the reduced solve, `Hidden`
contains reconstructed coordinates, `Obs` is the physical observation space,
and `Constraint` contains the linearized reconstruction equations.  Concrete
signed-mean work should instantiate these spaces from the imported source state
rather than treating this abstract block decomposition as a surrogate model.
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
  /-- Constraint response produced directly by an active tangent. -/
  constraintActive : Active →L[ℝ] Constraint
  /-- Constraint response produced by a hidden-state tangent. -/
  constraintHidden : Hidden →L[ℝ] Constraint
  /-- Observation block used by the reduced branch selection. -/
  reducedResponse : Active →L[ℝ] Obs
  /-- Observation of reconstructed hidden-state variation. -/
  hiddenObservation : Hidden →L[ℝ] Obs
  /-- Derivative of the reconstruction path actually used by the source. -/
  reconstructDeriv : Active →L[ℝ] Hidden
  /-- Differentiated reconstruction compatibility: hidden variation cancels
  the active constraint variation. -/
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

/-- Pointwise expansion of the full compatibility response. -/
@[simp]
theorem fullCompatibility_apply (K : CompatibilityBlocks Active Hidden Obs Constraint)
    (a : Active) :
    K.fullCompatibility a =
      K.reducedResponse a + K.hiddenObservation (K.reconstructDeriv a) := by
  rfl

/-- The subtraction-defined hidden response equals the observation of the
actual reconstruction derivative. -/
theorem hiddenResponse_eq_reconstructed
    (K : CompatibilityBlocks Active Hidden Obs Constraint) :
    K.hiddenResponse = K.hiddenObservation.comp K.reconstructDeriv := by
  ext a
  simp [hiddenResponse, fullCompatibility]

/-- Pointwise form of `hiddenResponse_eq_reconstructed`. -/
@[simp]
theorem hiddenResponse_apply (K : CompatibilityBlocks Active Hidden Obs Constraint)
    (a : Active) :
    K.hiddenResponse a = K.hiddenObservation (K.reconstructDeriv a) := by
  rw [K.hiddenResponse_eq_reconstructed]
  rfl

/-- Canonical decomposition `full = reduced + hidden`. -/
theorem fullCompatibility_eq_reduced_add_hidden
    (K : CompatibilityBlocks Active Hidden Obs Constraint) :
    K.fullCompatibility = K.reducedResponse + K.hiddenResponse := by
  ext a
  simp

/-- Every tangent produced by `reconstructDeriv` satisfies the differentiated
constraint equation. -/
theorem reconstructed_tangent_is_constrained
    (K : CompatibilityBlocks Active Hidden Obs Constraint) (a : Active) :
    K.constraintHidden (K.reconstructDeriv a) = -K.constraintActive a := by
  have h := congrArg (fun L : Active →L[ℝ] Constraint => L a) K.constraint_lift
  simpa using h

end CompatibilityBlocks

end NavierStokes.CounterProof
