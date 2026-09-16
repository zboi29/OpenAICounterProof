import Mathlib.Analysis.Calculus.VectorField

/-!
# Local lift curvature and hidden holonomy

This module formalizes the geometric layer of the general research note in a
local Banach chart.  A pair of lifted fields is required to project to the
chosen base fields, including at first derivative level.  The Lie bracket then
projects to the base bracket.  Consequently commuting base directions have a
vertical curvature, and nonzero curvature violates the integrability condition
that a concrete path-independent reconstruction must discharge.

The final section gives the note's exact three-coordinate holonomy loop.  Its
observable coordinates close exactly while the hidden coordinate changes by
`-ε²`; no asymptotic flow expansion is assumed.
-/

noncomputable section

namespace NavierStokes.CounterProof

open VectorField

variable {State Base : Type*}
  [NormedAddCommGroup State] [NormedSpace ℝ State]
  [NormedAddCommGroup Base] [NormedSpace ℝ Base]

/-- Two horizontal lifts in a local chart, together with the first-derivative
compatibility needed for Lie-bracket naturality. -/
structure HorizontalLiftPair (State Base : Type*)
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Base] [NormedSpace ℝ Base] where
  projection : State →L[ℝ] Base
  baseA : Base → Base
  baseB : Base → Base
  liftA : State → State
  liftB : State → State
  liftA_differentiable : Differentiable ℝ liftA
  liftB_differentiable : Differentiable ℝ liftB
  baseA_differentiable : Differentiable ℝ baseA
  baseB_differentiable : Differentiable ℝ baseB
  projectsA : ∀ x, projection (liftA x) = baseA (projection x)
  projectsB : ∀ x, projection (liftB x) = baseB (projection x)
  projectsDerivA : ∀ x v,
    projection (fderiv ℝ liftA x v) =
      fderiv ℝ baseA (projection x) (projection v)
  projectsDerivB : ∀ x v,
    projection (fderiv ℝ liftB x v) =
      fderiv ℝ baseB (projection x) (projection v)

namespace HorizontalLiftPair

/-- The vertical curvature of the selected horizontal pair. -/
def curvature (H : HorizontalLiftPair State Base) (x : State) : State :=
  lieBracket ℝ H.liftA H.liftB x

/-- The lifted Lie bracket projects exactly to the base Lie bracket. -/
theorem projection_curvature (H : HorizontalLiftPair State Base) (x : State) :
    H.projection (H.curvature x) =
      lieBracket ℝ H.baseA H.baseB (H.projection x) := by
  simp only [curvature, lieBracket, map_sub]
  rw [H.projectsDerivB x (H.liftA x), H.projectsDerivA x (H.liftB x),
    H.projectsA x, H.projectsB x]

/-- Commuting observed directions force the curvature into the vertical
kernel, even though the curvature itself may remain nonzero. -/
theorem curvature_mem_vertical (H : HorizontalLiftPair State Base) (x : State)
    (hcommutes : lieBracket ℝ H.baseA H.baseB (H.projection x) = 0) :
    H.curvature x ∈ H.projection.ker := by
  change H.projection (H.curvature x) = 0
  rw [H.projection_curvature, hcommutes]

/-- Vanishing-curvature integrability condition for the chosen horizontal pair
at a point.  A concrete reconstruction adapter must derive this condition from
its own mixed-derivative theorem. -/
def IsIntegrableAt (H : HorizontalLiftPair State Base) (x : State) : Prop :=
  H.curvature x = 0

/-- Nonzero curvature refutes the vanishing-curvature integrability
condition. -/
theorem not_integrable_of_curvature_ne_zero
    (H : HorizontalLiftPair State Base) (x : State)
    (hcurvature : H.curvature x ≠ 0) :
    ¬ H.IsIntegrableAt x :=
  hcurvature

end HorizontalLiftPair

namespace ExactHolonomy

/-- Local coordinates `(x,y,z)` with `z` the hidden vertical coordinate. -/
abbrev HolonomyState := (ℝ × ℝ) × ℝ

/-- The observable projection discards the hidden coordinate. -/
def observe (state : HolonomyState) : ℝ × ℝ := state.1

/-- Exact time-`ε` flow of `∂x + y ∂z`. -/
def flowA (ε : ℝ) (state : HolonomyState) : HolonomyState :=
  ((state.1.1 + ε, state.1.2), state.2 + ε * state.1.2)

/-- Exact time-`ε` flow of `∂y`. -/
def flowB (ε : ℝ) (state : HolonomyState) : HolonomyState :=
  ((state.1.1, state.1.2 + ε), state.2)

/-- The four-step commutator loop `+A,+B,-A,-B`. -/
def loop (ε : ℝ) (state : HolonomyState) : HolonomyState :=
  flowB (-ε) (flowA (-ε) (flowB ε (flowA ε state)))

/-- The observable coordinates return exactly after the commutator loop. -/
theorem observe_loop (ε : ℝ) (state : HolonomyState) :
    observe (loop ε state) = observe state := by
  ext <;> simp [observe, loop, flowA, flowB]

/-- The hidden coordinate acquires the exact displacement `-ε²`. -/
theorem hidden_loop (ε : ℝ) (state : HolonomyState) :
    (loop ε state).2 = state.2 - ε ^ 2 := by
  simp [loop, flowA, flowB]
  ring

/-- At the origin the loop is observably closed but physically displaced for
every nonzero step size. -/
theorem loop_origin_hidden_nonzero {ε : ℝ} (hε : ε ≠ 0) :
    loop ε ((0, 0), 0) ≠ ((0, 0), 0) := by
  intro h
  have hz := congrArg (fun state : HolonomyState => state.2) h
  rw [hidden_loop] at hz
  simp at hz
  exact hε hz

end ExactHolonomy

end NavierStokes.CounterProof
