import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Affine tangent-lift criterion

This module formalizes the first-order range criterion from the general
primitive-liftability note.  It separates the inhomogeneous constraint drift
from the homogeneous compatibility operator and proves that the resulting
range test is independent of the chosen particular constrained tangent.

The result is deliberately affine: `constraintDrift` and `observationDrift`
represent explicit time or parameter derivatives, while the range operator is
the observation derivative restricted to `ker constraint`.  The theorem
asserts existence of a first-order jet only; it does not assert integration to
a nonlinear path or control of a later correction tail.
-/

noncomputable section

namespace NavierStokes.CounterProof

variable {State Constraint Obs : Type*}
  [NormedAddCommGroup State] [NormedSpace ℝ State]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]

/-- The observation derivative restricted to homogeneous constrained
tangents.  This is the centralized compatibility operator from the general
research note. -/
def homogeneousCompatibility
    (constraint : State →L[ℝ] Constraint) (observe : State →L[ℝ] Obs) :
    constraint.ker →L[ℝ] Obs :=
  observe.domRestrict constraint.ker

/-- The observation component still to be supplied after choosing a particular
solution of the affine constraint equation.  Changing that particular solution
changes this vector by an element of the homogeneous compatibility range. -/
def affineCompatibilityTarget
    (observe : State →L[ℝ] Obs) (observationDrift target : Obs)
    (particular : State) : Obs :=
  target - observationDrift - observe particular

/-- A first-order state tangent satisfying both the affine constraint and the
requested observation equation.  This predicate is the Lean form of the two
differentiated equations in the affine tangent-lift criterion. -/
def IsAdmissibleFirstOrderLift
    (constraint : State →L[ℝ] Constraint) (observe : State →L[ℝ] Obs)
    (constraintDrift : Constraint) (observationDrift target : Obs)
    (stateTangent : State) : Prop :=
  constraint stateTangent = -constraintDrift ∧
    observe stateTangent = target - observationDrift

/-- Affine tangent-lift criterion: an admissible first-order lift exists
exactly when the residual target belongs to the range of the observation map
on homogeneous constrained tangents.  The forward proof subtracts the supplied
particular tangent; the reverse proof adds a homogeneous range preimage. -/
theorem admissible_first_order_lift_iff_mem_range
    (constraint : State →L[ℝ] Constraint) (observe : State →L[ℝ] Obs)
    (constraintDrift : Constraint) (observationDrift target : Obs)
    (particular : State) (hparticular : constraint particular = -constraintDrift) :
    (∃ stateTangent,
      IsAdmissibleFirstOrderLift constraint observe constraintDrift
        observationDrift target stateTangent) ↔
      affineCompatibilityTarget observe observationDrift target particular ∈
        Set.range (homogeneousCompatibility constraint observe) := by
  constructor
  · rintro ⟨stateTangent, hconstraint, hobserve⟩
    let homogeneous : constraint.ker :=
      ⟨stateTangent - particular, by
        change constraint (stateTangent - particular) = 0
        rw [map_sub, hconstraint, hparticular]
        abel⟩
    refine ⟨homogeneous, ?_⟩
    change observe (stateTangent - particular) =
      target - observationDrift - observe particular
    rw [map_sub, hobserve]
  · rintro ⟨homogeneous, hhomogeneous⟩
    refine ⟨particular + homogeneous, ?_, ?_⟩
    · rw [map_add, hparticular]
      have hzero : constraint (homogeneous : State) = 0 := homogeneous.property
      rw [hzero, add_zero]
    · rw [map_add]
      change observe particular +
          homogeneousCompatibility constraint observe homogeneous =
        target - observationDrift
      rw [hhomogeneous]
      simp only [affineCompatibilityTarget]
      abel

/-- Changing the particular solution of the affine constraint equation does
not change the truth of the compatibility range test. -/
theorem affine_range_condition_independent_of_particular
    (constraint : State →L[ℝ] Constraint) (observe : State →L[ℝ] Obs)
    (constraintDrift : Constraint) (observationDrift target : Obs)
    (particular₁ particular₂ : State)
    (hparticular₁ : constraint particular₁ = -constraintDrift)
    (hparticular₂ : constraint particular₂ = -constraintDrift) :
    affineCompatibilityTarget observe observationDrift target particular₁ ∈
        Set.range (homogeneousCompatibility constraint observe) ↔
      affineCompatibilityTarget observe observationDrift target particular₂ ∈
        Set.range (homogeneousCompatibility constraint observe) := by
  rw [← admissible_first_order_lift_iff_mem_range constraint observe constraintDrift
      observationDrift target particular₁ hparticular₁]
  exact admissible_first_order_lift_iff_mem_range constraint observe constraintDrift
    observationDrift target particular₂ hparticular₂

end NavierStokes.CounterProof
