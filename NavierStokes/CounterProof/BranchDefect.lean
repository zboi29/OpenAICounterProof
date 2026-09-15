import NavierStokes.CounterProof.Compatibility

/-!
# Reduced branches and their exact primitive defect

The reduced solve is retained as a first-class object.  Full compatibility is
equivalent to vanishing of the hidden response, rather than being assumed from
reduced cancellation.
-/

noncomputable section

namespace NavierStokes.CounterProof

variable {Active Hidden Obs Constraint : Type*}
  [NormedAddCommGroup Active] [NormedSpace ℝ Active]
  [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]

/-- A branch selected by solving only the reduced response equation. -/
structure ReducedBranch
    (K : CompatibilityBlocks Active Hidden Obs Constraint) (target : Obs) where
  active : Active
  reduced_eq : K.reducedResponse active = target

namespace ReducedBranch

/-- The exact full primitive defect of a reduced branch. -/
def defect {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (B : ReducedBranch K target) : Obs :=
  K.hiddenResponse B.active

/-- Full compatibility with the same target used by the reduced solve. -/
def FullCompatible {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (B : ReducedBranch K target) : Prop :=
  K.fullCompatibility B.active = target

theorem full_eq_target_add_defect
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (B : ReducedBranch K target) :
    K.fullCompatibility B.active = target + B.defect := by
  rw [K.fullCompatibility_apply]
  simp only [B.reduced_eq, defect, K.hiddenResponse_apply]

theorem fullCompatible_iff_defect_eq_zero
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (B : ReducedBranch K target) :
    B.FullCompatible ↔ B.defect = 0 := by
  rw [FullCompatible, B.full_eq_target_add_defect]
  simp

end ReducedBranch

end NavierStokes.CounterProof
