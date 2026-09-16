import NavierStokes.CounterProof.Compatibility

/-!
# Reduced branches and their exact primitive defect

This module records the reduced-branch layer of the reconstruction subsystem.

The reduced solve is retained as a first-class object.  Full compatibility is
equivalent to vanishing of the hidden response, rather than being assumed from
reduced cancellation.

This module corresponds to the exact reduced-branch defect proposition in the
signed-mean companion note.  It makes no smallness or tail claim: those enter
later through `QuantitativeObstruction` and `ResidualExposure`.
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
  /-- Active tangent chosen by the reduced solver. -/
  active : Active
  /-- Exact cancellation of the target in the reduced observation block. -/
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

/-- The full response is the requested target plus the exact hidden defect. -/
theorem full_eq_target_add_defect
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (B : ReducedBranch K target) :
    K.fullCompatibility B.active = target + B.defect := by
  rw [K.fullCompatibility_apply]
  simp only [B.reduced_eq, defect, K.hiddenResponse_apply]

/-- The exact reduced-branch defect identity from the companion note, stated
as a residual rather than as an affine decomposition. -/
theorem exact_reduced_branch_defect
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (B : ReducedBranch K target) :
    K.fullCompatibility B.active - target = B.defect := by
  rw [B.full_eq_target_add_defect]
  abel

/-- Reduced cancellation is full compatibility exactly when the hidden defect
vanishes. -/
theorem fullCompatible_iff_defect_eq_zero
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (B : ReducedBranch K target) :
    B.FullCompatible ↔ B.defect = 0 := by
  rw [FullCompatible, B.full_eq_target_add_defect]
  simp

end ReducedBranch

end NavierStokes.CounterProof
