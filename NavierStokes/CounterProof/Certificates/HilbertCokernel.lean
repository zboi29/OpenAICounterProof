import NavierStokes.CounterProof.Certificates.DualCertificate
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hilbert-space cokernel witnesses

This module connects the functional certificates used by the counter-proof
core to the adjoint-null and near-cokernel language of the research notes.
The main estimate is quantitative and does not require exact range failure.
-/

noncomputable section

open scoped InnerProductSpace

namespace NavierStokes.CounterProof

variable {Domain Obs : Type*}
  [NormedAddCommGroup Domain] [InnerProductSpace ℝ Domain] [CompleteSpace Domain]
  [NormedAddCommGroup Obs] [InnerProductSpace ℝ Obs] [CompleteSpace Obs]

/-- Hilbert-space range defect: the norm of the target component orthogonal to
the compatible response range. -/
def hilbertRangeDefect [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs) : ℝ :=
  ‖(operator.rangeᗮ).orthogonalProjectionOnto target‖

omit [CompleteSpace Domain] [CompleteSpace Obs] in
/-- In finite dimensions the range defect vanishes exactly on the operator
range. -/
theorem hilbertRangeDefect_eq_zero_iff [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs) :
    hilbertRangeDefect operator target = 0 ↔ target ∈ Set.range operator := by
  rw [hilbertRangeDefect, norm_eq_zero,
    Submodule.orthogonalProjectionOnto_eq_zero_iff]
  have hdouble : operator.rangeᗮᗮ = operator.range := by simp
  rw [hdouble]
  rfl

/-- The continuous dual functional represented by a Hilbert-space vector. -/
def cokernelFunctional (η : Obs) : Obs →L[ℝ] ℝ :=
  innerSL ℝ η

omit [CompleteSpace Obs] in
@[simp]
theorem cokernelFunctional_apply (η target : Obs) :
    cokernelFunctional η target = ⟪η, target⟫_ℝ := by
  rfl

/-- Composing the represented functional with an operator is represented by
the adjoint image of the same vector. -/
theorem cokernelFunctional_comp (operator : Domain →L[ℝ] Obs) (η : Obs) :
    (cokernelFunctional η).comp operator = cokernelFunctional (operator.adjoint η) := by
  exact ContinuousLinearMap.innerSL_apply_comp η operator

/-- The response size in direction `η` is exactly the norm of the adjoint
image. -/
theorem norm_cokernelFunctional_comp (operator : Domain →L[ℝ] Obs) (η : Obs) :
    ‖(cokernelFunctional η).comp operator‖ = ‖operator.adjoint η‖ := by
  rw [cokernelFunctional_comp, cokernelFunctional]
  exact innerSL_apply_norm ℝ _

/-- Exact adjoint-kernel membership is equivalent to annihilating the entire
operator range. -/
theorem annihilates_range_iff_adjoint_eq_zero
    (operator : Domain →L[ℝ] Obs) (η : Obs) :
    (∀ x, ⟪η, operator x⟫_ℝ = 0) ↔ operator.adjoint η = 0 := by
  constructor
  · intro h
    refine ext_inner_right ℝ fun x => ?_
    rw [operator.adjoint_inner_left x η, h x, inner_zero_left]
  · intro h x
    rw [← operator.adjoint_inner_left x η, h, inner_zero_left]

/-- An exact cokernel vector detecting a target excludes that target from the
operator range. -/
theorem target_not_mem_range_of_adjoint_eq_zero
    (operator : Domain →L[ℝ] Obs) {target η : Obs}
    (hadjoint : operator.adjoint η = 0) (hdetects : ⟪η, target⟫_ℝ ≠ 0) :
    target ∉ Set.range operator := by
  rintro ⟨x, rfl⟩
  apply hdetects
  rw [← operator.adjoint_inner_left x η, hadjoint, inner_zero_left]

/-- Near-cokernel reverse-triangle estimate.  It is the shared inequality
behind the quantitative lift bound and the Version 1.1 joint obstruction. -/
theorem near_cokernel_residual_lower_bound
    (operator : Domain →L[ℝ] Obs) (η target : Obs) (x : Domain) :
    |⟪η, target⟫_ℝ| - ‖operator.adjoint η‖ * ‖x‖ ≤
      |⟪η, target - operator x⟫_ℝ| := by
  calc
    |⟪η, target⟫_ℝ| - ‖operator.adjoint η‖ * ‖x‖
        ≤ |⟪η, target⟫_ℝ| - |⟪η, operator x⟫_ℝ| := by
          gcongr
          rw [← operator.adjoint_inner_left x η]
          calc
            |⟪operator.adjoint η, x⟫_ℝ| = ‖⟪operator.adjoint η, x⟫_ℝ‖ :=
              (Real.norm_eq_abs _).symm
            _ ≤ ‖operator.adjoint η‖ * ‖x‖ :=
              norm_inner_le_norm (operator.adjoint η) x
    _ ≤ |⟪η, target - operator x⟫_ℝ| := by
      rw [inner_sub_right]
      exact abs_sub_abs_le_abs_sub _ _

/-- Every exact lift pays the target component divided by the adjoint response
in the tested direction, stated without division so the exact-cokernel case is
included. -/
theorem exact_lift_product_lower_bound
    (operator : Domain →L[ℝ] Obs) (η target : Obs) (x : Domain)
    (hsolve : operator x = target) :
    |⟪η, target⟫_ℝ| ≤ ‖operator.adjoint η‖ * ‖x‖ := by
  rw [← hsolve, ← operator.adjoint_inner_left x η]
  calc
    |⟪operator.adjoint η, x⟫_ℝ| = ‖⟪operator.adjoint η, x⟫_ℝ‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ‖operator.adjoint η‖ * ‖x‖ := norm_inner_le_norm _ _

end NavierStokes.CounterProof
