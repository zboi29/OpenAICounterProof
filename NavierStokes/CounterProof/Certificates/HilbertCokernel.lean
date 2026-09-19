import NavierStokes.CounterProof.Certificates.DualCertificate
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hilbert-space cokernel witnesses

This module connects the functional certificates used by the counter-proof
core to the adjoint-null and near-cokernel language of the research notes.
The main estimate is quantitative and does not require exact range failure.

The canonical projection results below formalize the missing constructive
part of Proposition `prop:cokernel`, “Cokernel certificate for primitive
incompatibility”, in §4.2 of
`docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex`.  They turn a
positive Hilbert range defect into a unit adjoint-null direction whose target
pairing is exactly that defect.  Thus a source adapter may obtain the dual
direction from the full compatibility range instead of postulating an
unrelated functional.
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

/-- The canonical cokernel component of a target: its orthogonal projection
onto the orthogonal complement of the full compatible range.  This is the
vector denoted `P_{ker Comp*} β` in Proposition `prop:cokernel` of the general
research note. -/
def hilbertRangeDefectVector [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs) : Obs :=
  (operator.rangeᗮ).orthogonalProjectionOnto target

omit [CompleteSpace Domain] [CompleteSpace Obs] in
@[simp]
theorem norm_hilbertRangeDefectVector [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs) :
    ‖hilbertRangeDefectVector operator target‖ =
      hilbertRangeDefect operator target :=
  rfl

omit [CompleteSpace Domain] [CompleteSpace Obs] in
/-- The canonical range-defect vector is orthogonal to every compatible
response. -/
theorem hilbertRangeDefectVector_mem_orthogonal [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs) :
    hilbertRangeDefectVector operator target ∈ operator.rangeᗮ :=
  (operator.rangeᗮ).orthogonalProjectionOnto target |>.property

/-- Orthogonality of the canonical defect vector is exactly the adjoint-null
condition required by a cokernel certificate. -/
theorem adjoint_hilbertRangeDefectVector_eq_zero [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs) :
    operator.adjoint (hilbertRangeDefectVector operator target) = 0 := by
  refine ext_inner_right ℝ fun x => ?_
  rw [operator.adjoint_inner_left, inner_zero_left]
  exact Submodule.inner_left_of_mem_orthogonal
    (show operator x ∈ operator.range from ⟨x, rfl⟩)
    (hilbertRangeDefectVector_mem_orthogonal operator target)

omit [CompleteSpace Domain] [CompleteSpace Obs] in
/-- The canonical defect detects the target by its squared norm.  This is the
exact equality behind the dual range-defect formula, not merely a nonzero
pairing. -/
theorem inner_hilbertRangeDefectVector_target [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs) :
    ⟪hilbertRangeDefectVector operator target, target⟫_ℝ =
      hilbertRangeDefect operator target ^ 2 := by
  let η : operator.rangeᗮ :=
    (operator.rangeᗮ).orthogonalProjectionOnto target
  change ⟪(η : Obs), target⟫_ℝ = ‖(η : Obs)‖ ^ 2
  rw [← (operator.rangeᗮ).inner_orthogonalProjectionOnto_eq_of_mem_left η target]
  change ⟪(η : Obs), (η : Obs)⟫_ℝ = ‖(η : Obs)‖ ^ 2
  exact real_inner_self_eq_norm_sq _

/-- Normalize the canonical cokernel component.  Positivity of the range
defect is supplied separately to avoid an arbitrary choice in the compatible
case. -/
def normalizedRangeDefectDirection [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs) : Obs :=
  (hilbertRangeDefect operator target)⁻¹ •
    hilbertRangeDefectVector operator target

/-- A positive range defect canonically produces the unit dual witness from
Proposition `prop:cokernel`: it lies in `ker operator.adjoint` and its absolute
target pairing is exactly the range defect. -/
theorem normalizedRangeDefectDirection_spec [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs)
    (hdefect : 0 < hilbertRangeDefect operator target) :
    ‖normalizedRangeDefectDirection operator target‖ = 1 ∧
      operator.adjoint (normalizedRangeDefectDirection operator target) = 0 ∧
      |⟪normalizedRangeDefectDirection operator target, target⟫_ℝ| =
        hilbertRangeDefect operator target := by
  have hne : hilbertRangeDefect operator target ≠ 0 := ne_of_gt hdefect
  constructor
  · rw [normalizedRangeDefectDirection, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hdefect, norm_hilbertRangeDefectVector,
      inv_mul_cancel₀ hne]
  constructor
  · rw [normalizedRangeDefectDirection, map_smul,
      adjoint_hilbertRangeDefectVector_eq_zero, smul_zero]
  · rw [normalizedRangeDefectDirection, real_inner_smul_left,
      inner_hilbertRangeDefectVector_target]
    simp [abs_of_pos hdefect, hne, sq]

/-- Every candidate response misses the target by at least the exact Hilbert
range defect.  Together with `normalizedRangeDefectDirection_spec`, this is
the constructive lower-bound clause of general-note Proposition
`prop:cokernel`. -/
theorem hilbertRangeDefect_le_residual [FiniteDimensional ℝ Obs]
    (operator : Domain →L[ℝ] Obs) (target : Obs) (x : Domain) :
    hilbertRangeDefect operator target ≤ ‖target - operator x‖ := by
  by_cases hzero : hilbertRangeDefect operator target = 0
  · rw [hzero]
    exact norm_nonneg _
  · have hnonneg : 0 ≤ hilbertRangeDefect operator target := norm_nonneg _
    have hpos : 0 < hilbertRangeDefect operator target :=
      lt_of_le_of_ne hnonneg (Ne.symm hzero)
    let η := normalizedRangeDefectDirection operator target
    have hspec := normalizedRangeDefectDirection_spec operator target hpos
    have hresponse : ⟪η, operator x⟫_ℝ = 0 := by
      rw [← operator.adjoint_inner_left x η, hspec.2.1, inner_zero_left]
    have hdiff : ⟪η, target - operator x⟫_ℝ = ⟪η, target⟫_ℝ := by
      rw [inner_sub_right, hresponse, sub_zero]
    calc
      hilbertRangeDefect operator target = |⟪η, target⟫_ℝ| := hspec.2.2.symm
      _ = |⟪η, target - operator x⟫_ℝ| := congrArg abs hdiff.symm
      _ = ‖⟪η, target - operator x⟫_ℝ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖η‖ * ‖target - operator x‖ := norm_inner_le_norm _ _
      _ = ‖target - operator x‖ := by rw [hspec.1, one_mul]

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
