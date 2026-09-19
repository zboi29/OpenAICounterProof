import NavierStokes.CounterProof.Certificates.HilbertCokernel
import NavierStokes.CounterProof.Certificates.QuantitativeObstruction
import NavierStokes.CounterProof.Certificates.ResidualExposure

/-!
# Unified same-witness joint obstruction

Version 1.1 of the signed-mean companion note strengthens the counter-proof
target: one normalized dual direction should simultaneously show that the
reduced-branch defect survives the complete admissible future tail and that
the full-compatible target lies beyond that tail's response capacity.

This module packages that shared Hilbert-space direction.  The two conclusions
remain separate projections, so either branch can still be used independently.

`FunctionalJointCertificate` is the functional-first abstract theorem missing
from the source-facing API.  It formalizes Corollary `cor:joint-obstruction`,
“Joint-obstruction corollary” (Corollary 6.3), in §6.2 of
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`.
Its normalization is absorbed into the certified magnitude and capacities, so
finite-jet adapters may use their actual bounded scalar observation directly,
without first choosing a Riesz vector.  `JointCokernelCertificate` remains the
normalized Hilbert specialization and maps into the functional certificate.
-/

noncomputable section

open scoped InnerProductSpace

namespace NavierStokes.CounterProof

section Functional

variable {Active Hidden Obs Constraint Tail : Type*}
  [NormedAddCommGroup Active] [NormedSpace ℝ Active]
  [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]

/-- Same-witness joint obstruction stated with the bounded scalar functional
that a finite-jet source adapter actually constructs.  The two quantitative
hypotheses are exactly the target/response gap and complete-tail fraction in
companion-note Corollary `cor:joint-obstruction`. -/
structure FunctionalJointCertificate
    (K : CompatibilityBlocks Active Hidden Obs Constraint) (target : Obs)
    (branch : ReducedBranch K target)
    (response nonlinear : Tail → Obs) where
  /-- Shared finite-jet functional for both branches. -/
  functional : Obs →L[ℝ] ℝ
  /-- Positive detected margin after paying for the selected active response. -/
  magnitude : ℝ
  magnitude_pos : 0 < magnitude
  /-- Fraction of the joint margin available to the complete future tail. -/
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  theta_lt_one : theta < 1
  /-- Near-cokernel gap in the literal source functional. -/
  target_response_gap :
    magnitude ≤ |functional target| -
      ‖functional.comp K.fullCompatibility‖ * ‖branch.active‖
  /-- Complete linear and nonlinear future response capacity. -/
  tailCapacity : TailCapacity response nonlinear
  /-- The capacity is measured by the same functional. -/
  tail_functional_eq : tailCapacity.functional = functional
  /-- The future tail consumes at most a `theta` fraction of the margin. -/
  capacity_le :
    tailCapacity.linearCapacity + tailCapacity.nonlinearCapacity ≤ theta * magnitude

namespace FunctionalJointCertificate

/-- The scalar margin left after paying the complete future-tail fraction is
strictly positive. -/
theorem surviving_margin_pos
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : FunctionalJointCertificate K target branch response nonlinear) :
    0 < (1 - J.theta) * J.magnitude :=
  mul_pos (sub_pos.mpr J.theta_lt_one) J.magnitude_pos

/-- The same functional detects the exact reduced-branch defect by at least
the certified joint margin. -/
theorem detects_reduced_defect
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : FunctionalJointCertificate K target branch response nonlinear) :
    J.magnitude ≤ |J.tailCapacity.functional branch.defect| := by
  have hnear := functional_residual_lower_bound K.fullCompatibility
    J.functional target branch.active
  have hmargin : J.magnitude ≤
      |J.functional (target - K.fullCompatibility branch.active)| :=
    J.target_response_gap.trans hnear
  rw [branch.full_eq_target_add_defect] at hmargin
  have hneg : target - (target + branch.defect) = -branch.defect := by abel
  rw [hneg, map_neg, abs_neg] at hmargin
  rw [J.tail_functional_eq]
  exact hmargin

/-- The complete tail consumes strictly less than the detected target
component, giving the full-compatible capacity branch. -/
theorem target_exceeds_capacity
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : FunctionalJointCertificate K target branch response nonlinear) :
    J.tailCapacity.linearCapacity + J.tailCapacity.nonlinearCapacity <
      |J.tailCapacity.functional target| := by
  have hresponse_nonneg :
      0 ≤ ‖J.functional.comp K.fullCompatibility‖ * ‖branch.active‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hmagnitude_target : J.magnitude ≤ |J.functional target| := by
    linarith [J.target_response_gap]
  have htheta : J.theta * J.magnitude < J.magnitude := by
    simpa using mul_lt_mul_of_pos_right J.theta_lt_one J.magnitude_pos
  rw [J.tail_functional_eq]
  exact J.capacity_le.trans_lt (htheta.trans_le hmagnitude_target)

/-- Every admissible tail leaves the Corollary 6.3 margin in the reduced
defect direction. -/
theorem reduced_defect_survives_every_tail
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : FunctionalJointCertificate K target branch response nonlinear)
    (tail : Tail) :
    (1 - J.theta) * J.magnitude ≤
      |J.tailCapacity.functional
        (branch.defect + (response tail + nonlinear tail))| := by
  have htail :
      |J.tailCapacity.functional (response tail + nonlinear tail)| ≤
        J.theta * J.magnitude :=
    (J.tailCapacity.bound tail).trans J.capacity_le
  have hsurvives := interface_defect_survives_tail
    J.detects_reduced_defect htail
  simpa [map_add] using hsurvives

/-- No admissible future tail can erase the reduced defect exactly. -/
theorem final_mismatch_ne_zero
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : FunctionalJointCertificate K target branch response nonlinear)
    (tail : Tail) :
    branch.defect + (response tail + nonlinear tail) ≠ 0 := by
  intro hzero
  have hsurvives := J.reduced_defect_survives_every_tail tail
  rw [hzero, map_zero, abs_zero] at hsurvives
  exact (not_le_of_gt J.surviving_margin_pos) hsurvives

/-- The full-compatible target cannot be realized by any covered tail. -/
theorem no_full_compatible_tail
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : FunctionalJointCertificate K target branch response nonlinear) :
    ¬ ∃ tail, TailRealizes response nonlinear target tail :=
  J.tailCapacity.target_exceeds_admissible_tail J.target_exceeds_capacity

/-- Functional-first form of companion-note Corollary 6.3: one literal
finite-jet functional proves both tail-stable reduced mismatch and exclusion
of the full-compatible target from total future capacity. -/
theorem joint_obstruction
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : FunctionalJointCertificate K target branch response nonlinear) :
    (∀ tail, (1 - J.theta) * J.magnitude ≤
      |J.tailCapacity.functional
        (branch.defect + (response tail + nonlinear tail))|) ∧
      ¬ ∃ tail, TailRealizes response nonlinear target tail :=
  ⟨J.reduced_defect_survives_every_tail, J.no_full_compatible_tail⟩

end FunctionalJointCertificate

end Functional

variable {Active Hidden Obs Constraint Tail : Type*}
  [NormedAddCommGroup Active] [InnerProductSpace ℝ Active] [CompleteSpace Active]
  [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
  [NormedAddCommGroup Obs] [InnerProductSpace ℝ Obs] [CompleteSpace Obs]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]

/-- One near-cokernel direction controlling both counter-proof branches. -/
structure JointCokernelCertificate
    (K : CompatibilityBlocks Active Hidden Obs Constraint) (target : Obs)
    (branch : ReducedBranch K target)
    (response nonlinear : Tail → Obs) where
  /-- Shared observed direction for the defect and capacity estimates. -/
  direction : Obs
  /-- Unit normalization used by source-level quantitative estimates. -/
  direction_norm : ‖direction‖ = 1
  /-- Positive algebraic margin left after paying for the full response of the
  selected reduced active tangent. -/
  magnitude : ℝ
  magnitude_pos : 0 < magnitude
  /-- Fraction of the detected margin available to the complete future tail. -/
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  theta_lt_one : theta < 1
  /-- Version 1.1 near-cokernel margin hypothesis. -/
  target_response_gap :
    magnitude ≤ |⟪direction, target⟫_ℝ| -
      ‖K.fullCompatibility.adjoint direction‖ * ‖branch.active‖
  /-- Complete admissible linear and nonlinear future-tail capacity. -/
  tailCapacity : TailCapacity response nonlinear
  /-- The capacity ledger uses the same dual direction. -/
  tail_functional_eq : tailCapacity.functional = cokernelFunctional direction
  /-- The complete future capacity consumes at most a `theta` fraction of the
  detected joint margin. -/
  capacity_le :
    tailCapacity.linearCapacity + tailCapacity.nonlinearCapacity ≤ theta * magnitude

namespace JointCokernelCertificate

/-- Forget the Riesz-vector presentation and retain the literal bounded
functional needed by source finite-jet adapters.  This proves that the existing
Hilbert certificate is a specialization of companion-note Corollary 6.3's
functional-first criterion. -/
def functionalJointCertificate
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear) :
    FunctionalJointCertificate K target branch response nonlinear where
  functional := cokernelFunctional J.direction
  magnitude := J.magnitude
  magnitude_pos := J.magnitude_pos
  theta := J.theta
  theta_nonneg := J.theta_nonneg
  theta_lt_one := J.theta_lt_one
  target_response_gap := by
    rw [norm_cokernelFunctional_comp]
    exact J.target_response_gap
  tailCapacity := J.tailCapacity
  tail_functional_eq := J.tail_functional_eq
  capacity_le := J.capacity_le

/-- The scalar margin left after the complete future tail is strictly
positive. -/
theorem surviving_margin_pos
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear) :
    0 < (1 - J.theta) * J.magnitude :=
  mul_pos (sub_pos.mpr J.theta_lt_one) J.magnitude_pos

/-- Forgetful adapter to the existing quantitative dual certificate.  The
joint gap is stronger than target detection because it has already paid for
the selected branch's possible full response. -/
def quantitativeDualCertificate
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear) :
    QuantitativeDualCertificate K.fullCompatibility target where
  functional := cokernelFunctional J.direction
  targetMagnitude := J.magnitude
  responseMagnitude := ‖K.fullCompatibility.adjoint J.direction‖
  target_nonneg := J.magnitude_pos.le
  response_nonneg := norm_nonneg _
  detects_target := by
    have hresponse_nonneg :
        0 ≤ ‖K.fullCompatibility.adjoint J.direction‖ * ‖branch.active‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [cokernelFunctional_apply]
    linarith [J.target_response_gap]
  near_cokernel := by
    rw [norm_cokernelFunctional_comp]

/-- The near-cokernel target gap detects at least `magnitude` of the exact
reduced-branch defect. -/
theorem detects_reduced_defect
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear) :
    J.magnitude ≤ |J.tailCapacity.functional branch.defect| := by
  have hnear := near_cokernel_residual_lower_bound K.fullCompatibility
    J.direction target branch.active
  have hmargin : J.magnitude ≤
      |⟪J.direction, target - K.fullCompatibility branch.active⟫_ℝ| :=
    J.target_response_gap.trans hnear
  rw [branch.full_eq_target_add_defect] at hmargin
  have hneg : target - (target + branch.defect) = -branch.defect := by abel
  rw [hneg, inner_neg_right, abs_neg] at hmargin
  rw [J.tail_functional_eq, cokernelFunctional_apply]
  exact hmargin

/-- The detected target component strictly exceeds complete future response
capacity.  This is the full-compatible branch of the joint certificate. -/
theorem target_exceeds_capacity
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear) :
    J.tailCapacity.linearCapacity + J.tailCapacity.nonlinearCapacity <
      |J.tailCapacity.functional target| := by
  have hresponse_nonneg :
      0 ≤ ‖K.fullCompatibility.adjoint J.direction‖ * ‖branch.active‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hmagnitude_target : J.magnitude ≤ |⟪J.direction, target⟫_ℝ| := by
    linarith [J.target_response_gap]
  have htheta : J.theta * J.magnitude < J.magnitude := by
    simpa using mul_lt_mul_of_pos_right J.theta_lt_one J.magnitude_pos
  rw [J.tail_functional_eq, cokernelFunctional_apply]
  exact J.capacity_le.trans_lt (htheta.trans_le hmagnitude_target)

/-- Every admissible future tail leaves a positive reduced-branch mismatch in
the same dual direction. -/
theorem reduced_defect_survives_every_tail
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear)
    (tail : Tail) :
    (1 - J.theta) * J.magnitude ≤
      |J.tailCapacity.functional
        (branch.defect + (response tail + nonlinear tail))| := by
  have htail :
      |J.tailCapacity.functional (response tail + nonlinear tail)| ≤
        J.theta * J.magnitude :=
    (J.tailCapacity.bound tail).trans J.capacity_le
  have hsurvives := interface_defect_survives_tail
    J.detects_reduced_defect htail
  simpa [map_add] using hsurvives

/-- No covered future tail can cancel the reduced defect exactly. -/
theorem final_mismatch_ne_zero
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear)
    (tail : Tail) :
    branch.defect + (response tail + nonlinear tail) ≠ 0 := by
  intro hzero
  have hsurvives := J.reduced_defect_survives_every_tail tail
  rw [hzero, map_zero, abs_zero] at hsurvives
  exact (not_le_of_gt J.surviving_margin_pos) hsurvives

/-- No admissible tail can realize the full-compatible target component. -/
theorem no_full_compatible_tail
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear) :
    ¬ ∃ tail, TailRealizes response nonlinear target tail :=
  J.tailCapacity.target_exceeds_admissible_tail J.target_exceeds_capacity

/-- Version 1.1 joint-obstruction theorem.  One cokernel direction proves both
tail-stable reduced mismatch and full-compatible capacity exclusion. -/
theorem joint_obstruction
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear) :
    (∀ tail, (1 - J.theta) * J.magnitude ≤
      |J.tailCapacity.functional
        (branch.defect + (response tail + nonlinear tail))|) ∧
      ¬ ∃ tail, TailRealizes response nonlinear target tail := by
  exact ⟨J.reduced_defect_survives_every_tail, J.no_full_compatible_tail⟩

/-- The residual-exposure projection of the joint certificate.  Once the
surviving observed mismatch is generated by a physical residual up to a
controlled error, the same witness gives an explicit residual lower bound. -/
theorem residual_lower_bound
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    {branch : ReducedBranch K target} {response nonlinear : Tail → Obs}
    (J : JointCokernelCertificate K target branch response nonlinear)
    {Residual : Type*} [NormedAddCommGroup Residual] [NormedSpace ℝ Residual]
    (tail : Tail) (exposure : Residual →L[ℝ] Obs)
    (residual : Residual) (error : Obs) {sensitivity : ℝ}
    (hsensitivity_pos : 0 < sensitivity)
    (hexposure : branch.defect + (response tail + nonlinear tail) =
      exposure residual + error)
    (herror : |J.tailCapacity.functional error| ≤
      (1 - J.theta) * J.magnitude / 2)
    (hsensitivity : ‖J.tailCapacity.functional.comp exposure‖ ≤ sensitivity) :
    ((1 - J.theta) * J.magnitude / 2) / sensitivity ≤ ‖residual‖ := by
  have htail :
      |J.tailCapacity.functional (response tail + nonlinear tail)| ≤
        J.theta * J.magnitude :=
    (J.tailCapacity.bound tail).trans J.capacity_le
  exact tail_stable_residual_lower_bound
    J.tailCapacity.functional exposure
    (defect := branch.defect)
    (futureTail := response tail + nonlinear tail)
    (mismatch := branch.defect + (response tail + nonlinear tail))
    (error := error) (residual := residual)
    (magnitude := J.magnitude) (θ := J.theta) (sensitivity := sensitivity)
    J.magnitude_pos.le J.theta_nonneg J.theta_lt_one hsensitivity_pos
    rfl hexposure J.detects_reduced_defect htail herror hsensitivity

end JointCokernelCertificate

end NavierStokes.CounterProof
