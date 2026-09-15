import NavierStokes.CounterProof.DualCertificate
import NavierStokes.CounterProof.TailCapacity

/-!
# Quantitative range and tail-budget obstruction

This module formalizes the dual estimate in the companion note.  A target
component detected by a bounded functional forces a lower bound on every exact
full-compatible lift.  The same functional can also rule out realization by
the complete admissible future tail.
-/

noncomputable section

namespace NavierStokes.CounterProof

variable {Active Obs Tail : Type*}
  [NormedAddCommGroup Active] [NormedSpace ℝ Active]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]

/-- Quantitative near-cokernel data for one target direction. -/
structure QuantitativeDualCertificate
    (fullCompatibility : Active →L[ℝ] Obs) (target : Obs) where
  functional : Obs →L[ℝ] ℝ
  targetMagnitude : ℝ
  responseMagnitude : ℝ
  target_nonneg : 0 ≤ targetMagnitude
  response_nonneg : 0 ≤ responseMagnitude
  detects_target : targetMagnitude ≤ |functional target|
  near_cokernel : ‖functional.comp fullCompatibility‖ ≤ responseMagnitude

namespace QuantitativeDualCertificate

/-- Every exact lift is at least as expensive as the detected target component
divided by the near-cokernel response size. -/
theorem compatible_lift_product_lower_bound
    {fullCompatibility : Active →L[ℝ] Obs} {target : Obs}
    (Q : QuantitativeDualCertificate fullCompatibility target)
    (active : Active) (hactive : fullCompatibility active = target) :
    Q.targetMagnitude ≤ Q.responseMagnitude * ‖active‖ := by
  calc
    Q.targetMagnitude ≤ |Q.functional target| := Q.detects_target
    _ = ‖(Q.functional.comp fullCompatibility) active‖ := by
      rw [ContinuousLinearMap.comp_apply, hactive, Real.norm_eq_abs]
    _ ≤ ‖Q.functional.comp fullCompatibility‖ * ‖active‖ :=
      (Q.functional.comp fullCompatibility).le_opNorm active
    _ ≤ Q.responseMagnitude * ‖active‖ :=
      mul_le_mul_of_nonneg_right Q.near_cokernel (norm_nonneg active)

/-- Quotient form of the compatible-lift lower bound when the near-cokernel
response size is positive. -/
theorem compatible_lift_norm_lower_bound
    {fullCompatibility : Active →L[ℝ] Obs} {target : Obs}
    (Q : QuantitativeDualCertificate fullCompatibility target)
    (hresponse : 0 < Q.responseMagnitude)
    (active : Active) (hactive : fullCompatibility active = target) :
    Q.targetMagnitude / Q.responseMagnitude ≤ ‖active‖ := by
  apply (div_le_iff₀ hresponse).2
  simpa [mul_comm] using Q.compatible_lift_product_lower_bound active hactive

/-- A positive detected target and a zero response bound give exact range
failure. -/
theorem no_compatible_lift_of_response_zero
    {fullCompatibility : Active →L[ℝ] Obs} {target : Obs}
    (Q : QuantitativeDualCertificate fullCompatibility target)
    (htarget : 0 < Q.targetMagnitude)
    (hresponse : Q.responseMagnitude = 0) :
    ¬ ∃ active, fullCompatibility active = target := by
  rintro ⟨active, hactive⟩
  have hlower := Q.compatible_lift_product_lower_bound active hactive
  rw [hresponse, zero_mul] at hlower
  exact (not_lt_of_ge hlower) htarget

end QuantitativeDualCertificate

/-- The range-or-tail-budget theorem: exact compatible lifts obey the dual
lower bound, while a target larger than the total response capacity cannot be
realized by any admissible future tail. -/
theorem quantitative_range_or_tail_budget_obstruction
    {fullCompatibility : Active →L[ℝ] Obs} {target : Obs}
    (Q : QuantitativeDualCertificate fullCompatibility target)
    {response nonlinear : Tail → Obs}
    (C : TailCapacity response nonlinear)
    (hfunctional : C.functional = Q.functional)
    (hcapacity : C.linearCapacity + C.nonlinearCapacity < Q.targetMagnitude) :
    (∀ active, fullCompatibility active = target →
      Q.targetMagnitude ≤ Q.responseMagnitude * ‖active‖) ∧
      ¬ ∃ tail, TailRealizes response nonlinear target tail := by
  constructor
  · intro active hactive
    exact Q.compatible_lift_product_lower_bound active hactive
  · apply C.target_exceeds_admissible_tail
    rw [hfunctional]
    exact hcapacity.trans_le Q.detects_target

end NavierStokes.CounterProof
