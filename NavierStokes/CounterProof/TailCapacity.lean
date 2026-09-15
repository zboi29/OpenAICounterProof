import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Admissible future-tail capacity

The definitions here prevent a finite-stage mismatch from being promoted to a
terminal contradiction without controlling every later admissible correction.
-/

noncomputable section

namespace NavierStokes.CounterProof

variable {Tail Obs : Type*}
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]

/-- A tail realizes a target after both its linear response and nonlinear
remainder are recomputed. -/
def TailRealizes (response nonlinear : Tail → Obs) (target : Obs) (tail : Tail) : Prop :=
  response tail + nonlinear tail = target

/-- A dual upper bound for the complete admissible future response. -/
structure TailCapacity
    (response nonlinear : Tail → Obs) where
  functional : Obs →L[ℝ] ℝ
  linearCapacity : ℝ
  nonlinearCapacity : ℝ
  bound : ∀ tail,
    |functional (response tail + nonlinear tail)| ≤ linearCapacity + nonlinearCapacity

namespace TailCapacity

theorem target_exceeds_admissible_tail
    {response nonlinear : Tail → Obs} (C : TailCapacity response nonlinear)
    {target : Obs}
    (htarget : C.linearCapacity + C.nonlinearCapacity < |C.functional target|) :
    ¬ ∃ tail, TailRealizes response nonlinear target tail := by
  rintro ⟨tail, htail⟩
  have hbound := C.bound tail
  rw [htail] at hbound
  exact (not_lt_of_ge hbound) htarget

end TailCapacity

/-- Reverse-triangle lower bound used to show that an interface defect survives
a controlled future tail. -/
theorem interface_defect_survives_tail
    {defect tail magnitude θ : ℝ}
    (hdefect : magnitude ≤ |defect|)
    (htail : |tail| ≤ θ * magnitude) :
    (1 - θ) * magnitude ≤ |defect + tail| := by
  rw [sub_mul, one_mul]
  calc
    magnitude - θ * magnitude ≤ |defect| - |tail| := sub_le_sub hdefect htail
    _ = abs defect - abs (-tail) := by rw [abs_neg]
    _ ≤ abs (defect - (-tail)) := abs_sub_abs_le_abs_sub defect (-tail)
    _ = |defect + tail| := by rw [sub_neg_eq_add]

end NavierStokes.CounterProof
