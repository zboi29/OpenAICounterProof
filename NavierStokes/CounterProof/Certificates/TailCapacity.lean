import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Admissible future-tail capacity

The definitions here prevent a finite-stage mismatch from being promoted to a
terminal contradiction without controlling every later admissible correction.

`response` represents the complete linearized contribution of a candidate
tail and `nonlinear` represents all recomputed interactions omitted from that
linear part.  A concrete ledger instance must bound their sum for every
admissible tail, rather than only bounding one subsequent stage.
-/

noncomputable section

namespace NavierStokes.CounterProof

variable {Tail Obs : Type*}
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]

/-- A tail realizes a target after both its linear response and nonlinear
remainder are recomputed.  The type `Tail` should encode admissibility, so the
existential quantifier ranges only over ledger-compatible corrections. -/
def TailRealizes (response nonlinear : Tail → Obs) (target : Obs) (tail : Tail) : Prop :=
  response tail + nonlinear tail = target

/-- A dual upper bound for the complete admissible future response. -/
structure TailCapacity
    (response nonlinear : Tail → Obs) where
  /-- Dual direction in which total future correction capacity is measured. -/
  functional : Obs →L[ℝ] ℝ
  /-- Upper bound assigned to the complete linear tail response. -/
  linearCapacity : ℝ
  /-- Upper bound assigned to all nonlinear tail interactions. -/
  nonlinearCapacity : ℝ
  /-- Uniform bound on the recomputed linear-plus-nonlinear response of every
  admissible tail. -/
  bound : ∀ tail,
    |functional (response tail + nonlinear tail)| ≤ linearCapacity + nonlinearCapacity

namespace TailCapacity

/-- If the detected target component exceeds total admissible capacity, no
tail can realize the target. -/
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
a controlled future tail.  The estimate is deliberately scalar so callers can
apply it after evaluating any bounded dual functional. -/
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
