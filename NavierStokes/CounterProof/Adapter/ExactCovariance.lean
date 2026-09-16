import NavierStokes.SignedMeanGain

/-!
# Exact signed-covariance adapter

This module anchors the counter-proof program to the literal covariance objects
assembled by `SignedMeanGain`.  The imported split retains the complete signed
remainder; the helper identities expose either summand by subtraction without
introducing a surrogate covariance system.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

open SignedMeanGain

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {s : WeightedClasses.StripData D} {P : ι → ℕ → D → ℝ}
variable {α δ β η : ℝ}

/-- The source's assembled increment is exactly the primary–tangent cross
tensor plus the complete retained remainder. -/
theorem exact_covariance_split
    (f : LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f) :
    incrementTensor f a = crossTensor f a + remainderTensor f a :=
  incrementTensor_split f a

/-- The retained remainder can be recovered from the literal increment and
cross tensor, so later adapters cannot silently redefine it. -/
theorem remainderTensor_eq_increment_sub_cross
    (f : LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f) :
    remainderTensor f a = incrementTensor f a - crossTensor f a := by
  rw [exact_covariance_split]
  abel

/-- The reduced cross tensor is likewise determined by the exact update and
the retained remainder. -/
theorem crossTensor_eq_increment_sub_remainder
    (f : LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f) :
    crossTensor f a = incrementTensor f a - remainderTensor f a := by
  rw [exact_covariance_split]
  abel

/-- Exact identification of the reduced cross tensor with the full covariance
increment is equivalent to vanishing of the source's retained remainder. -/
theorem incrementTensor_eq_crossTensor_iff_remainderTensor_eq_zero
    (f : LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f) :
    incrementTensor f a = crossTensor f a ↔ remainderTensor f a = 0 := by
  rw [remainderTensor_eq_increment_sub_cross]
  constructor
  · intro h
    rw [h, sub_self]
  · intro h
    have hz : incrementTensor f a - crossTensor f a = 0 := h
    exact sub_eq_zero.mp hz

end NavierStokes.CounterProof.Adapter
