import NavierStokes.SignedMeanGain

/-!
# Exact signed-covariance adapter

This module anchors the counter-proof program to the literal covariance objects
assembled by `SignedMeanGain`.  The imported split retains the complete signed
remainder; the helper identities expose either summand by subtraction without
introducing a surrogate covariance system.

## Manuscript correspondence

This is the literal Lean bridge for §3.3 "Exact signed covariance data" and
Theorem 4.1 (`thm:covsplit`) of
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`.
The source theorem is `SignedMeanGain.incrementTensor_split`, listed in the
note's source-interface map.  The subtraction and zero-remainder equivalences
below are Lean normalization helpers used by `ReconstructedResponse`; they add
no analytic hypothesis and are not separate claims of the manuscript.
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

/-- Helper normal form for `exact_covariance_split`: the retained remainder
can be recovered from the literal increment and cross tensor, so downstream
adapters cannot silently redefine it. -/
theorem remainderTensor_eq_increment_sub_cross
    (f : LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f) :
    remainderTensor f a = incrementTensor f a - crossTensor f a := by
  rw [exact_covariance_split]
  abel

/-- Companion helper to `remainderTensor_eq_increment_sub_cross`; it isolates
the reduced summand when expanding the reconstructed response. -/
theorem crossTensor_eq_increment_sub_remainder
    (f : LabelSumBounds.SignedFamily s P α δ β η) (a : Assembly f) :
    crossTensor f a = incrementTensor f a - remainderTensor f a := by
  rw [exact_covariance_split]
  abel

/-- Algebraic helper for Theorem 4.1: exact identification of the reduced cross
tensor with the full covariance increment is equivalent to vanishing of the
source's retained remainder. -/
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
