import NavierStokes.CounterProof.Adapter.FullCompatibility
import NavierStokes.CounterProof.Reconstruction.BranchResolvent
import NavierStokes.CycleContinuationInvariant

/-!
# Conditioned reconstructed response

The request derivative must be transported through every bounded linear stage
of the reconstruction.  This file keeps the individual losses explicit and
provides product estimates for the resulting full physical-jet response.

## Manuscript correspondence

This is the operator-norm ledger requested by §8, Phase IV "differentiate the
weighted estimates through the inverse" of
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`.
It records the inverse, reconstruction, and physical-jet factors that must be
paid before the output-class gap discussed after Proposition 4.2 can imply the
relative contraction in Theorem 5.3 (`thm:resolvent`).  The need to retain the
inverse factor is also the "Flat edge" item of the §15 interface checklist and
is grounded in `CycleContinuationInvariant.lean`.  The product and exponent
lemmas are bookkeeping helpers for those source estimates; they do not provide
the missing numerical bounds themselves.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

variable {A B C D : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Explicit operator ledger for inverse solve, reconstruction, and physical
jet conversion.  Each bound is stage-independent at the fixed jet order. -/
structure ResponseLossLedger
    (inverseSolve : A →L[ℝ] B) (reconstruct : B →L[ℝ] C)
    (physicalJet : C →L[ℝ] D) where
  inverseLoss : ℝ
  reconstructionLoss : ℝ
  physicalLoss : ℝ
  inverse_nonneg : 0 ≤ inverseLoss
  reconstruction_nonneg : 0 ≤ reconstructionLoss
  physical_nonneg : 0 ≤ physicalLoss
  inverse_bound : ‖inverseSolve‖ ≤ inverseLoss
  reconstruction_bound : ‖reconstruct‖ ≤ reconstructionLoss
  physical_bound : ‖physicalJet‖ ≤ physicalLoss

namespace ResponseLossLedger

/-- The complete request-to-physical-jet derivative pays the product of the
three recorded losses. -/
theorem full_response_bound
    {inverseSolve : A →L[ℝ] B} {reconstruct : B →L[ℝ] C}
    {physicalJet : C →L[ℝ] D}
    (L : ResponseLossLedger inverseSolve reconstruct physicalJet) :
    ‖physicalJet.comp (reconstruct.comp inverseSolve)‖ ≤
      L.physicalLoss * (L.reconstructionLoss * L.inverseLoss) := by
  have hcomp : ‖reconstruct.comp inverseSolve‖ ≤
      L.reconstructionLoss * L.inverseLoss := by
    calc
      ‖reconstruct.comp inverseSolve‖ ≤ ‖reconstruct‖ * ‖inverseSolve‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ L.reconstructionLoss * L.inverseLoss :=
        mul_le_mul L.reconstruction_bound L.inverse_bound
          (norm_nonneg _) L.reconstruction_nonneg
  calc
    ‖physicalJet.comp (reconstruct.comp inverseSolve)‖ ≤
        ‖physicalJet‖ * ‖reconstruct.comp inverseSolve‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ L.physicalLoss * (L.reconstructionLoss * L.inverseLoss) :=
      mul_le_mul L.physical_bound hcomp (norm_nonneg _) L.physical_nonneg

/-- Pointwise form of the complete conditioned response estimate. -/
theorem full_response_apply_bound
    {inverseSolve : A →L[ℝ] B} {reconstruct : B →L[ℝ] C}
    {physicalJet : C →L[ℝ] D}
    (L : ResponseLossLedger inverseSolve reconstruct physicalJet) (a : A) :
    ‖physicalJet (reconstruct (inverseSolve a))‖ ≤
      (L.physicalLoss * (L.reconstructionLoss * L.inverseLoss)) * ‖a‖ := by
  exact (physicalJet.comp (reconstruct.comp inverseSolve)).le_of_opNorm_le
    L.full_response_bound a

end ResponseLossLedger

/-- Arithmetic helper for Phase IV and the admissible budgets in §6.1: a
positive algebraic gain remains positive after a fixed physical-jet loss. -/
theorem positive_gain_after_fixed_loss {gain loss ρ : ℝ}
    (hgain : loss + ρ ≤ gain) (hρ : 0 < ρ) :
    0 < gain - loss := by
  linarith

end NavierStokes.CounterProof.Adapter
