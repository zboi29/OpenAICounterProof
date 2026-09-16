import NavierStokes.CounterProof.Reconstruction.BranchDefect

/-!
# Dual certificates for primitive incompatibility

This module is the functional-analytic entry point of the `Certificates` subsystem.

This finite-jet interface implements the exact cokernel-witness route without
requiring a complete singular-value library.

The functional is evaluated on the same `Obs` space as `fullCompatibility`.
Thus a witness proves failure of the full reconstructed range, not merely
failure of a projected or reduced block.
-/

noncomputable section

namespace NavierStokes.CounterProof

variable {Active Hidden Obs Constraint : Type*}
  [NormedAddCommGroup Active] [NormedSpace ℝ Active]
  [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]

/-- A dual direction annihilating every full-compatible response but detecting
the requested target. -/
structure CokernelWitness
    (K : CompatibilityBlocks Active Hidden Obs Constraint) (target : Obs) where
  /-- Continuous dual functional exposing the obstructed direction. -/
  functional : Obs →L[ℝ] ℝ
  /-- Excludes the vacuous zero functional. -/
  functional_ne_zero : functional ≠ 0
  /-- The functional annihilates the entire full-compatible response range. -/
  annihilates : ∀ a, functional (K.fullCompatibility a) = 0
  /-- The requested target has a nonzero component in the exposed direction. -/
  detects_target : functional target ≠ 0

namespace CokernelWitness

/-- A cokernel witness proves that the target is outside the range of the full
compatibility operator. -/
theorem target_not_mem_range
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (W : CokernelWitness K target) :
    target ∉ Set.range K.fullCompatibility := by
  rintro ⟨a, ha⟩
  apply W.detects_target
  calc
    W.functional target = W.functional (K.fullCompatibility a) :=
      congrArg W.functional ha.symm
    _ = 0 := W.annihilates a

/-- Existential form of `target_not_mem_range`: no active tangent realizes the
target through the full response. -/
theorem no_full_solution
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (W : CokernelWitness K target) :
    ¬ ∃ a, K.fullCompatibility a = target := by
  simpa only [Set.mem_range] using W.target_not_mem_range

end CokernelWitness

end NavierStokes.CounterProof
