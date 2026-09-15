import NavierStokes.CounterProof.BranchDefect

/-!
# Dual certificates for primitive incompatibility

This finite-jet interface implements the exact cokernel-witness route without
requiring a complete singular-value library.
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
  functional : Obs →L[ℝ] ℝ
  functional_ne_zero : functional ≠ 0
  annihilates : ∀ a, functional (K.fullCompatibility a) = 0
  detects_target : functional target ≠ 0

namespace CokernelWitness

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

theorem no_full_solution
    {K : CompatibilityBlocks Active Hidden Obs Constraint} {target : Obs}
    (W : CokernelWitness K target) :
    ¬ ∃ a, K.fullCompatibility a = target := by
  simpa only [Set.mem_range] using W.target_not_mem_range

end CokernelWitness

end NavierStokes.CounterProof
