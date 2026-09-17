import NavierStokes.CounterProof.Adapter.DiagonalTail
import NavierStokes.CounterProof.Certificates.TerminalCertificate
import NavierStokes.JointResidualLimits

/-!
# Physical residual closure for independent branches

This is the terminal Adapter layer.  It keeps the reduced residual
contradiction and full-compatible capacity exclusion logically independent,
then packages their conclusions without identifying their dual witnesses.

## Manuscript correspondence

This is the terminal adapter for Proposition 6.2 (`prop:residual`), Corollary
6.3 (`cor:joint-obstruction`), and Theorem 7.1 parts (b)--(d) (`thm:main`) of
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`,
implementing Lean-instantiation Phase VII.
Its observation-to-residual map is the concrete specialization anticipated by
Proposition 8.2 (`prop:residualleakage`) and Corollary 8.3
(`cor:jetleakage`) of the general research note.  The packaging record is a
Lean-only interface: it deliberately preserves the manuscript's statement
that either branch closes independently even when no shared witness has yet
been instantiated.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

open NavierStokes.CounterProof

variable {Tail Obs Residual : Type*}
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
  [NormedAddCommGroup Residual] [NormedSpace ℝ Residual]

/-- Terminal conclusions of the two independent counter-proof branches. -/
structure IndependentBranchCertificates
    (residualSize : ℝ → ℝ)
    (response nonlinear : Tail → Obs) (target : Obs) : Prop where
  reduced_residual_not_flat : ¬ FlatAtZero residualSize
  full_target_not_reachable :
    ¬ ∃ tail, TailRealizes response nonlinear target tail

/-- Construct both independent terminal certificates from the quantitative
reduced residual theorem and a separately proved full-capacity witness. -/
theorem independent_counterproof_branches
    (functional : ℝ → Obs →L[ℝ] ℝ)
    (exposure : ℝ → Residual →L[ℝ] Obs)
    (defect futureTail error : ℝ → Obs) (residual : ℝ → Residual)
    {c C θ radius : ℝ} {α M : ℕ}
    (hc : 0 < c) (hC : 0 < C)
    (htheta_nonneg : 0 ≤ θ) (htheta : θ < 1)
    (hradius : 0 < radius)
    (hexposure : ∀ q, 0 < q → q < radius →
      defect q + futureTail q = exposure q (residual q) + error q)
    (hdefect : ∀ q, 0 < q → q < radius →
      c * q ^ α ≤ |functional q (defect q)|)
    (htail : ∀ q, 0 < q → q < radius →
      |functional q (futureTail q)| ≤ θ * (c * q ^ α))
    (herror : ∀ q, 0 < q → q < radius →
      |functional q (error q)| ≤ (1 - θ) * (c * q ^ α) / 2)
    (hsensitivity : ∀ q, 0 < q → q < radius →
      ‖(functional q).comp (exposure q)‖ ≤ C / q ^ M)
    {response nonlinear : Tail → Obs} {target : Obs}
    (full : FullCapacityWitness response nonlinear target) :
    IndependentBranchCertificates (fun q => ‖residual q‖)
      response nonlinear target where
  reduced_residual_not_flat :=
    tail_stable_defect_forces_nonflat_physical_residual
      functional exposure defect futureTail error residual hc hC
      htheta_nonneg htheta hradius hexposure hdefect htail herror hsensitivity
  full_target_not_reachable := full.no_realizing_tail

end NavierStokes.CounterProof.Adapter
