import NavierStokes.CounterProof.Adapter.ReducedCross
import NavierStokes.ActualCycleResidualBounds

/-!
# Actual residual-ledger adapter

This module exposes the two upstream objects needed at the terminal end of the
program: the stage-independent physical derivative loss and the actual finite-
cycle residual rates.  The helper theorem below proves that, assuming the
source invariant and physical realizations at every cycle, any fixed physical
jet can be placed in any prescribed finite algebraic rate by taking a late
enough cycle.  It deliberately keeps the selected cycle explicit; it is not a
claim about a completed infinite tail.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

open Filter
open ActualCycleResidualBounds

/-- For each fixed derivative and target exponent, the actual iteration ledger
provides a finite stage whose physical residual has at least that rate.  This
is the precise finite-cycle input used by a later diagonal or tail argument. -/
theorem exists_finite_residual_rate_at_least
    {B N0 N : ℕ}
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0) (hN : 4 ≤ N)
    (p : ℕ → CorrectionStep.CycleParameters (Index B N0))
    (u : ℕ → ProblemStatement.VelocityField)
    (P : ℕ → ProblemStatement.PressureField)
    (H : ∀ J, Invariant (ActualIterationLedger.sigma J)
      (CorrectionStep.CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B)
        (ActualInitialization.initialCycleState B N0) J))
    (d : ∀ J, PhysicalData B N
      (CorrectionStep.CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B)
        (ActualInitialization.initialCycleState B N0) J).state
      (u J) (P J))
    (m : ℕ) (rate : ℝ) :
    ∃ J, DiagonalResidual.JetRate GlobalBaseError.originPast
      (PhysicalWaveSum.physicalQ CorrectionInitialization.ActualPrimary.h)
      (fun w => ProblemStatement.navierStokesResidual (u J) (P J) w.1 w.2)
      m rate := by
  have hevent : ∀ᶠ J in atTop,
      rate ≤ ActualIterationLedger.gain CorrectionInitialization.ActualPrimary.h J - fixedLoss m := by
    have ht := ActualIterationLedger.gain_add_tendsto_atTop
      CorrectionInitialization.ActualPrimary.outgoing.data.h_pos (-(fixedLoss m))
    simpa only [sub_eq_add_neg] using ht.eventually (eventually_ge_atTop rate)
  obtain ⟨J, hJ⟩ := hevent.exists
  refine ⟨J, ?_⟩
  exact (finite_residual_rates hGeom hN p u P H d J m).weaken
    origin_positive_small hJ

/-- One sufficiently late finite cycle simultaneously attains the prescribed
rate for every physical derivative order through `M`.  This is stronger than
choosing a separate stage for each derivative and is the finite-jet form needed
before a common tail estimate can be attempted. -/
theorem exists_finite_residual_rates_through
    {B N0 N : ℕ}
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0) (hN : 4 ≤ N)
    (p : ℕ → CorrectionStep.CycleParameters (Index B N0))
    (u : ℕ → ProblemStatement.VelocityField)
    (P : ℕ → ProblemStatement.PressureField)
    (H : ∀ J, Invariant (ActualIterationLedger.sigma J)
      (CorrectionStep.CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B)
        (ActualInitialization.initialCycleState B N0) J))
    (d : ∀ J, PhysicalData B N
      (CorrectionStep.CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B)
        (ActualInitialization.initialCycleState B N0) J).state
      (u J) (P J))
    (M : ℕ) (rate : ℝ) :
    ∃ J, ∀ m ≤ M, DiagonalResidual.JetRate GlobalBaseError.originPast
      (PhysicalWaveSum.physicalQ CorrectionInitialization.ActualPrimary.h)
      (fun w => ProblemStatement.navierStokesResidual (u J) (P J) w.1 w.2)
      m rate := by
  have hevent : ∀ᶠ J in atTop, ∀ m : Fin (M + 1),
      rate ≤ ActualIterationLedger.gain CorrectionInitialization.ActualPrimary.h J -
        fixedLoss m := by
    rw [eventually_all]
    intro m
    have ht := ActualIterationLedger.gain_add_tendsto_atTop
      CorrectionInitialization.ActualPrimary.outgoing.data.h_pos (-(fixedLoss m))
    simpa only [sub_eq_add_neg] using ht.eventually (eventually_ge_atTop rate)
  obtain ⟨J, hJ⟩ := hevent.exists
  refine ⟨J, ?_⟩
  intro m hm
  exact (finite_residual_rates hGeom hN p u P H d J m).weaken
    origin_positive_small (hJ ⟨m, Nat.lt_succ_iff.mpr hm⟩)

/-- The actual physical loss used above is definitionally the loss recorded by
the iteration ledger, making the fixed-in-stage premise explicit. -/
theorem physicalLoss_eq_actualLedgerLoss (m : ℕ) :
    fixedLoss m = ActualIterationLedger.residualLoss
      CorrectionInitialization.ActualPrimary.h
      (2 * CorrectionInitialization.ActualPrimary.h) m :=
  fixedLoss_eq_ledger m

/- TODO(complete-tail control): Implement the admissible linear capacity and
nonlinear remainder from
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`,
sections "Admissible stage and tail budgets" and Lean-instantiation Phases
VI–VII.  The concrete proof must sum the actual increments produced by
`CorrectionAnalyticStep.iterate_results` using
the stage gain and fixed losses in `ActualIterationLedger.lean`, prove coverage
of the realized future tail, and terminate at
`ActualCycleResidualBounds.finite_residual_rates` /
`PhysicalResidualJetBounds.ResidualChartData.residual_jetRate` rather than at a
one-stage bound. -/

end NavierStokes.CounterProof.Adapter
