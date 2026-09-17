import NavierStokes.CounterProof.Adapter.FiniteJetWitness
import NavierStokes.CounterProof.Adapter.ResidualLedger
import NavierStokes.GenericRealization
import NavierStokes.MixedDiagonalResidual

/-!
# Complete diagonal-tail capacity

The actual endpoint uses one selected diagonal schedule.  This module packages
separate linear and nonlinear estimates into a capacity bound for every tail
represented by that schedule; it never replaces the diagonal tail by a fixed-q
infinite sum.

## Manuscript correspondence

The capacity is the Lean form of Γ + N in §6.1 "Admissible stage and tail
budgets", Theorem 6.1 (`thm:budget`), and Corollary 6.3
(`cor:joint-obstruction`) of the Version 1.1 companion note in
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`.
It implements
Lean-instantiation Phase VI.  `tailCapacityOfSeparateBounds` combines the
linearized response and nonlinear interaction estimates; `covered_tail_bound`
is a transport helper whose only role is to connect an actual selected
diagonal schedule to the admissible tail type.  Neither helper asserts that
the source's actual tail is covered; that remains an explicit premise.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

open NavierStokes.CounterProof

variable {Tail Obs : Type*}
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]

/-- Build total tail capacity from separately proved linear and nonlinear
functional bounds. -/
def tailCapacityOfSeparateBounds
    (functional : Obs →L[ℝ] ℝ) (response nonlinear : Tail → Obs)
    (linearCapacity nonlinearCapacity : ℝ)
    (hlinear : ∀ tail, |functional (response tail)| ≤ linearCapacity)
    (hnonlinear : ∀ tail, |functional (nonlinear tail)| ≤ nonlinearCapacity) :
    TailCapacity response nonlinear where
  functional := functional
  linearCapacity := linearCapacity
  nonlinearCapacity := nonlinearCapacity
  bound tail := by
    rw [map_add]
    exact (abs_add_le _ _).trans (add_le_add (hlinear tail) (hnonlinear tail))

/-- If both parts consume prescribed fractions of a positive defect, their
sum consumes the sum of those fractions. -/
theorem complete_tail_fraction_bound
    {linear nonlinear magnitude θlinear θnonlinear : ℝ}
    (hlinear : linear ≤ θlinear * magnitude)
    (hnonlinear : nonlinear ≤ θnonlinear * magnitude) :
    linear + nonlinear ≤ (θlinear + θnonlinear) * magnitude := by
  calc
    linear + nonlinear ≤ θlinear * magnitude + θnonlinear * magnitude :=
      add_le_add hlinear hnonlinear
    _ = (θlinear + θnonlinear) * magnitude := by ring

/-- Coverage transfers a capacity theorem from the schedule's tail type to the
literal realized future tail. -/
theorem covered_tail_bound
    {ScheduleTail ActualTail : Type*}
    (embed : ActualTail → ScheduleTail)
    (functional : Obs →L[ℝ] ℝ)
    (response nonlinear : ScheduleTail → Obs)
    {capacity : ℝ}
    (hcapacity : ∀ tail,
      |functional (response tail + nonlinear tail)| ≤ capacity)
    (tail : ActualTail) :
    |functional (response (embed tail) + nonlinear (embed tail))| ≤ capacity :=
  hcapacity (embed tail)

end NavierStokes.CounterProof.Adapter
