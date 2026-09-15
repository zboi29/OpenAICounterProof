import Mathlib.Data.Real.Basic

/-!
# Terminal residual exposure

The source-specific work must prove an exposure bridge from flat physical
residuals to flat observed mismatches.  The final logical contradiction is kept
separate and reusable here.
-/

namespace NavierStokes.CounterProof

/-- All-order decay at the positive side of `q = 0`. -/
def FlatAtZero (size : ℝ → ℝ) : Prop :=
  ∀ N : ℕ, ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
    ∀ q : ℝ, 0 < q → q < ε → size q ≤ C * q ^ N

/-- A proved transfer from the terminal physical residual to the selected
observable mismatch.  Polynomial sensitivity is established by concrete
instances, not assumed globally by the counter-proof core. -/
structure ResidualExposure (residualSize mismatchSize : ℝ → ℝ) where
  flat_transfer : FlatAtZero residualSize → FlatAtZero mismatchSize

namespace ResidualExposure

theorem residual_not_flat_of_mismatch_not_flat
    {residualSize mismatchSize : ℝ → ℝ}
    (E : ResidualExposure residualSize mismatchSize)
    (hmismatch : ¬ FlatAtZero mismatchSize) :
    ¬ FlatAtZero residualSize :=
  mt E.flat_transfer hmismatch

end ResidualExposure

end NavierStokes.CounterProof
