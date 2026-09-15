import NavierStokes.CounterProof.DualCertificate
import NavierStokes.CounterProof.TailCapacity
import NavierStokes.CounterProof.ResidualExposure

/-!
# Terminal counter-proof certificates

A completed certificate reaches the same all-order physical residual predicate
as the upstream construction.  Interface defects and tail estimates remain
separate inputs so neither can be silently skipped.
-/

namespace NavierStokes.CounterProof

/-- The terminal logical package for the residual-exposure route. -/
structure TerminalCertificate (residualSize mismatchSize : ℝ → ℝ) where
  exposure : ResidualExposure residualSize mismatchSize
  mismatch_not_flat : ¬ FlatAtZero mismatchSize

namespace TerminalCertificate

theorem residual_not_flat {residualSize mismatchSize : ℝ → ℝ}
    (C : TerminalCertificate residualSize mismatchSize) :
    ¬ FlatAtZero residualSize :=
  C.exposure.residual_not_flat_of_mismatch_not_flat C.mismatch_not_flat

end TerminalCertificate

end NavierStokes.CounterProof
