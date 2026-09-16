import NavierStokes.CounterProof.DualCertificate
import NavierStokes.CounterProof.TailCapacity
import NavierStokes.CounterProof.ResidualExposure

/-!
# Terminal counter-proof certificates

A completed certificate reaches the same all-order physical residual predicate
as the upstream construction.  Interface defects and tail estimates remain
separate inputs so neither can be silently skipped.

This lightweight package is useful when source-specific work has already
proved the entire flatness transfer.  For quantitative witnesses with explicit
tail and sensitivity bounds, use
`tail_stable_defect_forces_nonflat_physical_residual` instead.
-/

namespace NavierStokes.CounterProof

/-- The terminal logical package for the residual-exposure route. -/
structure TerminalCertificate (residualSize mismatchSize : ℝ → ℝ) where
  /-- Bridge from flatness of the physical residual to flatness of the exposed
  mismatch. -/
  exposure : ResidualExposure residualSize mismatchSize
  /-- Established failure of all-order decay for the exposed mismatch. -/
  mismatch_not_flat : ¬ FlatAtZero mismatchSize

namespace TerminalCertificate

/-- A terminal certificate negates the physical residual-flatness predicate. -/
theorem residual_not_flat {residualSize mismatchSize : ℝ → ℝ}
    (C : TerminalCertificate residualSize mismatchSize) :
    ¬ FlatAtZero residualSize :=
  C.exposure.residual_not_flat_of_mismatch_not_flat C.mismatch_not_flat

end TerminalCertificate

end NavierStokes.CounterProof
