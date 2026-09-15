# Navier–Stokes Counter-Proof Subsystem

This directory implements the downstream Lean program from the primitive-
liftability research note and its signed-mean companion. The modules follow the
companion note's formal dependency graph:

1. `Compatibility.lean` defines the full reconstructed response and hidden
   response.
2. `BranchDefect.lean` isolates the exact defect of a reduced solve.
3. `DualCertificate.lean` packages finite-jet range obstructions.
4. `QuantitativeObstruction.lean` proves the near-cokernel lift bound and joins
   it to the complete future-tail obstruction.
5. `TailCapacity.lean` rules out repair by the complete admissible future tail.
6. `ResidualExposure.lean` proves tail-stable physical residual lower bounds
   and converts every positive finite-order bound into nonflatness.
7. `TerminalCertificate.lean` packages the physical residual contradiction.
8. `SignedMeanInterface.lean` imports the actual upstream signed update,
   iteration ledger, and physical residual modules for concrete instantiation.

The three principal formal endpoints are
`ReducedBranch.exact_reduced_branch_defect`,
`quantitative_range_or_tail_budget_obstruction`, and
`tail_stable_defect_forces_nonflat_physical_residual`. Together they establish
the note's chain from an exact reduced-branch mismatch, through dual and tail
control, to failure of all-order physical residual flatness.

Do not replace source objects with surrogate covariance systems. A nonzero
finite-stage defect is not a counter-proof until a tail-stable certificate
reaches an exact terminal predicate used by the upstream construction.

## Source-Reuse Policy

Import completed proofs from the existing `NavierStokes/` proof system whenever
the full counter-proof needs an upstream identity, estimate, state invariant, or
terminal claim. Keep those results intact. New modules in this directory should
provide only the source-specific adapters, differentiations, primitive
obstruction certificates, and contradiction bridges needed by the downstream
program.
