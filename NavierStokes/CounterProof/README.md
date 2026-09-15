# Navier–Stokes Counter-Proof Subsystem

This directory implements the downstream Lean program from the primitive-
liftability research note and its signed-mean companion. The modules follow the
companion note's formal dependency graph:

1. `Compatibility.lean` defines the full reconstructed response and hidden
   response.
2. `BranchDefect.lean` isolates the exact defect of a reduced solve.
3. `DualCertificate.lean` packages finite-jet range obstructions.
4. `TailCapacity.lean` rules out repair by the complete admissible future tail.
5. `ResidualExposure.lean` separates polynomial-sensitivity work from the final
   nonflatness implication.
6. `TerminalCertificate.lean` packages the physical residual contradiction.
7. `SignedMeanInterface.lean` imports the actual upstream signed update,
   iteration ledger, and physical residual modules for concrete instantiation.

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
