# Navier–Stokes Counter-Proof Subsystem

This directory implements the downstream Lean program from the primitive-
liftability research note and the revised Version 1.1 signed-mean companion,
[`Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`](../../docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex).
The modules follow the companion note's formal dependency graph:

1. `Compatibility.lean` defines the full reconstructed response and hidden
   response.
2. `AffineLift.lean` proves that first-order liftability is exactly membership
   in the homogeneous compatibility range and that this test is independent of
   the chosen particular constrained tangent.
3. `SchurComplement.lean` derives the reconstruction and full-response Schur
   formulas and isolates the kernel condition for gauge independence.
4. `BranchDefect.lean` isolates the exact defect of a reduced solve.
5. `BranchResolvent.lean` proves the exact correct-branch resolvent and its
   relative-response inverse and displacement bounds.
6. `DualCertificate.lean` packages finite-jet range obstructions.
7. `QuantitativeObstruction.lean` proves the near-cokernel lift bound and joins
   it to the complete future-tail obstruction.
8. `TailCapacity.lean` rules out repair by the complete admissible future tail.
9. `ResidualExposure.lean` proves tail-stable physical residual lower bounds
   and converts every positive finite-order bound into nonflatness.
10. `TerminalCertificate.lean` packages the physical residual contradiction.
11. `SignedMeanInterface.lean` imports the actual upstream signed update,
   iteration ledger, and physical residual modules for concrete instantiation.

The three principal formal endpoints are
`ReducedBranch.exact_reduced_branch_defect`,
`quantitative_range_or_tail_budget_obstruction`, and
`tail_stable_defect_forces_nonflat_physical_residual`. Together they establish
the note's chain from an exact reduced-branch mismatch, through dual and tail
control, to failure of all-order physical residual flatness.

Version 1.1 strengthens the preferred endpoint to a joint certificate built
from one dual direction. Concrete instantiations should use that witness both
to prove that the reduced-branch defect survives every covered future
correction and to rule out reaching the full-compatible target within total
tail capacity. Keep the two conclusions modular: either independently closes a
counter-proof branch, and neither implication is reversible.

The preceding reconstruction layer is supplied by
`admissible_first_order_lift_iff_mem_range`,
`CompatibilityBlocks.fullCompatibility_eq_schur`, and
`correctBranch_sub_reducedBranch_relative`. The associated helper theorems
prove affine-origin independence, hidden-representative independence, the full
inverse bound, and the correct-versus-reduced branch displacement estimate.

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
