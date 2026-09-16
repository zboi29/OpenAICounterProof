# Reconstruction Subsystem

This subsystem isolates the algebra connecting the full compatibility problem
to its reduced signed-mean branch.

- `SchurComplement.lean` derives reconstruction, full-response Schur formulas,
  and the kernel condition needed for gauge independence.
- `BranchDefect.lean` records the exact hidden defect left by a reduced solve.
- `BranchResolvent.lean` compares the correct and reduced branches and proves
  inverse and displacement bounds.

Import `NavierStokes.CounterProof.Reconstruction` for the complete layer. These
modules establish exact branch mechanics only; tail stability and terminal
contradictions are deliberately discharged by `Certificates/`.
