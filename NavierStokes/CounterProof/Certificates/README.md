# Certificates Subsystem

This subsystem converts branch data into counter-proof certificates that
survive the complete admissible correction tail.

- `DualCertificate.lean`, `HilbertCokernel.lean`, and `RankCollapse.lean`
  establish exact or near cokernel witnesses and branch extinction.
- `TailCapacity.lean`, `QuantitativeObstruction.lean`, and
  `JointObstruction.lean` compare witness margins with all covered future
  corrections and unify the two Version 1.1 branches.
- `ResidualExposure.lean`, `DynamicalMismatch.lean`, and
  `TerminalCertificate.lean` carry the surviving mismatch to physical
  nonflatness and terminal contradiction predicates.

Import `NavierStokes.CounterProof.Certificates` for the complete layer. Prefer
`JointCokernelCertificate.joint_obstruction` when one witness supports both
branches, but preserve the independent branch endpoints for concrete adapters.
