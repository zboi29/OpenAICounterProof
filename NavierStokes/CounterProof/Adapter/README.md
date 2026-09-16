# Adapter Subsystem

This subsystem imports exact objects and completed proofs from the pinned
`NavierStokes/` construction and turns them into source-specific interfaces for
the abstract counter-proof layers.

The four initial source anchors are:

- `incrementTensor_split`, adapted in `ExactCovariance.lean` as the literal
  identity `ΔW = S + E`, with subtraction and vanishing criteria for `E`.
- The `waveStage_*` identities, packaged by `ReconstructedResponse.lean` as one
  proof object covering mean, covariance, radial source, pressure, and both
  tangential residual channels.
- `native_physical_cross` and `cross_cancels_with_defect`, adapted in
  `ReducedCross.lean` into the two-coordinate reduced response and an exact
  full-cancellation criterion.
- `finite_residual_rates` with `fixedLoss_eq_ledger`, used by
  `ResidualLedger.lean` to reach any prescribed finite rate, including at one
  common explicit cycle for every derivative order through a fixed finite jet.

Import `NavierStokes.CounterProof.SignedMeanInterface` for the complete layer.
That root-level module is the public adapter entry point and contains conclusions
derived from these focused bridges. The adapter modules preserve source objects
and hypotheses; they do not assume a full-response derivative, tail bound, or
cokernel witness before those are proved on the actual construction.
