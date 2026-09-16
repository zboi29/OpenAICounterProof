# Liftability Subsystem

This subsystem formalizes the source-independent geometry of primitive
compatibility and liftability.

- `AffineLift.lean` proves the affine first-order range criterion and its
  independence from the chosen constrained tangent.
- `PrimitiveFramework.lean` defines admissible fibers, extended-valued lift
  cost, branch extinction, and endpoint compatibility.
- `LiftCurvature.lean` proves vertical-curvature consequences and an exact
  hidden-holonomy model in local Banach charts.

Import `NavierStokes.CounterProof.Liftability` for the complete layer. Keep
this subsystem independent of signed-mean implementation details. Concrete
source adapters belong at the root interface, while dual and terminal
consequences belong in `Certificates/`.
