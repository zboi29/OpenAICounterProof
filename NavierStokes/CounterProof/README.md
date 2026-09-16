# Navier–Stokes Counter-Proof Subsystem

This directory implements the primitive-compatibility counter-proof program
from the general research note and its revised Version 1.1 signed-mean
companion. The layout separates reusable liftability geometry, concrete branch
reconstruction, and contradiction certificates. Relocation changes import
paths but preserves the public `NavierStokes.CounterProof` declaration
namespace.

The governing sources are the
[`Primitive_Liftability_Obstructions_NSE_Research_Note.tex`](../../docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex)
framework and its downstream
[`Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`](../../docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex).

## Subsystems

- [`Liftability/`](Liftability/) develops the source-independent affine range,
  lift-cost, endpoint, curvature, and holonomy framework.
- [`Reconstruction/`](Reconstruction/) derives the full and reduced signed-mean
  branch formulas and quantifies their exact displacement.
- [`Certificates/`](Certificates/) turns cokernel witnesses, tail bounds, and
  residual exposure into independent or unified terminal obstructions.

Each directory has a focused README and an umbrella import at
`NavierStokes.CounterProof.{Liftability,Reconstruction,Certificates}`.

## Root Modules

`Compatibility.lean` remains at the root because its block decomposition is
shared vocabulary across the proof program. `SignedMeanInterface.lean` also
remains here: it is the attachment boundary to completed proofs in the
upstream `NavierStokes/` system, not an abstract obstruction component.
The three other root modules are import-only entry points for their matching
subdirectories.

The dependency flow is:

`(Compatibility → Reconstruction) + Liftability → Certificates → SignedMeanInterface`.

The principal unified endpoint is
`JointCokernelCertificate.joint_obstruction`; its two conclusions remain
independently usable. `JointCokernelCertificate.residual_lower_bound` exposes
the surviving witness through the physical residual.

## Formalization Discipline

Use the exact source objects and import completed upstream identities,
estimates, invariants, and terminal claims rather than recreating them here.
New code should be limited to source adapters, differentiations, primitive
obstruction certificates, and contradiction bridges. A nonzero finite-stage
defect is insufficient: the certificate must cover every admissible future
correction and reach a pinned upstream endpoint.
