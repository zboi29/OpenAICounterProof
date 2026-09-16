import NavierStokes.CounterProof.Compatibility
import NavierStokes.CounterProof.Liftability
import NavierStokes.CounterProof.Reconstruction
import NavierStokes.CounterProof.Certificates
import NavierStokes.CounterProof.SignedMeanInterface

/-!
# Primitive-compatibility counter-proof program

Aggregate import for the source-grounded Navier–Stokes counter-proof subsystem.

The implementation is organized into three dependency-oriented subsystems:

1. `Liftability` for affine range tests, lift cost, endpoints, and curvature;
2. `Reconstruction` for full/reduced branch mechanics and resolvent bounds; and
3. `Certificates` for cokernel, tail, residual, joint, and terminal closure.

The shared compatibility blocks and signed-mean attachment remain root modules.

Importing this file provides the reusable theorem layer.  It does not by itself
instantiate a counterexample against the signed-mean construction; concrete
adapters must still connect the abstract spaces and bounds to pinned source
definitions.
-/
