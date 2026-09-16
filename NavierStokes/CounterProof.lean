import NavierStokes.CounterProof.Compatibility
import NavierStokes.CounterProof.AffineLift
import NavierStokes.CounterProof.PrimitiveFramework
import NavierStokes.CounterProof.SchurComplement
import NavierStokes.CounterProof.BranchDefect
import NavierStokes.CounterProof.BranchResolvent
import NavierStokes.CounterProof.DualCertificate
import NavierStokes.CounterProof.HilbertCokernel
import NavierStokes.CounterProof.RankCollapse
import NavierStokes.CounterProof.QuantitativeObstruction
import NavierStokes.CounterProof.TailCapacity
import NavierStokes.CounterProof.ResidualExposure
import NavierStokes.CounterProof.DynamicalMismatch
import NavierStokes.CounterProof.LiftCurvature
import NavierStokes.CounterProof.JointObstruction
import NavierStokes.CounterProof.TerminalCertificate
import NavierStokes.CounterProof.SignedMeanInterface

/-!
# Primitive-compatibility counter-proof program

Aggregate import for the source-grounded Navier–Stokes counter-proof subsystem.

The modules are ordered by proof dependency:

1. compatibility spaces, affine liftability, lift cost, and Schur reconstruction;
2. reduced/full branch comparison, cokernel certificates, and rank collapse;
3. local lift curvature, complete future-tail capacity, and residual exposure;
4. the same-witness joint obstruction; and
5. the signed-mean attachment importing completed upstream proofs.

Importing this file provides the reusable theorem layer.  It does not by itself
instantiate a counterexample against the signed-mean construction; concrete
adapters must still connect the abstract spaces and bounds to pinned source
definitions.
-/
