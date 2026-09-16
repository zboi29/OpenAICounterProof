import NavierStokes.CounterProof.Compatibility
import NavierStokes.CounterProof.AffineLift
import NavierStokes.CounterProof.SchurComplement
import NavierStokes.CounterProof.BranchDefect
import NavierStokes.CounterProof.BranchResolvent
import NavierStokes.CounterProof.DualCertificate
import NavierStokes.CounterProof.QuantitativeObstruction
import NavierStokes.CounterProof.TailCapacity
import NavierStokes.CounterProof.ResidualExposure
import NavierStokes.CounterProof.TerminalCertificate
import NavierStokes.CounterProof.SignedMeanInterface

/-!
# Primitive-compatibility counter-proof program

Aggregate import for the source-grounded Navier–Stokes counter-proof subsystem.

The modules are ordered by proof dependency:

1. compatibility spaces, affine liftability, and Schur reconstruction;
2. reduced/full branch comparison and dual obstruction certificates;
3. complete future-tail capacity and physical residual exposure; and
4. the signed-mean attachment importing completed upstream proofs.

Importing this file provides the reusable theorem layer.  It does not by itself
instantiate a counterexample against the signed-mean construction; concrete
adapters must still connect the abstract spaces and bounds to pinned source
definitions.
-/
