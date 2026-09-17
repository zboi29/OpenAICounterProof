import NavierStokes.CounterProof.Adapter.NativeDataObstruction.PhysicalScaleReplacement
import NavierStokes.CounterProof.Adapter.FiniteJetWitness

/-!
# NativeData obstruction feedback into dual certificates

The NativeData contradiction and the dual-branch program are independent
counter-proof routes:

* the standalone route refutes any claimed endpoint that entails existence of
  `NativeData` on the actual geometry;
* the dual route detects a full-response mismatch or excludes a target beyond
  complete tail capacity.

They can nevertheless reinforce one another.  The physical-scale bypass for
cross cancellation has an exact finite-prefix scalar defect.  When a concrete
finite-jet observation exposes that scalar as one coordinate of the complete
response defect, the constructors below turn it into a
`ReducedDefectWitness`.  That witness can supply the reduced side of the
independent dual branches and can feed a `JointCokernelCertificate` once the
same observation functional also satisfies the full-response near-cokernel
and complete-tail capacity hypotheses.

This module deliberately does not manufacture a joint certificate from the
NativeData contradiction alone.  Doing so would conflate two logically
different mechanisms.  It provides the exact bridge data that a genuine
same-witness instantiation must prove.

## Manuscript correspondence

The bridge implements companion-note §8 Phase V (finite-jet dual witness) from
the exact Phase-II physical cross defect.  Its remaining joint hypotheses are
precisely §8 Phase VI and the §15 "Weighted gain", "Iteration ledger", and
"Physical residual" checks.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter.NativeDataObstruction

open NavierStokes.CounterProof
open CorrectionInitialization.ActualPrimary
open ActualPrimaryCovariance

variable {Obs : Type*} [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]

/-- Concrete nonvanishing data for the physical-scale finite-prefix defect.
Unlike `NativeRouteAvailable`, this record belongs to the feedback path into
the reduced/joint certificate machinery. -/
structure FinitePrefixObstruction
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint) (n : ℕ)
    (x : ActualPoint) (i : Fin 2) : Prop where
  point_mem : x ∈ ActualInitialization.geometry.strip.domain
  missing_weight_ne_zero :
    missingWeight (choice B N0).prepared.N (physicalScale n x) ≠ 0
  request_ne_zero : actualRequestedComponent c u n x i ≠ 0

namespace FinitePrefixObstruction

/-- The finite-prefix data exposes a nonzero scalar cross defect. -/
theorem defect_ne_zero
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i) :
    actualCrossDefect B N0 c u n x i ≠ 0 :=
  actual_cross_defect_ne_zero_of_missing B N0 c u n W.point_mem i
    W.missing_weight_ne_zero W.request_ne_zero

/-- A finite-jet coordinate identifying the complete observed defect with the
physical cross defect yields a rigorous reduced-branch witness.  This is the
interface through which NativeData analysis can feed the dual or joint route. -/
def reducedDefectWitness
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i)
    (defect : Obs) (coordinate : Obs →L[ℝ] ℝ)
    (hcoordinate : coordinate defect = actualCrossDefect B N0 c u n x i) :
    ReducedDefectWitness defect where
  functional := coordinate
  magnitude := |actualCrossDefect B N0 c u n x i|
  magnitude_pos := abs_pos.mpr W.defect_ne_zero
  detects := by rw [hcoordinate]

/-- The witness exported to the certificate layer detects the exact absolute
finite-prefix margin, rather than merely an unspecified positive constant. -/
theorem reducedDefectWitness_magnitude
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i)
    (defect : Obs) (coordinate : Obs →L[ℝ] ℝ)
    (hcoordinate : coordinate defect = actualCrossDefect B N0 c u n x i) :
    (W.reducedDefectWitness defect coordinate hcoordinate).magnitude =
      |actualCrossDefect B N0 c u n x i| :=
  rfl

end FinitePrefixObstruction

end NavierStokes.CounterProof.Adapter.NativeDataObstruction
