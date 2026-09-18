import NavierStokes.CounterProof.Adapter.NativeDataObstruction.PhysicalScaleReplacement
import NavierStokes.CounterProof.Adapter.FiniteJetWitness

/-!
# NativeData bridge into dual certificates

The NativeData contradiction and the dual-branch program are logically
independent counter-proof routes:

* the completed NativeData counter-proof refutes availability of `NativeData`
  on the actual geometry and optionally transports to any claim entailing it;
* the dual route detects a full-response mismatch or excludes a target beyond
  complete tail capacity.

The Version 1.1 `JointCokernelCertificate` is the primary terminal target, and
NativeData is not a premise of its abstract construction.  For the pinned
source, however, the NativeData audit is the preferred robust instantiation
bridge.  Its forced physical-scale replacement has an exact finite-prefix
scalar defect and identifies the missing compatible repair.  When a concrete
finite-jet observation exposes that scalar as one coordinate of the complete
response defect, the constructors below turn it into a
`ReducedDefectWitness`.  That witness can supply the reduced side of the two
independent compatibility branches and can feed a `JointCokernelCertificate` once the
same observation functional also satisfies the full-response near-cokernel
and complete-tail capacity hypotheses.

This module deliberately does not manufacture a joint certificate from the
NativeData contradiction alone.  Doing so would conflate two logically
different mechanisms.  It provides the exact bridge data that a genuine
same-witness instantiation must prove.

## Manuscript correspondence

The bridge implements companion-note §8 Phase V (finite-jet dual witness) from
the exact Phase II physical cross defect, after the Phases III–IV full-response
and differentiated reconstruction analysis.  Its remaining joint hypotheses
are precisely §8 Phase VI and the §15 "Weighted gain", "Iteration ledger", and
"Physical residual" checks.  This is the first formal projection toward the
same-witness synthesis in Corollary 6.3; Theorem 6.1 and Proposition 6.2 supply
the branch obligations, and Theorem 7.1 supplies the terminal interpretation.
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

/-- The finite-prefix data exposes a nonzero scalar cross defect with its exact
factorized absolute margin.  This is the quantitative datum needed for tail
comparison, not merely a proposition asserting nonvanishing. -/
theorem defect_ne_zero
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i) :
    actualCrossDefect B N0 c u n x i ≠ 0 ∧
      0 < |actualCrossDefect B N0 c u n x i| ∧
      |actualCrossDefect B N0 c u n x i| =
        |missingWeight (choice B N0).prepared.N (physicalScale n x)| *
          |actualRequestedComponent c u n x i| :=
  actual_cross_defect_ne_zero_of_missing B N0 c u n W.point_mem i
    W.missing_weight_ne_zero W.request_ne_zero

/-- A finite-jet coordinate identifying the complete observed defect with the
physical cross defect yields a rigorous reduced-branch witness.  Its magnitude
is stored in the source-factorized form `|missingWeight| * |request|`, so later
tail estimates can compare against the two physical inputs directly.  This is
the first formal projection from the preferred NativeData source bridge toward
the two branches and primary joint certificate; full-response and
complete-tail capacity obligations remain to be proved for the same
coordinate. -/
def reducedDefectWitness
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i)
    (defect : Obs) (coordinate : Obs →L[ℝ] ℝ)
    (hcoordinate : coordinate defect = actualCrossDefect B N0 c u n x i) :
    ReducedDefectWitness defect where
  functional := coordinate
  magnitude :=
    |missingWeight (choice B N0).prepared.N (physicalScale n x)| *
      |actualRequestedComponent c u n x i|
  magnitude_pos := mul_pos (abs_pos.mpr W.missing_weight_ne_zero)
    (abs_pos.mpr W.request_ne_zero)
  detects := by
    rw [hcoordinate, ← W.defect_ne_zero.2.2]

/-- The witness exported to the certificate layer records all three equivalent
views of the exact finite-prefix margin: absolute defect, factorized physical
source, and exact functional detection. -/
theorem reducedDefectWitness_magnitude
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i)
    (defect : Obs) (coordinate : Obs →L[ℝ] ℝ)
    (hcoordinate : coordinate defect = actualCrossDefect B N0 c u n x i) :
    (W.reducedDefectWitness defect coordinate hcoordinate).magnitude =
        |actualCrossDefect B N0 c u n x i| ∧
      (W.reducedDefectWitness defect coordinate hcoordinate).magnitude =
        |missingWeight (choice B N0).prepared.N (physicalScale n x)| *
          |actualRequestedComponent c u n x i| ∧
      |(W.reducedDefectWitness defect coordinate hcoordinate).functional defect| =
        (W.reducedDefectWitness defect coordinate hcoordinate).magnitude := by
  have hmargin := W.defect_ne_zero.2.2
  exact ⟨hmargin.symm, rfl, by simpa [reducedDefectWitness, hcoordinate] using hmargin⟩

end FinitePrefixObstruction

end NavierStokes.CounterProof.Adapter.NativeDataObstruction
