import NavierStokes.CounterProof.Adapter.NativeDataObstruction.GeometryContradiction

/-!
# Physical-scale replacement and its exact defect

The actual correction cycle bypasses the unavailable normalized `NativeData`
package for one specific purpose: it proves a physical-scale cross identity
with a finite partition.  This module records exactly what that bypass proves
and, equally importantly, what it does not prove.

At an arbitrary band,

`actual cross = partitionFactor × requested stress`,

and therefore

`actual cross − requested stress = −missingWeight × requested stress`.

Only beyond the explicit partition threshold does the missing component
vanish and every finite physical jet of the cross agree with the request.  The
tail identity can replace the cross-cancellation field used by
`CorrectionAnalyticStep.StepData`; it does not construct the impossible
`NativeData` package or automatically recover every assembly, inverse,
reconstruction, and mean-gain consequence formerly obtained from that package.

For the pinned source this replacement is the common origin of the preferred
joint instantiation: its omitted finite-prefix component seeds the reduced
defect, while the compatible response needed to repair that component supplies
the lift/capacity obligation for the full-compatible branch.  NativeData is not logically
necessary for either branch or for `JointCokernelCertificate`, and direct
NativeData closure remains independently sufficient for endpoints that entail
the package.

## Manuscript correspondence

These identities implement the source audit demanded by companion-note §8
Phase II and the §15 "Cross cancellation" row.  Keeping the arbitrary-band
factor visible is also necessary for §8 Phases III–VI: hidden-response
subtraction, differentiation, finite-jet witness selection, and complete-tail
estimates must be established for the physical replacement, not inherited
from the unavailable normalized interface.  Theorem 6.1, Proposition 6.2, and
Corollary 6.3 describe the two branch estimates and their primary same-witness
synthesis.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter.NativeDataObstruction

open CorrectionInitialization.ActualPrimary
open ActualPrimaryCovariance

abbrev ActualPoint := ActualSignedMeanBinding.Point

/-- The actual two-coordinate cross response at a fixed band and point. -/
noncomputable def actualCrossComponent (B N0 : ℕ)
    (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint)
    (n : ℕ) (x : ActualPoint) (i : Fin 2) : ℝ :=
  StateMomentBalances.meanBar
    (ActualSignedMeanBinding.actualCross B N0 c u 0 i.succ) n x

/-- The physical request component that the cross response is intended to
realize. -/
noncomputable def actualRequestedComponent
    (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint)
    (n : ℕ) (x : ActualPoint) (i : Fin 2) : ℝ :=
  LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
    ActualInitialization.geometry.coord c u n x i

/-- Exact finite-prefix component omitted by the physical partition tail. -/
noncomputable def actualMissingComponent (B N0 : ℕ)
    (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint)
    (n : ℕ) (x : ActualPoint) (i : Fin 2) : ℝ :=
  missingWeight (choice B N0).prepared.N (physicalScale n x) *
    actualRequestedComponent c u n x i

/-- Scalar mismatch between the actual cross response and requested stress.
This is the form consumed by finite-jet obstruction functionals. -/
noncomputable def actualCrossDefect (B N0 : ℕ)
    (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint)
    (n : ℕ) (x : ActualPoint) (i : Fin 2) : ℝ :=
  actualCrossComponent B N0 c u n x i -
    actualRequestedComponent c u n x i

/-- Exact physical-scale replacement for the unavailable global native
identity.  It retains the partition factor at every band. -/
theorem actual_cross_eq_partition_factor
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint) (n : ℕ) {x : ActualPoint}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    actualCrossComponent B N0 c u n x i =
      partitionFactor B N0 n x * actualRequestedComponent c u n x i := by
  exact ActualSignedMeanBinding.requested_cross_factor B N0 c u n hx i

/-- Exact arbitrary-band defect of the physical replacement. -/
theorem actual_cross_defect_eq_neg_missing
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint) (n : ℕ) {x : ActualPoint}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    actualCrossDefect B N0 c u n x i =
      -actualMissingComponent B N0 c u n x i := by
  simpa [actualCrossDefect, actualCrossComponent, actualRequestedComponent,
    actualMissingComponent, neg_mul] using
    (ActualSignedMeanBinding.requested_cross_defect B N0 c u n hx i)

/-- Exact cancellation criterion for the physical replacement: cancellation
at a band is equivalent to vanishing of its omitted component. -/
theorem actual_cross_cancels_iff_missing_eq_zero
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint) (n : ℕ) {x : ActualPoint}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    actualCrossComponent B N0 c u n x i = actualRequestedComponent c u n x i ↔
      actualMissingComponent B N0 c u n x i = 0 := by
  have hdefect := actual_cross_defect_eq_neg_missing B N0 c u n hx i
  constructor
  · intro hcancel
    rw [actualCrossDefect, hcancel, sub_self] at hdefect
    exact neg_eq_zero.mp hdefect.symm
  · intro hmissing
    apply sub_eq_zero.mp
    rw [show actualCrossComponent B N0 c u n x i -
      actualRequestedComponent c u n x i =
        actualCrossDefect B N0 c u n x i from rfl, hdefect, hmissing, neg_zero]

/-- A nonzero missing weight and nonzero request give an exact finite-prefix
failure of physical cross cancellation. -/
theorem actual_cross_ne_request_of_missing
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint) (n : ℕ) {x : ActualPoint}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2)
    (hweight : missingWeight (choice B N0).prepared.N (physicalScale n x) ≠ 0)
    (hrequest : actualRequestedComponent c u n x i ≠ 0) :
    actualCrossComponent B N0 c u n x i ≠ actualRequestedComponent c u n x i := by
  intro hcancel
  have hzero := (actual_cross_cancels_iff_missing_eq_zero B N0 c u n hx i).mp hcancel
  exact (mul_ne_zero hweight hrequest) hzero

/-- Equivalent defect-level statement used by certificate constructors. -/
theorem actual_cross_defect_ne_zero_of_missing
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint) (n : ℕ) {x : ActualPoint}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2)
    (hweight : missingWeight (choice B N0).prepared.N (physicalScale n x) ≠ 0)
    (hrequest : actualRequestedComponent c u n x i ≠ 0) :
    actualCrossDefect B N0 c u n x i ≠ 0 := by
  rw [actual_cross_defect_eq_neg_missing B N0 c u n hx i]
  exact neg_ne_zero.mpr (mul_ne_zero hweight hrequest)

/-- Beyond the actual partition threshold, the missing component vanishes and
exact cross cancellation is recovered. -/
theorem actual_cross_tail_exact
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : ActualPoint}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    actualCrossComponent B N0 c u n x i = actualRequestedComponent c u n x i :=
  ActualSignedMeanBinding.requested_cross_tail B N0 c u hn hx i

/-- Every finite physical jet of the cross and request agrees on the same
tail.  This is the strongest direct cross-level replacement currently
available for the unavailable native package. -/
theorem actual_cross_tail_jets
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : ActualPoint}
    (hx : x ∈ ActualInitialization.geometry.strip.domain)
    (i : Fin 2) (m : ℕ) :
    iteratedFDeriv ℝ m
        (StateMomentBalances.meanBar
          (ActualSignedMeanBinding.actualCross B N0 c u 0 i.succ) n) x =
      iteratedFDeriv ℝ m
        (fun y => LocalSignedRequest.requestedStress
          ActualInitialization.geometry.patch ActualInitialization.geometry.coord
          c u n y i) x :=
  ActualSignedMeanBinding.requested_cross_tail_jets B N0 c u hn hx i m

end NavierStokes.CounterProof.Adapter.NativeDataObstruction
