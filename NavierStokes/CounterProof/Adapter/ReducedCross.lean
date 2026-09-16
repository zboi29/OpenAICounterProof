import NavierStokes.CounterProof.Adapter.ReconstructedResponse
import NavierStokes.CrossBasedMeanComposition

/-!
# Reduced cross-response adapter

The signed request cancels the intended physical cross channel only up to the
literal cross defect retained by the source.  The main helper below turns the
upstream cancellation identity into an exact equivalence: reduced cancellation
is full cancellation at a point exactly when the radial divergence of that
defect vanishes there.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

open SignedMeanGain CrossBasedMeanComposition
open Set MeanIncrementBounds CorrectionState

open PartitionedCovariance SignedWaveUpdate

/-- The two physical cross coordinates of the native signed assembly recover
the requested stress vector exactly.  This packages the source's componentwise
theorem as the concrete two-coordinate reduced response used by the companion
note. -/
theorem native_reduced_cross_realizes_request
    {d h : ℝ} {vr vt : TorusInverse.Plane} {sys : SlotSystem d h vr vt}
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position)
    (T σ : SignedWaveUpdate.Vec2)
    (hcone : ∀ U, mask d (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (P U).matrix (chartTarget h q N T U)) :
    let primary := nativeAssembly P hdet (physicalOuter h N) (physicalViscosity h N)
      (fun U => SmoothCovariance.amplitudes (P U).matrix (chartTarget h q N T U)) q x
    let signed := nativeAssembly P hdet (physicalOuter h N) (physicalViscosity h N)
      (fun U => SignedCovariance.increment (P U).matrix (chartTarget h q N T U)
        (SignedCovariance.chartStress h N σ U)) q x
    (fun i => doubleAverage (fun Y θ => primary Y θ 0 * signed Y θ i.succ +
      signed Y θ 0 * primary Y θ i.succ)) = σ := by
  dsimp only
  funext i
  exact native_physical_cross hdet N hN P hq hqN x T σ hcone i

/-- The exact criterion under which the source's reduced cross cancellation
becomes cancellation of the complete observed cross response. -/
theorem cross_cancellation_iff_divergence_defect_zero
    (G : Geometry) (e : ℕ) (he : e = 2 ∨ e = 1)
    {f X : SignedMeanGain.ScalarField SignedMeanGain.Point} (hf : SmoothOn G.domain f)
    (hs : ∀ n, LocalSignedRequest.MovingSupport
      G.patch.a G.patch.b G.coord G.region.carrier (f n))
    (hX : MovingField G X)
    (hD : SmoothOn G.strip.domain (crossDefect G e f X))
    (n : ℕ) {x : SignedMeanGain.Point} (hx : x ∈ G.strip.domain) :
    (StateMomentBalances.meanBar f n x +
        StateMomentBalances.meanBar (G.operators.radialDiv (e : ℝ) X) n x =
      removedBump G e f n x) ↔
      G.operators.radialDiv (e : ℝ) (crossDefect G e f X) n x = 0 := by
  rw [cross_cancels_with_defect G e he hf hs hX hD n hx]
  constructor <;> intro h
  · linarith
  · rw [h, add_zero]

/-- A nonzero divergence defect proves that the reduced cross identity is not
the complete cancellation identity at the same source point. -/
theorem reduced_cross_not_full_of_divergence_defect_ne_zero
    (G : Geometry) (e : ℕ) (he : e = 2 ∨ e = 1)
    {f X : SignedMeanGain.ScalarField SignedMeanGain.Point} (hf : SmoothOn G.domain f)
    (hs : ∀ n, LocalSignedRequest.MovingSupport
      G.patch.a G.patch.b G.coord G.region.carrier (f n))
    (hX : MovingField G X)
    (hD : SmoothOn G.strip.domain (crossDefect G e f X))
    (n : ℕ) {x : SignedMeanGain.Point} (hx : x ∈ G.strip.domain)
    (hdefect : G.operators.radialDiv (e : ℝ) (crossDefect G e f X) n x ≠ 0) :
    StateMomentBalances.meanBar f n x +
        StateMomentBalances.meanBar (G.operators.radialDiv (e : ℝ) X) n x ≠
      removedBump G e f n x := by
  intro hfull
  exact hdefect ((cross_cancellation_iff_divergence_defect_zero
    G e he hf hs hX hD n hx).mp hfull)

/-- Simultaneous theta/axial form of the exact reduced-cross criterion.  Both
physical request channels cancel completely exactly when both retained
divergence defects vanish at the same source point. -/
theorem tangential_cross_cancellation_iff_defects_zero
    (G : Geometry)
    {fθ Xθ fz Xz : SignedMeanGain.ScalarField SignedMeanGain.Point}
    (hfθ : SmoothOn G.domain fθ)
    (hsθ : ∀ n, LocalSignedRequest.MovingSupport
      G.patch.a G.patch.b G.coord G.region.carrier (fθ n))
    (hXθ : MovingField G Xθ)
    (hDθ : SmoothOn G.strip.domain (crossDefect G 2 fθ Xθ))
    (hfz : SmoothOn G.domain fz)
    (hsz : ∀ n, LocalSignedRequest.MovingSupport
      G.patch.a G.patch.b G.coord G.region.carrier (fz n))
    (hXz : MovingField G Xz)
    (hDz : SmoothOn G.strip.domain (crossDefect G 1 fz Xz))
    (n : ℕ) {x : SignedMeanGain.Point} (hx : x ∈ G.strip.domain) :
    ((StateMomentBalances.meanBar fθ n x +
          StateMomentBalances.meanBar (G.operators.radialDiv 2 Xθ) n x =
        removedBump G 2 fθ n x) ∧
      (StateMomentBalances.meanBar fz n x +
          StateMomentBalances.meanBar (G.operators.radialDiv ((1 : ℕ) : ℝ) Xz) n x =
        removedBump G 1 fz n x)) ↔
      (G.operators.radialDiv 2 (crossDefect G 2 fθ Xθ) n x = 0 ∧
        G.operators.radialDiv ((1 : ℕ) : ℝ) (crossDefect G 1 fz Xz) n x = 0) := by
  exact and_congr
    (cross_cancellation_iff_divergence_defect_zero
      G 2 (Or.inl rfl) hfθ hsθ hXθ hDθ n hx)
    (cross_cancellation_iff_divergence_defect_zero
      G 1 (Or.inr rfl) hfz hsz hXz hDz n hx)

/- TODO(inverse-loss propagation): Implement the request derivative and its
weighted inverse bounds from
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`,
section "Lean instantiation and formalization strategy," Phase IV, and the
"Flat edge" checklist row.  The source chain must retain
`SignedMeanGain.signed_tensor_bounds`,
`SignedCovariance.increment_eq_inverse`, and
`SmoothCovariance.contDiffOn_inverse_solution`, while discharging the explicit
flat-annulus warning in `NavierStokes/CycleContinuationInvariant.lean` before
constructing a source instance of `relativeResponse` in the physical jet norm. -/

end NavierStokes.CounterProof.Adapter
