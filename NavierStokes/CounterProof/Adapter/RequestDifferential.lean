import NavierStokes.CounterProof.Adapter.ReconstructedResponse
import NavierStokes.ActualSignedMeanBinding

/-!
# Request differential for the signed covariance solve

The signed covariance increment is linear in the requested stress once the
primary covariance and target are fixed.  This module exposes that literal
source map as a continuous linear map and records its Fréchet derivative.  It
also provides the derivative-level form of the exact cross--remainder split.

No inverse or covariance surrogate is introduced: the coefficients below are
the entries of the source's `H⁻¹.mulVec` solve divided by its actual primary
amplitudes.

## Manuscript correspondence

This module implements equation `eq:exact-remainder`, §3.3 "Exact signed
covariance data", Theorem 4.1 (`thm:covsplit`), and Lean-instantiation Phases
II--IV in
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`.
In particular, `remainderLinearPart` is the source-level object denoted `E₁`:
the remaining quadratic covariance is kept separately so it cannot be counted
as a first-order response.  `hasDerivAt_signedRemainder_component_zero` proves
this first-variation identification after every literal tensor/field
evaluation, without imposing a surrogate global function-space norm.  The
generic derivative helpers at the end are calculus glue for
`FullCompatibility.compatibility_hidden_exact`; they do not encode additional
manuscript assumptions.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

open SignedMeanGain

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The linear-in-request part of the literal signed remainder.  This is the
source representation of the note's
`E₁ = SymCov(primary,curl') + SymCov(old-primary,tangent'+curl')`, simplified
by bilinearity to the two terms already isolated by `signedRemainder_exact`. -/
noncomputable def remainderLinearPart
    (primary old tangent curl : CorrectionState.Oscillation D) :
    LabelSumBounds.Tensor D :=
  LabelSumBounds.symmetricCovariance (old - primary) tangent +
    LabelSumBounds.symmetricCovariance old curl

/-- The quadratic signed covariance, whose derivative vanishes at the zero
request in Theorem 4.1 of the companion note. -/
noncomputable def remainderQuadraticPart
    (tangent curl : CorrectionState.Oscillation D) : LabelSumBounds.Tensor D :=
  CorrectionState.bilinearCovariance (tangent + curl) (tangent + curl)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Base-point helper for Theorem 4.1: the isolated signed-square response is
zero at the zero request.  The manuscript's derivative-zero conclusion follows
after differentiating this genuinely quadratic map; this lemma does not by
itself claim differentiability of the assembled request fields. -/
@[simp] theorem remainderQuadraticPart_zero :
    remainderQuadraticPart (D := D) 0 0 = 0 := by
  funext i j n x
  simp [remainderQuadraticPart, CorrectionState.bilinearCovariance,
    CorrectionState.angularAverage]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Exact source decomposition of the retained remainder into its `E₁`
candidate and the quadratic response.  This is the algebraic input used by
`FullCompatibility.source_averaged_response_eq_reduced_add_hidden`. -/
theorem signedRemainder_eq_linear_add_quadratic
    (primary old tangent curl : CorrectionState.Oscillation D)
    (hp : LabelSumBounds.AngularContinuous primary)
    (ho : LabelSumBounds.AngularContinuous old)
    (ht : LabelSumBounds.AngularContinuous tangent)
    (hc : LabelSumBounds.AngularContinuous curl) :
    LabelSumBounds.signedRemainder primary old tangent curl =
      remainderLinearPart primary old tangent curl +
        remainderQuadraticPart tangent curl := by
  rw [LabelSumBounds.signedRemainder_exact primary old tangent curl hp ho ht hc]
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Bilinearity helper for Theorem 4.1: scalar multiplication in the first
oscillation slot passes through the literal angular covariance integral. -/
theorem bilinearCovariance_smul_left (a : ℝ)
    (u v : CorrectionState.Oscillation D) :
    CorrectionState.bilinearCovariance (a • u) v =
      a • CorrectionState.bilinearCovariance u v := by
  funext i j n x
  simp only [CorrectionState.bilinearCovariance, CorrectionState.angularAverage,
    Pi.smul_apply, smul_eq_mul]
  have hfun : (fun θ : ℝ => a * u n (x, θ) i * v n (x, θ) j) =
      fun θ => a * (u n (x, θ) i * v n (x, θ) j) := by
    funext θ
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Second-slot companion to `bilinearCovariance_smul_left`; together they
make the signed-square response visibly quadratic in the request scale. -/
theorem bilinearCovariance_smul_right (a : ℝ)
    (u v : CorrectionState.Oscillation D) :
    CorrectionState.bilinearCovariance u (a • v) =
      a • CorrectionState.bilinearCovariance u v := by
  funext i j n x
  simp only [CorrectionState.bilinearCovariance, CorrectionState.angularAverage,
    Pi.smul_apply, smul_eq_mul]
  have hfun : (fun θ : ℝ => u n (x, θ) i * (a * v n (x, θ) j)) =
      fun θ => a * (u n (x, θ) i * v n (x, θ) j) := by
    funext θ
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- The `E₁` candidate scales linearly along a request ray, as required in the
first-variation formula of companion-note Theorem 4.1. -/
theorem remainderLinearPart_smul (a : ℝ)
    (primary old tangent curl : CorrectionState.Oscillation D) :
    remainderLinearPart primary old (a • tangent) (a • curl) =
      a • remainderLinearPart primary old tangent curl := by
  unfold remainderLinearPart LabelSumBounds.symmetricCovariance
  rw [bilinearCovariance_smul_right, bilinearCovariance_smul_left,
    bilinearCovariance_smul_right, bilinearCovariance_smul_left]
  simp only [smul_add]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- The retained signed-square term scales quadratically along a request ray;
this helper is what makes its derivative vanish at the zero request. -/
theorem remainderQuadraticPart_smul (a : ℝ)
    (tangent curl : CorrectionState.Oscillation D) :
    remainderQuadraticPart (a • tangent) (a • curl) =
      a ^ 2 • remainderQuadraticPart tangent curl := by
  unfold remainderQuadraticPart
  rw [← smul_add, bilinearCovariance_smul_left,
    bilinearCovariance_smul_right, smul_smul]
  congr 1
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Exact polynomial response along a signed request ray.  This strengthens
`signedRemainder_eq_linear_add_quadratic` into the coefficient identity used
to prove the first variation in Theorem 4.1. -/
theorem signedRemainder_scaled_exact (a : ℝ)
    (primary old tangent curl : CorrectionState.Oscillation D)
    (hp : LabelSumBounds.AngularContinuous primary)
    (ho : LabelSumBounds.AngularContinuous old)
    (ht : LabelSumBounds.AngularContinuous tangent)
    (hc : LabelSumBounds.AngularContinuous curl) :
    LabelSumBounds.signedRemainder primary old (a • tangent) (a • curl) =
      a • remainderLinearPart primary old tangent curl +
        a ^ 2 • remainderQuadraticPart tangent curl := by
  have hat : LabelSumBounds.AngularContinuous (a • tangent) :=
    fun n x i => continuous_const.mul (ht n x i)
  have hac : LabelSumBounds.AngularContinuous (a • curl) :=
    fun n x i => continuous_const.mul (hc n x i)
  rw [signedRemainder_eq_linear_add_quadratic primary old
    (a • tangent) (a • curl) hp ho hat hac,
    remainderLinearPart_smul, remainderQuadraticPart_smul]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Componentwise Fréchet first variation of the literal source remainder at
the zero request.  The derivative is exactly `remainderLinearPart`; the
quadratic covariance contributes zero.  Componentwise evaluation is used
because the repository does not impose an artificial global norm on these
field spaces. -/
theorem hasDerivAt_signedRemainder_component_zero
    (primary old tangent curl : CorrectionState.Oscillation D)
    (hp : LabelSumBounds.AngularContinuous primary)
    (ho : LabelSumBounds.AngularContinuous old)
    (ht : LabelSumBounds.AngularContinuous tangent)
    (hc : LabelSumBounds.AngularContinuous curl)
    (i j : Fin 3) (n : ℕ) (x : D) :
    HasDerivAt
      (fun a : ℝ => LabelSumBounds.signedRemainder primary old
        (a • tangent) (a • curl) i j n x)
      (remainderLinearPart primary old tangent curl i j n x) 0 := by
  have hfun :
      (fun a : ℝ => LabelSumBounds.signedRemainder primary old
        (a • tangent) (a • curl) i j n x) =
      fun a => a * remainderLinearPart primary old tangent curl i j n x +
        a ^ 2 * remainderQuadraticPart tangent curl i j n x := by
    funext a
    have h := congrArg (fun X => X i j n x)
      (signedRemainder_scaled_exact a primary old tangent curl hp ho ht hc)
    simpa using h
  rw [hfun]
  change HasDerivAt
    ((fun a : ℝ => a * remainderLinearPart primary old tangent curl i j n x) +
      fun a => a ^ 2 * remainderQuadraticPart tangent curl i j n x)
    (remainderLinearPart primary old tangent curl i j n x) 0
  simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    zero_mul, mul_zero, add_zero, zero_add, one_mul] using
    ((hasDerivAt_id 0).mul_const
      (remainderLinearPart primary old tangent curl i j n x)).add
        ((hasDerivAt_pow 2 0).mul_const
          (remainderQuadraticPart tangent curl i j n x))

/-- The source's signed inverse solve, bundled as a linear map in the request. -/
def signedIncrementLinearMap (H : SignedCovariance.Mat2)
    (T : SignedCovariance.Vec2) :
    SignedCovariance.Vec2 →ₗ[ℝ] SignedCovariance.Vec2 where
  toFun R := fun j => (H⁻¹.mulVec R) j /
    (2 * SmoothCovariance.amplitudes H T j)
  map_add' R S := by
    funext j
    simp only [Matrix.mulVec_add, Pi.add_apply]
    ring
  map_smul' a R := by
    funext j
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    simp only [RingHom.id_apply]
    ring

/-- Finite dimensionality makes the literal request solve continuous. -/
def signedIncrementCLM (H : SignedCovariance.Mat2)
    (T : SignedCovariance.Vec2) :
    SignedCovariance.Vec2 →L[ℝ] SignedCovariance.Vec2 :=
  (signedIncrementLinearMap H T).toContinuousLinearMap

@[simp]
theorem signedIncrementCLM_apply (H : SignedCovariance.Mat2)
    (T R : SignedCovariance.Vec2) :
    signedIncrementCLM H T R = fun j => SignedCovariance.increment H T R j := by
  rfl

/-- The request derivative is the same inverse solve, with every inverse
factor retained definitionally. -/
theorem hasFDerivAt_signedIncrement (H : SignedCovariance.Mat2)
    (T : SignedCovariance.Vec2) (R : SignedCovariance.Vec2) :
    HasFDerivAt (fun S => fun j => SignedCovariance.increment H T S j)
      (signedIncrementCLM H T) R := by
  change HasFDerivAt (signedIncrementCLM H T) (signedIncrementCLM H T) R
  exact (signedIncrementCLM H T).hasFDerivAt

/-- Differentiating an exact cross--remainder decomposition preserves the
decomposition at the continuous-linear-map level. -/
theorem derivative_split
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {full cross remainder : E → F} {x : E}
    {cross' remainder' : E →L[ℝ] F}
    (hsplit : ∀ y, full y = cross y + remainder y)
    (hcross : HasFDerivAt cross cross' x)
    (hremainder : HasFDerivAt remainder remainder' x) :
    HasFDerivAt full (cross' + remainder') x := by
  rw [show full = fun y => cross y + remainder y from funext hsplit]
  exact hcross.add hremainder

/-- Subtraction form of `derivative_split`: the differentiated hidden response
is exactly the full derivative minus the differentiated cross response. -/
theorem derivative_hidden_eq_remainder
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {full cross remainder : E → F} {x : E}
    {full' cross' remainder' : E →L[ℝ] F}
    (hsplit : ∀ y, full y = cross y + remainder y)
    (hcross : HasFDerivAt cross cross' x)
    (hremainder : HasFDerivAt remainder remainder' x)
    (hfull : HasFDerivAt full full' x) :
    full' - cross' = remainder' := by
  have hsum := derivative_split hsplit hcross hremainder
  have heq : full' = cross' + remainder' := hfull.unique hsum
  rw [heq]
  abel

end NavierStokes.CounterProof.Adapter
