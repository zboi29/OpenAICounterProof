import NavierStokes.CounterProof.Certificates.TailCapacity

/-!
# Terminal residual exposure

The source-specific work must prove an exposure bridge from flat physical
residuals to flat observed mismatches.  The final logical contradiction is kept
separate and reusable here.

The quantitative route in this file is stronger: it starts from a dual defect
that survives the complete future tail, controls the observation error, pays a
polynomial sensitivity loss, and constructs an explicit finite-order lower
bound for the physical residual.  That lower bound is then shown incompatible
with `FlatAtZero`.

`flatAtZero_mismatch_of_polynomial_sensitivity` formalizes the forward
flatness implication in Proposition `prop:residualleakage`, “Primitive
mismatch--residual leakage”, and Corollary `cor:jetleakage`, “Finite-jet
Navier--Stokes form”, in §8.2 of
`docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex`.  In a
finite-jet application the finitely many residual derivatives are first
collected into one normed residual vector; the theorem then pays the fixed
polynomial sensitivity loss without assuming an algebraic mismatch lower
bound.
-/

namespace NavierStokes.CounterProof

/-- All-order decay at the positive side of `q = 0`: for every natural order
`N`, the size is eventually bounded by `C · q^N`, with `C` allowed to depend on
`N`. -/
def FlatAtZero (size : ℝ → ℝ) : Prop :=
  ∀ N : ℕ, ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
    ∀ q : ℝ, 0 < q → q < ε → size q ≤ C * q ^ N

/-- Polynomial observation sensitivity preserves all-order flatness.  The
residual estimate is requested at order `N + M`, exactly paying the fixed
loss `M` and leaving order `N` for the observed mismatch.  This is the
abstract forward implication used by both Proposition `prop:residualleakage`
and its finite-jet Corollary `cor:jetleakage` in the general research note. -/
theorem flatAtZero_mismatch_of_polynomial_sensitivity
    (residualSize mismatchSize : ℝ → ℝ) {C radius : ℝ} {M : ℕ}
    (hC : 0 ≤ C) (hradius : 0 < radius)
    (hresponse : ∀ q : ℝ, 0 < q → q < radius →
      mismatchSize q ≤ (C / q ^ M) * residualSize q)
    (hflat : FlatAtZero residualSize) :
    FlatAtZero mismatchSize := by
  intro N
  obtain ⟨Cresidual, ε, hCresidual, hε, hresidual⟩ := hflat (N + M)
  refine ⟨C * Cresidual, min radius ε, mul_nonneg hC hCresidual,
    lt_min hradius hε, ?_⟩
  intro q hq hqmin
  have hqradius : q < radius := hqmin.trans_le (min_le_left _ _)
  have hqε : q < ε := hqmin.trans_le (min_le_right _ _)
  have hqpow : 0 ≤ q ^ M := pow_nonneg hq.le M
  calc
    mismatchSize q ≤ (C / q ^ M) * residualSize q :=
      hresponse q hq hqradius
    _ ≤ (C / q ^ M) * (Cresidual * q ^ (N + M)) :=
      mul_le_mul_of_nonneg_left (hresidual q hq hqε) (div_nonneg hC hqpow)
    _ = (C * Cresidual) * q ^ N := by
      rw [pow_add]
      field_simp [hq.ne']

/-- A uniform positive algebraic lower bound near `q = 0`. -/
structure AlgebraicLowerBound (size : ℝ → ℝ) where
  /-- Strictly positive leading coefficient. -/
  coefficient : ℝ
  /-- Finite power of `q` appearing in the lower bound. -/
  order : ℕ
  /-- Positive radius on which the lower bound is valid. -/
  radius : ℝ
  /-- Positivity of the leading coefficient. -/
  coefficient_pos : 0 < coefficient
  /-- Positivity of the validity radius. -/
  radius_pos : 0 < radius
  /-- Uniform lower estimate throughout the punctured positive neighborhood. -/
  lower_bound : ∀ q : ℝ, 0 < q → q < radius → coefficient * q ^ order ≤ size q

namespace AlgebraicLowerBound

/-- Any positive finite-order lower bound rules out decay to every order. -/
theorem not_flat {size : ℝ → ℝ} (W : AlgebraicLowerBound size) :
    ¬ FlatAtZero size := by
  intro hflat
  obtain ⟨C, ε, hC, hε, hupper⟩ := hflat (W.order + 1)
  obtain ⟨x, hx, hCx⟩ := exists_pos_mul_lt W.coefficient_pos (C + 1)
  have hmin : 0 < min x (min ε W.radius) := by
    exact lt_min hx (lt_min hε W.radius_pos)
  obtain ⟨q, hq, hqmin⟩ := exists_between hmin
  have hqx : q < x := hqmin.trans_le (min_le_left _ _)
  have hqε : q < ε :=
    hqmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hqradius : q < W.radius :=
    hqmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hCq : C * q < W.coefficient := by
    calc
      C * q ≤ (C + 1) * q := by nlinarith
      _ < (C + 1) * x := mul_lt_mul_of_pos_left hqx (by linarith)
      _ < W.coefficient := hCx
  have hlower := W.lower_bound q hq hqradius
  have hu := hupper q hq hqε
  have hpow : 0 < q ^ W.order := pow_pos hq W.order
  have hproduct : W.coefficient * q ^ W.order ≤ (C * q) * q ^ W.order := by
    calc
      W.coefficient * q ^ W.order ≤ size q := hlower
      _ ≤ C * q ^ (W.order + 1) := hu
      _ = (C * q) * q ^ W.order := by rw [pow_succ]; ring
  have hcoefficient : W.coefficient ≤ C * q :=
    le_of_mul_le_mul_right hproduct hpow
  exact (not_lt_of_ge hcoefficient) hCq

end AlgebraicLowerBound

/-- A proved transfer from the terminal physical residual to the selected
observable mismatch.  Polynomial sensitivity is established by concrete
instances, not assumed globally by the counter-proof core. -/
structure ResidualExposure (residualSize mismatchSize : ℝ → ℝ) where
  /-- Flat physical residuals force flat observed mismatches. -/
  flat_transfer : FlatAtZero residualSize → FlatAtZero mismatchSize

/-- Package a proved polynomial sensitivity estimate as the reusable
`ResidualExposure` interface. -/
theorem ResidualExposure.ofPolynomialSensitivity
    (residualSize mismatchSize : ℝ → ℝ) {C radius : ℝ} {M : ℕ}
    (hC : 0 ≤ C) (hradius : 0 < radius)
    (hresponse : ∀ q : ℝ, 0 < q → q < radius →
      mismatchSize q ≤ (C / q ^ M) * residualSize q) :
    ResidualExposure residualSize mismatchSize where
  flat_transfer :=
    flatAtZero_mismatch_of_polynomial_sensitivity residualSize mismatchSize
      hC hradius hresponse

namespace ResidualExposure

/-- Contrapositive exposure principle: a nonflat observed mismatch forces a
nonflat physical residual. -/
theorem residual_not_flat_of_mismatch_not_flat
    {residualSize mismatchSize : ℝ → ℝ}
    (E : ResidualExposure residualSize mismatchSize)
    (hmismatch : ¬ FlatAtZero mismatchSize) :
    ¬ FlatAtZero residualSize :=
  mt E.flat_transfer hmismatch

end ResidualExposure

variable {Obs Residual : Type*}
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
  [NormedAddCommGroup Residual] [NormedSpace ℝ Residual]

/-- Pointwise tail-stable transfer from an observed interface defect to a
physical residual norm.  This is the quantitative core of the residual
exposure proposition in the companion note.  The conclusion pays half of the
surviving observed magnitude for exposure error and divides by the sensitivity
bound of `functional ∘ exposure`. -/
theorem tail_stable_residual_lower_bound
    (functional : Obs →L[ℝ] ℝ) (exposure : Residual →L[ℝ] Obs)
    {defect futureTail mismatch error : Obs} {residual : Residual}
    {magnitude θ sensitivity : ℝ}
    (hmagnitude : 0 ≤ magnitude)
    (_htheta_nonneg : 0 ≤ θ) (htheta : θ < 1)
    (hsensitivity : 0 < sensitivity)
    (hmismatch : mismatch = defect + futureTail)
    (hexposure : mismatch = exposure residual + error)
    (hdefect : magnitude ≤ |functional defect|)
    (htail : |functional futureTail| ≤ θ * magnitude)
    (herror : |functional error| ≤ (1 - θ) * magnitude / 2)
    (hexposure_norm : ‖functional.comp exposure‖ ≤ sensitivity) :
    ((1 - θ) * magnitude / 2) / sensitivity ≤ ‖residual‖ := by
  have hbase : 0 ≤ (1 - θ) * magnitude :=
    mul_nonneg (sub_nonneg.mpr htheta.le) hmagnitude
  have hsurvives : (1 - θ) * magnitude ≤ |functional mismatch| := by
    have h := interface_defect_survives_tail hdefect htail
    simpa [hmismatch, map_add] using h
  have hobserved : (1 - θ) * magnitude / 2 ≤ |functional (exposure residual)| := by
    have hsum :
        |functional mismatch| ≤
          |functional (exposure residual)| + |functional error| := by
      rw [hexposure, map_add]
      exact abs_add_le _ _
    have hcombined :
        (1 - θ) * magnitude ≤
          |functional (exposure residual)| + (1 - θ) * magnitude / 2 :=
      hsurvives.trans (hsum.trans (add_le_add_right herror _))
    linarith
  apply (div_le_iff₀ hsensitivity).2
  calc
    (1 - θ) * magnitude / 2 ≤ |functional (exposure residual)| := hobserved
    _ = ‖(functional.comp exposure) residual‖ := by
      rw [ContinuousLinearMap.comp_apply, Real.norm_eq_abs]
    _ ≤ ‖functional.comp exposure‖ * ‖residual‖ :=
      (functional.comp exposure).le_opNorm residual
    _ ≤ sensitivity * ‖residual‖ :=
      mul_le_mul_of_nonneg_right hexposure_norm (norm_nonneg residual)
    _ = ‖residual‖ * sensitivity := mul_comm _ _

/-- The complete tail-stable residual theorem.  Algebraic detection of the
stage defect, strict domination of the entire future tail, and polynomial
observation sensitivity force the physical residual to fail all-order
flatness.  With defect order `α` and sensitivity loss `M`, the constructed
physical lower bound has finite order `α + M` and positive coefficient
`(1 - θ) · c / (2 · C)`. -/
theorem tail_stable_defect_forces_nonflat_physical_residual
    (functional : ℝ → Obs →L[ℝ] ℝ)
    (exposure : ℝ → Residual →L[ℝ] Obs)
    (defect futureTail error : ℝ → Obs) (residual : ℝ → Residual)
    {c C θ radius : ℝ} {α M : ℕ}
    (hc : 0 < c) (hC : 0 < C)
    (htheta_nonneg : 0 ≤ θ) (htheta : θ < 1)
    (hradius : 0 < radius)
    (hexposure : ∀ q, 0 < q → q < radius →
      defect q + futureTail q = exposure q (residual q) + error q)
    (hdefect : ∀ q, 0 < q → q < radius →
      c * q ^ α ≤ |functional q (defect q)|)
    (htail : ∀ q, 0 < q → q < radius →
      |functional q (futureTail q)| ≤ θ * (c * q ^ α))
    (herror : ∀ q, 0 < q → q < radius →
      |functional q (error q)| ≤ (1 - θ) * (c * q ^ α) / 2)
    (hsensitivity : ∀ q, 0 < q → q < radius →
      ‖(functional q).comp (exposure q)‖ ≤ C / q ^ M) :
    ¬ FlatAtZero (fun q => ‖residual q‖) := by
  let coefficient : ℝ := (1 - θ) * c / (2 * C)
  have hcoefficient : 0 < coefficient := by
    dsimp [coefficient]
    positivity
  apply (AlgebraicLowerBound.mk coefficient (α + M) radius
    hcoefficient hradius ?_).not_flat
  intro q hq hqradius
  have hqpow : 0 < q ^ M := pow_pos hq M
  have hsensitivity_pos : 0 < C / q ^ M := div_pos hC hqpow
  have hlower := tail_stable_residual_lower_bound
    (functional q) (exposure q)
    (magnitude := c * q ^ α) (θ := θ) (sensitivity := C / q ^ M)
    (mul_nonneg hc.le (pow_nonneg hq.le α)) htheta_nonneg htheta hsensitivity_pos
    rfl (hexposure q hq hqradius) (hdefect q hq hqradius)
    (htail q hq hqradius) (herror q hq hqradius)
    (hsensitivity q hq hqradius)
  have heq :
      (((1 - θ) * (c * q ^ α) / 2) / (C / q ^ M)) =
        coefficient * q ^ (α + M) := by
    dsimp [coefficient]
    field_simp [hq.ne', hC.ne']
    ring
  rw [heq] at hlower
  exact hlower

end NavierStokes.CounterProof
