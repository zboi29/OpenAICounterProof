import NavierStokes.CounterProof.BranchDefect

/-!
# Correct-branch resolvent and perturbative closure

This module formalizes the companion note's exact relation between the branch
selected by the reduced response and the branch solving the full compatibility
equation.  It also derives inverse and branch-displacement bounds directly from
a uniform relative-response estimate.

Both `reduced` and `full` are supplied as continuous linear equivalences, as in
the theorem's invertible regime.  The factorization hypothesis identifies the
full map with `reduced + hidden`.  The quantitative results then use the single
dimensionless operator `T = reduced⁻¹ ∘ hidden`; when `‖T‖ ≤ ρ < 1`, the exact
relative equivalence controls both inverse cost and branch displacement.
-/

noncomputable section

namespace NavierStokes.CounterProof

variable {Active Obs : Type*}
  [NormedAddCommGroup Active] [NormedSpace ℝ Active]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]

/-- Branch selected by the invertible reduced response. -/
def reducedBranch (reduced : Active ≃L[ℝ] Obs) (target : Obs) : Active :=
  reduced.symm target

/-- Branch solving the invertible full compatibility equation. -/
def correctBranch (full : Active ≃L[ℝ] Obs) (target : Obs) : Active :=
  full.symm target

/-- The hidden response measured in reduced-branch coordinates. -/
def relativeResponse (reduced : Active ≃L[ℝ] Obs)
    (hidden : Active →L[ℝ] Obs) : Active →L[ℝ] Active :=
  reduced.symm.toContinuousLinearMap.comp hidden

/-- The relative full response `reduced⁻¹ ∘ full`. -/
def relativeEquiv (reduced full : Active ≃L[ℝ] Obs) : Active ≃L[ℝ] Active :=
  full.trans reduced.symm

/-- Factoring `full = reduced + hidden` gives the relative response
`reduced⁻¹ ∘ full = I + reduced⁻¹ ∘ hidden`. -/
theorem relativeEquiv_apply
    (reduced full : Active ≃L[ℝ] Obs) (hidden : Active →L[ℝ] Obs)
    (hsplit : full.toContinuousLinearMap = reduced.toContinuousLinearMap + hidden)
    (active : Active) :
    relativeEquiv reduced full active = active + relativeResponse reduced hidden active := by
  have hsplit_apply := congrArg (fun map : Active →L[ℝ] Obs => map active) hsplit
  have hsplit_apply' : full active = reduced active + hidden active := by
    simpa using hsplit_apply
  change reduced.symm (full active) = active + reduced.symm (hidden active)
  rw [hsplit_apply', map_add, reduced.symm_apply_apply]

/-- First exact resolvent identity:
`aᴄ - aᴸ = -full⁻¹(hidden(aᴸ))`. -/
theorem correctBranch_sub_reducedBranch
    (reduced full : Active ≃L[ℝ] Obs) (hidden : Active →L[ℝ] Obs)
    (hsplit : full.toContinuousLinearMap = reduced.toContinuousLinearMap + hidden)
    (target : Obs) :
    correctBranch full target - reducedBranch reduced target =
      -full.symm (hidden (reducedBranch reduced target)) := by
  apply full.injective
  have hsplit_apply := congrArg
    (fun map : Active →L[ℝ] Obs => map (reducedBranch reduced target)) hsplit
  have hsplit_apply' :
      full (reducedBranch reduced target) =
        reduced (reducedBranch reduced target) +
          hidden (reducedBranch reduced target) := by
    simpa using hsplit_apply
  have hfull_reduced :
      full (reducedBranch reduced target) =
        target + hidden (reducedBranch reduced target) := by
    rw [hsplit_apply']
    simp [reducedBranch]
  rw [map_sub, map_neg]
  simp only [correctBranch, full.apply_symm_apply, hfull_reduced]
  simp

/-- Second exact resolvent identity in relative coordinates:
`aᴄ - aᴸ = -(I + reduced⁻¹ ∘ hidden)⁻¹(reduced⁻¹(hidden(aᴸ)))`. -/
theorem correctBranch_sub_reducedBranch_relative
    (reduced full : Active ≃L[ℝ] Obs) (hidden : Active →L[ℝ] Obs)
    (hsplit : full.toContinuousLinearMap = reduced.toContinuousLinearMap + hidden)
    (target : Obs) :
    correctBranch full target - reducedBranch reduced target =
      -(relativeEquiv reduced full).symm
        (relativeResponse reduced hidden (reducedBranch reduced target)) := by
  rw [correctBranch_sub_reducedBranch reduced full hidden hsplit target]
  congr 1
  apply full.injective
  simp [relativeEquiv, relativeResponse]

/-- A robust inverse estimate for an equivalence represented as `I + T`.
No choice of a Neumann series or completeness assumption is needed once
invertibility is already known: the proof uses the reverse triangle inequality
pointwise and then bounds the operator norm. -/
theorem inverse_norm_le_of_equiv_eq_id_add
    (equiv : Active ≃L[ℝ] Active) (perturbation : Active →L[ℝ] Active)
    (hfactor : ∀ active, equiv active = active + perturbation active)
    {ρ : ℝ} (hperturbation : ‖perturbation‖ ≤ ρ) (hρ : ρ < 1) :
    ‖equiv.symm.toContinuousLinearMap‖ ≤ 1 / (1 - ρ) := by
  have hρ_nonneg : 0 ≤ ρ := (norm_nonneg perturbation).trans hperturbation
  have hone_sub : 0 < 1 - ρ := sub_pos.mpr hρ
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro target
  let active := equiv.symm target
  have hequiv : equiv active = target := equiv.apply_symm_apply target
  have hperturbation_active : ‖perturbation active‖ ≤ ρ * ‖active‖ :=
    (perturbation.le_of_opNorm_le hperturbation) active
  have htriangle : ‖active‖ ≤ ‖equiv active‖ + ‖perturbation active‖ := by
    calc
      ‖active‖ = ‖equiv active - perturbation active‖ := by
        rw [hfactor]
        simp
      _ ≤ ‖equiv active‖ + ‖perturbation active‖ := norm_sub_le _ _
  have hlower : (1 - ρ) * ‖active‖ ≤ ‖target‖ := by
    rw [hequiv] at htriangle
    nlinarith
  have hquotient : ‖active‖ ≤ ‖target‖ / (1 - ρ) :=
    (le_div_iff₀ hone_sub).2 (by simpa [mul_comm] using hlower)
  change ‖active‖ ≤ 1 / (1 - ρ) * ‖target‖
  simpa [div_eq_mul_inv, mul_comm] using hquotient

/-- Perturbative inverse bound
`‖full⁻¹‖ ≤ ‖reduced⁻¹‖ / (1 - ρ)`. -/
theorem fullInverse_norm_le
    (reduced full : Active ≃L[ℝ] Obs) (hidden : Active →L[ℝ] Obs)
    (hsplit : full.toContinuousLinearMap = reduced.toContinuousLinearMap + hidden)
    {ρ : ℝ} (hrelative : ‖relativeResponse reduced hidden‖ ≤ ρ)
    (hρ : ρ < 1) :
    ‖full.symm.toContinuousLinearMap‖ ≤
      ‖reduced.symm.toContinuousLinearMap‖ / (1 - ρ) := by
  have hinverse := inverse_norm_le_of_equiv_eq_id_add
    (relativeEquiv reduced full) (relativeResponse reduced hidden)
    (relativeEquiv_apply reduced full hidden hsplit) hrelative hρ
  have hfactor : full.symm.toContinuousLinearMap =
      (relativeEquiv reduced full).symm.toContinuousLinearMap.comp
        reduced.symm.toContinuousLinearMap := by
    ext target
    simp [relativeEquiv]
  rw [hfactor]
  calc
    ‖(relativeEquiv reduced full).symm.toContinuousLinearMap.comp
        reduced.symm.toContinuousLinearMap‖ ≤
        ‖(relativeEquiv reduced full).symm.toContinuousLinearMap‖ *
          ‖reduced.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (1 / (1 - ρ)) * ‖reduced.symm.toContinuousLinearMap‖ := by
      gcongr
    _ = ‖reduced.symm.toContinuousLinearMap‖ / (1 - ρ) := by
      ring

/-- Perturbative branch bound
`‖aᴄ - aᴸ‖ ≤ ρ / (1 - ρ) · ‖aᴸ‖`. -/
theorem correctBranch_displacement_norm_le
    (reduced full : Active ≃L[ℝ] Obs) (hidden : Active →L[ℝ] Obs)
    (hsplit : full.toContinuousLinearMap = reduced.toContinuousLinearMap + hidden)
    {ρ : ℝ} (hrelative : ‖relativeResponse reduced hidden‖ ≤ ρ)
    (hρ : ρ < 1) (target : Obs) :
    ‖correctBranch full target - reducedBranch reduced target‖ ≤
      ρ / (1 - ρ) * ‖reducedBranch reduced target‖ := by
  have hρ_nonneg : 0 ≤ ρ := (norm_nonneg (relativeResponse reduced hidden)).trans hrelative
  have hinverse := inverse_norm_le_of_equiv_eq_id_add
    (relativeEquiv reduced full) (relativeResponse reduced hidden)
    (relativeEquiv_apply reduced full hidden hsplit) hrelative hρ
  rw [correctBranch_sub_reducedBranch_relative reduced full hidden hsplit target,
    norm_neg]
  calc
    ‖(relativeEquiv reduced full).symm
        (relativeResponse reduced hidden (reducedBranch reduced target))‖ ≤
        ‖(relativeEquiv reduced full).symm.toContinuousLinearMap‖ *
          ‖relativeResponse reduced hidden (reducedBranch reduced target)‖ :=
      (relativeEquiv reduced full).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ (1 / (1 - ρ)) * (ρ * ‖reducedBranch reduced target‖) := by
      gcongr
      exact (relativeResponse reduced hidden).le_of_opNorm_le hrelative _
    _ = ρ / (1 - ρ) * ‖reducedBranch reduced target‖ := by
      ring

end NavierStokes.CounterProof
