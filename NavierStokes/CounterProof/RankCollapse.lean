import NavierStokes.CounterProof.HilbertCokernel
import NavierStokes.CounterProof.PrimitiveFramework
import Mathlib.Topology.Algebra.Order.Field

/-!
# Singular-direction rank collapse and branch extinction

The research note uses the least-controlled left singular direction to show
that bounded observable targets can require unbounded physical lifts.  This
module isolates exactly the data used by that proof: a normalized observed
direction and the norm of its adjoint image.  No pseudoinverse API is needed.
-/

noncomputable section

open Filter
open scoped InnerProductSpace Topology

namespace NavierStokes.CounterProof

variable {Domain Obs : Type*}
  [NormedAddCommGroup Domain] [InnerProductSpace ℝ Domain] [CompleteSpace Domain]
  [NormedAddCommGroup Obs] [InnerProductSpace ℝ Obs] [CompleteSpace Obs]

/-- A normalized left singular direction, expressed by the only identity the
branch-extinction estimate needs. -/
structure LeftSingularDirection (operator : Domain →L[ℝ] Obs) where
  vector : Obs
  singularValue : ℝ
  vector_norm : ‖vector‖ = 1
  singularValue_nonneg : 0 ≤ singularValue
  adjoint_norm : ‖operator.adjoint vector‖ = singularValue

namespace LeftSingularDirection

/-- A persistent target component in a singular direction forces every exact
lift to have reciprocal-size norm. -/
theorem lift_product_lower_bound
    {operator : Domain →L[ℝ] Obs} (S : LeftSingularDirection operator)
    {target : Obs} (x : Domain) (hsolve : operator x = target)
    {c : ℝ} (hdetects : c ≤ |⟪S.vector, target⟫_ℝ|) :
    c ≤ S.singularValue * ‖x‖ := by
  calc
    c ≤ |⟪S.vector, target⟫_ℝ| := hdetects
    _ ≤ ‖operator.adjoint S.vector‖ * ‖x‖ :=
      exact_lift_product_lower_bound operator S.vector target x hsolve
    _ = S.singularValue * ‖x‖ := by rw [S.adjoint_norm]

/-- Quotient form of the singular-direction lower bound. -/
theorem lift_norm_lower_bound
    {operator : Domain →L[ℝ] Obs} (S : LeftSingularDirection operator)
    {target : Obs} (x : Domain) (hsolve : operator x = target)
    {c : ℝ} (hdetects : c ≤ |⟪S.vector, target⟫_ℝ|)
    (hsigma : 0 < S.singularValue) :
    c / S.singularValue ≤ ‖x‖ := by
  apply (div_le_iff₀ hsigma).2
  simpa [mul_comm] using S.lift_product_lower_bound x hsolve hdetects

end LeftSingularDirection

variable {State Constraint : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State] [CompleteSpace State]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]

/-- Affine form of the singular-direction estimate.  Every admissible tangent
is the chosen particular tangent plus a homogeneous lift, so its norm is at
least the reciprocal singular cost minus the particular-tangent cost. -/
theorem affine_lift_norm_lower_bound
    (D : PrimitiveCompatibilityData State Constraint Obs)
    (S : LeftSingularDirection D.compatibility)
    {stateTangent : State} (hlift : stateTangent ∈ D.liftSet)
    {c : ℝ} (hdetects : c ≤ |⟪S.vector, D.affineTarget⟫_ℝ|)
    (hsigma : 0 < S.singularValue) :
    c / S.singularValue - ‖D.particular‖ ≤ ‖stateTangent‖ := by
  rcases hlift with ⟨hconstraint, hobserve⟩
  let homogeneous : D.constraint.ker :=
    ⟨stateTangent - D.particular, by
      change D.constraint (stateTangent - D.particular) = 0
      rw [map_sub, hconstraint, D.particular_solves]
      abel⟩
  have hsolve : D.compatibility homogeneous = D.affineTarget := by
    change D.observe (stateTangent - D.particular) =
      D.target - D.observationDrift - D.observe D.particular
    rw [map_sub, hobserve]
  have hlower := S.lift_norm_lower_bound homogeneous hsolve hdetects hsigma
  have hnorm : ‖(homogeneous : State)‖ ≤ ‖stateTangent‖ + ‖D.particular‖ := by
    exact (norm_sub_le stateTangent D.particular)
  dsimp [homogeneous] at hlower hnorm
  linarith

/-- Uniform singular-direction collapse forces the extended-valued affine lift
cost to converge to infinity.  This is the singular-liftability constructor of
primitive branch extinction. -/
theorem rank_collapse_forces_singular_liftability
    (D : ℕ → PrimitiveCompatibilityData State Constraint Obs)
    (S : ∀ n, LeftSingularDirection (D n).compatibility)
    (c particularBound : ℝ)
    (hc : 0 < c) (hparticularBound : 0 ≤ particularBound)
    (hdetects : ∀ n, c ≤ |⟪(S n).vector, (D n).affineTarget⟫_ℝ|)
    (hsigma_pos : ∀ n, 0 < (S n).singularValue)
    (hsigma_zero : Tendsto (fun n => (S n).singularValue) atTop (𝓝 0))
    (hparticular : ∀ n, ‖(D n).particular‖ ≤ particularBound) :
    SingularLiftability (fun n => (D n).liftCost) := by
  apply ENNReal.tendsto_nhds_top
  intro N
  let threshold : ℝ := N + 1
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hdenom : 0 < threshold + particularBound :=
    add_pos_of_pos_of_nonneg hthreshold hparticularBound
  have hsmall : ∀ᶠ n in atTop, (S n).singularValue < c / (threshold + particularBound) :=
    (tendsto_order.1 hsigma_zero).2 _ (div_pos hc hdenom)
  filter_upwards [hsmall] with n hn
  have hall : ∀ stateTangent, stateTangent ∈ (D n).liftSet →
      threshold ≤ ‖stateTangent‖ := by
    intro stateTangent hlift
    have hlower := affine_lift_norm_lower_bound (D n) (S n) hlift
      (hdetects n) (hsigma_pos n)
    have hratio : threshold + particularBound < c / (S n).singularValue := by
      apply (lt_div_iff₀ (hsigma_pos n)).2
      have := (lt_div_iff₀ hdenom).mp hn
      nlinarith
    linarith [hparticular n]
  have hcost : ENNReal.ofReal threshold ≤ (D n).liftCost :=
    (D n).ofReal_le_liftCost hall
  have hN : (N : ENNReal) < ENNReal.ofReal threshold := by
    apply ENNReal.natCast_lt_ofReal.mpr
    dsimp [threshold]
    exact_mod_cast Nat.lt_succ_self N
  exact hN.trans_le hcost

/-- If positive singular values collapse to zero while the target component
stays uniformly positive, every chosen exact lift eventually exceeds every
real norm threshold. -/
theorem singular_direction_forces_mandatory_blowup
    (operator : ℕ → Domain →L[ℝ] Obs) (target : ℕ → Obs)
    (direction : ∀ n, LeftSingularDirection (operator n))
    (lift : ℕ → Domain) (c : ℝ)
    (hc : 0 < c)
    (hsolve : ∀ n, operator n (lift n) = target n)
    (hdetects : ∀ n, c ≤ |⟪(direction n).vector, target n⟫_ℝ|)
    (hsigma_pos : ∀ n, 0 < (direction n).singularValue)
    (hsigma_zero : Tendsto (fun n => (direction n).singularValue) atTop (𝓝 0)) :
    ∀ R : ℝ, ∀ᶠ n in atTop, R ≤ ‖lift n‖ := by
  intro R
  by_cases hR : R ≤ 0
  · filter_upwards [] with n
    exact hR.trans (norm_nonneg _)
  · have hRpos : 0 < R := lt_of_not_ge hR
    have hsmall : ∀ᶠ n in atTop, (direction n).singularValue < c / R :=
      (tendsto_order.1 hsigma_zero).2 _ (div_pos hc hRpos)
    filter_upwards [hsmall] with n hn
    have hproduct := (direction n).lift_product_lower_bound
      (lift n) (hsolve n) (hdetects n)
    have hsigma := hsigma_pos n
    have hsigmaR : (direction n).singularValue * R < c :=
      (lt_div_iff₀ hRpos).mp hn
    by_contra hnorm
    have hnorm_lt : ‖lift n‖ < R := lt_of_not_ge hnorm
    have hstrict : (direction n).singularValue * ‖lift n‖ < c :=
      (mul_lt_mul_of_pos_left hnorm_lt hsigma).trans hsigmaR
    exact (not_lt_of_ge hproduct) hstrict

/-- Operator and witness convergence transports vanishing adjoint response to
an exact terminal cokernel direction. -/
theorem adjoint_limit_eq_zero
    (operator : ℕ → Domain →L[ℝ] Obs) (η : ℕ → Obs)
    (operator₀ : Domain →L[ℝ] Obs) (η₀ : Obs)
    (hoperator : Tendsto operator atTop (𝓝 operator₀))
    (hη : Tendsto η atTop (𝓝 η₀))
    (hadjoint_zero : Tendsto (fun n => (operator n).adjoint (η n)) atTop (𝓝 0)) :
    operator₀.adjoint η₀ = 0 := by
  have hop : Tendsto (fun n => (operator n).adjoint) atTop (𝓝 operator₀.adjoint) :=
    (ContinuousLinearMap.adjoint.continuous.tendsto operator₀).comp hoperator
  have hpair : Tendsto (fun n => (η n, (operator n).adjoint)) atTop
      (𝓝 (η₀, operator₀.adjoint)) := hη.prodMk_nhds hop
  have hcontinuous : Continuous
      (fun pair : Obs × (Obs →L[ℝ] Domain) => pair.2 pair.1) :=
    continuous_snd.clm_apply continuous_fst
  have hlimit : Tendsto (fun n => (operator n).adjoint (η n)) atTop
      (𝓝 (operator₀.adjoint η₀)) := by
    exact hcontinuous.continuousAt.tendsto.comp hpair
  exact tendsto_nhds_unique hlimit hadjoint_zero

/-- Rank collapse followed by a nonzero terminal pairing produces terminal
range loss, the second branch-extinction mode. -/
theorem terminal_range_loss_of_rank_collapse
    (operator : ℕ → Domain →L[ℝ] Obs) (η : ℕ → Obs)
    (operator₀ : Domain →L[ℝ] Obs) (η₀ target₀ : Obs)
    (hoperator : Tendsto operator atTop (𝓝 operator₀))
    (hη : Tendsto η atTop (𝓝 η₀))
    (hadjoint_zero : Tendsto (fun n => (operator n).adjoint (η n)) atTop (𝓝 0))
    (hdetects : ⟪η₀, target₀⟫_ℝ ≠ 0) :
    target₀ ∉ Set.range operator₀ := by
  apply target_not_mem_range_of_adjoint_eq_zero operator₀
    (adjoint_limit_eq_zero operator η operator₀ η₀ hoperator hη hadjoint_zero)
  exact hdetects

end NavierStokes.CounterProof
