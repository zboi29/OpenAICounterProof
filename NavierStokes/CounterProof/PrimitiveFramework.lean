import NavierStokes.CounterProof.AffineLift
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Inv

/-!
# Primitive state, lift-cost, and endpoint framework

This module supplies the centralized objects from the general primitive-
liftability research note.  The definitions are deliberately local: concrete
applications provide the derivatives of the physical constraint and
observation at the source point, while this file records the exact affine
compatibility problem and its extended-valued minimum cost.
-/

noncomputable section

open Filter
open scoped Topology

namespace NavierStokes.CounterProof

/-- A state satisfying the time-dependent physical constraint. -/
def IsAdmissible {Time State Constraint : Type*}
    [Zero Constraint] (constraint : Time → State → Constraint)
    (time : Time) (state : State) : Prop :=
  constraint time state = 0

/-- The admissible states producing a prescribed observation. -/
def ObservationFiber {Time State Constraint Obs : Type*}
    [Zero Constraint] (constraint : Time → State → Constraint)
    (observe : Time → State → Obs) (time : Time) (value : Obs) : Set State :=
  {state | IsAdmissible constraint time state ∧ observe time state = value}

/-- A state curve lifting an observation curve through the constraint set. -/
def IsAdmissiblyLiftable {Time State Constraint Obs : Type*}
    [Zero Constraint] (constraint : Time → State → Constraint)
    (observe : Time → State → Obs) (stateCurve : Time → State)
    (observationCurve : Time → Obs) : Prop :=
  ∀ time, IsAdmissible constraint time (stateCurve time) ∧
    observe time (stateCurve time) = observationCurve time

variable {State Constraint Obs : Type*}
  [NormedAddCommGroup State] [NormedSpace ℝ State]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]

/-- A continuously differentiable admissible lift of an observation curve.
The ambient constraint and observation regularity are source obligations; this
predicate records the regularity and exact identities of the two curves. -/
def IsC1AdmissiblyLiftable
    (constraint : ℝ → State → Constraint) (observe : ℝ → State → Obs)
    (stateCurve : ℝ → State) (observationCurve : ℝ → Obs) : Prop :=
  ContDiff ℝ 1 stateCurve ∧ ContDiff ℝ 1 observationCurve ∧
    IsAdmissiblyLiftable constraint observe stateCurve observationCurve

/-- Pointwise linearized primitive-compatibility data, including a chosen
particular solution of the inhomogeneous constraint equation. -/
structure PrimitiveCompatibilityData (State Constraint Obs : Type*)
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]
    [NormedAddCommGroup Obs] [NormedSpace ℝ Obs] where
  constraint : State →L[ℝ] Constraint
  observe : State →L[ℝ] Obs
  constraintDrift : Constraint
  observationDrift : Obs
  target : Obs
  particular : State
  particular_solves : constraint particular = -constraintDrift

namespace PrimitiveCompatibilityData

/-- The homogeneous compatibility operator on constrained tangents. -/
def compatibility (D : PrimitiveCompatibilityData State Constraint Obs) :
    D.constraint.ker →L[ℝ] Obs :=
  homogeneousCompatibility D.constraint D.observe

/-- The affine observation target remaining after the particular tangent. -/
def affineTarget (D : PrimitiveCompatibilityData State Constraint Obs) : Obs :=
  affineCompatibilityTarget D.observe D.observationDrift D.target D.particular

/-- The set of all admissible first-order lifts for the pointwise data. -/
def liftSet (D : PrimitiveCompatibilityData State Constraint Obs) : Set State :=
  {stateTangent | IsAdmissibleFirstOrderLift D.constraint D.observe
    D.constraintDrift D.observationDrift D.target stateTangent}

/-- The minimum lift cost, valued in `ℝ≥0∞` so an empty lift set has cost
`∞`.  The infimum form does not assume that a minimizing tangent is attained. -/
def liftCost (D : PrimitiveCompatibilityData State Constraint Obs) : ENNReal :=
  sInf ((fun stateTangent : State => ENNReal.ofReal ‖stateTangent‖) '' D.liftSet)

/-- The pointwise affine lift set is nonempty exactly when the centralized
compatibility range contains the affine target. -/
theorem liftSet_nonempty_iff_mem_range
    (D : PrimitiveCompatibilityData State Constraint Obs) :
    D.liftSet.Nonempty ↔ D.affineTarget ∈ Set.range D.compatibility := by
  simpa [liftSet, affineTarget, compatibility, Set.nonempty_def] using
    admissible_first_order_lift_iff_mem_range D.constraint D.observe
      D.constraintDrift D.observationDrift D.target D.particular D.particular_solves

/-- Every admissible tangent gives an upper bound for the infimal lift cost. -/
theorem liftCost_le (D : PrimitiveCompatibilityData State Constraint Obs)
    {stateTangent : State} (hlift : stateTangent ∈ D.liftSet) :
    D.liftCost ≤ ENNReal.ofReal ‖stateTangent‖ := by
  exact sInf_le ⟨stateTangent, hlift, rfl⟩

/-- A uniform real lower bound for every admissible tangent also bounds the
infimal extended-valued lift cost. -/
theorem ofReal_le_liftCost (D : PrimitiveCompatibilityData State Constraint Obs)
    {lower : ℝ} (hlower : ∀ stateTangent, stateTangent ∈ D.liftSet →
      lower ≤ ‖stateTangent‖) :
    ENNReal.ofReal lower ≤ D.liftCost := by
  unfold liftCost
  apply le_sInf
  rintro value ⟨stateTangent, hlift, rfl⟩
  exact ENNReal.ofReal_le_ofReal (hlower stateTangent hlift)

/-- If no affine tangent exists, the extended-valued lift cost is infinite. -/
theorem liftCost_eq_top_of_empty (D : PrimitiveCompatibilityData State Constraint Obs)
    (hempty : ¬ D.liftSet.Nonempty) : D.liftCost = ⊤ := by
  unfold liftCost
  rw [Set.not_nonempty_iff_eq_empty.mp hempty]
  simp

/-- A terminal range failure forces infinite lift cost. -/
theorem liftCost_eq_top_of_target_not_mem_range
    (D : PrimitiveCompatibilityData State Constraint Obs)
    (hfailure : D.affineTarget ∉ Set.range D.compatibility) :
    D.liftCost = ⊤ := by
  apply D.liftCost_eq_top_of_empty
  rwa [D.liftSet_nonempty_iff_mem_range]

/-- Infinite lift cost is exactly terminal range failure.  The reverse
direction uses any admissible tangent to give a finite upper bound. -/
theorem liftCost_eq_top_iff_target_not_mem_range
    (D : PrimitiveCompatibilityData State Constraint Obs) :
    D.liftCost = ⊤ ↔ D.affineTarget ∉ Set.range D.compatibility := by
  constructor
  · intro htop hmem
    obtain ⟨stateTangent, hlift⟩ := D.liftSet_nonempty_iff_mem_range.mpr hmem
    have hfinite := D.liftCost_le hlift
    rw [htop] at hfinite
    exact (not_le_of_gt ENNReal.ofReal_lt_top) hfinite
  · exact D.liftCost_eq_top_of_target_not_mem_range

end PrimitiveCompatibilityData

/-- Singular liftability: the minimum physical lift cost diverges along the
degenerating sequence. -/
def SingularLiftability (cost : ℕ → ENNReal) : Prop :=
  Tendsto cost atTop (𝓝 ⊤)

/-- The two logically distinct branch-extinction mechanisms in the general
research note. -/
inductive PrimitiveBranchExtinction (cost : ℕ → ENNReal)
    (terminalRangeLoss : Prop) : Prop
  | singular (h : SingularLiftability cost)
  | terminal (h : terminalRangeLoss)

/-- Data supplied by any claimed regular terminal continuation. -/
structure EndpointCompatibility (D : PrimitiveCompatibilityData State Constraint Obs) where
  terminalTangent : State
  terminalTangent_is_lift : terminalTangent ∈ D.liftSet

namespace EndpointCompatibility

/-- A regular terminal continuation necessarily satisfies the primitive range
condition at the endpoint. -/
theorem affineTarget_mem_range
    {D : PrimitiveCompatibilityData State Constraint Obs}
    (E : EndpointCompatibility D) :
    D.affineTarget ∈ Set.range D.compatibility := by
  rw [← D.liftSet_nonempty_iff_mem_range]
  exact ⟨E.terminalTangent, E.terminalTangent_is_lift⟩

end EndpointCompatibility

/-- Terminal range loss excludes a regular admissible continuation. -/
theorem no_endpoint_compatibility_of_range_loss
    (D : PrimitiveCompatibilityData State Constraint Obs)
    (hfailure : D.affineTarget ∉ Set.range D.compatibility) :
    ¬ Nonempty (EndpointCompatibility D) := by
  rintro ⟨E⟩
  exact hfailure E.affineTarget_mem_range

/-- A family in which every admissible tangent eventually exceeds every real
bound cannot be realized by a uniformly bounded tangent family. -/
theorem no_bounded_lift_family_of_mandatory_blowup
    (D : ℕ → PrimitiveCompatibilityData State Constraint Obs)
    (tangent : ℕ → State)
    (hlift : ∀ n, tangent n ∈ (D n).liftSet)
    (hblowup : ∀ R : ℝ, ∀ᶠ n in atTop,
      ∀ stateTangent, stateTangent ∈ (D n).liftSet → R ≤ ‖stateTangent‖)
    (hbounded : ∃ B : ℝ, ∀ n, ‖tangent n‖ ≤ B) : False := by
  obtain ⟨B, hB⟩ := hbounded
  obtain ⟨n, hn⟩ := (hblowup (B + 1)).exists
  have hlower := hn (tangent n) (hlift n)
  linarith [hB n]

end NavierStokes.CounterProof
