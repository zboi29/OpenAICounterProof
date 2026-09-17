import NavierStokes.CounterProof.Adapter.ConditionedResponse
import NavierStokes.CounterProof.Certificates.QuantitativeObstruction
import NavierStokes.PrimaryTargetBounds
import NavierStokes.AxisRootPressureBounds

/-!
# Independent finite-jet obstruction witnesses

Finite physical jets turn the reconstructed response into a normed observation
space on which bounded scalar functionals can detect the two independent
counter-proof branches.  The records here deliberately permit different
functionals while retaining a common response and target.

## Manuscript correspondence

`EvaluatedSignedJetState` mirrors the eleven coordinates of §3.2 "Evaluated
finite-jet constrained state" in
`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`.
`EvaluatedConstraintBlocks` names exactly the seven equality blocks listed
there; weighted membership, support, strict-cone, and smallness hypotheses are
intentionally not promoted to tangent equations.  The witness records encode
Theorem 6.1 (`thm:budget`) and Lean-instantiation Phase V.  Their elementary
constructors and nonvanishing/survival lemmas are Lean helpers used to feed
`DiagonalTail` and `PhysicalResidualExposure`, not additional analytic claims.
The two `source_*_lower` theorems retain concrete target and pressure-root
positivity already proved upstream.  They are candidate inputs to a finite-jet
dual pairing; neither theorem alone constructs the required functional.

`NativeDataObstruction.CertificateFeedback` is another source of a
`ReducedDefectWitness`: it promotes the exact physical finite-prefix cross
defect only after a coordinate of the complete observed defect is proved equal
to that scalar.  The underlying NativeData package contradiction remains a
separate counter-proof route and does not depend on this finite-jet layer.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter

open NavierStokes.CounterProof
open Set

variable {Active Hidden Obs Constraint Tail : Type*}
  [NormedAddCommGroup Active] [NormedSpace ℝ Active]
  [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
  [NormedAddCommGroup Obs] [NormedSpace ℝ Obs]
  [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint]

/-- The source coordinates evaluated at fixed stage, scale, jet order, and
finite point set, in the order displayed in companion-note §3.2.  Reusing the
`Velocity` and `Oscillation` types records that the pre/post and tangent/curl
coordinates inhabit the same spaces without identifying their values. -/
structure EvaluatedSignedJetState
    (Stage Context Active Velocity Oscillation WavePressure GaugeError
      Covariance Pressure : Type*) where
  stage : Stage
  context : Context
  active : Active
  priorVelocity : Velocity
  tangent : Oscillation
  curl : Oscillation
  wavePressure : WavePressure
  gaugeError : GaugeError
  updatedCovariance : Covariance
  updatedPressure : Pressure
  updatedVelocity : Velocity

/-- The seven equality-constraint components of companion-note §3.2. -/
inductive ConstraintKind where
  | representation
  | covariance
  | reconstruction
  | divergence
  | mass
  | coherence
  | phase
  deriving DecidableEq

/-- Linearized active/hidden blocks for the seven exact equality constraints.
The common codomain is the packed constraint space used by
`CompatibilityBlocks`; admissibility inequalities remain external premises. -/
structure EvaluatedConstraintBlocks
    (Active Hidden Constraint : Type*)
    [NormedAddCommGroup Active] [NormedSpace ℝ Active]
    [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
    [NormedAddCommGroup Constraint] [NormedSpace ℝ Constraint] where
  active : ConstraintKind → Active →L[ℝ] Constraint
  hidden : ConstraintKind → Hidden →L[ℝ] Constraint

namespace EvaluatedConstraintBlocks

/-- Lean helper expressing membership in the kernel of every equality block;
it is the componentwise form of `G a + D h = 0` from Theorem 5.1
(`thm:schur`). -/
def Satisfies
    (K : EvaluatedConstraintBlocks Active Hidden Constraint)
    (active : Active) (hidden : Hidden) : Prop :=
  ∀ kind, K.active kind active + K.hidden kind hidden = 0

/-- A reconstructed hidden tangent satisfies all seven blocks when its
componentwise constraint-lift identities hold.  This introduction helper is
used when constructing the packed `CompatibilityBlocks.constraint_lift`. -/
theorem satisfies_of_componentwise
    (K : EvaluatedConstraintBlocks Active Hidden Constraint)
    (active : Active) (hidden : Hidden)
    (h : ∀ kind, K.active kind active + K.hidden kind hidden = 0) :
    K.Satisfies active hidden :=
  h

end EvaluatedConstraintBlocks

/-- Source lower bound for the literal leading target, retained with the same
moving flat weight.  This imports `PrimaryTargetBounds.targetAmplitude_lower_all`
as a Phase-V witness input; a later theorem must still connect this scalar
amplitude to a component of the evaluated tangential target. -/
theorem source_target_amplitude_lower
    {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)
    (hcone : LeadingStressWeights.FullTrueCone v) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ PositiveRepresentatives.positivePart
      (PrimaryGeometryAssembly.referenceSet W),
      c * PrimaryTargetBounds.movingWeight W p ≤
        PrimaryTargetBounds.targetAmplitude v p :=
  PrimaryTargetBounds.targetAmplitude_lower_all v hcone

/-- Source lower bound for the actual integral-pressure contribution at the
unique natural-axis root.  It preserves
`AxisRootPressureBounds.ideal_prefix_root_pressure_lower` for the pressure
coordinate required by `FullCompatibility`; a later finite-jet theorem must
transport this pointwise margin through `dz` and the chosen dual functional. -/
theorem source_pressure_root_lower {h j : ℝ}
    (p : NaturalAxisRange.Parameters h j) {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧
      NaturalAxisData.H h j η₀ = 0 ∧
      j * B ^ 2 / 20 <
        NaturalAxisData.Z h j (PressureDatum.pressure g a) η₀ ∧
      ∀ η ∈ Icc (-1 : ℝ) 1,
        NaturalAxisData.H h j η = 0 → η = η₀ :=
  AxisRootPressureBounds.ideal_prefix_root_pressure_lower p hp hB hg ha

/-- Concrete data detecting a reduced-branch defect at one finite physical
jet. -/
structure ReducedDefectWitness (defect : Obs) where
  functional : Obs →L[ℝ] ℝ
  magnitude : ℝ
  magnitude_pos : 0 < magnitude
  detects : magnitude ≤ |functional defect|

namespace ReducedDefectWitness

/-- Constructor used by a concrete finite-jet estimate from Theorem 6.1: a
positive scalar lower bound immediately becomes a reduced-defect witness. -/
def ofLowerBound (defect : Obs) (functional : Obs →L[ℝ] ℝ)
    (magnitude : ℝ) (magnitude_pos : 0 < magnitude)
    (detects : magnitude ≤ |functional defect|) :
    ReducedDefectWitness defect :=
  ⟨functional, magnitude, magnitude_pos, detects⟩

/-- Helper consequence needed before terminal exposure: a positively detected
finite-jet defect cannot be the zero observation. -/
theorem defect_ne_zero {defect : Obs} (W : ReducedDefectWitness defect) :
    defect ≠ 0 := by
  intro hzero
  subst defect
  have hdetect : W.magnitude ≤ 0 := by simpa using W.detects
  exact (not_lt_of_ge hdetect) W.magnitude_pos

/-- Scalar persistence helper for Proposition 6.2 (`prop:residual`): any tail
using at most a `θ` fraction of the witnessed magnitude leaves the stated
margin in the same functional. -/
theorem survives_tail {defect tail : Obs} (W : ReducedDefectWitness defect)
    {θ : ℝ} (htail : |W.functional tail| ≤ θ * W.magnitude) :
    (1 - θ) * W.magnitude ≤ |W.functional (defect + tail)| := by
  rw [map_add]
  exact interface_defect_survives_tail W.detects htail

end ReducedDefectWitness

/-- Concrete data excluding a full-compatible target from the complete
admissible response capacity. -/
structure FullCapacityWitness
    (response nonlinear : Tail → Obs) (target : Obs) where
  capacity : TailCapacity response nonlinear
  target_exceeds :
    capacity.linearCapacity + capacity.nonlinearCapacity <
      |capacity.functional target|

namespace FullCapacityWitness

/-- A full-capacity witness rules out every admissible realizing tail. -/
theorem no_realizing_tail
    {response nonlinear : Tail → Obs} {target : Obs}
    (W : FullCapacityWitness response nonlinear target) :
    ¬ ∃ tail, TailRealizes response nonlinear target tail :=
  W.capacity.target_exceeds_admissible_tail W.target_exceeds

end FullCapacityWitness

/-- Two independently established source witnesses over the same observation
space.  No equality between their functionals is asserted. -/
structure IndependentFiniteJetWitnesses
    (defect target : Obs) (response nonlinear : Tail → Obs) where
  reduced : ReducedDefectWitness defect
  full : FullCapacityWitness response nonlinear target

namespace IndependentFiniteJetWitnesses

/-- Lean-only projection helper: independently certified finite-jet branches
already give a nonzero reduced defect and exclusion of every realizing tail.
No common-functional hypothesis is introduced. -/
theorem branch_conclusions
    {defect target : Obs} {response nonlinear : Tail → Obs}
    (W : IndependentFiniteJetWitnesses defect target response nonlinear) :
    defect ≠ 0 ∧ ¬ ∃ tail, TailRealizes response nonlinear target tail :=
  ⟨W.reduced.defect_ne_zero, W.full.no_realizing_tail⟩

end IndependentFiniteJetWitnesses

end NavierStokes.CounterProof.Adapter
