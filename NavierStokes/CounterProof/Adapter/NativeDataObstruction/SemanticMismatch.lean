import NavierStokes.CounterProof.Adapter.NativeDataObstruction.CertificateFeedback
import NavierStokes.ActualCyclePreservation

/-!
# NativeData bypass and semantic mismatch

The actual signed correction does not instantiate the normalized
`SignedMeanGain.NativeData` interface: that interface is empty on the actual
strip.  Instead, the correction step uses the algebraically valid physical
tail identity.  A finite head can then be retained in every requested
`MeanClass`, because the class constants may depend on the exponent.

The aggregation theorems below pin down the resulting semantic separation.
The first theorem says that universal weighted-class membership can coexist
with a nonzero complete field for the very cross defect being classified and
with failure of all-band `Agree`.  The second specializes the separation to
the actual iterative state: the cycle proves its next run invariant even when
a witnessed finite band fails exact cross compatibility, while the same cross
becomes `Set.EqOn` to the request on every admitted tail band.

These are interface-mismatch theorems, not terminal PDE contradictions.  A
terminal counter-proof beyond `native_route_unavailable` still needs the
finite defect to survive the complete correction tail and reach an exact
upstream endpoint.
-/

noncomputable section

namespace NavierStokes.CounterProof.Adapter.NativeDataObstruction

open CorrectionInitialization.ActualPrimary
open ActualPrimaryCovariance

/-- The actual averaged cross, packaged as the field type used by the claimed
mean-composition interface. -/
noncomputable def actualCrossField (B N0 : ℕ)
    (c : CorrectionState.Context ActualPoint) (u : CorrectionState.State ActualPoint)
    (i : Fin 2) : MeanIncrementBounds.Field ActualPoint :=
  fun n x => actualCrossComponent B N0 c u n x i

@[simp]
theorem actualCrossField_apply (B N0 : ℕ)
    (c : CorrectionState.Context ActualPoint) (u : CorrectionState.State ActualPoint)
    (i : Fin 2) (n : ℕ) (x : ActualPoint) :
    actualCrossField B N0 c u i n x = actualCrossComponent B N0 c u n x i :=
  rfl

/-- The requested stress, packaged in the same field type as the actual
averaged cross. -/
noncomputable def actualRequestedField
    (c : CorrectionState.Context ActualPoint) (u : CorrectionState.State ActualPoint)
    (i : Fin 2) : MeanIncrementBounds.Field ActualPoint :=
  fun n x => actualRequestedComponent c u n x i

@[simp]
theorem actualRequestedField_apply
    (c : CorrectionState.Context ActualPoint) (u : CorrectionState.State ActualPoint)
    (i : Fin 2) (n : ℕ) (x : ActualPoint) :
    actualRequestedField c u i n x = actualRequestedComponent c u n x i :=
  rfl

/-- The first requested component is the physical theta stress used by the
claimed mean-composition theorem. -/
@[simp] theorem actualRequestedField_zero
    (c : CorrectionState.Context ActualPoint) (u : CorrectionState.State ActualPoint) :
    actualRequestedField c u 0 =
      SignedMeanGain.physicalSigma ActualInitialization.geometry 2 (u.thetaResidual c) :=
  rfl

/-- The second requested component is the physical axial stress used by the
claimed mean-composition theorem. -/
@[simp] theorem actualRequestedField_one
    (c : CorrectionState.Context ActualPoint) (u : CorrectionState.State ActualPoint) :
    actualRequestedField c u 1 =
      SignedMeanGain.physicalSigma ActualInitialization.geometry 1 (u.axialResidual c) :=
  rfl

/-- Field-level form of the physical cross defect. -/
noncomputable def actualCrossDefectField (B N0 : ℕ)
    (c : CorrectionState.Context ActualPoint) (u : CorrectionState.State ActualPoint)
    (i : Fin 2) : MeanIncrementBounds.Field ActualPoint :=
  actualCrossField B N0 c u i - actualRequestedField c u i

@[simp]
theorem actualCrossDefectField_apply (B N0 : ℕ)
    (c : CorrectionState.Context ActualPoint) (u : CorrectionState.State ActualPoint)
    (i : Fin 2) (n : ℕ) (x : ActualPoint) :
    actualCrossDefectField B N0 c u i n x = actualCrossDefect B N0 c u n x i :=
  rfl

/-- The two source-level alternatives audited here for retaining the semantics
of the normalized native interface.  Either the complete `NativeData` package
exists, or the physical-scale replacement agrees with the requested stress on
every band of the actual strip.

This proposition deliberately says nothing about weighted-class membership:
membership in every `MeanClass` is weaker than all-band equality and is the
algebraically legal bypass whose semantics are audited below. -/
def NativeCrossSemanticsAvailable (B N0 : ℕ)
    (c : CorrectionState.Context ActualPoint) (u : CorrectionState.State ActualPoint)
    (i : Fin 2) : Prop :=
  NativeRouteAvailable ∨
    MeanIncrementBounds.Agree ActualInitialization.geometry.strip.domain
      (actualCrossField B N0 c u i) (actualRequestedField c u i)

/-- Selected cross component of an assembled signed family. -/
noncomputable def familyCrossField {ι : Type} {P : ι → ℕ → ActualPoint → ℝ}
    {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily ActualInitialization.geometry.strip P α δ β η)
    (a : SignedMeanGain.Assembly f) (i : Fin 2) : MeanIncrementBounds.Field ActualPoint :=
  StateMomentBalances.meanBar (SignedMeanGain.crossTensor f a 0 i.succ)

/-- Field-level family defect against the physical request. -/
noncomputable def familyCrossDefectField {ι : Type} {P : ι → ℕ → ActualPoint → ℝ}
    {α δ β η : ℝ} (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint)
    (f : LabelSumBounds.SignedFamily ActualInitialization.geometry.strip P α δ β η)
    (a : SignedMeanGain.Assembly f) (i : Fin 2) : MeanIncrementBounds.Field ActualPoint :=
  familyCrossField f a i - actualRequestedField c u i

/-- The family binding is an equality of complete fields, not merely equality
at the point later selected by a finite-prefix witness. -/
theorem familyCrossField_eq_actualCrossField
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint)
    {P : (CorrectionInitialization.ActualPrimary.Label B N0 × Fin 2) →
      ℕ → ActualPoint → ℝ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily ActualInitialization.geometry.strip P α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hprimary : f.primary = ActualInitialization.tangentBlock)
    (htangent : f.tangent = ActualSignedMeanBinding.actualSignedBlock c u)
    (hlabels : a.labels = CorrectionInitialization.ActualPrimary.activeLabels
      CorrectionInitialization.ActualPrimary.standardRegion B N0)
    (i : Fin 2) :
    familyCrossField f a i = actualCrossField B N0 c u i := by
  funext n x
  simp only [familyCrossField, actualCrossField]
  rw [ActualSignedMeanBinding.family_cross_eq c u f a hprimary htangent hlabels]
  rfl

/-- Subtracting the common requested field transports the exact family
binding to an exact equality of complete defect fields. -/
theorem familyCrossDefectField_eq_actualCrossDefectField
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint)
    {P : (CorrectionInitialization.ActualPrimary.Label B N0 × Fin 2) →
      ℕ → ActualPoint → ℝ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily ActualInitialization.geometry.strip P α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hprimary : f.primary = ActualInitialization.tangentBlock)
    (htangent : f.tangent = ActualSignedMeanBinding.actualSignedBlock c u)
    (hlabels : a.labels = CorrectionInitialization.ActualPrimary.activeLabels
      CorrectionInitialization.ActualPrimary.standardRegion B N0)
    (i : Fin 2) :
    familyCrossDefectField c u f a i = actualCrossDefectField B N0 c u i := by
  rw [familyCrossDefectField, actualCrossDefectField,
    familyCrossField_eq_actualCrossField B N0 c u f a hprimary htangent hlabels i]

namespace FinitePrefixObstruction

/-- Canonical `sub_ne_zero` form of the witnessed cross mismatch. -/
theorem cross_ne_requested
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i) :
    actualCrossField B N0 c u i n x ≠ actualRequestedField c u i n x := by
  simpa [actualCrossField, actualRequestedField, actualCrossDefect] using
    (sub_ne_zero.mp W.defect_ne_zero.1)

/-- A nonzero physical defect cannot occur in the exact tail, so its band is
strictly before the tail threshold. -/
theorem band_lt_tailStart
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i) :
    n < (choice B N0).prepared.N + 1 := by
  exact not_le.mp fun htail => W.cross_ne_requested (by
    simpa [actualCrossField, actualRequestedField] using
      (actual_cross_tail_exact B N0 c u htail W.point_mem i).1)

/-- One witnessed point refutes all-band agreement of the actual cross and
request fields on the physical strip. -/
theorem not_agree
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i) :
    ¬ MeanIncrementBounds.Agree ActualInitialization.geometry.strip.domain
      (actualCrossField B N0 c u i) (actualRequestedField c u i) := by
  intro hagree
  exact W.cross_ne_requested (hagree n W.point_mem)

/-- Strong closing helper for the source interface.  A witnessed finite-prefix
defect simultaneously rules out both ways of retaining native cross semantics:
the normalized route is empty on the actual geometry, while the physical
replacement fails exact all-band agreement.

This is stronger than merely negating `Agree`, and it is reusable for any
larger claimed endpoint that entails one of these two exact alternatives. -/
theorem no_native_cross_semantics
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i) :
    ¬ NativeCrossSemanticsAvailable B N0 c u i := by
  rintro (hnative | hagree)
  · exact native_route_unavailable hnative
  · exact W.not_agree hagree

/-- Transport the exact source-interface contradiction to any precisely
specified claim that would recover native cross semantics. -/
theorem refutes_claim_of_native_cross_semantics
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2} {claim : Prop}
    (W : FinitePrefixObstruction B N0 c u n x i)
    (requires : claim → NativeCrossSemanticsAvailable B N0 c u i) :
    ¬ claim :=
  mt requires W.no_native_cross_semantics

/-- The point witness promotes to nonvanishing of the complete defect field. -/
theorem defectField_ne_zero
    {B N0 : ℕ} {c : CorrectionState.Context ActualPoint}
    {u : CorrectionState.State ActualPoint} {n : ℕ}
    {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0 c u n x i) :
    actualCrossDefectField B N0 c u i ≠ 0 := by
  intro hzero
  apply W.defect_ne_zero.1
  have hpoint := congrFun (congrFun hzero n) x
  simpa using hpoint

end FinitePrefixObstruction

/-- Universal weighted-class promotion from the physical tail does not imply
exact native compatibility.  Under one concrete finite-prefix witness, the
literal family defects belong to every requested `MeanClass`, yet the selected
defect field is nonzero and the family cross fails `Agree` with the requested
stress on the strip.

This is the precise algebraic/semantic boundary used by the bypass: the class
statement is legal because it absorbs a finite head; interpreting it as exact
cross cancellation would be false. -/
theorem all_exponents_with_nonzero_cross_mismatch
    (B N0 : ℕ) (c : CorrectionState.Context ActualPoint)
    (u : CorrectionState.State ActualPoint)
    {P : (CorrectionInitialization.ActualPrimary.Label B N0 × Fin 2) →
      ℕ → ActualPoint → ℝ} {σ κ : ℝ}
    (f : LabelSumBounds.SignedFamily ActualInitialization.geometry.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ))
    (a : SignedMeanGain.Assembly f)
    (hprimary : f.primary = ActualInitialization.tangentBlock)
    (htangent : f.tangent = ActualSignedMeanBinding.actualSignedBlock c u)
    (hlabels : a.labels = CorrectionInitialization.ActualPrimary.activeLabels
      CorrectionInitialization.ActualPrimary.standardRegion B N0)
    (hS : ∀ i j, SignedMeanGain.MovingField ActualInitialization.geometry
      (SignedMeanGain.crossTensor f a i j))
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b c u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge c u).pressure =
      u.pressure)
    (hθ : WeightedClasses.MeanClass ActualInitialization.geometry.strip (1 + σ - κ)
      (u.thetaResidual c))
    (hz : WeightedClasses.MeanClass ActualInitialization.geometry.strip (1 + σ - κ)
      (u.axialResidual c))
    (n : ℕ) (x : ActualPoint) (i : Fin 2)
    (W : FinitePrefixObstruction B N0 c u n x i) :
    ¬ NativeRouteAvailable ∧
      (∀ γ : ℝ,
        WeightedClasses.MeanClass ActualInitialization.geometry.strip γ
            (CrossBasedMeanComposition.crossDefect ActualInitialization.geometry 2
              (u.thetaResidual c) (SignedMeanGain.crossTensor f a 0 1)) ∧
          WeightedClasses.MeanClass ActualInitialization.geometry.strip γ
            (CrossBasedMeanComposition.crossDefect ActualInitialization.geometry 1
              (u.axialResidual c) (SignedMeanGain.crossTensor f a 0 2))) ∧
      (∀ γ : ℝ, WeightedClasses.MeanClass ActualInitialization.geometry.strip γ
        (familyCrossDefectField c u f a i)) ∧
      n < (choice B N0).prepared.N + 1 ∧
      familyCrossDefectField c u f a i = actualCrossDefectField B N0 c u i ∧
      familyCrossDefectField c u f a i ≠ 0 ∧
      ¬ MeanIncrementBounds.Agree ActualInitialization.geometry.strip.domain
        (familyCrossField f a i) (actualRequestedField c u i) ∧
      StateMomentBalances.meanBar (SignedMeanGain.crossTensor f a 0 i.succ) n x ≠
        LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
          ActualInitialization.geometry.coord c u n x i ∧
      actualCrossDefect B N0 c u n x i ≠ 0 ∧
      0 < |actualCrossDefect B N0 c u n x i| ∧
      |actualCrossDefect B N0 c u n x i| =
        |missingWeight (choice B N0).prepared.N (physicalScale n x)| *
          |actualRequestedComponent c u n x i| := by
  have hclasses' := ActualSignedMeanBinding.family_defects_all_exponents
    (B := B) (N0 := N0) c u f a hprimary htangent hlabels hS H hfixed hθ hz
  have hclasses : ∀ γ : ℝ,
      WeightedClasses.MeanClass ActualInitialization.geometry.strip γ
          (CrossBasedMeanComposition.crossDefect ActualInitialization.geometry 2
            (u.thetaResidual c) (SignedMeanGain.crossTensor f a 0 1)) ∧
        WeightedClasses.MeanClass ActualInitialization.geometry.strip γ
          (CrossBasedMeanComposition.crossDefect ActualInitialization.geometry 1
            (u.axialResidual c) (SignedMeanGain.crossTensor f a 0 2)) := by
    simpa only [CrossBasedMeanComposition.crossDefect] using hclasses'
  have hselectedClasses : ∀ γ : ℝ,
      WeightedClasses.MeanClass ActualInitialization.geometry.strip γ
        (familyCrossDefectField c u f a i) := by
    intro γ
    fin_cases i
    · simpa [familyCrossDefectField, familyCrossField, actualRequestedField,
        actualRequestedComponent, actualRequestedField_zero,
        CrossBasedMeanComposition.crossDefect] using (hclasses γ).1
    · simpa [familyCrossDefectField, familyCrossField, actualRequestedField,
        actualRequestedComponent, actualRequestedField_one,
        CrossBasedMeanComposition.crossDefect] using (hclasses γ).2
  have hfield := familyCrossField_eq_actualCrossField B N0 c u f a
    hprimary htangent hlabels i
  have hdefectField := familyCrossDefectField_eq_actualCrossDefectField B N0 c u f a
    hprimary htangent hlabels i
  have hfamilyDefectNe : familyCrossDefectField c u f a i ≠ 0 := by
    rw [hdefectField]
    exact W.defectField_ne_zero
  have hnotAgree : ¬ MeanIncrementBounds.Agree
      ActualInitialization.geometry.strip.domain
      (familyCrossField f a i) (actualRequestedField c u i) := by
    intro hagree
    apply W.not_agree
    simpa only [hfield] using hagree
  have hfamily_ne :
      StateMomentBalances.meanBar (SignedMeanGain.crossTensor f a 0 i.succ) n x ≠
        LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
          ActualInitialization.geometry.coord c u n x i := by
    simpa [familyCrossField, actualRequestedField, actualRequestedComponent] using
      (show familyCrossField f a i n x ≠ actualRequestedField c u i n x by
        rw [hfield]
        exact W.cross_ne_requested)
  exact ⟨native_route_unavailable, hclasses, hselectedClasses, W.band_lt_tailStart,
    hdefectField, hfamilyDefectNe, hnotAgree, hfamily_ne, W.defect_ne_zero⟩

/-- State immediately after the actual cycle's particular correction and
before its signed correction.  This is the state whose requested stress is
fed to the physical-tail replacement. -/
noncomputable def actualCyclePostParticularState (B N0 j : ℕ) :
    CorrectionState.State ActualPoint :=
  let s := ActualCyclePreservation.state B N0 j
  (ActualCycleParameters.fixedParameters B N0).afterParticular s.coefficients
    (CorrectionInitialization.ActualPrimary.commonContext B) s.state

/-- The exact tail-only input package assembled by the claimed proof at an
actual cycle stage.  Unlike `ActualNativeData`, this type is inhabited. -/
abbrev ActualCycleStepData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :=
  CorrectionAnalyticStep.StepData ActualInitialization.geometry
    CorrectionInitialization.ActualPrimary.h
    (CorrectionInitialization.CommonWindow.index CorrectionInitialization.ActualPrimary.h)
    ActualInitialization.axial
    (fun l => ActualParticularStageControls.canonicalParameters (l.2, l.1))
    ActualSignedStageControls.parameters CorrectionInitialization.ActualPrimary.rankData
    (CorrectionInitialization.ActualPrimary.commonContext B)
    (ActualCyclePreservation.state B N0 j) ActualInitialization.tangentBlock
    ActualInitialization.envelope ActualCoreSupport.refinedCarrier
    (ActualCyclePreservation.staticData B)
    (ActualCyclePreservation.state_invariant B N0 hN j)
    (ActualIterationLedger.sigma_admissible j)

/-- The analytic output produced by consuming `ActualCycleStepData` in the
claimed correction step. -/
abbrev ActualCycleStepResult (B N0 j : ℕ) :=
  CorrectionAnalyticStep.StepResult ActualInitialization.geometry
    CorrectionInitialization.ActualPrimary.h
    (CorrectionInitialization.CommonWindow.index CorrectionInitialization.ActualPrimary.h)
    ActualInitialization.axial
    (fun l => ActualParticularStageControls.canonicalParameters (l.2, l.1))
    ActualSignedStageControls.parameters CorrectionInitialization.ActualPrimary.rankData
    (CorrectionInitialization.ActualPrimary.commonContext B)
    (ActualCyclePreservation.state B N0 j) ActualInitialization.tangentBlock
    ActualInitialization.envelope ActualCoreSupport.refinedCarrier
    (σ := ActualIterationLedger.sigma j) (κ := ChartScales.kappa)

/-- The precise semantic closure claim refuted by the finite-prefix
obstruction.  It packages the outputs the actual cycle really proves together
with the additional assertion that the signed cross still has native
semantics.  The first two fields are inhabited by the claimed proof; the third
is the incompatible semantic strengthening. -/
structure ActualCycleNativeSemanticClosure (B N0 j : ℕ) (i : Fin 2) : Prop where
  step_result : ActualCycleStepResult B N0 j
  next_invariant : ActualCyclePreservation.RunInvariant
    (ActualIterationLedger.sigma (j + 1))
    (ActualCyclePreservation.state B N0 (j + 1))
  native_cross : NativeCrossSemanticsAvailable B N0
    (CorrectionInitialization.ActualPrimary.commonContext B)
    (actualCyclePostParticularState B N0 j) i

/-- Major source-level aggregation for the actual correction cycle.

At a witnessed finite band, exact cross compatibility fails with a positive,
factorized defect.  At every admitted tail band, the physical replacement is
exact.  The claimed correction machinery nevertheless constructs the next
full run invariant from that tail-only contract, even though the normalized
native route is unavailable.  Thus cycle advancement has the semantics of
"tail agreement plus finite-head class absorption", not the semantics of the
uninhabited all-band `NativeData` contract. -/
theorem actual_cycle_advances_across_native_semantic_mismatch
    (B N0 j n : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : ActualPoint) (i : Fin 2)
    (W : FinitePrefixObstruction B N0
      (CorrectionInitialization.ActualPrimary.commonContext B)
      (actualCyclePostParticularState B N0 j) n x i) :
    ¬ NativeRouteAvailable ∧
      n < (choice B N0).prepared.N + 1 ∧
      ¬ MeanIncrementBounds.Agree ActualInitialization.geometry.strip.domain
        (actualCrossField B N0 (CorrectionInitialization.ActualPrimary.commonContext B)
          (actualCyclePostParticularState B N0 j) i)
        (actualRequestedField (CorrectionInitialization.ActualPrimary.commonContext B)
          (actualCyclePostParticularState B N0 j) i) ∧
      actualCrossDefectField B N0 (CorrectionInitialization.ActualPrimary.commonContext B)
        (actualCyclePostParticularState B N0 j) i ≠ 0 ∧
      actualCrossComponent B N0 (CorrectionInitialization.ActualPrimary.commonContext B)
          (actualCyclePostParticularState B N0 j) n x i ≠
        actualRequestedComponent (CorrectionInitialization.ActualPrimary.commonContext B)
          (actualCyclePostParticularState B N0 j) n x i ∧
      actualCrossDefect B N0 (CorrectionInitialization.ActualPrimary.commonContext B)
          (actualCyclePostParticularState B N0 j) n x i ≠ 0 ∧
      0 < |actualCrossDefect B N0 (CorrectionInitialization.ActualPrimary.commonContext B)
        (actualCyclePostParticularState B N0 j) n x i| ∧
      |actualCrossDefect B N0 (CorrectionInitialization.ActualPrimary.commonContext B)
          (actualCyclePostParticularState B N0 j) n x i| =
        |missingWeight (choice B N0).prepared.N (physicalScale n x)| *
          |actualRequestedComponent (CorrectionInitialization.ActualPrimary.commonContext B)
            (actualCyclePostParticularState B N0 j) n x i| ∧
      (∀ k : Fin 2, ∀ m, (choice B N0).prepared.N + 1 ≤ m →
        Set.EqOn
          (actualCrossField B N0 (CorrectionInitialization.ActualPrimary.commonContext B)
            (actualCyclePostParticularState B N0 j) k m)
          (actualRequestedField (CorrectionInitialization.ActualPrimary.commonContext B)
            (actualCyclePostParticularState B N0 j) k m)
          ActualInitialization.geometry.strip.domain) ∧
      (∃ d : ActualCycleStepData B N0 hN j,
        d.tailStart = (choice B N0).prepared.N + 1) ∧
      ActualCycleStepResult B N0 j ∧
      ActualCyclePreservation.RunInvariant (ActualIterationLedger.sigma (j + 1))
        (ActualCyclePreservation.state B N0 (j + 1)) := by
  have hdefect := W.defect_ne_zero
  have hcrossNe :
      actualCrossComponent B N0 (CorrectionInitialization.ActualPrimary.commonContext B)
          (actualCyclePostParticularState B N0 j) n x i ≠
        actualRequestedComponent (CorrectionInitialization.ActualPrimary.commonContext B)
          (actualCyclePostParticularState B N0 j) n x i := by
    simpa [actualCrossField, actualRequestedField] using W.cross_ne_requested
  refine ⟨native_route_unavailable, W.band_lt_tailStart, W.not_agree,
    W.defectField_ne_zero, hcrossNe,
    hdefect.1, hdefect.2.1, hdefect.2.2, ?_, ?_,
    ActualCyclePreservation.state_result B N0 hN j,
    ActualCyclePreservation.state_runInvariant B N0 hN (j + 1)⟩
  · intro k m hm y hy
    simpa [actualCrossField, actualRequestedField] using
      (actual_cross_tail_exact B N0
        (CorrectionInitialization.ActualPrimary.commonContext B)
        (actualCyclePostParticularState B N0 j) hm hy k).1
  · exact ⟨ActualCyclePreservation.state_stepData B N0 hN j, rfl⟩

/-- Closing aggregation: the actual correction machinery proves its analytic
step result and next run invariant, but those outputs cannot be strengthened
to the native cross semantics.  Thus the physical-tail replacement advances
the claimed cycle only under the weaker "tail equality plus finite-head class
absorption" contract.

This closes the source-interface implication once a `FinitePrefixObstruction`
is supplied; it does not construct that witness.  Nor does it identify the
finite-prefix defect with a nonflat physical residual: that separate terminal
PDE transport still requires a residual-exposure certificate. -/
theorem actual_cycle_advances_without_native_semantic_closure
    (B N0 j n : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : ActualPoint) (i : Fin 2)
    (W : FinitePrefixObstruction B N0
      (CorrectionInitialization.ActualPrimary.commonContext B)
      (actualCyclePostParticularState B N0 j) n x i) :
    ActualCycleStepResult B N0 j ∧
      ActualCyclePreservation.RunInvariant (ActualIterationLedger.sigma (j + 1))
        (ActualCyclePreservation.state B N0 (j + 1)) ∧
      ¬ ActualCycleNativeSemanticClosure B N0 j i := by
  refine ⟨ActualCyclePreservation.state_result B N0 hN j,
    ActualCyclePreservation.state_runInvariant B N0 hN (j + 1), ?_⟩
  exact W.refutes_claim_of_native_cross_semantics
    ActualCycleNativeSemanticClosure.native_cross

/-- Closing corollary in contradiction form: an actual finite-prefix witness
and a claimed native-semantic closure of that cycle produce `False`. -/
theorem actual_cycle_native_semantic_closure_contradiction
    {B N0 j n : ℕ} {x : ActualPoint} {i : Fin 2}
    (W : FinitePrefixObstruction B N0
      (CorrectionInitialization.ActualPrimary.commonContext B)
      (actualCyclePostParticularState B N0 j) n x i)
    (closure : ActualCycleNativeSemanticClosure B N0 j i) : False :=
  W.no_native_cross_semantics closure.native_cross

end NavierStokes.CounterProof.Adapter.NativeDataObstruction
