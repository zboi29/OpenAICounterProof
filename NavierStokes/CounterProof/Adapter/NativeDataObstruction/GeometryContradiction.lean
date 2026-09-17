import NavierStokes.ActualSignedMeanBinding

/-!
# NativeData geometry obstruction

This module isolates a concrete obstruction to the claimed native signed
mean-gain route.  It is not an obstacle to the counter-proof formalization:
it is evidence produced by that formalization.

`SignedMeanGain.NativeData G` is the complete input package used by both
`SignedMeanGain.native_signed_mean_gain` and
`BandReindexedSignedMeanGain.native_signed_mean_gain`.  On the actual geometry
its `tail_bound` field requires

`coordinateQ ≤ Q (index n) ≤ 1/2`,

whereas membership in the actual strip requires `1/2 < coordinateQ`.  Hence no
such package exists.  Relabeling the finite sums does not change this
geometric contradiction because the band-reindexed theorem retains the same
`NativeData` argument.

This is an independently sufficient, source-instantiated counter-proof of the
pinned native route.  It is complete at `native_route_unavailable`; no endpoint
wrapper, cokernel direction, tail budget, or `JointCokernelCertificate` is
needed.  `refute_claim_of_native_data_requirement` only transports the result
to a broader claim that entails existence of the impossible package.
NativeData is not logically required to construct either dual branch or the
primary joint certificate.  On the pinned source, however, this exact geometry
failure forces scrutiny of the physical replacement and is the preferred
starting point for generating both branch obligations and their common witness.

## Manuscript correspondence

The companion note's §8 Phase II requires the reduced operator to come from
the exact cross tensor, while §8 Phases III–VI and the §15 rows "Weighted gain"
and "Flat edge" require hidden reconstruction, differentiated estimates, a
finite-jet witness, and complete-tail control.  The contradiction below is the
exact source-level audit of that interface: the normalized native package
cannot be instantiated on the geometry whose reconstruction and weighted gain
it is meant to control.  This NativeData incompatibility is a new Lean audit
derived from the manuscript program, not a contradiction stated in the note.
-/

namespace NavierStokes.CounterProof.Adapter.NativeDataObstruction

/-- The exact native package required by the generic signed mean-gain route on
the geometry used by the claimed proof. -/
abbrev ActualNativeData :=
  SignedMeanGain.NativeData ActualInitialization.geometry

/-- Availability of the generic native route is existence of its required
input package, not merely existence of one cross-cancellation identity. -/
def NativeRouteAvailable : Prop := Nonempty ActualNativeData

/-- A concrete point witnesses that the actual strip lies on the forbidden
side of the normalized half-scale bound. -/
theorem exists_actual_strip_point_above_half :
    ∃ x : ActualSignedMeanBinding.Point,
      x ∈ ActualInitialization.geometry.strip.domain ∧
        (1 / 2 : ℝ) < SimilarityCoordinates.coordinateQ
          ActualInitialization.geometry.coord x.2.1 := by
  obtain ⟨x, hx⟩ := ActualSignedMeanBinding.actual_strip_nonempty
  exact ⟨x, hx, (ActualInitialization.geometry.strip_subset hx).2.1⟩

/-- Every proposed actual NativeData package forces every strip point back to
the incompatible normalized half scale. -/
theorem native_tail_bound_le_half (data : ActualNativeData) (n : ℕ)
    {x : ActualSignedMeanBinding.Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) :
    SimilarityCoordinates.coordinateQ ActualInitialization.geometry.coord x.2.1 ≤
      (1 / 2 : ℝ) :=
  (data.tail_bound n x hx).trans
    (ActualSignedMeanBinding.Q_le_half (data.index_pos n))

/-- Pointwise core of the obstruction.  The contradiction already occurs in
`NativeData.tail_bound`; none of the later cone, assembly, or gain fields can
repair it. -/
theorem tail_bound_contradiction
    (data : ActualNativeData) {x : ActualSignedMeanBinding.Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) : False := by
  have hlarge : (1 / 2 : ℝ) < SimilarityCoordinates.coordinateQ
      ActualInitialization.geometry.coord x.2.1 :=
    (ActualInitialization.geometry.strip_subset hx).2.1
  exact (not_lt_of_ge (native_tail_bound_le_half data 0 hx)) hlarge

/-- Direct eliminator for the impossible source package, with the actual strip
witness and the conflicting half-scale bounds made explicit in this module. -/
theorem actual_native_data_impossible (data : ActualNativeData) : False := by
  obtain ⟨x, hx, hlarge⟩ := exists_actual_strip_point_above_half
  exact (not_lt_of_ge (native_tail_bound_le_half data 0 hx)) hlarge

/-- Type-level form of the completed obstruction: the actual NativeData package
is empty. -/
theorem actual_nativeData_isEmpty : IsEmpty ActualNativeData :=
  ⟨actual_native_data_impossible⟩

/-- The genuine NativeData obstruction: the complete generic native route has
no input on the actual geometry. -/
theorem native_route_unavailable : ¬ NativeRouteAvailable := by
  rintro ⟨data⟩
  exact actual_nativeData_isEmpty.false data

/-- Optional transport data for a broader proposition whose proof would
produce the complete `NativeData` package on the actual geometry.  This record
is not required to complete `native_route_unavailable`; concrete applications
should instantiate it only for the additional endpoint being transported. -/
structure ClaimRequiresNativeData (claim : Prop) : Prop where
  nativeData_of_claim : claim → NativeRouteAvailable

namespace ClaimRequiresNativeData

/-- Optional transport of the completed NativeData counter-proof to a broader
NativeData-dependent endpoint.  A claim requiring the impossible package is
false before any dual-tail analysis.  The same discovery can still seed the
preferred source instantiation of the primary joint certificate through
`PhysicalScaleReplacement`. -/
theorem refutes_claim {claim : Prop} (requirement : ClaimRequiresNativeData claim) :
    ¬ claim := by
  intro hclaim
  exact native_route_unavailable (requirement.nativeData_of_claim hclaim)

end ClaimRequiresNativeData

/-- Function-form optional transport helper for an additional endpoint without
first packaging a `ClaimRequiresNativeData` record. -/
theorem refute_claim_of_native_data_requirement {claim : Prop}
    (requires : claim → NativeRouteAvailable) : ¬ claim :=
  (ClaimRequiresNativeData.mk requires).refutes_claim

end NavierStokes.CounterProof.Adapter.NativeDataObstruction
