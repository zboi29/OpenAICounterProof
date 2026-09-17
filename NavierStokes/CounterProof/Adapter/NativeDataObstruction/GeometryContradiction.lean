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

This gives an independently sufficient direct closure.  Whenever a claimed
endpoint entails the existence of this native package,
`refute_claim_of_native_data_requirement` refutes that endpoint directly; no
cokernel direction, tail budget, or `JointCokernelCertificate` is needed.
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

/-- The genuine NativeData obstruction: the complete generic native route has
no input on the actual geometry. -/
theorem native_route_unavailable : ¬ NativeRouteAvailable := by
  rintro ⟨data⟩
  exact ActualSignedMeanBinding.no_legacy_nativeData.false data

/-- Pointwise core of the obstruction.  The contradiction already occurs in
`NativeData.tail_bound`; none of the later cone, assembly, or gain fields can
repair it. -/
theorem tail_bound_contradiction
    (data : ActualNativeData) {x : ActualSignedMeanBinding.Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) : False :=
  ActualSignedMeanBinding.legacy_nativeData_excludes_strip data hx

/-- A proposition is dependent on the native route when proving it would
produce the complete `NativeData` package on the actual geometry.  Concrete
audits should instantiate `nativeData_of_claim` at the precise claimed
endpoint rather than assuming the dependency informally. -/
structure ClaimRequiresNativeData (claim : Prop) : Prop where
  nativeData_of_claim : claim → NativeRouteAvailable

namespace ClaimRequiresNativeData

/-- Direct counter-proof rule for NativeData-dependent endpoints.  It is
logically independent of both branches of `JointCokernelCertificate`: a claim
requiring an impossible native package is false before any dual-tail analysis.
The same discovery can still seed the preferred source instantiation of the
primary joint certificate through `PhysicalScaleReplacement`. -/
theorem refutes_claim {claim : Prop} (requirement : ClaimRequiresNativeData claim) :
    ¬ claim := by
  intro hclaim
  exact native_route_unavailable (requirement.nativeData_of_claim hclaim)

end ClaimRequiresNativeData

/-- Function-form helper for auditing an endpoint without first packaging a
`ClaimRequiresNativeData` record. -/
theorem refute_claim_of_native_data_requirement {claim : Prop}
    (requires : claim → NativeRouteAvailable) : ¬ claim :=
  (ClaimRequiresNativeData.mk requires).refutes_claim

end NavierStokes.CounterProof.Adapter.NativeDataObstruction
