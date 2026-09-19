# NativeData Obstruction Subsystem

This subsystem formalizes a concrete obstruction discovered while instantiating
the companion note’s dual-branch counter-proof program against the pinned
`NavierStokes/` source. The result is stronger than a warning about a difficult
formal interface: the complete native signed mean-gain input required by two
generic source theorems cannot exist on the actual geometry used by the claimed
proof.

The obstruction is exact, geometric, and independent of numerical estimates.
It is strategically central but logically nonessential to the reduced branch,
the full-compatible branch, and their unified `JointCokernelCertificate`.
The Version 1.1 joint certificate is the project’s primary terminal target;
NativeData is not a premise of its abstract theory. For this pinned source,
however, the NativeData discovery is the preferred robust bridge to both
branches and their common witness. The NativeData counter-proof is already
source-instantiated and complete; either completed individual branch remains
independently sufficient as well.

For new readers, `NativeData` is a Lean structure containing a complete native
assembly interface—matrices, targets, masks, oscillatory data, support and cone
conditions, label coverage, and a normalized tail bound. It does not mean
“whatever data the actual correction cycle happens to use.” The distinction is
central: proving one physical cross identity does not construct this structure.

## Research scope and subsystem boundary

The Adapter originally treated `NativeData` as one source object among many.
The deeper audit showed that three different logical layers had been conflated:

1. existence of the normalized native package;
2. the narrower physical-scale cross identity used by the actual cycle; and
3. finite-jet defects that may be tested by cokernel functionals.

Separating these layers prevents two opposite errors. First, the absence of
`NativeData` must not be misread as a limitation of the counter-proof code—it
is a new Lean source audit obtained by following the manuscripts’ prescribed
instantiation program, not a contradiction asserted in either manuscript.
Second, an eventual physical cross identity must not be advertised as if it
reconstructed every field and estimate contained in the impossible package.

The new subsystem gives each layer its own module and exposes only explicit
bridges between them.

## Conceptual map

Six terms organize the argument:

- **Native package:** the full `SignedMeanGain.NativeData` value required by the
  generic native mean-gain theorems.
- **NativeData obstruction:** the completed proof that the pinned native route's
  required package cannot exist on the actual geometry.
- **Optional endpoint transport:** a proof that another named claim entails
  availability of that impossible package.
- **Physical replacement** (or bypass): the partition-factor cross identity
  used by the actual correction cycle instead of `NativeData` for one specific
  cross-cancellation obligation.
- **Certificate feedback:** promotion of a concrete defect from that physical
  replacement into a finite-jet witness used by the reduced branch or primary
  joint certificate.
- **Preferred instantiation bridge:** use of the replacement’s common source
  defect and repair obligation to construct both branch estimates and one
  shared finite-jet functional for the primary joint certificate.

The complete NativeData counter-proof is

`NativeRouteAvailable → False`.

It is already specialized to `ActualInitialization.geometry` and needs no
further instantiation. An optional transport to a broader named claim is

`Claim → NativeRouteAvailable → False`.

The preferred source-instantiation chain is different:

`NativeData audit → forced physical replacement → common defect/repair obligation → two branch estimates → JointCokernelCertificate`.

The first chain does not depend on completing the second. Conversely, the
joint certificate does not logically depend on NativeData: a different exact
source argument could supply the same defect, repair, functional,
inverse/reconstruction losses, and complete-tail control.

## Discovery through dependency tracing

The companion note’s
[§8 Phases II–VI](../../../../docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex)
require the exact cross response, hidden-response subtraction, differentiated
inverse and reconstruction estimates, a finite-jet dual witness, and control
of the complete admissible tail. Following that dependency chain led to the two
generic mean-gain theorems:

- `SignedMeanGain.native_signed_mean_gain`;
- `BandReindexedSignedMeanGain.native_signed_mean_gain`.

Both quantify over the same input `B : SignedMeanGain.NativeData G`. Inspecting
that structure revealed the decisive `tail_bound` field. For every band `n`
and every point `x` in the strip, it demands

`coordinateQ(G, x) ≤ Q(B.index n)`.

The same structure requires `1 ≤ B.index n`, and the chart-scale theorem gives

`Q(B.index n) ≤ 1/2`.

For `ActualInitialization.geometry`, however, strip membership gives

`1/2 < coordinateQ(actual geometry, x)`.

Combining the inequalities yields

`1/2 < coordinateQ ≤ Q(B.index n) ≤ 1/2`,

which is impossible. `ActualSignedMeanBinding.actual_strip_nonempty` supplies a
concrete strip point, so the contradiction cannot be avoided by vacuous domain
membership. The upstream theorem `no_legacy_nativeData` proves the resulting
`IsEmpty` statement; this subsystem exposes it as a complete counter-proof and
provides a separate optional dependency-transport rule.

Band reindexing does not change the conclusion. It reindexes finite labels and
their coefficient identities, but its theorem still accepts the same
`NativeData G`. The conflict concerns physical strip scale, not label naming.

## Formal counter-proof statement and scope

The central theorem is `native_route_unavailable`:

`¬ Nonempty (SignedMeanGain.NativeData ActualInitialization.geometry)`.

This is already a terminal counter-proof of the pinned native route; the target
`NativeRouteAvailable` and actual geometry are concrete. It does not await a
finite-jet witness, tail estimate, joint certificate, or endpoint wrapper.

The subsystem additionally supports optional transport. Let `Claim` be another
proposition associated with the claimed construction. If an audit proves

`Claim → Nonempty ActualNativeData`,

then `Claim` is also false. `ClaimRequiresNativeData.refutes_claim` and
`refute_claim_of_native_data_requirement` formalize exactly this inference.

That dependency premise matters only for the broader transported claim; it is
not a missing hypothesis or final-instantiation obligation for
`native_route_unavailable`. Nonexistence of one proof object does not, by
itself, refute an unrelated proposition that might have a wholly different
proof. Any optional transport should therefore pin the broader endpoint and
prove the implication rather than relying on prose-level association.

In this README, a **route** means such a complete implication chain from pinned
source assumptions to a contradiction. An **obstruction** is the incompatible
interface or estimate in that chain. This terminology prevents the local fact
`NativeRouteAvailable → False` from being confused with an unqualified claim
about every possible proof of the final analytic theorem.

The logical sufficiency and project priority are distinct:

| Route | Logically sufficient? | Requires NativeData? | Project role |
| --- | --- | --- | --- |
| NativeData obstruction | Yes; already complete | Its nonexistence is the conclusion | Complete pinned-source counter-proof |
| Reduced branch | Yes | No | Independent terminal route |
| Full-compatible branch | Yes | No | Independent terminal route |
| Joint certificate | Yes | No | Primary project endpoint |
| NativeData-driven joint instantiation | Yes | Uses the discovery as evidence | Preferred implementation strategy |

Companion-note Theorem 6.1 and Proposition 6.2 give the quantitative branch
mechanisms, Corollary 6.3 gives their same-witness synthesis, and Theorem 7.1
connects either decisive branch to a terminal counter-proof. The §15 interface
checklist identifies the concrete Lean obligations. Thus the completed
NativeData counter-proof needs neither a cokernel direction nor a tail budget,
while the joint certificate remains available to any source argument that
supplies its hypotheses without NativeData.

## Physical-scale replacement: exact scope

The actual correction cycle does not construct `NativeData`. Instead,
`ActualSignedMeanBinding` proves the narrower identity

`actual cross = partitionFactor × requested stress`.

At an arbitrary band this gives the exact defect

`actual cross − requested stress = −missingWeight × requested stress`.

Beyond the explicit threshold `(choice B N0).prepared.N + 1 ≤ n`, where `n` is
the scale/band index, the partition factor is one. The source consequently
proves exact cross agreement and equality of every finite physical jet on that
tail. Here a finite jet means all derivatives through one fixed finite order.
This is the theorem inserted into `CorrectionAnalyticStep.StepData.cross_tail`.

That replacement is mathematically meaningful, but its scope must be
preserved. A cross-tail identity is one field-level conclusion. `NativeData`
packages much more: matrices, targets, masks, units, frequencies, phases,
angular modes, carrier matches, cone conditions, finite coverage, and the
normalized tail condition used by generic assembly and gain proofs. The bypass
neutralizes the direct obstruction only for an endpoint if the claimed proof
independently reconstructs every native consequence needed by that endpoint on
the actual physical scale.

`PhysicalScaleReplacement.lean` therefore records both sides of the audit:

- the exact arbitrary-band partition factor and missing component;
- the eventual exact cross and finite-jet identities.

It neither suppresses the finite prefix nor treats tail agreement as a value of
`NativeData`.

## Preferred bridge into the two branches and joint certificate

The NativeData analysis is the preferred source-specific way to construct the
two compatibility branches. The forced physical replacement produces the exact finite-prefix
defect used to seed the reduced branch and identifies the missing compatible
repair whose lift cost or total capacity drives the full-compatible branch. Thus one
source incompatibility organizes both targets, reduces duplicated witness
discovery, and gives the most natural provenance for a common finite-jet
functional. If `missingWeight ≠ 0` and the requested component is nonzero, the
physical finite-prefix cross defect is nonzero; a concrete observation may
expose it as one coordinate of the full observed branch defect.

This organization follows companion-note §8 Phases II–VI. The underlying
range/lift-cost, compatibility, and tail-survival interpretation comes from the
[general research note](../../../../docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex).

The dual language is simple at this level: a bounded scalar functional reads
one component of the observed response. It is useful when it detects the
defect but vanishes—or is quantitatively small—on responses allowed by the
full compatibility operator. That operator maps an admissible active variation,
including its forced hidden reconstruction, to the complete observed response.
A same-witness joint certificate uses one induced functional for both the
surviving-defect and unreachable-target estimates.

`CertificateFeedback.lean` formalizes that promotion. A
`FinitePrefixObstruction` stores the actual strip point and the two
nonvanishing hypotheses. Given

`coordinate(complete defect) = actualCrossDefect`,

`FinitePrefixObstruction.reducedDefectWitness` constructs a
`ReducedDefectWitness` with the exact, source-factorized magnitude
`|missingWeight| · |requested component|`. The bridge proves this is equal to
`|actualCrossDefect|` and to the absolute value detected by the observation
functional, so no quantitative information is lost at certificate promotion.

This witness can be used in either of two ways:

- as the reduced witness in the independent-branch pipeline; or
- as candidate data for the reduced side of a `JointCokernelCertificate`.

The preferred second promotion requires more than nonvanishing. The same
coordinate functional must also control the full reconstructed response, agree
with the tail-capacity functional, and retain a positive margin after the
complete linear and nonlinear future tail. Those are genuine Phase VI
obligations and are not inferred from the NativeData contradiction. They
implement companion-note Theorem 6.1, Proposition 6.2, and Corollary 6.3.

The bridge is therefore:

`exact bypass defect and repair → common finite-jet witness candidate → two quantitative branch estimates → joint certificate`.

It preserves the completed NativeData counter-proof while making the
same-witness formulation the primary implementation target. A non-NativeData
construction could still reach that target, but it would have to reproduce
independently the complete observed defect, compatible repair target, common
functional, inverse/reconstruction losses, and complete-tail control.

## Module map

### `GeometryContradiction.lean`

- Names the actual native package and route-availability proposition.
- Proves `native_route_unavailable` from an explicit actual-strip witness at
  exact normalized coordinate `1` and the full incompatible chain
  `coordinateQ ≤ Q(index n) ≤ 1/2` for every band `n`.
- Exposes `exists_actual_strip_point_above_half`,
  `native_tail_bound_le_half`, `tail_bound_contradiction`, the direct eliminator
  `actual_native_data_impossible`, and `actual_nativeData_isEmpty`.
- Defines `ClaimRequiresNativeData` and optional transport rules for broader
  claims.

### `PhysicalScaleReplacement.lean`

- Defines the actual cross, requested component, missing component, and scalar
  defect.
- Proves the partition-factor and negative-missing-component identities while
  retaining the exact absolute margin
  `|defect| = |missingWeight| · |requested component|`.
- Characterizes exact cancellation simultaneously as zero missing component
  and zero scalar defect.
- Proves nonzero finite-prefix mismatch, positive absolute defect, and the
  exact factorized margin from nonzero weight and request.
- Exports simultaneous tail closure—factor one, missing component zero, defect
  zero, and exact cancellation—and agreement of every derivative order
  `k ≤ m` in one finite-jet theorem.

### `CertificateFeedback.lean`

- Packages nonzero finite-prefix data.
- Proves the associated scalar defect is nonzero and has the exact positive
  factorized magnitude.
- Constructs a `ReducedDefectWitness` from a verified observation-coordinate
  identity without replacing the physical product margin by an opaque
  constant.
- Stops before asserting the near-cokernel and complete-tail hypotheses needed
  for a joint certificate.

### `SemanticMismatch.lean`

- Binds the literal claimed-proof cross field to the actual physical-scale
  cross and promotes a finite-prefix point witness to failure of all-band
  `MeanIncrementBounds.Agree`.
- Defines `NativeCrossSemanticsAvailable` as the two source alternatives
  audited here: availability of the normalized native route or exact all-band
  agreement of its physical replacement.
- Proves the strong reusable helper
  `FinitePrefixObstruction.no_native_cross_semantics` and its generic claim
  transport rule.
- Packages the claimed proof's actual `StepResult` and next `RunInvariant` in
  `ActualCycleNativeSemanticClosure`, then proves that the cycle advances
  without this semantic closure and derives the closing contradiction from any
  asserted closure object together with a `FinitePrefixObstruction` witness.
- Keeps this source-interface contradiction separate from a physical-residual
  contradiction: the latter still requires complete-tail survival and a
  concrete residual-exposure certificate.

Import `NavierStokes.CounterProof.Adapter.NativeDataObstruction` for the whole
subsystem. The public `SignedMeanInterface` re-exports its principal types and
theorems.

## Optional transport and extension protocol

No work is required to complete `native_route_unavailable`. To transport that
result to a broader endpoint or audit the physical replacement, proceed as
follows:

1. Select a precise claimed endpoint, not the entire project informally.
2. Trace which generic native theorem or native consequence the endpoint uses.
3. For optional transport, prove `ClaimRequiresNativeData Claim`; otherwise
   isolate the exact consequence that the physical replacement must reproduce.
4. Apply the already-complete `native_route_unavailable` result.
5. Separately audit any proposed physical replacement through request
   differentiation, inverse loss, full reconstruction, and complete-tail
   control.
6. If using certificate feedback, prove the scalar-to-observation coordinate
   identity before invoking `reducedDefectWitness`.
7. Prefer a joint instantiation when this same functional satisfies both the
   full-response and tail-capacity estimates; preserve either completed branch
   as an independent terminal counter-proof.

This discipline prevents specification drift between normalized chart data,
physical-scale data, reduced cancellation, and full primitive compatibility.

## Source correspondence and validation

The formal audit is motivated by §8 Phases II–VI, Theorem 6.1, Proposition 6.2,
Corollary 6.3, Theorem 7.1, and the §15 interface checklist in
[`Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`](../../../../docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex).
The broader range/lift-cost, compatibility, tail-survival, and residual-leakage
framework is grounded in
[`Primitive_Liftability_Obstructions_NSE_Research_Note.tex`](../../../../docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex).
In particular, its Proposition 8.2 and Corollary 8.3 transport a surviving
observed mismatch to physical residual nonflatness. The exact NativeData
incompatibility is not claimed by either manuscript; it is the Lean source
audit produced by applying their program to the pinned definitions.

Validate focused changes with:

```text
lake build NavierStokes.CounterProof.Adapter.NativeDataObstruction
lake build NavierStokes.CounterProof
lake build NavierStokes
```

No module in this subsystem may introduce `sorry` or `admit`.
