# NativeData Obstruction Subsystem

This subsystem formalizes a concrete obstruction discovered while instantiating
the companion note’s dual-branch counter-proof program against the pinned
`NavierStokes/` source. The result is stronger than a warning about a difficult
formal interface: the complete native signed mean-gain input required by two
generic source theorems cannot exist on the actual geometry used by the claimed
proof.

The obstruction is exact, geometric, and independent of numerical estimates.
It is also logically independent of the reduced/full dual branches and their
unified `JointCokernelCertificate`. Those routes can exchange evidence, but
neither should be presented as a prerequisite for the other.

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
is a discovered incompatibility in the claimed proof route. Second, an eventual
physical cross identity must not be advertised as if it reconstructed every
field and estimate contained in the impossible package.

The new subsystem gives each layer its own module and exposes only explicit
bridges between them.

## Conceptual map

Four terms organize the argument:

- **Native package:** the full `SignedMeanGain.NativeData` value required by the
  generic native mean-gain theorems.
- **Dependency obstruction:** a proof that a claimed endpoint requires that
  package, combined with a proof that the package cannot exist.
- **Physical replacement** (or bypass): the partition-factor cross identity
  used by the actual correction cycle instead of `NativeData` for one specific
  cross-cancellation obligation.
- **Certificate feedback:** promotion of a concrete defect from that physical
  replacement into a finite-jet witness used by the reduced or joint route.

The standalone logical chain is

`Claim → NativeRouteAvailable → False`.

The optional feedback chain is different:

`physical replacement defect → finite-jet witness → tail-stable dual certificate`.

The first chain does not depend on completing the second.

## Discovery through dependency tracing

The companion note’s dual-branch formulation requires the reduced operator to
be differentiated from the exact source cross tensor, then requires all
inverse, reconstruction, and weighted estimates to be propagated through the
complete physical response. Following that dependency chain led to the two
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
`IsEmpty` statement; this subsystem promotes it into an explicit counter-proof
interface and dependency rule.

Band reindexing does not change the conclusion. It reindexes finite labels and
their coefficient identities, but its theorem still accepts the same
`NativeData G`. The conflict concerns physical strip scale, not label naming.

## Formal counter-proof statement and scope

The central theorem is `native_route_unavailable`:

`¬ Nonempty (SignedMeanGain.NativeData ActualInitialization.geometry)`.

This supports a standalone counter-proof schema. Let `Claim` be the proposition
expressing one pinned endpoint of the claimed construction. If the audit proves

`Claim → Nonempty ActualNativeData`,

then `Claim` is false. `ClaimRequiresNativeData.refutes_claim` and
`refute_claim_of_native_data_requirement` formalize exactly this inference.

The dependency premise matters. Nonexistence of one proof object does not, by
itself, refute an unrelated mathematical proposition that might have a wholly
different proof. The relevant counter-proof target is a claimed endpoint whose
source dependency genuinely entails the native package or one of its
unrecovered obligations. Concrete uses should therefore pin the endpoint and
prove the implication rather than relying on prose-level association.

In this README, a **route** means such a complete implication chain from pinned
source assumptions to a contradiction. An **obstruction** is the incompatible
interface or estimate in that chain. This terminology prevents the local fact
`NativeRouteAvailable → False` from being confused with an unqualified claim
about every possible proof of the final analytic theorem.

This route is separate from the companion note’s two compatibility branches:

| Route | Decisive input | Required terminal work |
| --- | --- | --- |
| NativeData dependency | `Claim → NativeRouteAvailable` | Apply package nonexistence |
| Reduced-response branch | Detected complete-response defect | Prove survival through every admissible tail and residual exposure |
| Full-compatible branch | Target exceeds full response capacity | Exclude every admissible realizing tail |
| Joint route | One functional supports both branch estimates | Instantiate `JointCokernelCertificate` |

Thus the NativeData route needs neither a cokernel direction nor a tail budget.
Conversely, proving a joint certificate is not necessary to validate the
NativeData contradiction.

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
preserved. A
cross-tail identity is one field-level conclusion. `NativeData` packages much
more: matrices, targets, masks, units, frequencies, phases, angular modes,
carrier matches, cone conditions, finite coverage, and the normalized tail
condition used by generic assembly and gain proofs. The bypass neutralizes the
standalone obstruction only for an endpoint if the claimed proof independently
reconstructs every native consequence needed by that endpoint on the actual
physical scale.

`PhysicalScaleReplacement.lean` therefore records both sides of the audit:

- the exact arbitrary-band partition factor and missing component;
- the eventual exact cross and finite-jet identities.

It neither suppresses the finite prefix nor treats tail agreement as a value of
`NativeData`.

## Certificate feedback into dual and joint routes

Although logically independent, the NativeData analysis can strengthen the
dual-branch program. If `missingWeight ≠ 0` and the requested component is
nonzero, then the physical finite-prefix cross defect is nonzero. A concrete
finite-jet observation may expose this scalar as one coordinate of the full
observed branch defect.

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
`ReducedDefectWitness` with the exact magnitude `|actualCrossDefect|`.

This witness can be used in either of two ways:

- as the reduced witness in the independent-branch pipeline; or
- as candidate data for the reduced side of a `JointCokernelCertificate`.

The second promotion requires more than nonvanishing. The same coordinate
functional must also control the full reconstructed response, agree with the
tail-capacity functional, and retain a positive margin after the complete
linear and nonlinear future tail. Those are genuine Phase-VI obligations and
are not inferred from the NativeData contradiction.

This one-way bridge is intentional:

`NativeData contradiction → exact bypass audit → finite-jet witness candidate`.

It preserves the standalone obstruction while allowing its concrete defect to
participate in the stronger same-witness formulation.

## Module map

### `GeometryContradiction.lean`

- Names the actual native package and route-availability proposition.
- Proves `native_route_unavailable`.
- Exposes the pointwise `tail_bound_contradiction`.
- Defines `ClaimRequiresNativeData` and the standalone refutation rules.

### `PhysicalScaleReplacement.lean`

- Defines the actual cross, requested component, missing component, and scalar
  defect.
- Proves the partition-factor and negative-missing-component identities.
- Characterizes exact cancellation.
- Proves nonzero finite-prefix defect from nonzero weight and request.
- Exports eventual cross and all-finite-jet agreement.

### `CertificateFeedback.lean`

- Packages nonzero finite-prefix data.
- Proves the associated scalar defect is nonzero.
- Constructs a `ReducedDefectWitness` from a verified observation-coordinate
  identity.
- Stops before asserting the near-cokernel and complete-tail hypotheses needed
  for a joint certificate.

Import `NavierStokes.CounterProof.Adapter.NativeDataObstruction` for the whole
subsystem. The public `SignedMeanInterface` re-exports its principal types and
theorems.

## Extension protocol

New work should proceed in the following order:

1. Select a precise claimed endpoint, not the entire project informally.
2. Trace which generic native theorem or native consequence the endpoint uses.
3. Prove `ClaimRequiresNativeData Claim`, or isolate the exact consequence that
   the physical replacement must reproduce.
4. Apply `native_route_unavailable` for the standalone route.
5. Separately audit any proposed physical replacement through request
   differentiation, inverse loss, full reconstruction, and complete-tail
   control.
6. If using certificate feedback, prove the scalar-to-observation coordinate
   identity before invoking `reducedDefectWitness`.
7. Instantiate a joint certificate only after proving that this same functional
   satisfies both the full-response and tail-capacity estimates.

This discipline prevents specification drift between normalized chart data,
physical-scale data, reduced cancellation, and full primitive compatibility.

## Source correspondence and validation

The formal audit is motivated by §8 Phases II and IV–VI and the §15 interface
checklist in
[`Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`](../../../../docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex).
The broader interpretation as a primitive liftability/interface obstruction is
grounded in
[`Primitive_Liftability_Obstructions_NSE_Research_Note.tex`](../../../../docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex).

Validate focused changes with:

```text
lake build NavierStokes.CounterProof.Adapter.NativeDataObstruction
lake build NavierStokes.CounterProof
lake build NavierStokes
```

No module in this subsystem may introduce `sorry` or `admit`.
