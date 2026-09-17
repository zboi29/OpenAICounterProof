# Adapter Subsystem

This subsystem audits the pinned `NavierStokes/` construction using its exact
objects and completed proofs. It connects source-specific data to the abstract
liftability, reconstruction, and certificate layers without replacing the
claimed construction by a surrogate model.

Its governing question is not merely whether an isolated source identity is
true. The Adapter asks whether the exact objects used by the claimed proof can
be instantiated on the actual geometry, differentiated through the actual
reconstruction, controlled through every admissible correction, and connected
to the claimed smooth/flat endpoint.

## Working vocabulary

The documentation uses several terms in a precise, repository-specific sense:

- A **claimed endpoint** is a theorem-level conclusion of the pinned source,
  such as flatness of a physical residual or existence of a smooth extension.
- A **source package** is a Lean structure containing the data and hypotheses
  required to apply an upstream theorem. `SignedMeanGain.NativeData` is one
  such package; it is not merely a collection of numerical input values.
- A **physical replacement** (also called a bypass) is an alternative source
  theorem that proves a narrower obligation without constructing the original
  package.
- A **finite-jet witness** is a bounded scalar observation of finitely many
  derivatives at selected physical points.
- The **complete tail** includes every later admissible correction, both linear
  and nonlinear. A finite-stage mismatch is terminal only after this tail is
  controlled or excluded.

These definitions make it possible to distinguish failure of a required
interface from a mismatch inside a successfully instantiated interface.

## Architecture and data flow

The public import is `NavierStokes.CounterProof.SignedMeanInterface`. Internally
the preferred source attachment follows this pipeline:

`NativeData audit → forced physical replacement → common defect/repair obligation → two branch estimates → JointCokernelCertificate`.

This is an implementation preference, not a logical premise of the abstract
certificate theory. A non-NativeData source argument could instantiate either
branch or the joint certificate if it supplied the same exact defect, compatible
repair, finite-jet functional, reconstruction losses, and complete-tail bounds.
For the pinned source, however, the NativeData audit is the most efficient and
robust bridge: its contradiction is geometry-pinned, its physical replacement
exhibits an exact omitted component, and that single incompatibility gives the
reduced defect and full-compatible repair obligation a common provenance.

The implementation work has four stages:

| Stage | Responsibility | Principal modules |
| --- | --- | --- |
| Interface audit | Determine whether required source packages exist and preserve exact physical-replacement factors | `NativeDataObstruction/` |
| Exact reconstruction | Retain covariance remainder, inverse solve, pressure feedback, and full response | `ExactCovariance`, `RequestDifferential`, `ReconstructedResponse`, `FullCompatibility` |
| Quantitative transport | Track conditioning, stage loss, finite jets, and future capacity | `ConditionedResponse`, `ResidualLedger`, `FiniteJetWitness`, `DiagonalTail` |
| Terminal exposure | Push a surviving observed defect to physical residual nonflatness or target nonreachability | `PhysicalResidualExposure` |

The intended dependency direction is

`pinned source → exact adapters → finite-jet witnesses → tail certificates → physical endpoint`.

Imports should follow that direction. In particular, an upstream identity
should not import a downstream certificate merely to disguise a missing source
premise.

## Discovery and architectural rationale

The NativeData subsystem emerged from following the companion note’s
instantiation order rather than beginning with the already-packaged actual
cycle. In [§8 Phases II–VI of the companion note](../../../docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex),
the audit progresses from the exact cross response through hidden-response
subtraction, differentiated reconstruction and weighted estimates, finite-jet
witness selection, and complete-tail control. Tracing Phases II and IV to the
pinned source made both generic theorem paths converge on the same `NativeData`
premise. Comparing its normalized `tail_bound` with the actual strip exposed
the exact `q > 1/2` versus `q ≤ 1/2` contradiction. That incompatibility is a
new Lean source audit obtained by carrying out the manuscript’s instantiation
program; neither manuscript states this source-specific contradiction.

The subsequent audit found that the actual cycle replaced this premise for one
cross-cancellation obligation with a physical partition identity. That
replacement exposes the exact missing component which seeds the reduced defect
and identifies the compatible repair whose lift cost or total response capacity
must be controlled on the full-compatible branch. This is the concrete source version of
the range, lift-cost, compatibility, tail-survival, and residual-leakage
framework in the
[general research note](../../../docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex).
Using one source incompatibility for both obligations avoids duplicated witness
discovery, gives the strongest basis for choosing one common finite-jet
functional, and prevents unavailable normalized gain estimates from entering
either branch.

## Counter-proof route map

The Version 1.1 same-witness `JointCokernelCertificate` is the primary terminal
route. “Primary” records project priority and the strength of its joint
conclusion; it does not make NativeData, or either individual branch, a logical
prerequisite. The precise route hierarchy is:

| Route | Logically sufficient? | Requires NativeData? | Project role |
| --- | --- | --- | --- |
| NativeData obstruction | Yes; already complete | Its nonexistence is the conclusion | Complete pinned-source counter-proof |
| Reduced branch | Yes | No | Independent terminal route |
| Full-compatible branch | Yes | No | Independent terminal route |
| Joint certificate | Yes | No | Primary project endpoint |
| NativeData-driven joint instantiation | Yes | Uses the discovery as evidence | Preferred implementation strategy |

The companion note’s Theorem 6.1 and Proposition 6.2 establish the quantitative
branch mechanisms, Corollary 6.3 gives their same-witness joint synthesis, and
Theorem 7.1 states the terminal signed-mean counter-proof. Its §15 interface
checklist connects those obligations to the concrete Lean audit. These are the
manuscript grounds for route sufficiency; the NativeData incompatibility itself
is the Lean-derived source discovery described above.

### NativeData dependency obstruction

The generic and band-reindexed signed mean-gain theorems both require
`SignedMeanGain.NativeData ActualInitialization.geometry`. The
[`NativeDataObstruction/`](NativeDataObstruction/) subsystem proves that no such
value exists: `NativeData.tail_bound` forces the normalized strip coordinate
to be at most `1/2`, whereas every point in the actual strip has coordinate
strictly greater than `1/2`.

This is a complete, source-instantiated counter-proof of the pinned native
route: `native_route_unavailable` directly proves that its required input does
not exist on the actual geometry. No further instantiation, endpoint wrapper,
reduced/full-compatible branch comparison, dual functional, or
`JointCokernelCertificate` is needed. `ClaimRequiresNativeData.refutes_claim`
is only an optional transport rule: if a broader named endpoint entails the
impossible package, the completed counter-proof also refutes that endpoint.

For cross cancellation, the actual cycle replaces the unavailable package with
the narrower identity

`actual cross = partitionFactor × requested stress`.

That identity becomes exact only after an explicit tail threshold. It replaces
one cross-tail obligation; it does not itself reproduce the package's assembly,
uniform-bound, inverse, reconstruction, or mean-gain consequences. The audit
must identify and prove every such replacement on the physical-scale route.

### Independent compatibility branches

The companion note's two branches analyze that physical-scale route directly:

- The reduced branch proves that a mismatch produced by reduced cancellation
  survives the complete future tail and reaches a nonflat physical residual.
- The full-compatible branch proves that the requested target lies beyond the
  total response capacity of all admissible future corrections.

`FiniteJetWitness.lean`, `DiagonalTail.lean`, and
`PhysicalResidualExposure.lean` keep these witnesses independent. Either
branch is sufficient when its own source identification and tail hypotheses
are discharged, as formalized by companion-note Theorem 6.1, Proposition 6.2,
and Theorem 7.1. For the reduced route, transport from a surviving observed
mismatch to physical residual nonflatness is also grounded in Proposition 8.2
and Corollary 8.3 of the
[general research note](../../../docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex).

### Unified same-witness route

`JointCokernelCertificate` is the primary terminal target and strengthens the
two compatibility branches by using
one observed direction for both conclusions. The direction is a vector in the
Hilbert observation space; inner product with that vector induces a bounded
scalar functional. The functional nearly annihilates admissible full responses
while detecting the target or defect. The Adapter does not yet instantiate that
certificate. It preserves the exact source data needed to do so without
pretending that separately constructed functionals are already equal.

NativeData is not logically necessary to construct this certificate. It is the
preferred source-instantiation bridge for the pinned source because the forced
physical replacement has the exact finite-prefix defect

`cross − request = −missingWeight × request`.

`NativeDataObstruction/CertificateFeedback.lean` turns a proved nonzero defect
and a matching finite-jet coordinate into a `ReducedDefectWitness`. If that
same coordinate also satisfies the full-response near-cokernel and complete
tail-capacity bounds, it can become the shared functional of a
`JointCokernelCertificate`, following companion-note §8 Phases V–VI and
Corollary 6.3. The completed NativeData counter-proof alone does not discharge
those quantitative obligations. Failure to complete the promotion does not
weaken the independent NativeData counter-proof or either independently
completed branch.

## Route-selection criteria

Target the primary joint certificate when the pinned source supplies a common
witness, while retaining every independently complete closure:

- Treat the NativeData obstruction as complete for the pinned native route. If
  applying it to a broader named endpoint, separately prove that endpoint's
  dependency on the impossible package and use the optional transport rule.
- Use the reduced route when an actual reconstructed mismatch can be detected
  and shown to survive every admissible future correction.
- Use the full-compatible route when the target component is larger than the
  total response capacity, even if no reduced branch has been selected.
- Instantiate the joint certificate when one functional supports the reduced
  defect, near-cokernel response estimate, and complete-tail bound
  simultaneously.
- Prefer the NativeData-driven bridge for the current pinned source: audit the
  forced physical replacement, derive the common defect/repair obligation, and
  prove both branch estimates for the same finite-jet functional.

These routes are logically distinct even though the preferred implementation
shares their source geometry. A non-NativeData construction remains possible,
but it must independently reproduce the complete defect, compatible repair,
finite-jet functional, inverse/reconstruction losses, and complete-tail control
prescribed by companion-note §8 Phases II–VI and §15.

## Module organization

- `NativeDataObstruction/` centralizes the actual-geometry contradiction, the
  exact physical-scale replacement, and its certificate feedback.
- `NativeDataObstruction.lean` is the focused umbrella import for that nested
  subsystem.
- `ExactCovariance.lean` adapts `incrementTensor_split` as the literal identity
  `ΔW = S + E`, retaining subtraction and vanishing criteria for `E`.
- `ReconstructedResponse.lean` packages the `waveStage_*` identities for mean,
  covariance, radial source, pressure, and both tangential residual channels.
- `ReducedCross.lean` adapts `native_physical_cross` and
  `cross_cancels_with_defect` into the two-coordinate reduced response and an
  exact full-cancellation criterion.
- `RequestDifferential.lean` and `FullCompatibility.lean` expose the literal
  inverse solve, the `E₁` and quadratic covariance pieces, and the exact
  averaged θ/z response including reconstructed pressure.
- `ConditionedResponse.lean` and `ResidualLedger.lean` retain inverse,
  reconstruction, physical-jet, and stage-loss accounting.
- `FiniteJetWitness.lean` represents the eleven evaluated state coordinates,
  seven equality-constraint blocks, and independent dual witnesses.
- `DiagonalTail.lean` and `PhysicalResidualExposure.lean` connect complete
  linear/nonlinear tail capacity to the terminal branch conclusions.

Import `NavierStokes.CounterProof.SignedMeanInterface` for the public adapter
layer. Import `NavierStokes.CounterProof.Adapter.NativeDataObstruction` when
working on the completed NativeData counter-proof or the preferred source
bridge into the primary joint certificate.

## Proof discipline

Keep these distinctions explicit in new work:

- Do not describe the NativeData obstruction as awaiting instantiation; prove
  an endpoint dependency only when transporting it beyond the pinned native
  route it already refutes.
- Do not treat eventual cross-tail agreement as construction of NativeData.
- Keep the partition factor when reasoning before its threshold.
- Do not promote a scalar cross defect to a complete-response defect without a
  proved finite-jet coordinate identity.
- Do not claim a joint certificate until the same functional controls the
  reduced defect, full response, and complete admissible tail.

## Development workflow

When adding a source adapter:

1. Pin the upstream declaration and record the relevant manuscript section in
   the module documentation.
2. Preserve the source statement exactly before deriving a simplified helper.
3. State whether the result transports the completed NativeData obstruction,
   closes the reduced or full-compatible route, instantiates the joint
   certificate, or advances the preferred NativeData-driven joint instantiation.
4. Keep finite-prefix factors, inverse losses, reconstructed pressure, and
   nonlinear tail terms visible until a theorem removes them.
5. Export only stable route-level declarations through
   `SignedMeanInterface.lean`.
6. Validate the focused module, then both the CounterProof subsystem and the
   complete Navier–Stokes library.

Useful commands are:

```text
lake build NavierStokes.CounterProof.Adapter.NativeDataObstruction
lake build NavierStokes.CounterProof
lake build NavierStokes
```

Compilation is the proof gate. Adapter modules must not contain `sorry` or
`admit`.

## Manuscript map

Every Lean module records its manuscript correspondence. The primary locations
are §3.2–§3.4 and Theorem 4.1 / Proposition 4.2 for exact state and response,
Theorem 5.1 / Proposition 5.2 for compatibility and branch defect, Theorem 6.1
/ Proposition 6.2 / Corollary 6.3 for dual and tail estimates, and §8 Phases
I–VII for source instantiation in
[`Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`](../../../docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex).
The terminal residual bridge also uses Proposition 8.2 and Corollary 8.3 of
[`Primitive_Liftability_Obstructions_NSE_Research_Note.tex`](../../../docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex).
