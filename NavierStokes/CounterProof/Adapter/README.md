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
the source attachment follows four stages:

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
cycle. Phase II required tracing the reduced cross response to its source
construction, and Phase IV required identifying the theorem that supplied its
weighted gain. Both generic theorem paths converged on the same `NativeData`
premise. Comparing that premise’s normalized `tail_bound` with the actual strip
then exposed the exact `q > 1/2` versus `q ≤ 1/2` contradiction.

The subsequent audit found that the actual cycle replaced this premise for one
cross-cancellation obligation with a physical partition identity. That
discovery did not erase the contradiction; it created a second audit
obligation: determine exactly which NativeData
consequences the replacement reconstructs. The directory split reflects this
proof history and keeps future work from collapsing package existence,
cross-tail cancellation, and complete reconstructed compatibility into one
assertion.

## Counter-proof route map

The Adapter exposes four usable routes organized into three families: the
standalone NativeData dependency obstruction; the independently closable
reduced and full-compatible branches; and their stronger same-witness
unification. They share source objects, but their hypotheses and conclusions
must remain distinct.

### NativeData dependency obstruction

The generic and band-reindexed signed mean-gain theorems both require
`SignedMeanGain.NativeData ActualInitialization.geometry`. The
[`NativeDataObstruction/`](NativeDataObstruction/) subsystem proves that no such
value exists: `NativeData.tail_bound` forces the normalized strip coordinate
to be at most `1/2`, whereas every point in the actual strip has coordinate
strictly greater than `1/2`.

This is a genuine alternative counter-proof route. If a claimed endpoint
entails existence of the complete native package, then
`ClaimRequiresNativeData.refutes_claim` disproves that endpoint immediately.
It does not require a reduced/full branch comparison, a dual functional, or a
`JointCokernelCertificate`.

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
are discharged.

### Unified same-witness route

`JointCokernelCertificate` strengthens the two compatibility branches by using
one observed direction for both conclusions. The direction is a vector in the
Hilbert observation space; inner product with that vector induces a bounded
scalar functional. The functional nearly annihilates admissible full responses
while detecting the target or defect. The Adapter does not yet instantiate that
certificate. It preserves the exact source data needed to do so without
pretending that separately constructed functionals are already equal.

The NativeData route can feed this unified route without being reduced to it.
The physical replacement has the exact finite-prefix defect

`cross − request = −missingWeight × request`.

`NativeDataObstruction/CertificateFeedback.lean` turns a proved nonzero defect
and a matching finite-jet coordinate into a `ReducedDefectWitness`. If that
same coordinate also satisfies the full-response near-cokernel and complete
tail-capacity bounds, it can become the shared functional of a
`JointCokernelCertificate`. Failure to complete that promotion does not weaken
the independent NativeData dependency obstruction.

## Route-selection criteria

Start with the smallest route that reaches a pinned claimed endpoint:

- Use the NativeData route when the endpoint entails the complete normalized
  native package. Prove that dependency explicitly, then apply package
  nonexistence.
- Use the reduced route when an actual reconstructed mismatch can be detected
  and shown to survive every admissible future correction.
- Use the full-compatible route when the target component is larger than the
  total response capacity, even if no reduced branch has been selected.
- Use the joint route only when one functional supports the reduced defect,
  near-cokernel response estimate, and complete-tail bound simultaneously.

These are not maturity levels of one proof. They are distinct logical routes.
A direct source-interface contradiction may be both simpler and stronger than
a quantitative joint certificate for the endpoint that depends on that source
interface.

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
working specifically on the alternative NativeData route.

## Proof discipline

Keep these distinctions explicit in new work:

- Prove an endpoint's dependency on NativeData before using package
  nonexistence to refute that endpoint.
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
3. State whether the result belongs to the NativeData, reduced, full-compatible,
   or joint route.
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
