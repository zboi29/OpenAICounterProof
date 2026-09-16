# Primitive compatibility counter-proof for the Navier–Stokes construction

[![CounterProof Lean pass rate](https://github.com/zboi29/OpenAICounterProof/actions/workflows/counterproof-lean.yml/badge.svg?branch=main&event=push)](https://github.com/zboi29/OpenAICounterProof/actions/workflows/counterproof-lean.yml?query=branch%3Amain)
[![NavierStokes + Comparator Lean pass rate](https://github.com/zboi29/OpenAICounterProof/actions/workflows/navier-stokes-comparator-lean.yml/badge.svg?branch=main&event=push)](https://github.com/zboi29/OpenAICounterProof/actions/workflows/navier-stokes-comparator-lean.yml?query=branch%3Amain)

These badges are independent, all-or-nothing Lean compilation pass rates:

- **CounterProof Lean** is 100% only when
  `lake build NavierStokes.CounterProof` succeeds for the focused
  `NavierStokes/CounterProof/` import closure.
- **NavierStokes + Comparator Lean** is 100% only when
  `lake build NavierStokes ComparatorChallenges` succeeds for the complete
  `NavierStokes/` and `ComparatorChallenges/` libraries. It intentionally
  excludes the `Euler/` library as a top-level build target.

This repository is a fork of
[OpenAI's `NavierStokesAndEuler` Lean formalization](https://github.com/openai/NavierStokesAndEuler),
released with its proposed three-dimensional Navier–Stokes and Euler blowup
proofs. The fork retains the upstream development as the object of a
source-grounded counter-proof program.

The counter-proof targets a **primitive compatibility/liftability obstruction**:
a reduced correction branch can remain smooth and algebraically coherent while
failing to lift to the complete constrained physical state, or while requiring
uncontrolled inverse amplification, holonomy, or derivative loss. This is not a
claim of a basic algebraic, normalization, or omitted-term error. A decisive
counter-proof must instantiate the obstruction on the actual Lean objects,
control the complete future correction tail, and contradict the claimed flat
physical residual, terminal regularity, or smooth force extension.

The research program and its Lean targets are developed in:

- [`docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex`](docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex)
- [`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`](docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex),
  the revised Version 1.1 downstream companion to the preceding primitive-
  liftability research note. Its crucial upgrade is a preferred same-witness
  joint obstruction: one dual direction simultaneously certifies that the
  reduced defect survives the complete admissible tail and that the full-
  compatible target exceeds total tail capacity. Each branch remains an
  independently decisive counter-proof route
- [`docs/Joseph_2026_Primitive_Compatibility_Counterproof_References_v1.bib`](docs/Joseph_2026_Primitive_Compatibility_Counterproof_References_v1.bib)

The notes define a counter-proof program and explicit closure criteria; they do
not treat a nonzero intermediate defect alone as a completed disproof. Version
1.1 makes the joint certificate the strengthened target without requiring both
branches when one already closes against an exact upstream endpoint.

## Upstream sources

- [Read the blog post](https://openai.com/index/navier-stokes-solution/)
- [Read the Navier-Stokes paper](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
- [Read the Euler paper](https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf)

## Upstream Navier–Stokes claim

For every positive viscosity, the upstream formalization claims two results:

- **Whole space $\mathbb{R}^3$:** There exist smooth initial data and forcing for
  which no global smooth solution with uniformly bounded kinetic energy exists.
- **Periodic torus $\mathbb{R}^3/\mathbb{Z}^3$:** There exist smooth periodic
  initial data and forcing for which no global smooth solution exists.

These are alternatives [**(C)**](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf#page=2) “Breakdown of Navier–Stokes solutions on ℝ³”
and [**(D)**](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf#page=2) “Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³”
in the Clay Mathematics Institute’s [official problem description](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf)
of the [Navier–Stokes existence and smoothness](https://www.claymath.org/millennium/navier-stokes-equation/)
[Millennium Prize Problem](https://www.claymath.org/millennium-problems/).

## Upstream Euler claim

The upstream formalization constructs smooth, compactly supported,
divergence-free initial velocity on
$\mathbb{R}^3$ whose solution to the unforced incompressible Euler equations
develops a singularity in finite time. The velocity’s $C^1$ norm becomes unbounded
near that time, and the time integral of the vorticity’s $L^\infty$ norm diverges.

## Building the formalizations

The project uses Lean 4.34.0-rc2, Mathlib, and Lake. With
[elan](https://github.com/leanprover/elan) installed, fetch the mathlib cache and build the formalizations with:

```sh
lake exe cache get
lake build NavierStokes ComparatorChallenges
```

## Independent proof checking

For instructions on checking the formalizations with Comparator, see the
[ComparatorChallenges README](ComparatorChallenges/README.md).

## Future Euler counter-proof

After the Navier–Stokes primitive-obstruction program, this project intends to
develop a separate, source-grounded counter-proof program targeting the upstream
Euler formalization. It will follow substantially the same methodology and
mathematical structure as the three-dimensional Navier–Stokes counter-proof—in
particular, auditing primitive compatibility, liftability, correction tails, and
terminal physical claims—while using localized obstructions, interfaces, and
formal theorem targets specific to the Euler construction.
