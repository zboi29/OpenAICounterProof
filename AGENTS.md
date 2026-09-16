# Repository Guidelines

## Project Scope & Structure

This fork uses OpenAI's `NavierStokesAndEuler` formalization as the audit target for a Lean counter-proof of primitive compatibility/liftability. It is not a routine algebraic, normalization, projection, or omitted-term critique. A defect counts only if it survives the correction tail and contradicts an exact upstream endpoint such as residual flatness or smooth force extension.

`NavierStokes.lean` and `Euler.lean` are entry points; modules live in matching directories, with whole-space work under `NavierStokes/R3/`. `NavierStokes/CounterProof/` separates liftability, reconstruction, and certificate modules into matching subdirectories while retaining shared interfaces at its root. `ComparatorChallenges/` holds independent checks. Keep paths, namespaces, and imports aligned.

## Counter-Proof Sources

Read and exploit these sources before formalizing the counter-proof program:

- [`docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex`](docs/Primitive_Liftability_Obstructions_NSE_Research_Note.tex) defines the range, lift-cost, curvature, endpoint, and residual-leakage framework.
- [`docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex`](docs/Joseph_2026_Primitive_Compatibility_Counterproof_Signed_Mean_Update_Companion_Note_v1_1.tex) is the revised Version 1.1 downstream companion to the general research note. It strengthens the signed-mean program with a preferred same-witness joint obstruction: one dual direction should both preserve the reduced-branch defect through the complete admissible tail and place the full-compatible target beyond total tail capacity. Either branch remains independently decisive.
- [`docs/Joseph_2026_Primitive_Compatibility_Counterproof_References_v1.bib`](docs/Joseph_2026_Primitive_Compatibility_Counterproof_References_v1.bib) records the analytical and formal references.

Anchor proofs to pinned definitions. Prefer Version 1.1's joint certificate when the source estimates support it, while retaining either independently closed branch. Use full-response, complete-tail, and residual-exposure targets rather than surrogates.

## Build, Test, and Development Commands

- `lake exe cache get` downloads cached mathlib artifacts.
- `lake build` compiles all default targets: `NavierStokes`, `Euler`, and `ComparatorChallenges`.
- `lake build Euler` checks one library during focused work.
- `lake env lean Euler/Solution.lean` elaborates a single file.
- `lake exe comparator ComparatorChallenges/Euler.json` runs the independent check; use the analogous Navier–Stokes configuration. It requires `landrun`, `lean4export`, and `nanoda_bin`.

## Coding Style & Naming Conventions

Follow Lean/mathlib style: two-space indentation, focused imports, and short public doc comments. Use `UpperCamelCase.lean` filenames, matching namespaces, and descriptive declarations. Keep assumptions explicit; Euler treats warnings as errors. Match neighboring code.

## Mathematical Communication

When communicating with users, write rigorous mathematics in explicit plain-print form. Do not use LaTeX commands, LaTeX delimiters, or MathJax by default. Use applicable Unicode notation generously—such as ∀, ∃, →, ↔, ∈, ∉, ≤, ≥, Σ, and ∘—while defining symbols and keeping expressions readable in a linear text layout. Use LaTeX only when the user explicitly requests it or when the task or deliverable inherently requires LaTeX, such as editing a `.tex` source.

## Testing Guidelines

Compilation is the test gate. Build the affected library, then run `lake build`. Do not add `sorry` or `admit` to proof modules; placeholders in `ComparatorChallenges/*.lean` are intentional. Run Comparator when changing exported adapters or challenge definitions.

## Commit & Pull Request Guidelines

Use scoped prefix notation, for example `feat(optimization, leray-hopf): optimize energy estimate`, with prefixes such as `feat`, `fix`, `refactor`, `docs`, or `chore`.

Write the commit body as bullet points describing changes and affected declarations. End it with a `Validation:` subsection containing bullet-pointed Lean commands and results:

```text
feat(optimization, leray-hopf): optimize energy estimate

- Simplify the dissipation-bound argument.
- Preserve the exported theorem statement.

Validation:
- `lake env lean NavierStokes/R3/H3Energy.lean` — passed
- `lake build NavierStokes` — passed
```

Pull requests should summarize and link the mathematical target, flag axiom or dependency changes, and reproduce validation results.
