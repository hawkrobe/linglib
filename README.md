# Linglib

[![CI](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml/badge.svg)](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml)

A Lean 4 library for formal linguistics.

## Why

Formal linguistics has a dependency problem. Theories of modality rely on theories of propositions, which rely on theories of quantification, which rely on theories of types. A change anywhere can silently break things downstream — but the field tracks these dependencies informally, in prose scattered across hundreds of papers.

Linglib puts the theories in one place so a proof assistant can do the bookkeeping:

- **Detect breakage.** If you change your semantics for attitude verbs, Lean tells you exactly which downstream theorems about conditionals, questions, or pragmatic inference no longer follow. No more discovering an inconsistency from a reviewer.

- **Check predictions.** Theories are often stated in notation ambiguous enough to hide gaps between what is claimed and what actually follows from the definitions. Lean won't let a proof go through unless the prediction genuinely follows from the theory.

- **Compare theories.** When two theories (RSA vs. exhaustification, Kratzer vs. Kripke modals) both claim to handle the same data, we can formally characterize where they agree and where they diverge — rather than arguing past each other with different formalisms.

## How It's Organized

Linglib separates **phenomena** (what we observe) from **theories** (what explains it).

`Phenomena/` contains theory-neutral empirical data — acceptability judgments, experimental results, distributional patterns. `Theories/` contains formal theories that make predictions about those phenomena. The connection between them is explicit: theories prove theorems that reference the data.

Other top-level directories: `Core/` (shared infrastructure like propositions, intensions, accessibility relations), `Fragments/` (lexical data for specific languages), `Comparisons/` (cross-theory results).

## Building

```bash
lake exe cache get  # Get mathlib cache
lake build
```

## Docs

[https://hawkrobe.github.io/linglib/](https://hawkrobe.github.io/linglib/)

## License

Apache 2.0
