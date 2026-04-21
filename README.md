# Linglib

[![CI](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml/badge.svg)](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.29.1-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib-v4.29.1-blueviolet)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache%202.0-green)](LICENSE)

A Lean 4 library for formal linguistics — semantics, syntax, pragmatics, morphology, phonology, and processing — covering ~76 phenomenon categories and ~100 languages, with multiple competing frameworks formalized for the same phenomenon.

> ⚠️ This is an experiment in "AI for Linguistics" using recent advances in proof assistants. Please let us know if you identify any inaccuracies. 

## Why

Decades of progress in formal linguistics live in prose scattered across hundreds of papers. Linglib is an attempt to gather the machinery in one place so a proof assistant can do the bookkeeping:

- **Detect breakage.** If you change your semantics for attitude verbs, Lean tells you exactly which downstream theorems about conditionals, questions, or pragmatic inference no longer follow. No more discovering an inconsistency from a reviewer.

- **Check predictions.** Theories are often stated in notation ambiguous enough to hide gaps between what is claimed and what actually follows from the definitions. Lean won't let a proof go through unless the prediction genuinely follows from the theory.

- **Compare theories.** When two theories both claim to handle the same data, we can formally characterize where they agree and where they diverge rather than arguing past each other with different formalisms.

## How It's Organized

Linglib separates **phenomena** (what we observe) from **theories** (what explains it).

`Phenomena/` contains theory-neutral empirical data — acceptability judgments, experimental results, distributional patterns. `Theories/` contains formal theories that make predictions about those phenomena. The connection between them is explicit: theories prove theorems that reference the data.
 `Core/` has shared infrastructure like propositions, intensions, accessibility relations, `Fragments/` exposes typological and lexical data for specific languages. 

## Building

```bash
lake exe cache get  # Get mathlib cache
lake build
```

## Using Linglib in your own Lake project

Add to your `lakefile.lean`:

```lean
require linglib from git
  "https://github.com/hawkrobe/linglib" @ "main"
```

Then `import Linglib` — or, more selectively, e.g. `import Linglib.Theories.Pragmatics.RSA.Basic`.

## Docs

[https://hawkrobe.github.io/linglib/](https://hawkrobe.github.io/linglib/)

## License

Apache 2.0 — see [LICENSE](LICENSE).
