# Linglib

[![CI](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml/badge.svg)](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.31.0-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib-v4.31.0-blueviolet)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache%202.0-green)](LICENSE)

A Lean 4 library for formal linguistics — semantics, syntax, pragmatics, morphology, phonology, and processing.

> ⚠️ This is an experiment in "AI for Linguistics" using recent advances in proof assistants. Spotted an inaccuracy? [Open an issue](https://github.com/hawkrobe/linglib/issues) — we'd love to hear about it.

## Why

Decades of progress in formal linguistics live in prose scattered across hundreds of papers. Linglib is an attempt to gather the machinery in one place so a proof assistant can do the bookkeeping:

- **Detect breakage.** If you change your semantics for attitude verbs, Lean tells you exactly which downstream theorems about conditionals, questions, or pragmatic inference no longer follow. No more discovering an inconsistency from a reviewer.

- **Check predictions.** Theories are often stated in notation ambiguous enough to hide gaps between what is claimed and what actually follows from the definitions. Lean won't let a proof go through unless the prediction genuinely follows from the theory.

- **Compare theories.** When two theories both claim to handle the same data, we can formally characterize where they agree and where they diverge rather than arguing past each other with different formalisms.

## How It's Organized

Linglib is built in layers, each grounded in the one below it by `import` rather than restated independently:

- **`Core/`, `Features/`** — framework-agnostic infrastructure: propositions, intensions, accessibility relations, scales, and per-entry feature taxonomies.
- **Theory layer** (`Semantics/`, `Syntax/`, `Pragmatics/`, `Morphology/`, `Phonology/`, `Processing/`, `Discourse/`) — reusable formal theories that make predictions.
- **`Typology/`, `Data/`** — per-language typological substrate and theory-neutral empirical data (per-paper example sets, pooled cross-paper datasets). `Data/` imports no theories.
- **`Fragments/`** — lexical entries for ~100 languages, typed by the theory layer.
- **`Studies/`** — paper-anchored studies, the test suite: each file formalizes a paper and proves its predictions against the data.

The connection between data and theory is explicit: studies prove theorems that reference the empirical rows, so changing a theory surfaces exactly which downstream predictions no longer follow.

## Building

```bash
lake exe cache get  # Get mathlib cache
lake build
```

## Using Linglib in your own Lake project

Linglib pins a specific toolchain (currently **Lean v4.31.0 / mathlib v4.31.0**), so your project's `lean-toolchain` must match. Add to your `lakefile.lean`:

```lean
require linglib from git
  "https://github.com/hawkrobe/linglib" @ "v4.31.0"
```

(Use `@ "main"` to track the latest development instead of the pinned release.)

Then `import Linglib` — or, more selectively, e.g. `import Linglib.Pragmatics.RSA.Basic`.

## Links

- **Project site & API docs:** [linglib.io](https://linglib.io/) — also hosts the blog, an interactive dependency map, and the bibliography.
- **Contributing:** see [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Apache 2.0 — see [LICENSE](LICENSE).
