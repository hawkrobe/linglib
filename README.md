# Linglib

[![CI](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml/badge.svg)](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.1-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib-v4.33.1-blueviolet)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-Apache%202.0-green)](LICENSE)

A Lean 4 library for formal linguistics — semantics, syntax, pragmatics, morphology, phonology, and processing.

> ⚠️ Among other things, this repository is an experiment in "AI for Linguistics" using recent advances in proof assistants. If you find any inaccuracies or errors, please [open an issue](https://github.com/hawkrobe/linglib/issues)! 

## Overview

Decades of progress in linguistics live in prose scattered across hundreds of papers. Here are a few benefits of using Lean to formalize in a shared library:

- **Detect breakage.** If you tweak semantics for (say) attitude verbs, Lean can tell you exactly which downstream theorems about conditionals, questions, or pragmatic inference no longer follow. 

- **Check predictions.** Theories are often stated in notation ambiguous enough to hide gaps between what is claimed and what actually follows from the definitions. 

- **Compare theories.** When two theories both claim to handle the same data, we can formally characterize where they agree and where they diverge rather than arguing past each other with different formalisms.

## Building

```bash
lake exe cache get  # Get mathlib cache
lake build
```

## Using Linglib in your own Lake project

Linglib pins a specific toolchain (currently **Lean v4.33.1 / mathlib v4.33.1**), so your project's `lean-toolchain` must match. Add to your `lakefile.lean`:

```lean
require linglib from git
  "https://github.com/hawkrobe/linglib" @ "v4.32.2"
```

(Use `@ "main"` to track the latest development instead of the pinned release.)

Then `import Linglib` — or, more selectively, e.g. `import Linglib.Pragmatics.RSA.Basic`.

## Links

- **Project site & API docs:** [linglib.io](https://linglib.io/) — also hosts the blog, an interactive dependency map, and the bibliography.
- **Contributing:** see [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Apache 2.0 — see [LICENSE](LICENSE).
