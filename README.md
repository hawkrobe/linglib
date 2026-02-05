# Linglib

[![CI](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml/badge.svg)](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml)

A Lean 4 library for formal linguistics. The goal is to state linguistic theories precisely enough that a proof assistant can check whether they actually predict the phenomena they claim to explain.

## How It's Organized

Linglib separates **phenomena** (what we observe) from **theories** (what explains it).

`Phenomena/` contains theory-neutral empirical data — acceptability judgments, experimental results, distributional patterns. For example, `Phenomena/Modality/` records that *"John must be home"* is judged true in certain scenarios, without committing to any particular theory of modals.

`Theories/` contains formal theories that make predictions about those phenomena. For example, `Theories/IntensionalSemantics/Modal/Kratzer.lean` formalizes Kratzer's conversational backgrounds and proves they predict the judgments in `Phenomena/Modality/`.

The payoff: when two theories both claim to handle the same data, we can formally compare their predictions — proving equivalence, identifying divergence, or characterizing the exact boundary between them.

Other top-level directories: `Core/` (shared infrastructure), `Fragments/` (lexical data for specific languages), `Comparisons/` (cross-theory comparisons). See `CLAUDE.md` for the full directory tree.

## Building

```bash
lake exe cache get  # Get mathlib cache
lake build
```

## Docs

[https://hawkrobe.github.io/linglib/](https://hawkrobe.github.io/linglib/)

## License

Apache 2.0
