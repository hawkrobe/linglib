# Linglib

[![CI](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml/badge.svg)](https://github.com/hawkrobe/linglib/actions/workflows/ci.yml)

Linglib is a Lean 4 library for formal linguistics, covering semantics, pragmatics, and their interfaces. The goal is to state linguistic theories precisely enough that a proof assistant can check whether they actually predict the phenomena they claim to explain.

## Organizing Principle

Linglib separates **theory-neutral phenomena** from **theories that explain them**:

```
Phenomena/           — What we observe (acceptability judgments, experimental data, ...)
Theories/            — Formal theories that make predictions about phenomena
```

**Phenomena/** contains empirical facts with no theoretical commitments. Each file records what native speakers judge, what experiments measured, or what distributional patterns exist. For example, `Phenomena/Modality/Data.lean` records that *"John must be home"* is judged true in certain scenarios — without committing to Kratzer's framework or any alternative.

**Theories/** contains formal semantic and pragmatic theories. Each theory defines its own types, operations, and evaluation functions, then proves theorems connecting those definitions to phenomena. For example, `Theories/IntensionalSemantics/Modal/Kratzer.lean` defines conversational backgrounds and ordering sources, and proves that Kratzer's semantics predicts the judgments recorded in `Phenomena/Modality/`.

The payoff: when two theories (say Kratzer modals vs. simple Kripke modals) both claim to handle the same data, we can formally compare their predictions — proving equivalence, identifying divergence, or characterizing the boundary.

### Directory Overview

```
Linglib/
├── Core/                     — Shared infrastructure (no theoretical commitments)
│   ├── Proposition.lean      — BProp (W → Bool), classical Prop' (W → Prop)
│   ├── Intension.lean        — Intension W τ, rigid designators
│   ├── ModalLogic.lean       — Kripke frames, accessibility relations
│   ├── Conjectures.lean      — Open conjectures (stated, not asserted)
│   └── ...                   — Distributions, scales, duality, QUD
│
├── Phenomena/                — Theory-neutral empirical data
│   ├── Modality/             — Modal judgment data
│   ├── ScalarImplicatures/   — SI rates, task effects
│   ├── Imprecision/          — Homogeneity, non-maximality, numeral imprecision
│   └── ...                   — 50+ files of empirical observations
│
├── Theories/
│   ├── TruthConditional/     — Extensional semantics (Montague-style)
│   │   ├── Basic.lean        — Types, composition, truth conditions
│   │   ├── Determiner/       — Quantifiers, numerals
│   │   └── Sentence/         — Entailment, focus, presupposition
│   │
│   ├── IntensionalSemantics/ — Possible-worlds semantics
│   │   ├── Modal/            — Kratzer vs simple modals
│   │   ├── Attitude/         — Believe, know, hope, fear
│   │   ├── Conditional/      — Counterfactuals, causal models
│   │   └── Causative/        — Cause, let, make
│   │
│   ├── QuestionSemantics/    — Hamblin, partition, inquisitive semantics
│   │
│   ├── RSA/                  — Rational Speech Acts (pragmatics)
│   │   ├── Core/             — L0, S1, L1 definitions
│   │   └── Implementations/  — 14 paper replications
│   │
│   ├── NeoGricean/           — Categorical implicature theory
│   ├── CCG/                  — Combinatory Categorial Grammar
│   ├── HPSG/                 — Head-Driven Phrase Structure Grammar
│   ├── Minimalism/           — Minimalist Program
│   └── DependencyGrammar/    — Word Grammar
│
├── Fragments/                — Reusable lexical fragments (English, Dutch, Mandarin, ...)
│
└── Comparisons/              — Cross-theory comparisons
```

### Conventions

- **`sorry`** marks a theorem we believe is true but haven't fully proved yet. The statement is intended to be correct.
- **`Core/Conjectures.lean`** contains `def : Prop` statements for open conjectures — things that *might or might not* be true. These don't introduce axioms or unsoundness.
- **Phenomena files never import Theories.** They are strictly theory-neutral.
- **Theories prove grounding theorems** connecting their definitions to `Core/` types and `Phenomena/` data.

## API Documentation

[https://hawkrobe.github.io/linglib/](https://hawkrobe.github.io/linglib/)

## Building

```bash
lake exe cache get  # Get mathlib cache
lake build
```

## License

Apache 2.0
