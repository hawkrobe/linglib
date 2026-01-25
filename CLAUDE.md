# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
lake build          # Build the entire project
lake build Linglib # Build just the main library
```

## Project Overview

Linglib is a Lean 4 library for formalizing syntactic theories from theoretical linguistics and connecting them to computational pragmatics (RSA - Rational Speech Acts).

## Architecture

### Pipeline: Dependency-Based Theory Composition

The core architectural principle is that **theories are composable components with explicit dependencies**. A theory declares what it provides and what it requires. An analysis is complete when all requirements bottom out.

```
Core/Pipeline.lean
├── TheoryComponent: { provides: [...], requires: [...] }
├── GroundedTheory: components where all requires are satisfied
└── CompleteAnalysis: grounded theory + predictions match data
```

**Key insight**: We don't assume fixed levels (syntax → semantics → pragmatics). Some theories cross boundaries (CCG couples syntax-semantics, DRT couples semantics-discourse). The architecture only requires that the dependency graph bottoms out.

Example:
```
RSA                          Montague.Scope
├─ requires: meaning         ├─ requires: {}  ← bottoms out
├─ provides: probDist        └─ provides: meaning
└────────────────────────────────────┘
         requirement satisfied!
```

### Core/ - Shared Types and Interfaces

- `Basic.lean`: Shared types (`Cat`, `ClauseType`, `Word`, `Lexicon`)
- `Grammar.lean`: Abstract `Grammar` typeclass that all frameworks implement
- `SemanticTypes.lean`: Basic semantic types
- `SemanticBackend.lean`: Interface pragmatics needs from semantics (Utterance, World, φ function)
- `RSA.lean`: RSA infrastructure (`FiniteSemanticBackend`, `ParametricSemanticBackend`)
- `Pipeline.lean`: Theory composition architecture (provides/requires model)
- `Frac.lean`: Exact rational arithmetic for RSA probabilities

### Theories/ - Theoretical Frameworks

All syntactic/semantic/pragmatic frameworks. Each theory should declare what it provides and requires:

| Theory | Provides | Requires | Status |
|--------|----------|----------|--------|
| `CCG/` | Derivations, categories | Lexicon | Partial |
| `HPSG/` | Feature structures | - | Partial |
| `Minimalism/` | SynObj trees, Merge/Move | - | Partial |
| `DependencyGrammar/` | Dependency structures | - | Partial |
| `Montague/` | Truth conditions, φ function | Derivations | Working |
| `NeoGricean/` | Implicatures, SI derivation | SemDeriv, Entailment | Working (toy) |
| `RSA/` | Probability distributions | SemanticBackend | Working (toy) |

Each theory directory contains:
- `Basic.lean`: Core machinery for that framework
- `{Phenomenon}.lean`: Theory's coverage of specific phenomena

### Phenomena/ - Empirical Data (Theory-Independent)

**Pure empirical facts only** - no semantic content, no theoretical commitments:

- `Basic.lean`: `MinimalPair`, `PhenomenonData` data structures
- `{Study}/Data.lean`: Experimental results (percentages, judgments)
- `ScalarImplicatures/Data.lean`: SI patterns and examples
- `GeurtsPouscoulous2009/Data.lean`: Task effect experimental data
- `ScontrasPearl2021/Data.lean`: Scope ambiguity truth-value judgments

**Anti-pattern**: Don't put semantic content (truth conditions, entailment) in Phenomena/. That belongs in Theories/Montague/.

### Key Interfaces

| Interface | Purpose | Implemented By |
|-----------|---------|----------------|
| `Grammar` | Derivation, realizes, derives | CCG, HPSG, Minimalism, DG |
| `SemanticBackend` | Utterance, World, φ | Montague |
| `ParametricSemanticBackend` | + Interp parameter for ambiguity | RSA.ScontrasPearl2021 |
| `ImplicatureTheory` | SI derivation, comparison | NeoGricean, RSA |
| `CoreferenceTheory` | Binding, command relations | HPSG, Minimalism, DG |

### Grounding: RSA ← Montague Connection

RSA's meaning function should be **derived from compositional semantics**, not stipulated:

```lean
-- In RSA/ScontrasPearl2021.lean
def everyHorseDidntJump_parametric : WorldParametricScopeDerivation Nat :=
  { meaningAt := λ scope w => ...  -- compositional semantics
  , worlds := [0, 1, 2] }

def scopeMeaning := meaningFromDerivation everyHorseDidntJump_parametric
-- RSA uses compositional meaning, doesn't stipulate its own

theorem rsa_meaning_from_montague :
    scopeMeaning = everyHorseDidntJump_parametric.meaningAt := ...
```

### Theory-Phenomena Architecture

```
Phenomena/Study/Data.lean          -- Pure empirical data (numbers, observations)
    ↑ imports
Theories/Framework/Predictions.lean -- Derives predictions, proves they match data
```

**Phenomena files contain:**
- Raw experimental results (percentages, counts)
- Data structures for observations
- Theorems about the data itself
- NO theory-specific predictions or semantic content

**Theory files contain:**
- Parameters characterizing theory variants
- Functions deriving predictions
- Theorems proving predictions match data
- Grounding proofs (e.g., meaning comes from compositional semantics)

### Known Architectural Issues (v0.5)

1. **Syntax → Semantics gap**: No syntax theory implements `MontagueSyntax` interface yet
2. **Entailment ungrounded**: NeoGricean's entailment checker is hardcoded, not proven to match Montague
3. **RSA incomplete**: Missing full L₁ computation and prior P(w)
4. **Toy models only**: Most theories work on small fixed domains, not general English

## Lean Conventions

- `autoImplicit` is disabled (explicit type parameters required)
- `pp.unicode.fun` is enabled for pretty printing
- No external dependencies beyond Lean 4 standard library + Mathlib
- `Core/Frac.lean`: Minimal exact rational arithmetic (cross-multiply for comparison)

## References

- Gibson (2025) "Syntax", MIT Press
- Hudson (1984, 1990) "Word Grammar" / "English Word Grammar"
- Pollard & Sag (1994) "Head-Driven Phrase Structure Grammar"
- Chomsky (1995) "The Minimalist Program"
- Frank & Goodman (2012) "Predicting Pragmatic Reasoning in Language Games"
- Goodman & Frank (2016) "Pragmatic Language Interpretation as Probabilistic Inference"
- Scontras & Pearl (2021) "When pragmatics matters more for truth-value judgments"
