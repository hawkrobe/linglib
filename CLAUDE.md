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

### Core/ - Shared Types and Interfaces

Minimal, theory-neutral definitions that all frameworks can extend:

- `Basic.lean`: Shared types (`Cat`, `ClauseType`, `Word`, `Lexicon`)
- `Grammar.lean`: Abstract `Grammar` typeclass that all frameworks implement
- `SemanticTypes.lean`: Basic semantic types
- `SemanticBackend.lean`: Interface RSA needs from syntax (Utterance, World, φ function)

### Theories/ - Theoretical Frameworks

All syntactic/semantic frameworks live here. Theories can extend Core types and implement interfaces:

- `CCG/`: Combinatory Categorial Grammar
- `HPSG/`: Head-Driven Phrase Structure Grammar (constraint-based, feature structures)
- `Minimalism/`: Minimalist Program (derivational, Merge + Move operations)
- `DependencyGrammar/`: Word Grammar (Hudson 1984, 1990) - dependency-based
- `Montague/`: Montague-style compositional semantics
- `NeoGricean/`: Neo-Gricean pragmatics (Geurts 2010) - scalar implicatures, competence, defaultism vs contextualism
- `RSA/`: Rational Speech Acts (computational pragmatics, scalar implicature)
- `Surface/`: Simple constraint-checking grammar for basic phenomena

Each theory directory contains:
- `Basic.lean`: Core machinery for that framework
- `{Phenomenon}.lean`: Theory's coverage of specific phenomena (e.g., `Coordination.lean`, `Inversion.lean`)

### Phenomena/ - Empirical Data (Theory-Independent)

Pure empirical facts with citations, no theoretical commitments:

- `Basic.lean`: `MinimalPair`, `PhenomenonData` - data structures for empirical generalizations
- `EmpiricalData.lean`: Data types, linking functions
- `SubjectAuxInversion/Data.lean`: Inversion minimal pairs
- `Coordination/Data.lean`: Coordination minimal pairs
- `LongDistanceDependencies/Data.lean`: Wh-questions, relative clauses
- `ScalarImplicature/Data.lean`: Scalar implicature data (some/all, or/and scales)
- `BasicPhenomena/`: Agreement, case, subcategorization, word order, etc.

### Key Abstractions

- **Grammar typeclass**: Defines `Derivation`, `realizes`, and `derives` - any syntactic framework must implement this
- **SemanticBackend typeclass**: What pragmatics needs from syntax - utterances, worlds, and agreement function φ
- **Captures* typeclasses**: Framework-neutral specs that a grammar correctly handles a phenomenon

### Design Pattern

- **Phenomena/X/Data.lean** = empirical facts + citations (theory-neutral)
- **Theories/Y/X.lean** = theory Y's coverage of phenomenon X
- Missing `Theories/Y/X.lean` = conjecture (theory hasn't proven it handles X)

Multiple frameworks can implement analyses for the same empirical data. This enables comparing frameworks on identical data.

### Theory-Phenomena Architecture

**Key principle**: Theories make claims about phenomena by importing the data and proving their predictions match. Phenomena files stay theory-neutral.

```
Phenomena/Study/Data.lean          -- Pure empirical data (numbers, observations)
    ↑ imports
Theories/Framework/Predictions.lean -- Derives predictions, proves they match data
```

**Phenomena files contain:**
- Raw experimental results (percentages, counts)
- Data structures for organizing observations
- Theorems about the data itself (e.g., "rate A > rate B")
- NO theory-specific predictions

**Theory files contain:**
- Parameters that characterize theory variants (e.g., `levinsonParams`, `geurtsParams`)
- Functions that derive predictions from parameters
- Theorems proving predictions match empirical data
- Theorems showing where theory variants make different predictions

**Example** (NeoGricean vs Geurts & Pouscoulous 2009):
```lean
-- In Phenomena/GeurtsPouscoulous2009/Data.lean (just data)
def mainFinding : TaskEffectDatum :=
  { inferenceTaskRate := 62, verificationTaskRate := 34, ... }

-- In Theories/NeoGricean/Basic.lean (theory parameters)
def levinsonParams : NeoGriceanParams :=
  { trigger := .default, predictedNeutralRate := 90, ... }
def geurtsParams : NeoGriceanParams :=
  { trigger := .contextual, predictedNeutralRate := 35, ... }

-- In Theories/NeoGricean/ScalarImplicatures.lean (derived + compared)
theorem data_supports_contextualism_over_defaultism :
    predictsTaskEffect geurtsParams = true ∧
    (geurtsParams.predictedNeutralRate - mainFinding.verificationTaskRate) < 5 ∧
    levinsonParams.predictedNeutralRate - mainFinding.verificationTaskRate > 50 := by
  native_decide
```

This architecture ensures:
1. **Dependencies are explicit** - theory claims are derived from parameters
2. **Inconsistencies are caught** - predictions must actually match data
3. **Theories are comparable** - same data, different predictions
4. **Phenomena are reusable** - multiple theories can import the same data

### Coverage Matrix

```
                    Coordination  Inversion  LongDistance  ScalarImplicature
CCG                      ✓            -           -              -
HPSG                     -            ✓           -              -
Minimalism               -            ✓           -              -
DependencyGrammar        ✓            ✓           ✓              -
Montague                 -            -           -              -
NeoGricean               -            -           -              ✓
RSA                      -            -           -              ✓
```

## Lean Conventions

- `autoImplicit` is disabled (explicit type parameters required)
- `pp.unicode.fun` is enabled for pretty printing
- No external dependencies beyond Lean 4 standard library
- `Core/Frac.lean`: Minimal exact rational arithmetic (cross-multiply for comparison)

## References

- Gibson (2025) "Syntax", MIT Press. https://mitpress.mit.edu/9780262553575/syntax/
- Hudson (1984, 1990) "Word Grammar" / "English Word Grammar"
- Pollard & Sag (1994) "Head-Driven Phrase Structure Grammar"
- Chomsky (1995) "The Minimalist Program"
- Frank & Goodman (2012) "Predicting Pragmatic Reasoning in Language Games"
- Goodman & Frank (2016) "Pragmatic Language Interpretation as Probabilistic Inference"
