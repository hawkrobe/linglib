# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
lake build          # Build the entire project
lake build LingLean # Build just the main library
```

## Project Overview

LingLean is a Lean 4 library for formalizing syntactic theories from theoretical linguistics and connecting them to computational pragmatics (RSA - Rational Speech Acts).

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

### Coverage Matrix

```
                    Coordination  Inversion  LongDistance
CCG                      ✓            -           -
HPSG                     -            ✓           -
Minimalism               -            ✓           -
DependencyGrammar        ✓            ✓           ✓
Montague                 -            -           -
```

## Lean Conventions

- `autoImplicit` is disabled (explicit type parameters required)
- `pp.unicode.fun` is enabled for pretty printing
- No external dependencies beyond Lean 4 standard library

## References

- Gibson (2025) "Syntax", MIT Press. https://mitpress.mit.edu/9780262553575/syntax/
- Hudson (1984, 1990) "Word Grammar" / "English Word Grammar"
- Pollard & Sag (1994) "Head-Driven Phrase Structure Grammar"
- Chomsky (1995) "The Minimalist Program"
