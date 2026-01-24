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

### Three-Layer Design

1. **Syntax Layer** (`LingLean/Syntax/`)
   - `Basic.lean`: Shared types (`Cat`, `ClauseType`, `Word`, `Lexicon`)
   - `Grammar.lean`: Abstract `Grammar` typeclass that all frameworks implement
   - `HPSG/`: Head-Driven Phrase Structure Grammar (constraint-based, feature structures)
   - `Minimalism/`: Minimalist Program (derivational, Merge + Move operations)

2. **Semantics Layer** (`LingLean/Semantics/`)
   - `Basic.lean`: Semantic types (`Model`, `SemType`)
   - `Backend.lean`: `SemanticBackend` typeclass defining the interface RSA needs (Utterance, World, φ function)

3. **Phenomena Layer** (`LingLean/Phenomena/`)
   - `Basic.lean`: `MinimalPair`, `PhenomenonData` - data structures for empirical generalizations
   - `SubjectAuxInversion/`: Case study with both HPSG and Minimalist analyses

### Key Abstractions

- **Grammar typeclass**: Defines `Derivation`, `realizes`, and `derives` - any syntactic framework must implement this
- **CapturesInversion typeclass**: Framework-neutral spec that a grammar correctly handles subject-aux inversion
- **SemanticBackend typeclass**: What pragmatics needs from syntax - utterances, worlds, and agreement function φ

### Design Pattern

Phenomena are specified as minimal pairs (grammatical/ungrammatical sentence lists with clause types). Multiple frameworks (HPSG, Minimalism) implement analyses. Proofs show each framework captures the phenomenon. This enables comparing frameworks on the same empirical data.

## Lean Conventions

- `autoImplicit` is disabled (explicit type parameters required)
- `pp.unicode.fun` is enabled for pretty printing
- No external dependencies beyond Lean 4 standard library
