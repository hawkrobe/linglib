# Changelog

## [0.2.0] - 2025-01-24

### Added
- **Mathlib integration**: Use `Set` for predicate extensions with proper set lemmas (`Set.mem_setOf_eq`, `Set.mem_singleton_iff`)
- **Montague/Attitudes.lean**: Propositional attitudes (believe, know, want) with accessibility relations
- **Montague/Modality.lean**: Possible worlds semantics, necessity/possibility operators
- **Montague/Derivations.lean**: Proofs that Montague predicts correct truth conditions
- **Montague/SyntaxInterface.lean**: Documents what Montague requires from syntax vs is agnostic to
- **Montague/SemanticBackendInstance.lean**: Shows Montague implementing RSA's SemanticBackend interface
- **Phenomena/Semantics/TruthConditions.lean**: Theory-neutral empirical truth judgments
- **CCG/Semantics.lean**: Type preservation theorems, homomorphism principle (compositionality)
- **docs/MATHLIB_INTEGRATION.md**: Documents Mathlib usage and design decisions

### Changed
- Moved `Theories/Semantics/{Entailment,Numbers,Scales}.lean` under `Theories/Montague/`
- `Basic.lean` now uses Mathlib's `Set` for characteristic function correspondence
- Keep custom `FiniteModel` class (not Mathlib's `Fintype`) for `#eval` computability

### Design Decisions
- **Phenomena vs Theories**: Phenomena contain only empirical data; proofs stay in Theories
- **Horn Sets not Scales**: Following Geurts (2010), use sets where ordering is derivable from semantics
- **Sentence-level strength**: Alternatives are stronger sentences, not words (handles DE environments)

## [0.1.0] - 2025-01-23

### Added
- Core infrastructure: `Frac`, `Word`, basic types
- **Theories**: CCG, HPSG, Minimalism syntax; Montague semantics; NeoGricean pragmatics; RSA
- **Phenomena**: CCG coordination, Geurts (2010) quantity implicatures
- SemanticBackend interface connecting syntax to pragmatics
