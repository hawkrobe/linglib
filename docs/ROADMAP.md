# Linglib Roadmap

This document tracks architectural improvements and technical debt to address in future work.

## High Priority

### 1. Intensional Montague Semantics

**Current state**: Montague meanings are extensional - evaluated in a fixed model, producing values like `Bool`.

**Problem**: RSA needs `meaning : World → Bool` to compute L0. Currently the RSA bridge is shallow - it pattern-matches on scalar items and returns pre-computed results rather than actually evaluating Montague meanings in RSA worlds.

**Solution**: Add an intensional layer where meanings are functions from worlds to extensions:

```lean
-- Current (extensional)
meaning : m.interpTy .t  -- just Bool

-- Desired (intensional)
meaning : World → Bool   -- varies with world
```

**Implementation path**:
1. Add `Montague/Intensional.lean` with world-parameterized types
2. Phenomena scenarios provide world structure + lexical interpretations
3. RSA's L0 evaluates the intensional meaning: `L0(u, w) = ⟦u⟧(w)`

**Files affected**: `Montague/Basic.lean`, `Montague/SemDerivation.lean`, `RSA/*.lean`

---

### 2. Type-Safe Scale Positions

**Current state**: Implicatures use string matching: `hasImplicature results "all"`

**Problem**: Fragile - renaming breaks silently, no compile-time checking.

**Solution**: Use the `QuantExpr` / `ConnExpr` types from `Montague/Scales.lean`:

```lean
-- Current
hasImplicature results "all"

-- Desired
hasImplicature results .all  -- type-checked!
```

**Files affected**: `NeoGricean/ScalarImplicatures.lean`, `RSA/ScalarImplicatures.lean`

---

### 3. Parameterized Lexicon for Competing Analyses

**Current state**: `Montague/Numbers.lean` has lower-bound semantics. Exact semantics proofs are scattered.

**Problem**: No clean way to compare competing semantic proposals (lower-bound vs exact numerals, Kratzer vs simple modals).

**Solution**: Parameterized lexicon structure:

```
Montague/Lexicon/
├── Numerals/
│   ├── LowerBound.lean   -- "two" means ≥2
│   └── Exact.lean        -- "two" means =2
├── Modals/
│   ├── Kratzer.lean      -- ordering source + modal base
│   └── Simple.lean       -- accessible worlds
└── Quantifiers/...
```

Each variant defines:
- Denotations
- Empirical predictions
- Which phenomena it handles/fails

**Files affected**: Create new `Lexicon/` structure, refactor `Numbers.lean`

---

## Medium Priority

### 4. CCG Compositional Semantics

**Current state**: `CCG/Interpret.lean` requires meanings to be provided separately - doesn't compute them compositionally.

**Problem**: The type alignment exists (`CCG/Semantics.lean`) but actual meaning computation isn't implemented.

**Solution**: Implement compositional interpretation:
```lean
def interpret : DerivStep → Option (Σ ty, toyModel.interpTy ty)
```

**Files affected**: `CCG/Interpret.lean`, `CCG/Semantics.lean`

---

### 5. Unify Example Derivations

**Current state**: Example derivations (`someStudentsSleep`, etc.) live in `SemDerivation.lean`.

**Problem**: These are used by both NeoGricean and RSA - awkward location.

**Solution**: Create `Examples/ScalarImplicature.lean` or similar with shared test cases.

---

### 6. RSA DE Context Handling

**Current state**: NeoGricean handles DE blocking; RSA doesn't.

**Problem**: The RSA bridge ignores context polarity.

**Solution**: Extend `rsaFromDerivation` to handle DE contexts, or document why RSA's treatment differs.

---

## Lower Priority

### 7. Reorganize Pragmatic Theories

**Current state**: `NeoGricean/` and `RSA/` are top-level under `Theories/`.

**Problem**: Inconsistent with the syntax/semantics/pragmatics layering. Both are pragmatic theories.

**Solution**: Move under `Theories/Pragmatics/`:
```
Theories/Pragmatics/
├── NeoGricean/
├── RSA/
└── Comparison.lean  (currently PragmaticComparison.lean)
```

**Files affected**: All imports of `NeoGricean.*` and `RSA.*` (~20 files)

---

### 8. HPSG/Minimalism → SemDerivation

**Current state**: Only CCG implements the syntax→semantics interface.

**Problem**: Other theories can't feed into pragmatics.

**Solution**: Implement `toDerivation` for HPSG and Minimalism.

---

### 9. Embedded Implicatures

**Current state**: Only simple sentences handled.

**Problem**: "John believes some students passed" has complex implicature patterns.

**Solution**: Extend derivation structure to track embedding; implement Geurts' analysis.

---

### 10. RSA α Parameter

**Current state**: RSA uses fixed rationality.

**Problem**: Can't model gradient speaker optimality / competence.

**Solution**: Parameterize RSA by α; relate to NeoGricean competence assumption.

---

## Architectural Principles

1. **Syntax-agnostic pragmatics**: Pragmatics imports `SemDerivation`, not specific syntax theories
2. **Phenomena-driven**: Empirical data in `Phenomena/`, theory coverage tracked
3. **Competing analyses explicit**: Different semantic proposals in separate files with empirical predictions
4. **Proofs over examples**: Prefer theorems to `#eval` demonstrations

---

## Completed

- [x] Consolidate `ContextPolarity` (was duplicated in SemDeriv and Alternatives)
- [x] Move `Comparison.lean` to `Theories/Pragmatics/`
- [x] End-to-end scalar implicature pipeline (CCG → Montague → NeoGricean/RSA)
- [x] Agreement theorem: both theories derive "not all" from "some"
