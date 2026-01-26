# Linglib Roadmap

This document tracks architectural improvements organized by priority phase.

---

## Phase 1: Intensional Grounding (Highest Priority)

**Goal**: Make RSA's L0 actually evaluate compositional Montague semantics.

Currently RSA pattern-matches on scalar items and returns pre-computed results.
The intensional layer enables: `L0(u, w) ∝ δ⟦u⟧(w) · P(w)`

### 1.1 Intensional Montague Semantics ✓ DONE

**Status**: Implemented in `Montague/Intensional.lean`

Provides:
- `IntensionalModel`: Model with explicit World type
- `Intension m τ`: World → Extension(τ)
- `Proposition m`: World → Bool
- `IntensionalDerivation`: Derivation with world-parameterized meaning
- `phi`: RSA's literal semantics function
- Example: `someStudentsSleep_intensional` with proven truth conditions at each world

### 1.2 RSA with Intensional Meanings ✓ DONE

**Status**: Implemented in `RSA/Intensional.lean`

Provides:
- `PropDerivation`: Propositional derivation (type t) for RSA
- `L0_from_derivation`: L0 computed by evaluating Montague meaning
- `S1_from_derivations`, `L1_from_derivations`: Full RSA pipeline
- `IntensionalScenario`: RSA scenario from compositional derivations

Key results verified by #eval:
- L0 for "some": `someNotAll=1/2, all=1/2` (weak "some")
- S1 at "all" world: speaker prefers "every" (2/3) over "some" (1/3)
- L1 for "some": `someNotAll=1/1, all=1/3` → scalar implicature emerges!

### 1.3 Grounding Theorem ✓ DONE

**Status**: Fully proven in `RSA/Intensional.lean`

```lean
theorem l0_uses_compositional_meaning :
    (L0_prob d worlds w ≠ 0) → d.eval w = true

theorem l0_zero_when_false :
    d.eval w = false → L0_prob d worlds w = 0 ∨ w ∉ worlds
```

Proves that L0 only assigns positive probability to worlds where the compositional meaning is true. Uses Mathlib lemmas: `List.find?_map`, `Option.map_eq_some_iff`, `List.find?_some`.

Also provides:
- `l0_some_zero_at_none`: "some" has zero prob at "none" world (proven by rfl)
- `l0_every_zero_at_someNotAll`: "every" has zero prob at "someNotAll" (proven by rfl)
- `scalar_implicature_from_grounded_rsa`: L1 prefers someNotAll over all (native_decide)

---

## Phase 2: Type Safety & Robustness

### 2.1 Type-Safe Scale Positions ✓ DONE

Replaced string matching with typed `QuantExpr`/`ConnExpr` in scale operations.

### 2.2 NeoGricean Entailment → Montague Model ✓ DONE

Unified entailment checking via Montague semantics.

### 2.3 RSA Simplified to ℚ ✓ DONE

**Status**: `Core/RSA.lean` now uses ℚ directly instead of `RSAScore` typeclass.

- Removed `RSAScore` typeclass overhead
- All RSA computation uses exact rational arithmetic
- `L0_zero_when_false` theorem proven using `Rat.mul_zero`, `Rat.div_def`
- Enables Mathlib lemmas directly on RSA computations

### 2.4 Distribution Type (TODO)

**Goal**: Make L0/S1/L1 return typed probability distributions with proofs.

```lean
structure Distribution (X : Type) where
  scores : List (X × ℚ)
  nonneg : ∀ p ∈ scores.map (·.2), p ≥ 0
  sums_to_one : sumScores (scores.map (·.2)) = 1

theorem normalize_valid :
    (∀ p ∈ dist.map (·.2), p ≥ 0) →
    sumScores (dist.map (·.2)) > 0 →
    Distribution.mk (normalize dist) ...
```

This would give compile-time guarantees that RSA outputs are valid distributions.

### 2.5 RSA DE Context Handling

**Current state**: NeoGricean handles DE blocking; RSA doesn't.

**Problem**: RSA model incomplete—can't represent embedded contexts.

**Solution**: Either:
- Extend RSA with compositional alternative generation
- Or document why RSA's treatment differs (QUD-based blocking)

**Files affected**: `RSA/ScalarImplicatures.lean`

---

## Phase 3: Competing Analyses Infrastructure

### 3.1 Parameterized Lexicon Structure ✓ DONE

**Status**: Implemented in `Montague/Lexicon/Numerals/`

```
Montague/Lexicon/Numerals/
├── Theory.lean      -- NumeralTheory structure
├── LowerBound.lean  -- "two" means ≥2 (Horn 1972)
├── Exact.lean       -- "two" means =2
└── Compare.lean     -- Comparison theorems
```

Provides:
- `NumeralTheory` structure with meaning function, derived RSA scenario
- `LowerBound`, `Exact` as concrete theory instances
- Comparison functions: `theoriesAgreeOn`, `divergingWorlds`
- Key theorems: `lowerBound_exact_differ_on_two`, `ambiguity_presence_differs`
- Connection to G&S 2013 empirical adjudication (ambiguity required for cancellation)

**Next**: Apply same pattern to Modals (Kratzer vs Simple)

### 3.2 Embedded Implicatures

**Current state**: Only simple sentences handled.

**Problem**: "John believes some students passed" has complex implicature patterns.

**Solution**: Extend derivation structure to track embedding depth; implement Geurts' globalist vs localist analysis.

---

## Phase 4: Syntax Expansion

### 4.1 Formal Language Theory & CCG Generative Capacity

**Current state**: `ccg_is_mildly_context_sensitive` is just an assertion.

**Problem**: Steedman claims CCG > CFG, but we don't prove it rigorously.

**Solution**: Formalize Chomsky hierarchy and prove CCG's position:

```
Core/FormalLanguageTheory.lean
  - FormalLanguage, ContextFreeLanguage, MildlyContextSensitive
  - Pumping lemma for CFLs
  - Theorem: {aⁿbⁿcⁿdⁿ} is not context-free

Theories/CCG/GenerativeCapacity.lean
  - Theorem: CCG generates {aⁿbⁿcⁿdⁿ} (via B² composition)
  - Theorem: CCG ⊃ CFL (strictly)
```

### 4.2 HPSG/Minimalism → SemDerivation

**Current state**: Only CCG implements the syntax→semantics interface.

**Problem**: Other theories can't feed into pragmatics.

**Solution**: Implement `toDerivation` for HPSG and Minimalism.

### 4.3 CCG-Montague Homomorphism

**Current state**: `CCG/Semantics.lean` has `catToTy` and trivial preservation theorems.

**Problem**: The homomorphism property (syntax composition → semantic application) not proven.

**Solution**: Prove fundamental theorem of compositional semantics:

```lean
theorem fapp_homomorphism :
    (DerivStep.fapp d₁ d₂).eval m lex = apply (d₁.eval m lex) (d₂.eval m lex)
```

See `docs/plans/wise-wiggling-parrot.md` for full plan.

---

## Lower Priority / Future Work

### Reorganize Pragmatic Theories

Move `NeoGricean/` and `RSA/` under `Theories/Pragmatics/` for consistency.

### RSA α Parameter

Parameterize RSA by rationality α; relate to NeoGricean competence assumption.

### B² Cross-Serial Derivations for 3+ Verbs

`CCG/CrossSerial.lean` has 2-verb derivations but simplified 3-verb case.
Full solution requires B² (generalized composition) to thread multiple argument slots.

### Compute NP-V Bindings from Derivation Structure

Extract which NP binds to which verb from CCG derivation tree, proving bindings emerge from structure.

### CCG Gapping Derivations & Category Decomposition

Implement generalized backward composition for type-raised categories and category decomposition rule (§7.3.3).

### Sentence Processing & Incremental Interpretation

Formalize CCG's left-prefix constituency and connect to processing data.

---

## Architectural Principles

1. **Syntax-agnostic pragmatics**: Pragmatics imports `SemDerivation`, not specific syntax theories
2. **Phenomena-driven**: Empirical data in `Phenomena/`, theory coverage tracked
3. **Competing analyses explicit**: Different semantic proposals in separate files with empirical predictions
4. **Proofs over examples**: Prefer theorems to `#eval` demonstrations
5. **Grounding over stipulation**: RSA should use compositional semantics, not pattern-match

---

## Completed

- [x] Consolidate `ContextPolarity` (was duplicated)
- [x] Move `Comparison.lean` to `Theories/Pragmatics/`
- [x] End-to-end scalar implicature pipeline (CCG → Montague → NeoGricean/RSA)
- [x] Agreement theorem: both theories derive "not all" from "some"
- [x] CCG Compositional Semantics (`CCG/Semantics.lean`, `CCG/TruthConditions.lean`)
- [x] Scope interfaces (`Core/Interfaces/ScopeTheory.lean`, `Montague/Scope.lean`, `CCG/Scope.lean`)
- [x] Information Structure (`Core/InformationStructure.lean`, `CCG/Intonation.lean`)
- [x] Cross-serial dependencies (`Phenomena/CrossSerialDependencies/Data.lean`, `CCG/CrossSerial.lean`)
- [x] Coreference theory interface (`Core/Interfaces/CoreferenceTheory.lean`)
- [x] Pipeline architecture (`Core/Pipeline.lean`)
- [x] RSA scope ambiguity model (`RSA/ScontrasPearl2021.lean`)
- [x] Gapping word order typology (`Phenomena/Gapping/Data.lean`, `CCG/Gapping.lean`)
- [x] Generalized conjunction (`Montague/Conjunction.lean`)
- [x] Real cross-serial derivations for 2-verb case (`CCG/CrossSerial.lean`)
- [x] Catalan bracketing proofs (`CCG/Equivalence.lean`)
- [x] **Intensional Montague Semantics** (`Montague/Intensional.lean`)
- [x] **Grounding theorems fully proven** (`RSA/Intensional.lean` - no sorries)
- [x] **Migrate to Mathlib ℚ** (removed custom `Frac` type)
- [x] **Simplify RSA to ℚ-only** (removed `RSAScore` typeclass)
- [x] **Type-safe scales** (`QuantExpr`/`ConnExpr` in scale operations)
- [x] **Unified entailment** (NeoGricean uses Montague semantics)
- [x] **Parameterized Lexicon: Numerals** (`Montague/Lexicon/Numerals/` - LowerBound, Exact, Compare)
