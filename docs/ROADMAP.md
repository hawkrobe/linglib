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

### 1.2 Refactor RSA to Use Intensional Meanings

**Current state**: `RSA/ScalarImplicatures.lean` pattern-matches on "some"/"all" strings.

**Problem**: The meaning function is stipulated, not derived from compositional semantics.

**Solution**: Replace `rsaFromDerivation` with version that uses `IntensionalDerivation`:

```lean
-- Current (stipulated)
def rsaFromDerivation d :=
  if hasSomeQuantifier d then rsaSomeResult  -- pre-computed

-- Desired (compositional)
def rsaFromDerivation (d : IntensionalDerivation m) (prior : m.World → Frac) :=
  L0_normalize (fun w => if d.evalAt w then prior w else 0)
```

**Files affected**: `RSA/ScalarImplicatures.lean`, `RSA/Basic.lean`

### 1.3 Grounding Theorem: RSA Uses Montague

**Goal**: Prove that RSA's L0 distribution comes from evaluating compositional meanings.

```lean
theorem rsa_l0_from_montague (d : IntensionalDerivation m) (prior : Distribution m.World) :
    L0 d prior w = normalize (fun w' => δ(d.evalAt w') * prior w') w
```

This formalizes that RSA doesn't stipulate meanings—it uses compositional semantics.

**Files affected**: `RSA/ScalarImplicatures.lean` or new `RSA/Grounding.lean`

---

## Phase 2: Type Safety & Robustness

### 2.1 Type-Safe Scale Positions

**Current state**: Implicatures use string matching: `hasImplicature results "all"`

**Problem**: Fragile—renaming breaks silently, no compile-time checking.

**Solution**: Use `QuantExpr` / `ConnExpr` types from `Montague/Scales.lean`:

```lean
-- Current
hasImplicature results "all"

-- Desired
hasImplicature results .all  -- type-checked!
```

**Files affected**: `NeoGricean/ScalarImplicatures.lean`, `RSA/ScalarImplicatures.lean`

### 2.2 NeoGricean Entailment → Montague Model

**Current state**: `NeoGricean/ScalarImplicatures.lean` has hardcoded entailment checker.

**Problem**: Not proven to match Montague's model-theoretic entailment.

**Solution**: Either:
- Prove equivalence: `neoGriceanEntails ↔ montagueEntails`
- Or replace hardcoded checker with Montague evaluation

**Files affected**: `NeoGricean/ScalarImplicatures.lean`, `Montague/Entailment.lean`

### 2.3 RSA DE Context Handling

**Current state**: NeoGricean handles DE blocking; RSA doesn't.

**Problem**: RSA model incomplete—can't represent embedded contexts.

**Solution**: Either:
- Extend RSA with compositional alternative generation
- Or document why RSA's treatment differs (QUD-based blocking)

**Files affected**: `RSA/ScalarImplicatures.lean`

---

## Phase 3: Competing Analyses Infrastructure

### 3.1 Parameterized Lexicon Structure

**Current state**: `Montague/Numbers.lean` has lower-bound semantics only.

**Problem**: No clean way to compare competing semantic proposals.

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
