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

### 2.4 Distribution Type ✓ DONE

**Status**: Implemented in `Core/Distribution.lean`

Provides:
- `ExactDist α`: Typed distribution with `mass : α → ℚ`, `nonneg`, `sum_one` proofs
- `ExactDist.normalize`: Constructor from unnormalized scores with proofs
- `ExactDist.uniform`, `ExactDist.pure`: Standard distributions
- `support_nonempty`, `mass_le_one`: Key theorems
- `toPMF`: Bridge to Mathlib's PMF for measure-theoretic properties

### 2.5 RSA DE Context Handling ✓ DONE

**Status**: Implemented in `RSA/PottsLU.lean`

Implements the full Potts et al. (2016) Lexical Uncertainty model:
- 10 world classes (3 players × 3 outcomes)
- 4 lexica (2 refinable items: quantifier + predicate)
- 11 utterances (quantifier × predicate combinations)

Key theorems:
- `potts_model_derives_de_blocking`: Global > Local in DE contexts
- `potts_model_derives_ue_implicature`: Local > Global in UE contexts
- `simplified_model_fails`: Regression test showing 3-world model fails
- `world_space_is_critical`: Rich world space is necessary for correct predictions

---

## Phase 3: Competing Analyses Infrastructure

### 3.1 Parameterized Lexicon Structure ✓ DONE

**Status**: Implemented in `Montague/Lexicon/Numerals/`

```
Montague/Lexicon/Numerals/
├── Theory.lean      -- NumeralTheory structure
├── LowerBound.lean  -- "two" means ≥2 (Horn 1972)
├── Bilateral.lean   -- "two" means =2 via maximality (Kennedy 2015)
└── Compare.lean     -- Comparison theorems
```

Provides:
- `NumeralTheory` structure with meaning function, derived RSA scenario
- `LowerBound`, `Bilateral` as concrete theory instances
- Comparison functions: `theoriesAgreeOn`, `divergingWorlds`
- Key theorems: `lowerBound_bilateral_differ_on_two`, `ambiguity_presence_differs`
- Connection to G&S 2013 empirical adjudication (ambiguity required for cancellation)
- Bilateral.lean documents Kennedy's maximality derivation for degree modifier support

### 3.1b Parameterized Lexicon: Modals ✓ DONE

**Status**: Implemented in `Montague/Lexicon/Modals/`

```
Montague/Lexicon/Modals/
├── Theory.lean    -- ModalTheory structure
├── Simple.lean    -- Kripke-style accessibility relations
├── Kratzer.lean   -- Conversational backgrounds (modal base + ordering)
└── Compare.lean   -- Comparison theorems
```

Provides:
- `ModalTheory` structure with eval function, duality property
- `Simple R`, `Kratzer params` as concrete theory instances
- `theoriesAgreeOn`, `divergingWorlds` comparison functions
- Key theorems: `minimal_kratzer_equals_universal_simple_necessity`, `epistemic_vs_minimal_differ`
- Kratzer context-dependence: same modal verb, different backgrounds → different truth values

### 3.2 Embedded Implicatures (Partial)

**Status**: DE contexts handled in `RSA/PottsLU.lean`

Completed:
- Embedded scalars under "no" (DE blocking)
- Full Potts et al. (2016) model with proven theorems
- Regression tests showing simplified models fail

Remaining:
- Attitude verb embedding ("John believes some students passed")
- Conditional antecedents
- Questions
- Geurts' globalist vs localist analysis for complex embeddings

---

## Phase 4: Syntax Expansion

### 4.1 Formal Language Theory & CCG Generative Capacity (Partial)

**Status**: Infrastructure implemented, proofs sketched with `sorry`

**Current state**:
- `Core/FormalLanguageTheory.lean`: Defines {aⁿbⁿcⁿdⁿ}, pumping lemma (axiom), `anbncndn_not_context_free` theorem (sorry)
- `Theories/CCG/GenerativeCapacity.lean`: Connects to CCG, `ccg_strictly_more_expressive_than_cfg` (sorry)

**Remaining work**:
- Fill in pumping lemma proof details (case analysis on decomposition)
- Prove `makeString_anbncndn n` satisfies the membership predicate for all n
- Complete the connection between CCG derivations and the formal language

```
Core/FormalLanguageTheory.lean
  - FourSymbol/ThreeSymbol alphabets ✓
  - isInLanguage_anbncndn membership predicate ✓
  - makeString_anbncndn generator ✓
  - Pumping lemma (axiom) ✓
  - anbncndn_not_context_free (sorry)
  - MildlyContextSensitive structure ✓

Theories/CCG/GenerativeCapacity.lean
  - Imports FormalLanguageTheory + CrossSerial ✓
  - ccg_strictly_more_expressive_than_cfg (sorry)
  - cross_serial_requires_mcs ✓ (proven by rfl)
  - ccg_is_mildly_context_sensitive ✓ (proven by rfl)
```

### 4.2 HPSG/Minimalism → SemDerivation

**Current state**: Only CCG implements the syntax→semantics interface.

**Problem**: Other theories can't feed into pragmatics.

**Solution**: Implement `toDerivation` for HPSG and Minimalism.

### 4.3 CCG-Montague Homomorphism ✓ DONE

**Status**: Implemented in `CCG/Homomorphism.lean` and `CCG/Semantics.lean`

**Implementation**:
- `DerivStep.interp` in Semantics.lean directly implements the homomorphism:
  - Forward application → function application (`m1 m2'`)
  - Backward application → function application (`m2 m1'`)
  - Forward composition → B combinator (`B m1 m2'`)
  - Type-raising → T combinator (`T m`)
- `Homomorphism.lean` proves structural properties:
  - `fapp_sem`, `bapp_sem`: Application = function application
  - `fcomp_sem`: Composition = B combinator
  - `ftr_sem`: Type-raising = T combinator
  - `ccgHomomorphism`: All properties hold together
  - `ccgRuleToRule`: Steedman's rule-to-rule relation

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

### Horn (1972) Further Extensions

Additional formalizations from Horn's dissertation:

- **Scale Reversal**: Golf scores, rankings, budgets (descending scales)
- **Forced vs Invited Inference**: Endpoint vs non-endpoint implicatures (§2.15)
- **Ordinal-as-Rank**: "finished third" implicates "not second" (reversed direction)
- **Presupposition-Implicature Distinction**: Conjunction redundancy test

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
- [x] **Parameterized Lexicon: Modals** (`Montague/Lexicon/Modals/` - Simple, Kratzer, Compare)
- [x] **Implicature Operations** (`NeoGricean/Operations.lean` - assert/contradict/suspend from Horn 1972 §1.22)
- [x] **Negation Scope Asymmetry** (`NeoGricean/NegationScope.lean` - internal vs external negation from Horn 1972)
- [x] **RSA DE Context Handling** (`RSA/PottsLU.lean` - full Potts et al. 2016 Lexical Uncertainty model)
- [x] **Distribution Type** (`Core/Distribution.lean` - ExactDist with proofs)
- [x] **Formal Language Theory** (`Core/FormalLanguageTheory.lean` - infrastructure for {aⁿbⁿcⁿdⁿ})
- [x] **CCG Generative Capacity** (`CCG/GenerativeCapacity.lean` - connects CCG to formal language theory)
- [x] **CCG-Montague Homomorphism** (`CCG/Homomorphism.lean` - rule-to-rule correspondence)
