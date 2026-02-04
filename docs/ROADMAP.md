# Linglib Roadmap

Future work and wishlist items.

---

## North Stars

> **For phenomenon P with behavioral data D, prove that theory T₁ predicts D and theory T₂ doesn't (or both do, via different assumptions).**

### The Characterization Theorem (Meta-Goal)

```lean
theorem rsa_exh_equivalence_conditions :
    (∀ u w, RSA.L1 α scenario u w > 0 ↔ EXH.eval alternatives u w) ↔
    (alternatives_match ∧ uniform_prior ∧ high_rationality ∧ depth_one ∧ no_qud)
```

### Priority Phenomena

| Phenomenon | Why Interesting |
|------------|-----------------|
| **Scope Freezing** | Prove CCG and Minimalism predict same freezing via different mechanisms |
| **RSA ≅ EXH Equivalence** | Characterize when grammar/pragmatics debates are notational |

---

## Algebraic Metatheory

### Key Theorems to Prove

```lean
-- Lexicon refinement transfers to inference strength
theorem lexicon_refinement_monotone :
    ⟦·⟧₁ ≤ ⟦·⟧₂ → ∀ u w, RSA.L1 scenario₁ u w ≥ RSA.L1 scenario₂ u w

-- RSA iteration converges to a unique fixed point
theorem rsa_fixed_point_unique (scenario : RSAScenario U W) (α : ℚ) (hα : α > 0) :
    ∃! (L, S), RSA.iterate scenario α (L, S) = (L, S)

-- α → ∞ limit coincides with tropical semiring / iterated best response
theorem rsa_tropical_deformation :
    ∀ ε > 0, ∃ α₀, ∀ α > α₀, dist (RSA.S1 α scenario) (tropicalArgmax scenario) < ε
```

---

## Neural-Symbolic Emergence

### Project A: Formalize Futrell & Hahn

```lean
theorem dependency_locality_optimal :
    ∀ tree₁ tree₂ : DependencyTree,
    avgDependencyLength tree₁ < avgDependencyLength tree₂ →
    predictiveInfo tree₁ ≤ predictiveInfo tree₂
```

### Project B: RSA from LLM

```lean
theorem rsa_emerges_from_lm (M : LanguageModel) (coarsen : Continuation → Meaning) (α : ℚ) :
    ∃ ε > 0, ∀ u w, |M.coarsened_prob coarsen w u - RSA.L1 α scenario w u| < ε
```

---

## Short-term TODO

### Documentation

```
docs/
├── tutorial/
│   ├── 01-first-rsa-model.md
│   ├── 02-scalar-implicatures.md
│   └── 03-competing-analyses.md
├── replications/
│   ├── FrankGoodman2012.md
│   └── ...
└── coverage.md
```

### Scenario Combinators

```lean
def RSAScenario.withUtterances (s : RSAScenario U W) (us : List U') : RSAScenario (U ⊕ U') W
def RSAScenario.restrictWorlds (s : RSAScenario U W) (ws : List W) : RSAScenario U W
```

### Automatic Divergence Detection

```lean
structure TheoryDivergence where
  theory1 : String
  theory2 : String
  phenomenon : String
  divergingCases : List (String × (ℚ × ℚ))

def findDivergences (t1 t2 : ImplicatureTheory) (data : PhenomenonData) : List TheoryDivergence
```

### Proofs to Fill

- `ccg_strictly_more_expressive_than_cfg` uses `sorry`
- Grounding proofs for PottsLU, AttitudeEmbedding, etc.

---

## RSA Papers TODO

- **Egré et al. (2023)** "Around" — Vagueness as communicative resource
- Acquisition models (Bohn, Frank, Stiller)
- Social meaning (Burnett, dogwhistles)

---

## Deferred

- **HPSG/Minimalism → SemDerivation**: Syntax expansion beyond CCG
- **Sentence processing**: Incremental interpretation
- **Full Horn (1972)**: Scale reversal, forced vs invited inference
- **Neo-Davidsonian event semantics**: Event arguments, thematic roles

### Hot Topics

- **Presupposition triggering**: Experimental data (Bade, Schlenker, Chemla 2024)
- **Soft vs hard triggers**: Romoli, Abusch
- **Plurals & distributivity**: Link semantics + RSA

### Speech Acts (Long-term)

```
Theories/SpeechActs/
├── Basic.lean           -- Illocutionary acts, perlocutionary effects
├── Performatives.lean   -- "I promise", "I bet", "I name this ship"
├── Directives.lean      -- Commands, requests, suggestions
├── Commissives.lean     -- Promises, threats, offers
└── RSAIntegration.lean  -- Speech acts as rational social actions
```
