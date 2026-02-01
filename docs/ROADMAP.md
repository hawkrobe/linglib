# Linglib Roadmap

This document tracks future work and wishlist items.

---

## Strategic Decisions

### Target User
**Primary**: Pragmatics researchers wanting to test RSA model variants against empirical data.

**Secondary**: Formal semanticists wanting compositional analyses with proven properties.

**Deferred**: Syntacticians comparing CCG/HPSG/Minimalism (syntax theories remain as infrastructure, not primary focus).

### Depth vs Breadth
**Choice**: Depth first. We aim for 3-4 phenomena with fully competing analyses from multiple theories, rather than 10 phenomena with single pipelines. This demonstrates the comparison value proposition—the system's core contribution.

### Syntax Story
**Choice**: CCG as the primary syntax-semantics interface. HPSG/Minimalism remain as documented infrastructure but aren't prioritized for Montague integration. Pragmatics research doesn't typically need multiple syntax frameworks—it needs correct compositional meanings.

---

## North Stars

The actual north star for LingLib is:

> **For phenomenon P with behavioral data D, prove that theory T₁ predicts D and theory T₂ doesn't (or both do, via different assumptions).**

This is what makes formalization scientifically valuable—not just implementing a textbook, but using formalization to adjudicate between theories or reveal hidden equivalences.

### The Characterization Theorem (Meta-Goal)

The most scientifically valuable theorem would characterize when grammar/pragmatics debates are empirical vs. notational:

```lean
theorem rsa_exh_equivalence_conditions :
    (∀ u w, RSA.L1 α scenario u w > 0 ↔ EXH.eval alternatives u w) ↔
    (alternatives_match ∧ uniform_prior ∧ high_rationality ∧ depth_one ∧ no_qud)
```

### Priority North Stars

| Phenomenon | Why Interesting | Priority |
|------------|-----------------|----------|
| **Scope Freezing** | Different mechanisms in Minimalism vs CCG; testable predictions | Immediate |
| **Free Choice** | Grammatical (Innocent Inclusion) vs pragmatic (RSA) debate | Near-term |
| **RSA ≅ EXH Equivalence** | Characterize when grammar/pragmatics debates are empirical vs notational | Medium-term |
| **Homogeneity/Non-maximality** | Spector 2018 is RSA-based | Medium-term |

### Scope Freezing

**Phenomenon**: Inverse scope disappears in certain configurations.

- "A student attended every seminar" → ∀>∃ and ∃>∀ both available
- "A student's teacher attended every seminar" → Only ∃>∀ (surface scope)

**Why interesting**: Different theories explain this differently:
- **Minimalism**: QR is clause-bounded, possessor blocks movement
- **CCG**: Derivational ambiguity is structurally constrained

**The theorem**: Prove that Minimalism and CCG both predict scope freezing, but via different mechanisms. Or prove they diverge somewhere.

### Free Choice

**Phenomenon**: "You can have cake or ice cream" → You can have either.

**Competing theories**:
- **Grammatical**: Bar-Lev & Fox's Innocent Inclusion
- **Pragmatic**: RSA derives it from speaker uncertainty (Franke 2011)

**Infrastructure needed**:
- `Theories/Exhaustivity/InnocentInclusion.lean` — Bar-Lev & Fox
- RSA formulation of free choice

### RSA ≅ EXH Equivalence

**Core insight**: RSA and EXH are different kinds of theories that happen to make overlapping predictions for core cases.

**Conditions for equivalence** (conjecture):
1. Alternatives match
2. Priors are uniform
3. α → ∞ (rationality limit)
4. Recursion depth = 1
5. No QUD effects

**Where they probably diverge**:
- **Embedded implicatures**: RSA computes globally; EXH allows local computation
- **Prior-sensitive cases**: RSA predictions depend on P(w); grammar can't access world knowledge
- **Iterated reasoning**: M-implicatures, politeness phenomena

---

## Algebraic Metatheory (Research Frontier)

**Goal**: Characterize the algebraic structure of RSA models analogous to Barker & Pullum's lattice results for command relations.

### Candidate Structures

| Structure | Mathlib Support | Priority |
|-----------|-----------------|----------|
| **Lexicon lattice** | Complete lattice theory | Tractable now |
| **Horn scale lattice** | Order theory | Tractable now |
| **α → ∞ limit** | Limits, filters | Near-term |
| **Tropical semiring** | Would need to add | Medium-term |
| **Fixed-point theory** | Some CPO support | Medium-term |
| **Information geometry** | Limited | Long-term |

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

## Neural-Symbolic Emergence (Research Frontier)

**Goal**: Establish formal syntax/semantics as an "effective theory" of neural language models — the way thermodynamics emerges from statistical mechanics.

### Concrete Projects

**Project A: Formalize Futrell & Hahn**

Prove that CCG/DG structures minimize predictive information among compositional representations.

```lean
theorem dependency_locality_optimal :
    ∀ tree₁ tree₂ : DependencyTree,
    avgDependencyLength tree₁ < avgDependencyLength tree₂ →
    predictiveInfo tree₁ ≤ predictiveInfo tree₂
```

**Project B: RSA from LLM**

Prove that RSA pragmatics emerges from LLM next-token prediction under appropriate coarse-graining.

```lean
theorem rsa_emerges_from_lm (M : LanguageModel) (coarsen : Continuation → Meaning) (α : ℚ) :
    ∃ ε > 0, ∀ u w, |M.coarsened_prob coarsen w u - RSA.L1 α scenario w u| < ε
```

### Proposed Module Structure

```
Linglib/Emergence/
├── LanguageModel.lean      -- Minimal LM interface (next-token distributions)
├── CoarseGraining.lean     -- Discretization, marginalization, projection
├── InformationBottleneck.lean -- I(X;T), I(T;Y), rate-distortion
├── Approximation.lean      -- ε-δ bounds, distortion metrics
├── RSAEmergence.lean       -- RSA from LLM coarse-graining
└── Probing.lean            -- Linear encoding, probe optimality
```

---

## Short-term TODO

### Documentation (Highest Priority)

The main remaining gap for researcher usability.

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

Extending existing scenarios (add utterance, change prior) still requires rebuilding.

```lean
def RSAScenario.withUtterances (s : RSAScenario U W) (us : List U') : RSAScenario (U ⊕ U') W
def RSAScenario.restrictWorlds (s : RSAScenario U W) (ws : List W) : RSAScenario U W
```

### Automatic Divergence Detection

A generic tool for finding where theories diverge:

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
- Replace some `native_decide` with full proofs where meaningful

### CI Setup

```yaml
# .github/workflows/test.yml
- name: Build all theories
- name: Run theory comparison tests
```

---

## RSA Papers TODO

### High Priority (foundational for comparison work)
1. **Cremers, Wilcox & Spector (2023)** — Exhaustivity vs anti-exhaustivity; model comparison
2. **Champollion et al. (2019)** Free Choice — RSA for free choice disjunction
3. **Yoon et al. (2020)** Politeness — Three-goal utility (partially done)

### Medium Priority (extends coverage)
4. **Kao et al. (2014a)** Metaphor — Metaphor comprehension
5. **Tessler & Goodman (2019)** Generics — QUD-sensitive generics
6. **Hawkins et al. (2022)** Convention formation — Population-level conventions
7. **Egré et al. (2023)** "Around" — Vagueness as communicative resource

### Lower Priority (specialized domains)
8. Acquisition models (Bohn, Frank, Stiller)
9. Social meaning (Burnett, dogwhistles)
10. **Spector (2017)** / **Križ & Spector (2020)** — Homogeneity, non-maximality

---

## Deferred

These are valuable but not on the critical path:

- **HPSG/Minimalism → SemDerivation**: Syntax expansion beyond CCG
- **Sentence processing**: Incremental interpretation
- **B² generalized composition**: 3+ verb cross-serial
- **Full Horn (1972)**: Scale reversal, forced vs invited inference
- **Scope-word order interactions**: Dutch/German data
- **Neo-Davidsonian event semantics**: Event arguments, thematic roles

### Hot Topics (potential future North Stars)

- **Presupposition triggering**: Experimental data (Bade, Schlenker, Chemla 2024)
- **Soft vs hard triggers**: Romoli, Abusch
- **Modal anchoring**: Kratzer's framework extended to RSA contexts
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

### Graded/Quantitative Theories

**Architectural decision**: LingLib focuses on categorical/ordering checks. Quantitative model fitting belongs in external tools (R/Python) that can import Lean-verified theory structure.

---

## References

### RSA Foundations
- Frank & Goodman (2012). Predicting Pragmatic Reasoning in Language Games.
- Goodman & Frank (2016). Pragmatic Language Interpretation as Probabilistic Inference.

### Algebraic Metatheory
- Barker & Pullum (1990) "A Theory of Command Relations"
- Zaslavsky et al. (2020) "Rate-distortion theory of neural coding"
- Franke & Jäger (2016) "Probabilistic pragmatics"

### Neural-Symbolic
- Futrell & Hahn (2025) "Linguistic structure from a bottleneck on sequential information processing"
- Hewitt & Manning (2019) "A Structural Probe for Finding Syntax in Word Representations"
