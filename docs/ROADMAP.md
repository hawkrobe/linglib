# Linglib Roadmap

This document tracks architectural improvements organized by release tiers.

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

### Publication Path
A SALT/ESSLLI paper on architecture + 2-3 deep case studies (scalar implicatures, numerals, scope) could establish credibility. The system should be able to replicate key RSA papers (Frank & Goodman 2012, Goodman & Stuhlmüller 2013, Scontras & Pearl 2021, Kao et al. 2014) in minimal code.

---

## North Stars

The actual north star for LingLib is:

> **For phenomenon P with behavioral data D, prove that theory T₁ predicts D and theory T₂ doesn't (or both do, via different assumptions).**

This is what makes formalization scientifically valuable—not just implementing a textbook, but using formalization to adjudicate between theories or reveal hidden equivalences.

### The Characterization Theorem (Meta-Goal)

The most scientifically valuable theorem would characterize when grammar/pragmatics debates are empirical vs. notational:

```lean
-- RSA and EXH make identical predictions if and only if:
-- (a) Alternatives match
-- (b) Priors are uniform
-- (c) α → ∞
-- (d) Recursion depth = 1
-- (e) No QUD effects
-- When any of (a)-(e) fails, here's how they diverge: [specific predictions]

theorem rsa_exh_equivalence_conditions :
    (∀ u w, RSA.L1 α scenario u w > 0 ↔ EXH.eval alternatives u w) ↔
    (alternatives_match ∧ uniform_prior ∧ high_rationality ∧ depth_one ∧ no_qud)
```

This tells us exactly when the grammar/pragmatics debate is empirical vs. notational, and where to look for decisive data.

### Candidate North Stars (by tractability)

| Phenomenon | Why Interesting | Data Available | LingLib Readiness | Priority |
|------------|-----------------|----------------|-------------------|----------|
| **Binding Theory Unification** | Three theories already formalized; prove agreement or find divergence | Classic data | High—ready now | Immediate |
| **Scope Freezing** | Different mechanisms in Minimalism vs CCG; testable predictions | Experimental literature | High—scope machinery exists | Near-term |
| **Free Choice** | Grammatical (Innocent Inclusion) vs pragmatic (RSA) debate | Tieu et al. 2024 | Medium—need EXH operator | Medium-term |
| **Question Exhaustivity** | Direct RSA application; Xiang's work is RSA-adjacent | Xiang, Cremers | Medium—need question semantics | Medium-term |
| **Homogeneity/Non-maximality** | Spector 2018 is RSA-based | Križ & Spector 2020 | Medium—need plural semantics | Medium-term |
| **Presupposition Projection** | Major competing frameworks (satisfaction, dynamic, trivalent) | Chemla 2024 | Low—substantial new infrastructure | Long-term |

### 1. Binding Theory Unification (Immediate)

**Phenomenon**: Principles A/B/C are formalized in Minimalism, HPSG, and Dependency Grammar.

**The theorem**:
```lean
-- For all sentences in the test suite, all three theories agree
theorem binding_theories_agree (ws : List Word) :
    coreferenceStatus MinimalismTheory ws i j =
    coreferenceStatus HPSGTheory ws i j ∧
    coreferenceStatus HPSGTheory ws i j =
    coreferenceStatus DGTheory ws i j := by
  ...
```

Or more interestingly: find where they *don't* agree and characterize it.

**Why tractable**: Machinery exists in all three theories. The comparison theorem is the spec—missing unit tests reveal themselves as you try to prove it.

**Infrastructure needed**:
- `Minimalism/Coreference.lean` — c-command, locality, φ-agreement ✓
- `HPSG/Coreference.lean` — o-command, LOCAL features ✓
- `DependencyGrammar/Coreference.lean` — dependency paths ✓
- `Comparisons/BindingTheories.lean` — the comparison theorem ✗

### 2. Scope Freezing (Near-term)

**Phenomenon**: Inverse scope disappears in certain configurations.

- "A student attended every seminar" → ∀>∃ and ∃>∀ both available
- "A student's teacher attended every seminar" → Only ∃>∀ (surface scope)

**Why interesting**: Different theories explain this differently:
- **Minimalism**: QR is clause-bounded, possessor blocks movement
- **CCG**: Derivational ambiguity is structurally constrained

**The theorem**: Prove that Minimalism and CCG both predict scope freezing, but via different mechanisms. Or prove they diverge somewhere.

**Connects to**: Existing scope ambiguity work (Scontras & Pearl 2021).

### 3. Free Choice (Medium-term)

**Phenomenon**: "You can have cake or ice cream" → You can have either.

**Competing theories**:
- **Grammatical**: Bar-Lev & Fox's Innocent Inclusion
- **Pragmatic**: RSA derives it from speaker uncertainty (Franke 2011)

**The theorem**: Show RSA + basic alternatives derives free choice *and* characterize whether the derivation mirrors Innocent Inclusion's logic. If mechanisms differ, that's evidence they're distinct theories that happen to converge.

**Infrastructure needed**:
- `Theories/Exhaustivity/EXH.lean` — Fox's EXH operator ✗
- `Theories/Exhaustivity/InnocentInclusion.lean` — Bar-Lev & Fox ✗
- RSA formulation of free choice ✗

### 4. Question Exhaustivity (Medium-term)

**Phenomenon**: "Who came?" answered "John" implies only John came.

**Competing analyses**:
- **Grammatical**: Exhaustivity is part of question semantics
- **Pragmatic**: RSA derives exhaustivity from alternatives

**The theorem**: Prove RSA + standard question semantics → exhaustivity. Then compare to grammatical exhaustivity theories. Show which assumptions drive the prediction.

**Infrastructure needed**:
- `Montague/Questions.lean` — Hamblin/partition semantics ✗
- RSA over question-answer pairs ✗

### 5. RSA ≅ EXH Equivalence (Long-term)

**Core insight**: RSA and EXH are different kinds of theories that happen to make overlapping predictions for core cases.

**Key differences**:
- RSA is probabilistic; EXH is categorical
- RSA is context-sensitive (priors matter); EXH is context-independent
- RSA can do iterated reasoning (L2, L3...); EXH has no analog
- EXH is compositional (applies at LF positions); RSA reasons over whole utterances

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

**Valuable theorems**:
- Equivalence: "For fragment F with conditions C, RSA and EXH make identical predictions"
- Divergence: "For phenomenon P, RSA predicts X while EXH predicts Y"
- Reduction: "EXH can be viewed as RSA with α→∞, uniform priors, and alternatives A"

---

## Algebraic Metatheory (Research Frontier)

**Goal**: Characterize the algebraic structure of RSA models analogous to Barker & Pullum's lattice results for command relations.

### The B&P Analogy

The elegance of B&P (1990) comes from:
- A parameterized schema: C_P defined by property P
- A natural operation: intersection of command relations
- A key theorem: C_P ∩ C_Q = C_{P∪Q} (intersection over relations = union over properties)
- This yields a join semilattice

**Question**: Does RSA have analogous algebraic structure? The answer likely involves different mathematics (measure theory, convexity, information geometry) rather than pure lattice theory, since RSA is fundamentally probabilistic.

### Candidate Structures

#### 1. Tropical/Idempotent Limit (α → ∞)

As α → ∞, softmax becomes argmax, and RSA operations become:
- `max` (replacing log-sum-exp)
- `+` (combining log-probabilities)

This is the **tropical semiring** (ℝ ∪ {-∞}, max, +), which has beautiful algebraic properties:
- Idempotent: max(x, x) = x
- Forms a complete lattice under max
- Connects to Viterbi algorithms, tropical geometry

**Potential theorem**:
```lean
-- The family of RSA models indexed by α forms a deformation from
-- the tropical semiring (α → ∞) to uniform distributions (α → 0)
theorem rsa_tropical_deformation :
    ∀ ε > 0, ∃ α₀, ∀ α > α₀,
    dist (RSA.S1 α scenario) (tropicalArgmax scenario) < ε
```

**Connection to EXH**: The α → ∞ limit is exactly where RSA becomes categorical like EXH. Formalizing this limit gives the "RSA ≅ EXH under conditions" theorem concrete mathematical content.

#### 2. Lexicon Lattice

The space of lexicons ⟦·⟧ : U → P(W) has natural lattice structure:

**Partial order**: ⟦·⟧₁ ≤ ⟦·⟧₂ iff ∀u. ⟦u⟧₁ ⊆ ⟦u⟧₂ (more specific meanings)

**Operations**:
- Meet: (⟦·⟧₁ ∧ ⟦·⟧₂)(u) = ⟦u⟧₁ ∩ ⟦u⟧₂
- Join: (⟦·⟧₁ ∨ ⟦·⟧₂)(u) = ⟦u⟧₁ ∪ ⟦u⟧₂

This forms a complete distributive lattice (pointwise extension of powerset lattice).

**Potential theorem**:
```lean
-- Lexicon refinement transfers to inference strength
theorem lexicon_refinement_monotone :
    ⟦·⟧₁ ≤ ⟦·⟧₂ →
    ∀ u w, RSA.L1 scenario₁ u w ≥ RSA.L1 scenario₂ u w
    -- (or the reverse, depending on how informativity works)
```

**Connection to Lexical Uncertainty**: Bergen et al.'s LU model averages over lexicons. The lexicon lattice structure might characterize which lexicon mixtures are coherent.

#### 3. Fixed-Point Structure

The RSA recursion L₀ → S₁ → L₁ → S₂ → ... is a fixed-point iteration. This connects to:
- **Kleene's theorem**: Scott-continuous functions on CPOs
- **Tarski's theorem**: Monotone functions on complete lattices have least fixed points
- **Banach fixed-point**: Contractions on complete metric spaces

**Question**: Is there a natural partial order on (listener, speaker) strategy pairs such that RSA iteration is monotone?

**Potential theorem**:
```lean
-- RSA iteration converges to a unique fixed point
theorem rsa_fixed_point_unique (scenario : RSAScenario U W) (α : ℚ) (hα : α > 0) :
    ∃! (L, S), RSA.iterate scenario α (L, S) = (L, S)
```

If so, the fixed points form a complete lattice, and we get existence/uniqueness for free.

#### 4. Horn Scale Lattice

Existing scale infrastructure already contains implicit lattice structure:

If scales are ordered by informativity (⟨some, all⟩ where "all" ⊐ "some"), the scales themselves form partial orders.

**Potential theorem**:
```lean
-- Scalar implicature strength is a lattice homomorphism
theorem si_strength_homomorphism (scale : HornScale) :
    Monotone (λ item => implicatureStrength scale item)
```

This would formalize "stronger scalar items yield stronger implicatures."

#### 5. Parameterized RSA Schema

Following B&P's template: Is there a single parameterized schema RSA_Θ such that all RSA variants are instances?

**Parameter space** Θ = (P, ⟦·⟧, U, α, n, C) where:
- P : W → ℚ (prior)
- ⟦·⟧ : U → W → ℚ (lexicon/semantics)
- U : W × U → ℚ (utility)
- α : ℚ (rationality)
- n : ℕ (recursion depth)
- C : U → ℚ (cost function)

**Potential structure**: The space of RSA models might form a convex cone or fiber bundle over the space of lexicons.

```lean
-- RSA models form a convex space
theorem rsa_convex_combination (s₁ s₂ : RSAScenario U W) (t : ℚ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ s, RSA.L1 s = t • RSA.L1 s₁ + (1 - t) • RSA.L1 s₂
```

#### 6. Information-Geometric Structure (Long-term)

RSA operates on probability distributions, which have natural geometry:

- **Exponential families**: RSA's softmax defines an exponential family with natural parameter αU(w,u)
- **Duality**: Natural parameters θ ↔ expectation parameters η via Legendre transform
- **Bregman divergences**: KL-divergence appears in RSA's information-theoretic interpretation

The space of RSA "meaning distributions" L(·|u) for different utterances might form a statistical manifold with Fisher information metric.

**Connection to Zaslavsky et al.**: The rate-distortion formulation already uses information-theoretic concepts. Information geometry would give this a differential-geometric foundation.

### Tractability Assessment

| Structure | Mathlib Support | LingLib Readiness | Priority |
|-----------|-----------------|-------------------|----------|
| **Lexicon lattice** | Complete lattice theory | Lexicons exist | Tractable now |
| **Horn scale lattice** | Order theory | Scales exist | Tractable now |
| **α → ∞ limit** | Limits, filters | Rate-distortion exists | Near-term |
| **Tropical semiring** | Would need to add | — | Medium-term |
| **Fixed-point theory** | Some CPO support | RSA iteration exists | Medium-term |
| **Parameterized schema** | Depends on formulation | — | Medium-term |
| **Information geometry** | Limited | — | Long-term |
| **Galois connections** | Category theory basics | — | Long-term |

### Key Insight

The B&P result works because command relations are fundamentally **set-theoretic** (dominance, property satisfaction). RSA is fundamentally **measure-theoretic** (probability distributions), where the natural structures are:
- Convexity (mixtures of distributions)
- Exponential families (softmax structure)
- Information geometry (Fisher metric, KL divergence)

Rather than lattices per se.

### Research Directions

**Concrete project (Near-term)**: Formalize that the α → ∞ limit of RSA coincides with iterated best response in signaling games, and show this limit inherits tropical semiring structure.

This would give:
1. Exact lattice structure at α = ∞
2. A "deformation" parameter α connecting soft and hard rationality
3. Connection to game theory literature (Lewis signaling games)

**Theoretical project (Long-term)**: Characterize the Galois connection (if any) between:
- The lattice of lexicons (ordered by refinement)
- The space of pragmatic interpretations (ordered by informativity)

This would formalize the intuition that "more specific meanings yield more informative inferences."

### References

- Barker & Pullum (1990) "A Theory of Command Relations"
- Zaslavsky et al. (2020) "Rate-distortion theory of neural coding" (information-theoretic RSA)
- Franke & Jäger (2016) "Probabilistic pragmatics" (game-theoretic foundations)
- Lewis (1969) "Convention" (signaling games)
- Amari (2016) "Information Geometry and Its Applications"

---

## Neural-Symbolic Emergence (Research Frontier)

**Goal**: Establish formal syntax/semantics as an "effective theory" of neural language models — the way thermodynamics emerges from statistical mechanics.

### The Physics Analogy

In physics, effective theories work via coarse-graining:

| Microscopic | Macroscopic | Relation |
|-------------|-------------|----------|
| Particle positions/momenta | Temperature, pressure, entropy | Ensemble averages |
| Quantum field theory | Classical mechanics | ℏ → 0 limit |
| Lattice spin models | Continuous field theories | Renormalization group flow |

**Key insight**: Macroscopic quantities are *sufficient statistics* for predicting macroscopic observables. You lose information but retain what's relevant.

### The Linguistic Analogy

| Neural (microscopic) | Formal (macroscopic) | Relation to establish |
|---------------------|---------------------|----------------------|
| Token embeddings | Lexical categories | Clustering / discretization |
| Attention patterns | Syntactic dependencies | Projection / sparsification |
| Hidden state trajectories | Derivations | Coarse-graining over paths |
| Next-token distributions | Compositional semantics | ??? |

**Research program**: Prove that formal structures are *optimal coarse-grainings* of neural representations for certain prediction classes.

### Three Formalization Strategies

#### 1. Information Bottleneck / Predictive Information Approach

**Core idea** (Futrell & Hahn 2025): Languages minimize **predictive information** — the mutual information between past and future of a stochastic process (also called excess entropy).

**Key result**: Codes that minimize predictive information spontaneously develop:
- Approximately independent features (→ morphemes, words)
- Systematic local expression (→ phrases, constituency)
- This matches actual language structure at phonology, morphology, syntax, and lexical semantics levels

**The information bottleneck framing**:
```
       neural states X (past context)
             |
             v
      [compression T]  ← minimize I(past; T)
             |
             v
       formal structure (words, phrases)
             |
             v
    future predictions Y   ← maximize I(T; future)
```

This makes precise: *"Linguistic structure is what you need to remember about the past to predict the future, and no more."*

**Lean formalization**: Prove that formal representations achieve predictive information optimality.

```lean
-- Predictive information: I(past; future) through representation
def predictiveInfo (rep : Context → Representation) : ℝ :=
  mutualInfo (past ∘ rep) future

-- Formal syntax minimizes predictive information
theorem syntax_minimizes_predictive_info (M : LanguageModel) :
    ∃ π : HiddenState → SyntacticStructure,
    π ∈ argmin (predictiveInfo ∘ encode)
    subject to (decodability π ≥ threshold)
```

**Connection to Futrell & Hahn**: Their simulations show this emergence computationally. LingLib could provide the *formal proof* that specific syntactic structures (CCG derivations, dependency trees) achieve this optimality.

#### 2. Renormalization Group Approach

In physics, RG flow shows how theories change under coarse-graining. Fixed points of RG flow are scale-invariant theories.

**Conjecture**: Formal grammars are *fixed points* of a linguistic RG flow. As you coarse-grain neural representations, the structure stabilizes to formal grammar.

This would explain **universality**: why different neural architectures (LSTMs, Transformers, Mamba) trained on language converge to similar syntactic representations — they're all flowing to the same RG fixed point.

**Coarse-graining operations**:
- Dimensionality reduction (PCA, sparse coding)
- Discretization / clustering
- Marginalization over contexts
- Time-averaging over sequential states

```lean
-- Formal grammar is a fixed point of linguistic RG flow
theorem grammar_is_rg_fixed_point (coarsen : NeuralRep → NeuralRep) :
    ∃ Grammar, ∀ M : LanguageModel,
    limit (iterate coarsen M.representations) ≅ Grammar
```

#### 3. Homomorphism + Approximation Approach

More modest but tractable: Show there exists a structure-preserving map from neural representations to formal structures, with bounded error.

```lean
-- Neural representations approximately embed formal structure
theorem formal_structure_embedded (M : LanguageModel) :
    ∃ π : HiddenStates → FormalStructure,
    -- π respects composition
    (∀ h₁ h₂, dist (π (compose h₁ h₂)) (compose (π h₁) (π h₂)) < ε₁) ∧
    -- π has bounded distortion
    (∀ h h', d(h, h') ≤ d(π h, π h') ≤ C · d(h, h')) ∧
    -- π preserves relevant predictions
    (∀ j : Judgment, |P_M(j | h) - P_formal(j | π h)| < ε₂)
```

### Concrete First Projects

#### Project A: Formalize Futrell & Hahn

**Goal**: Provide formal proofs for the Futrell & Hahn (2025) framework.

They show *computationally* that predictive-information-minimizing codes develop linguistic structure. LingLib could prove *mathematically*:

1. **CCG derivations minimize predictive information** among compositional representations
2. **Dependency locality** (shorter dependencies) ↔ lower predictive information
3. **Morphological paradigms** as optimal codes for feature bundles

```lean
-- Dependency length correlates with predictive information
theorem dependency_locality_optimal :
    ∀ tree₁ tree₂ : DependencyTree,
    avgDependencyLength tree₁ < avgDependencyLength tree₂ →
    predictiveInfo tree₁ ≤ predictiveInfo tree₂
```

This would give Futrell & Hahn's empirical findings a formal foundation.

#### Project B: RSA from LLM

**Project**: Prove that RSA pragmatics emerges from LLM next-token prediction under appropriate coarse-graining.

**Setup**:
1. LLM defines P(continuation | context) over tokens
2. Define coarse-graining: P(meaning | utterance) = Σ_{continuations c ∈ meaning} P(c | u)
3. Show coarse-grained distribution satisfies RSA equations (approximately)

```lean
-- RSA emerges from language model coarse-graining
theorem rsa_emerges_from_lm
    (M : LanguageModel)
    (coarsen : Continuation → Meaning)
    (α : ℚ) :
    ∃ ε > 0, ∀ u w,
    |M.coarsened_prob coarsen w u - RSA.L1 α scenario w u| < ε
```

**Why tractable**: We already have RSA formalized. We'd need to:
1. Define a minimal `LanguageModel` interface
2. Define coarse-graining operations
3. Prove approximation bounds

This gives a precise sense in which *"RSA is the effective theory of LLM pragmatics."*

### The Scaling Limits Question

Physics has natural limits where approximations become exact:
- N → ∞ (thermodynamic limit)
- ℏ → 0 (classical limit)
- Lattice spacing → 0 (continuum limit)

**What's the analogous limit for linguistics?**
- Vocabulary size → ∞?
- Context length → ∞?
- Training data → ∞?
- Model parameters → ∞?

**Speculative conjecture**: In the limit of infinite context and vocabulary, LLM hidden states become *isomorphic* (not just approximately homomorphic) to formal semantic representations.

### Existing Work to Build On

**Probing classifiers** (Hewitt & Manning 2019): Syntax trees are linearly encoded in BERT hidden states. Formalization: What does "linearly encoded" mean precisely? When is linear probing optimal?

**Tensor networks**: Matrix product states ↔ weighted finite automata. MERA ↔ context-free grammars. Tensor bond dimension ↔ grammatical complexity. Formal language classes as "coarse-grainings" of tensor networks.

**Mechanistic interpretability** (Anthropic, Neel Nanda): Transformers implement discrete algorithms via attention heads. Already a kind of "derivation of formal structure from neural substrate."

### Success Criteria for Linguistic Statistical Mechanics

A mature theory would have:

1. **Emergence theorems**: "Under conditions C, formal structure S emerges from neural model class M"
2. **Universality results**: "All models in class M converge to the same formal structure under coarse-graining"
3. **Fluctuation relations**: "Deviations from formal predictions scale as 1/√N"
4. **Phase transitions**: "As parameter α crosses threshold, system transitions from [one regime] to [another]" — maybe already happening with RSA's α!
5. **Effective Hamiltonians**: "The free energy of linguistic representations is minimized by [specific formal structure]"

### Tractability Assessment

| Component | Mathlib Support | LingLib Readiness | Priority |
|-----------|-----------------|-------------------|----------|
| **Futrell & Hahn formalization** | Entropy basics | CCG, DG exist | **High — builds on F&H** |
| **LanguageModel interface** | — | Would need to add | Tractable |
| **Coarse-graining operations** | Some measure theory | — | Tractable |
| **RSA emergence theorem** | Limits, approximation | RSA exists | Near-term |
| **Predictive info / bottleneck** | Would need entropy | Rate-distortion exists | Medium-term |
| **Probing formalization** | Linear algebra | — | Medium-term |
| **RG flow formalization** | Would need dynamics | — | Long-term |
| **Full emergence theory** | Substantial | — | Research frontier |

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

### Connection to Algebraic Metatheory

The two research frontiers connect:

- **Algebraic metatheory**: Structure of RSA *itself* (lattices, fixed points, tropical limits)
- **Neural-symbolic emergence**: RSA as *coarse-graining* of neural models

Together they ask: What is the algebraic structure of the effective theory, and how does it emerge from the microscopic dynamics?

The α → ∞ limit appears in both:
- Algebraic: RSA becomes tropical/categorical
- Emergence: Coarse-graining becomes sharper (less averaging)

### References

**Foundational**:
- **Futrell & Hahn (2025)** "Linguistic structure from a bottleneck on sequential information processing" *Nature Human Behaviour* — Key paper showing linguistic systematicity emerges from minimizing predictive information
- Tishby & Zaslavsky (2015) "Deep Learning and the Information Bottleneck Principle"

**Probing & Encoding**:
- Hewitt & Manning (2019) "A Structural Probe for Finding Syntax in Word Representations"
- Mechanistic interpretability: Elhage et al. (2021), Nanda et al. (2023)

**Mathematical Foundations**:
- Tensor networks: Pestun & Vlassopoulos (2017), Miller (2021)
- Renormalization in ML: Mehta & Schwab (2014) "An exact mapping between the Variational Renormalization Group and Deep Learning"

---

## Current State Assessment

### Working End-to-End Pipelines
- CCG → Montague → RSA/NeoGricean (scalar implicatures)
- Montague → RSA (scope ambiguity, reference games, hyperbole)
- Theory comparison: Numerals (LowerBound vs Bilateral)
- Theory comparison: RSA vs NeoGricean (agreement proofs)

### Selective Depth
| Area | Status |
|------|--------|
| Numerals | Full comparison infrastructure |
| Modals | Kratzer/Simple comparison exists but not RSA-integrated |
| Scalar implicatures | Works for simple cases |
| Embedded implicatures | DE blocking via Potts LU model, attitudes/conditionals/questions |
| Exhaustivity operators | Spector (2016) exhMW/exhIE equivalence, Fox & Spector (2018) economy |
| Context polarity | Grounded UE/DE with compositional tracking |
| Reference games | Frank & Goodman 2012 working |
| Scope ambiguity | Scontras & Pearl 2021 working |
| Hyperbole | Kao et al. 2014 working |

### Known Gaps (from review)
1. Fragment library problem—too much boilerplate to build scenarios
2. No automatic divergence detection across theories
3. Documentation is code-oriented, not researcher-oriented
4. Only CCG → semantics; HPSG/Minimalism stubs
5. Some proofs use `sorry` or `native_decide` instead of full proof terms

---

## Tier 1: Researchers Can Use It (MVP)

**Goal**: A pragmatics researcher can replicate a paper's RSA model in ~20 lines.

### 1.1 Fragment Library ✗ TODO

**Problem**: Building an RSA scenario requires ~100 lines of boilerplate (domain types, semantics, priors, enumerations).

**Solution**: Pre-built fragments that compose.

```
Core/Fragments/
├── ReferenceGames.lean     -- Objects, colors, shapes, utterances
├── ScalarContexts.lean     -- Some/all, or/and, might/must scales
├── ScopeScenarios.lean     -- QNP scope ambiguity setups
├── NumberDomains.lean      -- Discrete quantities (0-10 typical)
└── Combinators.lean        -- Compose fragments, add priors
```

**Test**: Can we express Frank & Goodman 2012 as:
```lean
def refGame := ReferenceGame.withContext
  [.blue_square, .blue_circle, .green_square]
  [.blue, .green, .square, .circle]

#eval RSA.L1 refGame.scenario .square
```

### 1.2 Scale Library ✗ TODO

**Problem**: Scales are hardcoded per phenomenon.

**Solution**: Reusable scale definitions.

```lean
-- In Core/Scales.lean
def hornQuantifiers : Scale QuantExpr := ⟨[.some, .most, .all], ...⟩
def fauconnierConnectives : Scale ConnExpr := ⟨[.or, .and], ...⟩
def degreeModifiers : Scale DegreeExpr := ⟨[.warm, .hot], ...⟩
```

### 1.3 Scenario Combinators ✗ TODO

**Problem**: Extending a scenario (add utterance, change prior) requires rebuilding from scratch.

**Solution**: Combinator functions.

```lean
def RSAScenario.withUtterances (s : RSAScenario U W) (us : List U') : RSAScenario (U ⊕ U') W
def RSAScenario.withPrior (s : RSAScenario U W) (p : W → ℚ) : RSAScenario U W
def RSAScenario.restrictWorlds (s : RSAScenario U W) (ws : List W) : RSAScenario U W
```

### 1.4 Documentation ✗ TODO

**Needs**:
1. **Tutorial**: Walk through building an analysis from scratch (30-60 min)
2. **Paper replications**: Worked examples mapping to real papers
   - Frank & Goodman 2012 (reference game)
   - Goodman & Stuhlmüller 2013 (simple/complex)
   - Scontras & Pearl 2021 (scope)
   - Kao et al. 2014 (hyperbole)
3. **Coverage statement**: Clear table of what's implemented vs. promissory

```
docs/
├── tutorial/
│   ├── 01-first-rsa-model.md
│   ├── 02-scalar-implicatures.md
│   └── 03-competing-analyses.md
├── replications/
│   ├── FrankGoodman2012.md
│   ├── GoodmanStuhlmuller2013.md
│   └── ScontrasPearl2021.md
└── coverage.md
```

### 1.5 Fill Critical Phenomenon Gaps ✗ PARTIAL

**Needed for credibility**:

| Gap | Current | Target |
|-----|---------|--------|
| Embedded implicatures (globalist/localist) | DE via Potts LU | Add Geurts' globalist analysis |
| Modal semantics → RSA | Kratzer/Simple exist separately | Integrate with RSA scenarios |
| HPSG/Minimalism → SemDerivation | Stubs only | Keep as stubs (defer) |

**Decision**: Focus on DE blocking and modal RSA integration. Defer HPSG/Minimalism.

---

## Tier 2: Comparison Infrastructure Works

**Goal**: `#eval findDivergences NeoGricean RSA scalarImplicatureData` returns something useful.

### 2.1 Automatic Divergence Detection ✗ TODO

```lean
-- In Core/Comparison.lean
structure TheoryDivergence where
  theory1 : String
  theory2 : String
  phenomenon : String
  divergingCases : List (String × (ℚ × ℚ))  -- case name, predictions

def findDivergences (t1 t2 : ImplicatureTheory) (data : PhenomenonData)
    : List TheoryDivergence
```

### 2.2 Three Deep Comparison Phenomena ✗ PARTIAL

**Need 3 phenomena with multiple theories fully implemented**:

| Phenomenon | Theories | Status |
|------------|----------|--------|
| **Numerals** | LowerBound, Bilateral | ✓ Comparison infrastructure done |
| **Scalar implicatures** | RSA, NeoGricean | ✓ Agreement proofs, need divergence cases |
| **Scope ambiguity** | Lifted-variable RSA, world-sensitive RSA | ✗ Need second approach |

**Alternative third phenomenon**: Hyperbole (literal vs QUD-sensitive RSA).

### 2.3 Empirical Adjudication Connections ✗ PARTIAL

**Current**: Geurts & Pouscoulous 2009 data exists but isn't wired to theory comparison.

**Target**:
```lean
-- Connect predictions to empirical rates
theorem rsa_matches_gp2009_verification :
    RSA.predictedRate verificationTask someAllPattern
    ≈ GeurtsPouscoulous2009.observedRate verificationTask someAllPattern
```

### 2.4 Coverage Matrix Automation ✗ TODO

The coverage matrix in CLAUDE.md is manually maintained. Auto-generate from:
```lean
#eval generateCoverageMatrix
-- Outputs markdown table of which theories prove which phenomena
```

---

## Tier 3: Proofs Are Meaningful

**Goal**: Proofs give the formalization credibility as formal linguistics.

### 3.1 Distribution Type Guarantees ✓ DONE

`Core/Distribution.lean` provides `ExactDist` with compile-time proofs:
- `sum_one : ∑ x, d.mass x = 1`
- `nonneg : ∀ x, 0 ≤ d.mass x`
- `toPMF`: Bridge to Mathlib's PMF

### 3.2 CCG Generative Capacity Proofs ✗ PARTIAL

**Current**: `ccg_strictly_more_expressive_than_cfg` uses `sorry`.

**Target**: Full proof that CCG generates {aⁿbⁿcⁿdⁿ} via pumping lemma argument.

**Priority**: Medium. The infrastructure is there; filling proofs is incremental.

### 3.3 CCG-Montague Homomorphism ✓ DONE

`CCG/Homomorphism.lean` proves:
- `fapp_sem`, `bapp_sem`: Application = function application
- `fcomp_sem`: Composition = B combinator
- `ccgHomomorphism`: All properties hold together

### 3.4 Grounding Theorems ✓ PARTIAL

**Done**:
- `RSA/Intensional.lean`: L0 uses compositional meaning
- `RSA/ScontrasPearl2021.lean`: Meaning matches WorldMeaning

**Remaining**: Grounding proofs for other RSA models (PottsLU, AttitudeEmbedding, etc.)

---

## Tier 4: Maintainable and Extensible

**Goal**: System scales with contributors and catches regressions.

### 4.1 Mathlib Integration ✓ PARTIAL

Using: `ℚ`, `Finset`, `Fintype`, basic algebra

Could use more: `PMF`, measure theory, topology (for limits)

### 4.2 Clear Extension Patterns ✗ TODO

**Need documentation**:
- How to add a new syntactic theory
- How to add a new semantic analysis
- How to add a new RSA model variant
- How to add empirical data and connect to predictions

### 4.3 CI for Cross-Theory Regressions ✗ TODO

The whole point is catching when adding phenomenon X breaks theory Y.

```yaml
# .github/workflows/test.yml
- name: Build all theories
- name: Run theory comparison tests
- name: Check coverage matrix didn't shrink
```

---

## Phase Mapping (Review Tiers → Work Items)

### Immediate (Tier 1 MVP)
1. Fragment library (Core/Fragments/)
2. Scale library (Core/Scales.lean)
3. Tutorial documentation (docs/tutorial/)
4. Paper replication docs (docs/replications/)

### Near-term (Tier 2 Comparison)
1. `findDivergences` function
2. Third deep comparison phenomenon
3. Wire Geurts & Pouscoulous data to comparison
4. Auto-generate coverage matrix

### Medium-term (Tier 3 Proofs)
1. Fill CCG generative capacity proofs
2. Add grounding proofs to remaining RSA models
3. Replace `native_decide` with full proofs where meaningful

### Ongoing (Tier 4 Maintenance)
1. Extension pattern documentation
2. CI setup
3. Mathlib integration as needed

---

## Phase Mapping (North Stars → Work Items)

### Immediate: Binding Theory Unification
1. Audit `Minimalism/Coreference.lean`, `HPSG/Coreference.lean`, `DependencyGrammar/Coreference.lean`
2. Identify common test suite (Phenomena/Coreference/Data.lean)
3. Draft `Comparisons/BindingTheories.lean` with comparison theorem statement
4. Fill lemmas as needed to complete proof (or characterize divergence)

### Near-term: Scope Freezing
1. Extend `Montague/Scope.lean` with freezing configurations
2. Formalize QR clause-boundedness in Minimalism
3. Formalize derivational constraints in CCG
4. Prove both predict freezing (or find divergence)

### Medium-term: Exhaustivity Infrastructure
1. `Theories/Exhaustivity/EXH.lean` — Fox's exhaustivity operator
2. `Theories/Exhaustivity/Alternatives.lean` — Katzir's algorithm
3. `Theories/Exhaustivity/InnocentExclusion.lean` — IE computation
4. `Theories/Exhaustivity/InnocentInclusion.lean` — Bar-Lev & Fox

### Medium-term: Question Semantics
1. `Montague/Questions.lean` — Hamblin alternatives / partition semantics
2. RSA over question-answer pairs
3. Exhaustivity derivation theorem

### Long-term: RSA ≅ EXH Characterization
1. Formalize α → ∞ limit behavior
2. Prove scalar implicature equivalence under conditions
3. Characterize embedded implicature divergence
4. Identify empirically decisive test cases

### Long-term: Algebraic Metatheory
1. Formalize lexicon lattice (⟦·⟧₁ ≤ ⟦·⟧₂ iff ∀u. ⟦u⟧₁ ⊆ ⟦u⟧₂)
2. Prove Horn scale → implicature strength is monotone
3. Characterize α → ∞ limit as tropical semiring
4. Investigate RSA fixed-point structure (Tarski/Banach)
5. Explore information-geometric structure of L(·|u) manifold

### Medium-term: Futrell & Hahn Formalization
1. Define predictive information I(past; future) over sequences
2. Prove CCG/DG structures minimize predictive info among compositional representations
3. Prove dependency locality ↔ predictive information relationship
4. Connect to existing rate-distortion work in RSA

### Long-term: Neural-Symbolic Emergence
1. Define minimal `LanguageModel` interface (next-token distributions)
2. Define coarse-graining operations (discretization, marginalization)
3. Prove RSA emerges from LLM under coarse-graining (ε-approximation)
4. Formalize "syntax is linearly encoded" (probing classifiers)
5. Investigate information bottleneck characterization of syntax
6. Explore RG fixed-point interpretation of formal grammar

### In Progress: Presupposition Projection
1. ✓ Schlenker local context computation
2. ✓ Tonhauser taxonomy derivation (SCF × OLE → 4 classes)
3. ✓ Belief embedding for OLE
4. ✓ Degen & Tonhauser empirical data
5. Connect to soft/hard trigger literature (Romoli, Abusch)
6. RSA-style model for gradient projection

### Medium-term: Fragment Lexicon with Projection
1. Define `AttitudeLexEntry` structure (semantics + projection + entailment)
2. Implement entries for 20 D&T predicates
3. Compositional derivation of embedded presuppositions
4. Verify projection behavior matches empirical data
5. Connect to BeliefEmbedding.lean machinery

### Long-term: Speech Acts
1. Define illocutionary force types (assertion, question, command, promise)
2. Formalize felicity conditions (Austin/Searle)
3. Social/deontic modality (what speech acts create)
4. RSA perspective: speech acts as rational social actions
5. Case studies: promises, threats, bets

---

## Completed

- [x] Intensional Montague Semantics (`Montague/Intensional.lean`)
- [x] RSA with compositional meanings (`RSA/Intensional.lean`)
- [x] Grounding theorems for L0 (`RSA/Intensional.lean`)
- [x] Distribution type with proofs (`Core/Distribution.lean`)
- [x] RSA DE context handling (`RSA/PottsLU.lean`)
- [x] QUD infrastructure (`Core/QUD.lean`)
- [x] Hyperbole model (`RSA/KaoEtAl2014.lean`)
- [x] Parameterized Lexicon: Numerals (`Montague/Lexicon/Numerals/`)
- [x] Parameterized Lexicon: Modals (`Montague/Lexicon/Modals/`)
- [x] CCG-Montague Homomorphism (`CCG/Homomorphism.lean`)
- [x] RSA-NeoGricean Comparison (`Comparisons/RSANeoGricean.lean`)
- [x] Scope ambiguity RSA (`RSA/ScontrasPearl2021.lean`)
- [x] Reference game RSA (`RSA/FrankGoodman2012.lean`)
- [x] Cross-serial dependencies (`CCG/CrossSerial.lean`)
- [x] Formal language theory infrastructure (`Core/FormalLanguageTheory.lean`)
- [x] Type-safe scales (`QuantExpr`/`ConnExpr`)
- [x] Embedded implicatures: DE, attitudes, conditionals, questions
- [x] Presupposition projection infrastructure (Schlenker local contexts, Tonhauser taxonomy)
- [x] Degen & Tonhauser (2021) empirical data on factive predicates

---

## Deferred

These are valuable but not on the critical path to researcher usability:

- **HPSG/Minimalism → SemDerivation**: Syntax expansion beyond CCG
- **Sentence processing**: Incremental interpretation
- **B² generalized composition**: 3+ verb cross-serial
- **Full Horn (1972)**: Scale reversal, forced vs invited inference
- **Scope-word order interactions**: Dutch/German data
- **Imprecision/homogeneity**: Haslinger 2024 integration

### Selectional Restrictions / Category Mistakes (potential future phenomenon)

The `HasColor`/`HasShape` typeclasses in `Montague/Lexicon/Features.lean` suggest a type-theoretic approach to **selectional restrictions** and **category mistakes** (Chomsky's "colorless green ideas"):

**Core insight**: Only entities implementing `HasColor` can have color predicates meaningfully applied:
```lean
-- Ideas don't implement HasColor, so this fails to typecheck:
-- Feature.appliesTo (.color .green) someIdea  -- Error: no HasColor Idea instance
```

**Connections**:
- **Ryle's category mistakes**: "The number 7 is green" is infelicitous, not false
- **Sortal restrictions**: Predicates select for arguments of appropriate semantic types
- **Pustejovsky's Generative Lexicon**: Typed feature structures encode selectional restrictions

**Potential extensions**:
```lean
class HasMood (E : Type) where mood : E → Mood       -- Only sentient beings
class HasTemperature (E : Type) where temp : E → Temp -- Only physical objects
```

This would make "angry rock" or "cold number" fail to typecheck, capturing that they're infelicitous rather than false.

**Research question**: Can typeclass constraints model the full range of selectional restriction phenomena? How does this interact with coercion ("the ham sandwich wants his check")?

### Hot Topics (potential future North Stars)

These are active research areas (2020-2025) that could become targets once core infrastructure is in place:

- **Presupposition triggering**: Experimental data (Bade, Schlenker, Chemla 2024) shows speakers productively assign presuppositions to novel words
- **Soft vs hard triggers**: Romoli, Abusch — different projection behaviors
- **Modal anchoring**: Kratzer's framework extended to RSA contexts
- **Unconditionals**: "Whoever goes, it'll be fun" — understudied in formal pragmatics
- **Plurals & distributivity**: Link semantics + RSA for collective/distributive readings
- **Mention-some vs mention-all**: Question answerhood with pragmatic variation

### Presupposition Projection (In Progress)

**Current infrastructure**:
- `Core/CommonGround.lean` — Context sets, Stalnaker update
- `Core/Presupposition.lean` — PrProp type, filtering connectives
- `Montague/Projection/LocalContext.lean` — Schlenker (2009) local context computation
- `Montague/Projection/BeliefEmbedding.lean` — OLE derivation via belief local contexts
- `Montague/Projection/TonhauserDerivation.lean` — Tonhauser et al. (2013) taxonomy derivation
- `Phenomena/Presuppositions/ProjectiveContent.lean` — SCF/OLE classification
- `Phenomena/Factives/DegenTonhauser2021.lean` — Empirical projection ratings

**Key findings formalized**:
- Tonhauser taxonomy (Class A/B/C/D) derived from SCF × OLE
- Schlenker's local satisfaction explains filtering
- Belief embedding explains OLE (attitude holder attribution)
- Degen & Tonhauser: No categorical factive/nonfactive distinction

**Open questions**:
- How to model gradient projection (RSA-style?)
- Connect to soft/hard trigger literature
- Fragment lexicon with projection properties per predicate

### Fragment Lexicon with Projection Properties (Long-term Vision)

**Goal**: Build a fragment where attitude verbs have:
1. Compositional semantics (Montague-style λ-terms)
2. Projection properties (Tonhauser class or empirical rating)
3. Entailment properties (from Degen & Tonhauser inference data)

**Architecture**:
```
Theories/Montague/Lexicon/Attitudes/
├── Basic.lean           -- LexicalEntry structure with projection
├── Factives.lean        -- know, discover, realize, etc.
├── Semifactives.lean    -- stop, continue, etc.
├── Communication.lean   -- say, tell, announce, etc.
└── Composition.lean     -- How projection composes under embedding
```

**Example entry**:
```lean
def know : AttitudeLexEntry where
  semantics := λ p agent w => ∀ w' ∈ Dox agent w, p w'
  projectionClass := .classC  -- SCF=no, OLE=yes
  projectionRating := 0.84    -- From Degen & Tonhauser Exp 1a
  inferenceRating := 0.90     -- From Degen & Tonhauser Exp 2a
```

**Downstream check**: Derive "John believes Mary stopped smoking" compositionally and verify:
- Presupposition "Mary used to smoke" attributed to John (OLE=yes)
- Projection strength matches empirical data

### Speech Acts (Long-term Goal)

**Ultimate target**: Formal analysis of performatives (promises, threats, requests, etc.)

**Why interesting**:
- Speech acts are where syntax, semantics, and pragmatics truly interact
- Classic question: Are performatives truth-conditional or not?
- RSA perspective: Speech acts as rational actions with social effects

**Building blocks needed**:
1. Illocutionary force (assertion, question, command, promise, etc.)
2. Social/deontic modality (obligations, permissions created by speech acts)
3. Speaker intentions and hearer recognition
4. Felicity conditions (Austin/Searle)

**Potential architecture**:
```
Theories/SpeechActs/
├── Basic.lean           -- Illocutionary acts, perlocutionary effects
├── Performatives.lean   -- "I promise", "I bet", "I name this ship"
├── Directives.lean      -- Commands, requests, suggestions
├── Commissives.lean     -- Promises, threats, offers
└── RSAIntegration.lean  -- Speech acts as rational social actions
```

**Research question**: Can RSA derive speech act felicity from rational social coordination?

### Graded/Quantitative Theories (Long-term Infrastructure)

**The problem**: Many phenomena show gradient behavior (projection, scope preferences, SI rates) but current theories make categorical predictions.

**Current approach**: Encode orderings and negative findings (no categorical gap), check theories for *consistency* with orderings.

**Long-term vision**: Support truly quantitative theories that predict distributions, not just orderings.

**What this would require**:
- Item-level empirical data (not just predicate means)
- Probabilistic theories making numerical predictions
- Statistical inference machinery (likely external to Lean)

**Architectural decision**: LingLib focuses on categorical/ordering checks. Quantitative model fitting belongs in external tools (R/Python) that can import Lean-verified theory structure.

**Possible bridge**: Export Lean-verified RSA model structure to Python/WebPPL for fitting, import fit parameters back for consistency checks.

---

## Success Criteria

### For v1.0 Release
1. **Fragment test**: Frank & Goodman 2012 in ≤30 lines
2. **Comparison test**: `findDivergences RSA NeoGricean data` works
3. **Documentation test**: New user can build first model in <1 hour with tutorial
4. **Proof test**: No `sorry` in core theory files
5. **Replication test**: 4 papers fully replicated with verified predictions

### For Publication
1. Architecture description with formal properties
2. 2-3 deep case studies showing comparison value
3. Comparison with existing tools (webppl-rsa, rational-speech-acts)
4. Clear statement of limitations and future work

### For North Stars
1. **Binding unification**: Theorem proving 3 syntactic theories agree on coreference (or characterization of divergence)
2. **Scope freezing**: Proof that Minimalism and CCG both predict freezing via different mechanisms
3. **RSA/EXH equivalence**: Formal characterization of when grammatical and pragmatic theories converge
4. **Empirical adjudication**: At least one case where formalization reveals which theory is empirically correct

### For Algebraic Metatheory
1. **Lexicon lattice**: Formalize refinement order on lexicons, prove it transfers to inference structure
2. **Tropical limit**: Prove RSA α → ∞ coincides with game-theoretic best response
3. **Fixed-point existence**: Prove RSA iteration converges (Banach or Tarski style)
4. **B&P-style theorem**: Find an intersection/union theorem for some RSA-relevant structure

### For Neural-Symbolic Emergence
1. **Futrell & Hahn formalization**: Prove CCG/DG minimizes predictive information (formalizing their empirical result)
2. **RSA emergence**: Prove RSA is ε-approximation of coarse-grained LLM predictions
3. **Syntax encoding**: Formalize "syntax trees are linearly encoded in hidden states"
4. **Information bottleneck**: Prove formal structure achieves rate-distortion optimality
5. **Universality**: Show different architectures converge to same formal structure under coarse-graining
