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

### Immediate (Tier 1 MVP) — ~4-6 weeks
1. Fragment library (Core/Fragments/)
2. Scale library (Core/Scales.lean)
3. Tutorial documentation (docs/tutorial/)
4. Paper replication docs (docs/replications/)

### Near-term (Tier 2 Comparison) — ~4-6 weeks after MVP
1. `findDivergences` function
2. Third deep comparison phenomenon
3. Wire Geurts & Pouscoulous data to comparison
4. Auto-generate coverage matrix

### Medium-term (Tier 3 Proofs) — Ongoing
1. Fill CCG generative capacity proofs
2. Add grounding proofs to remaining RSA models
3. Replace `native_decide` with full proofs where meaningful

### Ongoing (Tier 4 Maintenance)
1. Extension pattern documentation
2. CI setup
3. Mathlib integration as needed

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

---

## Deferred

These are valuable but not on the critical path to researcher usability:

- **HPSG/Minimalism → SemDerivation**: Syntax expansion beyond CCG
- **Sentence processing**: Incremental interpretation
- **B² generalized composition**: 3+ verb cross-serial
- **Full Horn (1972)**: Scale reversal, forced vs invited inference
- **RSA α → ∞ limit proof**: Requires analysis
- **Scope-word order interactions**: Dutch/German data
- **Imprecision/homogeneity**: Haslinger 2024 integration

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
