# Imprecision & Homogeneity: Formalization Roadmap

Based on Nina Haslinger's dissertation "Pragmatic Constraints on Imprecision" (2024?).

## Current Linglib Infrastructure

### What We Have
- **RSA framework** (Core/RSA.lean): L0/S1/L1 with exact rational arithmetic
- **QUD/Issue infrastructure** (Core/InformationStructure.lean): Partition type exists
- **Horn scales** (Theories/Montague/Scales.lean): Alternative sets for implicatures
- **Vagueness data** (Phenomena/Vagueness/Data.lean): Extensive, includes Kennedy typology
- **Comparison class** (Phenomena/ComparisonClass/Data.lean): Tessler & Goodman patterns
- **Numeral theory** (Theories/Montague/Lexicon/Numerals/): LowerBound vs Bilateral

### What's Missing (Theory Infrastructure)
1. **Trivalent/supervaluationist semantics** - truth-value gaps
2. **Parameter vectors** - parameterized semantic evaluation
3. **Syntactic complexity measures** - for form/meaning constraints
4. **Plural semantics** - sums, distributivity, Link-style
5. **Strong relevance predicate** - partition alignment
6. **Exhaustification operators** - exh with innocent inclusion

## Phase 1: Phenomena (Data Structures) — COMPLETE

All phenomena files created and building successfully (2026-01-26).

### 1.1 Homogeneity Gaps (Phenomena/Imprecision/Homogeneity.lean)
- [x] Plural definites: "The doors are open" vs "The doors aren't open"
- [x] Conjunctions: "Ann and Bert have red hair"
- [x] Summative predicates: "The flag is blue"
- [x] Conditionals: "They play if the sun shines"
- [x] Collective predicates: "The teachers met"
- [x] Cumulative predicates: "The teachers sent the students grades"

### 1.2 Non-Maximality (Phenomena/Imprecision/NonMaximality.lean)
- [x] SWITCHES scenarios (maximal vs non-maximal contexts)
- [x] BANK ROBBERY scenario (fine-grained non-maximality)
- [x] Issue-sensitivity patterns
- [x] All removes non-maximality
- [x] Strong relevance data structures

### 1.3 Numeral Imprecision (Phenomena/Imprecision/Numerals.lean)
- [x] Round vs non-round asymmetry (100 vs 99)
- [x] CARS scenarios (exact vs inexact contexts)
- [x] Negation constraint (Solt & Waldon 2019)
- [x] Game show scenario (multiple thresholds salient)
- [x] Granularity/scale data structures
- [x] Time expression patterns

### 1.4 Form/Meaning Correspondences (Phenomena/Imprecision/FormMeaning.lean)
- [x] Complexity pairs: "the doors" / "all the doors"
- [x] Complexity pairs: "100 cars" / "exactly 100 cars"
- [x] Complexity pairs: "Ann and Bert" / "both Ann and Bert"
- [x] Unattested patterns: *DEF [all doors] → "the doors"
- [x] Markedness data structures
- [x] Cross-linguistic patterns

### 1.5 Projection Patterns (Phenomena/Imprecision/Projection.lean)
- [x] Under `every`: strong reading
- [x] Under `no`: strong reading, limited non-maximality
- [x] Under `exactly one`: strong reading
- [x] Under `not every`: permits non-maximality (Augurzky et al. 2023)
- [x] Križ & Chemla (2015) experimental patterns
- [x] QUD manipulation data (Augurzky et al. 2023)
- [x] No vs not-every asymmetry data

### 1.6 Inference Preservation (Phenomena/Imprecision/InferencePreservation.lean)
- [x] Conjunction entailments: "A and B are P" |= "A is P"
- [x] Numeral alternatives: 99 vs 100 asymmetry
- [x] Blocked imprecision patterns
- [x] Alternative set asymmetry data
- [x] Collective/cumulative exceptions

### 1.7 Module Integration (Phenomena/Imprecision/Basic.lean)
- [x] Proper attribution to Nina Haslinger
- [x] Comprehensive references section
- [x] Re-exports for convenient access
- [x] Phenomena summary statistics
- [x] Imported in main Linglib.lean

## Phase 2: Theoretical Infrastructure — PROMISSORY NOTES

### 2.1 Core/Trivalent.lean
```lean
-- PROMISSORY NOTE
inductive TruthValue where
  | true | false | gap
  deriving DecidableEq, Repr

def strongKleeneNot : TruthValue → TruthValue
def strongKleeneAnd : TruthValue → TruthValue → TruthValue
def strongKleeneOr : TruthValue → TruthValue → TruthValue
def supertruth (interpretations : Set (α → Bool)) (p : α → TruthValue) : TruthValue
```

### 2.2 Core/ParameterVector.lean
```lean
-- PROMISSORY NOTE
structure ParameterVector where
  homogeneityParams : ℕ → (Set α → Set α)  -- f^i
  granularityParams : ℕ → ℚ                 -- d^i for numerals
  alternativeSets : Expr → Set Expr         -- ALT function
  selectionFunctions : Prop → Set Prop → Prop  -- S_p

def potentiallyImprecise (φ : Expr) : Prop :=
  ∃ v v', meaning φ v ≠ meaning φ v'
```

### 2.3 Core/StrongRelevance.lean
```lean
-- PROMISSORY NOTE
def stronglyRelevant (p : Prop) (I : Partition) : Prop :=
  ∃ cells ⊆ I.cells, p ↔ (∃ c ∈ cells, c)

-- Derives non-maximality availability from QUD
def nonMaxAvailable (sentence : Sentence) (qud : Partition) : Bool
```

### 2.4 Core/SyntacticComplexity.lean
```lean
-- PROMISSORY NOTE
def complexity : Expr → ℕ  -- tree size, node count, etc.
def moreComplex (φ ψ : Expr) : Prop := complexity φ > complexity ψ
def structuralAlternatives (φ : Expr) : Set Expr  -- Katzir (2007)
```

### 2.5 Theories/Imprecision/Exhaustification.lean
```lean
-- PROMISSORY NOTE
def innocentlyExcludable (p : Prop) (alts : Set Prop) : Set Prop
def innocentlyIncludable (p : Prop) (alts : Set Prop) : Set Prop
def exh (φ : Expr) (alts : Set Expr) : TruthValue
-- exh can introduce gaps via innocent inclusion
```

### 2.6 Theories/Imprecision/PluralSemantics.lean
```lean
-- PROMISSORY NOTE
-- Link-style plural semantics
def atomicPart (x : Entity) (y : Entity) : Prop
def sum : Entity → Entity → Entity
def distributivity : (Entity → Prop) → (Entity → Prop)
def cumulativity : (Entity → Entity → Prop) → (Entity → Entity → Prop)
```

## Phase 3: Theoretical Predictions — PROMISSORY NOTES

### 3.1 NO NEEDLESS MANNER VIOLATIONS
```lean
-- PROMISSORY NOTE
theorem manner_constraint :
  ∀ φ ψ, truthEquivalent φ ψ →
    moreComplex ψ φ → (morePrecise ψ φ ∨ blocked φ)

-- Derives: "all the doors" more complex → must be more precise than "the doors"
-- Derives: no language has DEF that adds imprecision
```

### 3.2 INFERENCE PRESERVATION
```lean
-- PROMISSORY NOTE
theorem inference_preservation :
  ∀ φ ψ ∈ alternatives φ,
    impreciseConstrual φ c →
    (preciseConstrual φ |= ψ) → (impreciseConstrual φ c |= ψ)

-- Derives: 99 can't be imprecise (would need to entail ¬100)
-- Derives: "A and B are P" can't non-max to "only A is P"
```

### 3.3 Projection Predictions
```lean
-- PROMISSORY NOTE
theorem no_vs_not_every_asymmetry :
  -- `no` resists non-maximality but `not every` permits it
  -- despite both being downward-entailing
  ∀ φ, ¬nonMaxAvailable (no φ) ∧ nonMaxAvailable (not_every φ)

-- Explanation: `not every` has scalar implicature creating
-- non-monotonic context where embedded exh can strengthen
```

### 3.4 Homogeneity-Imprecision Dissociation
```lean
-- PROMISSORY NOTE
theorem gaps_without_nonmax :
  -- Some constructions have gaps but not non-maximality
  ∃ φ, hasHomogeneityGap φ ∧ ¬permitsNonMaximality φ

theorem nonmax_without_gaps :
  -- Some constructions have non-maximality but no clear gaps
  ∃ φ, permitsNonMaximality φ ∧ ¬hasHomogeneityGap φ
```

## Key References

### Primary Source
- Haslinger, N. (2024?). Pragmatic Constraints on Imprecision. Doctoral Dissertation.

### Homogeneity
- Löbner (2000): Polarity in natural language
- Križ (2015, 2016): Trivalent homogeneity
- Križ & Spector (2021): Supervaluationist approach
- Križ & Chemla (2015): Projection experiments

### Non-Maximality
- Lasersohn (1999): Pragmatic halos
- Malamud (2012): Plural definites
- Burnett (2017): Tolerance relations

### Numerals
- Krifka (2007): Approximate interpretation
- Sauerland & Stateva (2007): Scalar alternatives
- Solt (2014, 2018, 2023): Imprecise numerals
- Solt & Waldon (2019): Numerals under negation

### Exhaustification
- Bar-Lev (2021a): Exhaustification + pruning
- Bar-Lev & Fox (2020): Free choice, innocent inclusion
- Bassi, Del Pinal, & Sauerland (2021): Presuppositional exhaustification

### Experimental
- Augurzky et al. (2023): every/no/not every asymmetry
- Tieu, Križ, & Chemla (2019): Acquisition of homogeneity

### Complexity and Alternatives
- Horn (1984): Division of pragmatic labor
- Katzir (2007): Structurally-defined alternatives

## Success Criteria

### Phase 1 — COMPLETE
- [x] All phenomena data structures compile
- [x] Examples cover key patterns from dissertation
- [x] Clear separation of data from theoretical commitments
- [x] References to source literature
- [x] Proper attribution to Nina Haslinger
- [x] Module integrated into main Linglib

### Phase 2 — NOT STARTED
- [ ] Trivalent logic operational
- [ ] Parameter vectors can derive multiple construals
- [ ] Strong relevance computable for finite partitions
- [ ] Complexity measure defined
- [ ] Plural semantics formalized

### Phase 3 — NOT STARTED
- [ ] NO NEEDLESS MANNER VIOLATIONS derivable
- [ ] INFERENCE PRESERVATION derivable
- [ ] Projection patterns predicted from theory
- [ ] Dissociation predictions verified

## Notes

The phenomena documented here are **theory-neutral**. Multiple theoretical approaches
could derive the same predictions:

1. **Trivalent semantics** (Križ 2015): Gaps are primitive, non-max from context
2. **Supervaluationism** (Križ & Spector 2021): Gaps from multiple candidates
3. **Exhaustification** (Bar-Lev 2021): Gaps from innocent inclusion in exh

The data structures in Phase 1 are designed to be compatible with any of these
theoretical implementations. Future work should formalize at least one approach
and prove it derives the documented patterns.
