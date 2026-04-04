import Linglib.Theories.Semantics.Degree.Intensional
import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Comparison.Delineation
import Linglib.Phenomena.Comparison.Compare

/-!
# Von Stechow 1984: Comparing Semantic Theories of Comparison
@cite{von-stechow-1984}

Arnim von Stechow. Comparing Semantic Theories of Comparison.
Journal of Semantics 3(1-2): 1–77.

## Core Contribution

A systematic evaluation of seven semantic theories of the comparative
(Russell, Postal, Williams, Seuren, Lewis, Klein, Cresswell, Hellan)
against nine empirical phenomena, culminating in a synthesis that
combines Russellian definite descriptions with an ACTUALLY operator.

The key insight: Russell's ambiguity ("I thought your yacht was larger
than it is") is explained by the presence or absence of ACTUALLY in
the than-clause, NOT by scope differences of degree operators. This
is simpler and better motivated than competing scope-based analyses.

## Synthesis Rules (§XI)

- R1: Property abstraction — than/as-clauses determine properties of degrees
- R2: Nominalization — the Max operator makes a definite description
- R3: Adjectives as 2-place relations (individuals × degrees)
- R4: *more* / *-er* = addition: ⟦more⟧(d₁)(A⁰)(d₂)(x) iff A⁰(x, d₁ + d₂)
- R5: *as* = multiplication: ⟦as⟧(d₁)(A⁰)(d₂)(x) iff A⁰(x, d₁ · d₂)
- R6: *pos* with comparison class (average-based contextual standard)

-/

namespace Phenomena.Comparison.Studies.VonStechow1984

open Semantics.Degree.Intensional
open Semantics.Degree.Comparative (comparativeSem)
open Semantics.Degree.DegreeAbstraction (IsMaxDeg)
open Semantics.Degree.Differential (differentialComparative factorEquative)

-- ════════════════════════════════════════════════════
-- § 1. Descriptive Adequacy Scorecard (Table xvii, p. 4)
-- ════════════════════════════════════════════════════

/-- Theory families evaluated by von Stechow. -/
inductive TheoryFamily where
  | russellPostalWilliams   -- Russell 1905 / Postal 1974 / Williams 1977
  | seurenLewisKlein        -- Seuren 1973 / Lewis 1972 / Klein 1980
  | cresswell               -- Cresswell 1976
  | hellan                  -- Hellan 1981
  | synthesis               -- von Stechow's own proposal (§XI)
  deriving DecidableEq, Repr

/-- The nine phenomena used as evaluation criteria. -/
inductive Phenomenon where
  | russellAmbiguity        -- RA: "I thought your yacht was larger than it is"
  | ambiguousCounterfactual -- AC: "If she had smoked less, she'd be healthier"
  | npiLicensing            -- NPI: "cleverer than anyone"
  | quantConnectives        -- Q&C: "fatter than Düsseldorf or Stuttgart"
  | unwarrantedInference    -- UI: "fatter than Otto ⊬ fatter than everyone"
  | negativeQuantifiers     -- NQ: "*more intelligent than no one"
  | modalComparative        -- ◇: "A polar bear could be bigger than a grizzly"
  | differentialReadings    -- DR: "six inches taller than Mary"
  | iteratedModality        -- IM: "I thought Plato could have been more boring"
  deriving DecidableEq, Repr

/-- Adequacy scores from von Stechow's evaluation. -/
inductive Score where
  | plus       -- +  handles phenomenon
  | weakPlus   -- (+) handles with extra assumptions
  | plusMinus   -- +/− partially handles
  | weakMinus  -- (-) could potentially handle with modifications
  | minus      -- -  cannot handle
  | minusStar  -- -* cannot handle, serious deficiency
  deriving DecidableEq, Repr

structure ScorecardEntry where
  theory : TheoryFamily
  phenomenon : Phenomenon
  score : Score
  deriving Repr

-- UNVERIFIED: individual cell scores in this table should be checked
-- against Table xvii (p. 4) of the original paper. Theory family
-- groupings may also conflate scores that differ between individual
-- theories within a family (e.g., Seuren vs. Lewis vs. Klein).
/-- Von Stechow's descriptive adequacy scorecard (p. 4, Table xvii).
    Scores: Russell ((5)), Seuren/Lewis/Klein (3½), Cresswell (5), Hellan (3).
    The synthesis achieves 9/9. -/
def scorecard : List ScorecardEntry :=
  -- Russell / Postal / Williams
  [ ⟨.russellPostalWilliams, .russellAmbiguity,        .plus⟩
  , ⟨.russellPostalWilliams, .ambiguousCounterfactual,  .weakPlus⟩
  , ⟨.russellPostalWilliams, .npiLicensing,             .minusStar⟩
  , ⟨.russellPostalWilliams, .quantConnectives,         .minusStar⟩
  , ⟨.russellPostalWilliams, .unwarrantedInference,     .plus⟩
  , ⟨.russellPostalWilliams, .negativeQuantifiers,      .plus⟩
  , ⟨.russellPostalWilliams, .modalComparative,         .minusStar⟩
  , ⟨.russellPostalWilliams, .differentialReadings,     .minusStar⟩
  , ⟨.russellPostalWilliams, .iteratedModality,         .weakPlus⟩
  -- Seuren / Lewis / Klein
  , ⟨.seurenLewisKlein, .russellAmbiguity,        .plus⟩
  , ⟨.seurenLewisKlein, .ambiguousCounterfactual,  .minusStar⟩
  , ⟨.seurenLewisKlein, .npiLicensing,             .plus⟩
  , ⟨.seurenLewisKlein, .quantConnectives,         .plusMinus⟩
  , ⟨.seurenLewisKlein, .unwarrantedInference,     .minus⟩
  , ⟨.seurenLewisKlein, .negativeQuantifiers,      .weakMinus⟩
  , ⟨.seurenLewisKlein, .modalComparative,         .plus⟩
  , ⟨.seurenLewisKlein, .differentialReadings,     .minus⟩
  , ⟨.seurenLewisKlein, .iteratedModality,         .minus⟩
  -- Cresswell
  , ⟨.cresswell, .russellAmbiguity,        .plus⟩
  , ⟨.cresswell, .ambiguousCounterfactual,  .minusStar⟩
  , ⟨.cresswell, .npiLicensing,             .plus⟩
  , ⟨.cresswell, .quantConnectives,         .plus⟩
  , ⟨.cresswell, .unwarrantedInference,     .plus⟩
  , ⟨.cresswell, .negativeQuantifiers,      .plus⟩
  , ⟨.cresswell, .modalComparative,         .minusStar⟩
  , ⟨.cresswell, .differentialReadings,     .minusStar⟩
  , ⟨.cresswell, .iteratedModality,         .minus⟩
  -- Hellan
  , ⟨.hellan, .russellAmbiguity,        .plus⟩
  , ⟨.hellan, .ambiguousCounterfactual,  .minusStar⟩
  , ⟨.hellan, .npiLicensing,             .minus⟩
  , ⟨.hellan, .quantConnectives,         .minus⟩
  , ⟨.hellan, .unwarrantedInference,     .plus⟩
  , ⟨.hellan, .negativeQuantifiers,      .minus⟩
  , ⟨.hellan, .modalComparative,         .minus⟩
  , ⟨.hellan, .differentialReadings,     .plus⟩
  , ⟨.hellan, .iteratedModality,         .minus⟩
  -- Von Stechow's synthesis: handles all 9
  , ⟨.synthesis, .russellAmbiguity,        .plus⟩
  , ⟨.synthesis, .ambiguousCounterfactual,  .plus⟩
  , ⟨.synthesis, .npiLicensing,             .plus⟩
  , ⟨.synthesis, .quantConnectives,         .plus⟩
  , ⟨.synthesis, .unwarrantedInference,     .plus⟩
  , ⟨.synthesis, .negativeQuantifiers,      .plus⟩
  , ⟨.synthesis, .modalComparative,         .plus⟩
  , ⟨.synthesis, .differentialReadings,     .plus⟩
  , ⟨.synthesis, .iteratedModality,         .plus⟩
  ]

-- Von Stechow's synthesis handles all 9 phenomena.
#guard (scorecard.filter (λ e => e.theory == .synthesis && e.score == .plus)).length == 9

-- No other theory handles all 9.
#guard (scorecard.filter (λ e => e.theory == .cresswell && e.score == .plus)).length == 5

-- ════════════════════════════════════════════════════
-- § 2. Russell's Ambiguity via ACTUALLY (§§II–V)
-- ════════════════════════════════════════════════════

-- Cross-reference: @cite{heim-2001} independently notes the Russell
-- ambiguity is not DegP-scope. Von Stechow's ACTUALLY analysis is
-- the mechanism behind Heim's observation.

-- The two readings distinguished by ACTUALLY. Instantiated at
-- `World := Bool` (actual = true, belief = false) for concreteness.
section RussellExample

  private def yachtLength : Bool → Unit → ℕ
    | true,  () => 5   -- actual length
    | false, () => 8   -- believed length (John's overestimate)

  /-- De re reading (with ACTUALLY): John's belief-world length (8)
      exceeds the actual length (5). Consistent thought. -/
  example : deReComparative yachtLength true false () := by
    simp [deReComparative, actuallyDeg, Core.Intension.evalAt, yachtLength]

  /-- De dicto reading: contradictory by `deDicto_absurd`. -/
  example : ¬ deDictoComparative yachtLength false () :=
    deDicto_absurd yachtLength false ()

end RussellExample

-- ════════════════════════════════════════════════════
-- § 3. Ambiguous Counterfactuals (§III)
-- ════════════════════════════════════════════════════

/-- "If Mary had smoked less than she did, she would be healthier
    than she is" (p. 12, ex. 26). The nontrivial reading requires
    ACTUALLY in the than-clauses of both antecedent and consequent:
    the standards of comparison are actual-world values. -/
structure AmbiguousCounterfactualDatum where
  sentence : String
  trivialReading : String
  informativeReading : String
  requiresActually : Bool
  deriving Repr

def ambiguousCounterfactual : AmbiguousCounterfactualDatum :=
  { sentence := "If Mary had smoked less than she did, she would be healthier than she is"
  , trivialReading := "antecedent and consequent both inconsistent (vacuously true)"
  , informativeReading := "if actual smoking were reduced, actual health would improve"
  , requiresActually := true }

-- ════════════════════════════════════════════════════
-- § 4. NPI Licensing in Than-Clauses (§VI)
-- ════════════════════════════════════════════════════

-- Von Stechow's explanation: the Max operator makes the than-clause
-- a downward-entailing environment. Replacing the than-clause S̄ with
-- a more informative S̄' yields a valid inference — the DE condition.
--
-- This connects two existing results:
-- 1. `Comparative.comparative_than_DE` (generic DE of quantification)
-- 2. `Ladusaw1979.licensingStrength .comparativeThan = .downwardEntailing`
--
-- Von Stechow shows (p. 28–30) that Cresswell's λ-abstraction approach
-- is DE, while Russell/Postal/Hellan's are not — explaining why Cresswell
-- correctly predicts NPI licensing.

/-- NPI data from §VI (pp. 26–27). -/
structure NPIDatum where
  sentence : String
  npiItem : String
  grammatical : Bool
  deriving Repr

def npiData : List NPIDatum :=
  [ ⟨"Ede is cleverer than anyone of us", "anyone", true⟩
  , ⟨"Max is as well as ever", "ever", true⟩
  , ⟨"*Any of my friends could ever solve these problems faster than Ede", "any/ever", false⟩
  , ⟨"Ede could solve these problems faster than any of my friends could ever do", "any/ever", true⟩
  , ⟨"You have already got less support than he has", "already", true⟩
  , ⟨"*He has got more support than you already have", "already", false⟩
  ]

-- ════════════════════════════════════════════════════
-- § 5. Quantifiers and Connectives in Than-Clauses (§VII)
-- ════════════════════════════════════════════════════

/-- "Konstanz is nicer than Düsseldorf or Stuttgart" entails
    "Konstanz is nicer than Düsseldorf and Stuttgart" (p. 2, ex. v).
    The than-clause maximum over a disjunctive standard is the max
    of the individual maxima: exceeding max(μb, μc) entails exceeding
    both individually. -/
theorem disjunction_to_conjunction_in_than {D : Type*} [LinearOrder D]
    (μa μb μc : D) (h : μa > μb ⊔ μc) :
    μa > μb ∧ μa > μc :=
  ⟨lt_of_le_of_lt le_sup_left h, lt_of_le_of_lt le_sup_right h⟩

/-- Blocking unwarranted inferences (p. 3, ex. vii):
    "Ede is fatter than Max" does NOT entail "Ede is fatter than everyone."
    Only Russell's theory correctly blocks this — the definite description
    ιd[everyone is d-fat] may not denote if people differ in fatness. -/
structure InferenceDatum where
  premise : String
  conclusion : String
  valid : Bool
  explanation : String
  deriving Repr

def inferences : List InferenceDatum :=
  [ ⟨"Konstanz is nicer than Düsseldorf or Stuttgart"
   , "Konstanz is nicer than Düsseldorf and Stuttgart"
   , true, "DE-ness: ∨ → ∧ in DE contexts"⟩
  , ⟨"Ede is fatter than anyone of us"
   , "Ede is fatter than everyone of us"
   , true, "existential → universal in DE context"⟩
  , ⟨"Ede is fatter than Max"
   , "Ede is fatter than everyone"
   , false, "Russell: ιd[everyone is d-fat] doesn't denote unless all same degree"⟩
  ]

/-- Negative quantifiers (p. 3, ex. viii–ix):
    "*Ede is more intelligent than no one of us" — in Russell's theory,
    the definite description ιd[no one is d-intelligent] doesn't denote
    (there's no maximal degree of zero-person intelligence).
    In Cresswell's theory, (99) is a logical falsehood. -/
def negativeQuantifierData : List InferenceDatum :=
  [ ⟨"Irene is prettier than neither Ede nor Senta"
   , "(oddness explained by: ιd[neither is d-pretty] fails to denote)"
   , false, "Russell: definite description fails; Cresswell: logical falsehood"⟩
  , ⟨"Irene is prettier than no one of us"
   , "(oddness explained by: no maximal degree of zero-person prettiness)"
   , false, "Russell: ιd[no one is d-pretty] doesn't denote"⟩
  ]

-- ════════════════════════════════════════════════════
-- § 6. Modal Comparatives (§VIII)
-- ════════════════════════════════════════════════════

/-- "A polar bear could be bigger than a grizzly bear could be" (p. 3).
    Only Seuren/Lewis can treat this natively. Russell's theory fails
    because the definite terms don't denote (indefinitely many possible
    sizes). Von Stechow's synthesis repairs Russell via the Max operator:
    compare max possible sizes across ◇-accessible worlds. -/
structure ModalComparativeDatum where
  sentence : String
  analysis : String
  theoriesThatHandle : List String
  deriving Repr

def modalComparativeData : ModalComparativeDatum :=
  { sentence := "A polar bear could be bigger than a grizzly bear could be"
  , analysis := "max.d[◇(polar bear is d-big)] > max.d[◇(grizzly bear is d-big)]"
  , theoriesThatHandle := ["Seuren/Lewis (natively)", "Russell + Max (repaired)", "von Stechow synthesis"] }

/-- Modal comparative: if the max possible A-degree exceeds the max
    possible B-degree, there is a witness world where A beats every
    possible B (via `maxDeg_witness` from the theory layer). -/
theorem modalComparative_from_maxDeg {W : Type*} {D : Type*} [LinearOrder D]
    (acc : Set W) (μPolar μGrizzly : W → D)
    (maxP maxG : D)
    (hmaxP : IsMaxDegOverWorlds acc μPolar maxP)
    (hmaxG : IsMaxDegOverWorlds acc μGrizzly maxG)
    (hgt : maxP > maxG) :
    ∃ w ∈ acc, ∀ v ∈ acc, μPolar w > μGrizzly v :=
  maxDeg_witness acc μPolar μGrizzly maxP maxG hmaxP hmaxG hgt

-- ════════════════════════════════════════════════════
-- § 7. Klein Criticism (§XI)
-- ════════════════════════════════════════════════════

/-- @cite{klein-1980}'s degree-free approach cannot handle:
    1. Differential readings: "John is six inches taller than Mary"
    2. Factor equatives: "Ede is twice as fat as Angelika"
    3. Cross-dimensional: "Ede is more tall than broad"

    Klein's framework has no degree ontology, so metric information
    (distances, ratios) cannot be expressed. The existing
    `klein_measure_equivalence` shows Klein agrees on simple
    comparatives (via `measureDelineation`), but this agreement
    breaks down for measure phrase constructions.

    This limitation motivates von Stechow's R4/R5 (addition and
    multiplication on degrees) which Klein cannot express. -/
structure KleinLimitation where
  sentence : String
  phenomenon : String
  explanation : String
  deriving Repr

def kleinLimitations : List KleinLimitation :=
  [ ⟨"John is six inches taller than Mary"
   , "differential reading"
   , "Klein has no degrees to measure the 6-inch gap"⟩
  , ⟨"Ede is twice as fat as Angelika"
   , "factor equative"
   , "Klein has no ratio structure (no meaningful zero point)"⟩
  , ⟨"Ede is more tall than broad"
   , "cross-dimensional comparison"
   , "Klein compares delineation boundaries, but tall and broad have incommensurable comparison classes"⟩
  ]

/-- Klein agrees with von Stechow's synthesis on simple comparatives:
    the degree comparison μ(a) > μ(b) induces a Klein ordering via
    `measureDelineation` (from `Compare.klein_measure_equivalence`).
    The divergence is only on differential and factor constructions. -/
theorem klein_agrees_on_simple {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (cc : Set Entity) (a b : Entity)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    comparativeSem μ a b .positive ↔
      Semantics.Comparison.Delineation.ordering
        (Semantics.Comparison.Delineation.measureDelineation μ) cc a b :=
  Phenomena.Comparison.Compare.klein_measure_equivalence μ cc a b ha hb

-- ════════════════════════════════════════════════════
-- § 8. Cross-Category Generalization (§XI.4)
-- ════════════════════════════════════════════════════

/-- Von Stechow's rules R7–R8 extend *more* uniformly across categories.
    Plural nouns: "more toads" = |X| > n (cardinality as degree).
    Mass nouns: "more gold" = amount(X) > d.
    Adverbs: "more loudly" = loudness(e) > d.
    The comparative morpheme is category-blind — only the measure
    function μ varies. -/
structure CrossCategoryDatum where
  sentence : String
  category : String
  measureFunction : String
  deriving Repr

def crossCategoryData : List CrossCategoryDatum :=
  [ ⟨"At least 6 more toads than frogs croak", "plural noun", "|X| (set cardinality)"⟩
  , ⟨"Ede owns at most 3 ounces more gold than Kurt", "mass noun", "amount(X) (totality)"⟩
  , ⟨"Tristan yells three times as loudly as Otto", "adverb", "loudness(e) (event measure)"⟩
  , ⟨"More silly lectures have been given by more silly professors than I expected"
   , "multihead comparative", "cardinality on both subject and by-phrase"⟩
  ]

-- ════════════════════════════════════════════════════
-- § 9. *too* as Counterfactual Comparative (§XI.6)
-- ════════════════════════════════════════════════════

/-- R13: *too* is a counterfactual comparative morpheme.
    "This pack is at least 50 kg too heavy to lift" means:
    if it were lighter by 50 kg, one could lift it.

    R13 (p. 69): ⟦too⟧(d₁)(A⁰)(p)(x) = the max.d [x is d-A⁰]
    λd₂ [p □→ A⁰(x, d₂ − d₁)]. Here d₂ is the actual degree and
    d₁ is the excess; the counterfactual threshold is d₂ − d₁.

    This is `DegPType.excessive` from `Degree.Core` — the degree
    construction where the differential measures the excess over a
    counterfactual threshold. Von Stechow's analysis shows that
    *too* and *-er* share the same additive structure (R4),
    differing only in that *too*'s standard comes from a
    counterfactual rather than a than-clause. -/
structure TooCounterfactualDatum where
  sentence : String
  differential : String
  counterfactualBase : String
  degPType : Semantics.Degree.DegPType
  deriving Repr

def tooData : List TooCounterfactualDatum :=
  [ ⟨"This pack is at least 50 kg too heavy to lift"
   , "50 kg"
   , "if one could lift this pack, it would be at most d₂-heavy"
   , .excessive⟩
  , ⟨"The weather is too good to stay at home"
   , "(contextually supplied)"
   , "if the weather were d₂-good, one would stay at home"
   , .excessive⟩
  ]

-- All *too* data entries are of the excessive DegP type.
#guard tooData.all (·.degPType == .excessive)

/-- Concrete instantiation: a pack weighing 80 kg with a liftable
    threshold of 30 kg is at least 50 kg too heavy (80 ≥ 50 + 30). -/
example : tooSem (λ _ : Unit => (80 : ℚ)) () 50 30 := by
  simp [tooSem, moreSem]; norm_num

end Phenomena.Comparison.Studies.VonStechow1984
