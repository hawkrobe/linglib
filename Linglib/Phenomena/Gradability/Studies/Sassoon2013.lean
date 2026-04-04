import Linglib.Theories.Semantics.Lexical.Adjective.Theory
import Linglib.Theories.Semantics.Degree.Core
import Linglib.Core.Scales.Scale

/-!
# @cite{sassoon-2013}

Galit W. Sassoon (2013). A Typology of Multidimensional Adjectives.
*Journal of Semantics* 30: 335–380.

## Key Claims

Multidimensional adjectives bind their dimensions via implicit quantifiers:
- *healthy* is **conjunctive**: healthy in ALL dimensions (blood pressure AND
  cholesterol AND lung function …)
- *sick* is **disjunctive**: sick in SOME dimension (blood pressure OR cholesterol …)
- *intelligent* is **mixed**: context determines ∀ vs ∃

Three hypothesis sets connect dimension binding to other properties:

1. **Typology** (Hypothesis 1): adjectives classify as conjunctive, disjunctive, or mixed
   based on co-occurrence with exception phrases (*except*)
2. **Polarity** (Hypothesis 2): positive antonyms are conjunctive, negative are
   disjunctive — follows from a negation theory of antonymy + De Morgan
3. **Standard type** (Hypothesis 3): total (max standard) → conjunctive,
   partial (min standard) → disjunctive, relative → mixed

## Formalization

The dimension-binding operations and De Morgan theorems are in
`Theories/Semantics/Lexical/Adjective/Theory.lean`. This file contains:
- The 18-adjective sample with empirical classifications from (36a–c), p. 359–360
- Corpus data from Table 3 (conjunctivity/disjunctivity raw counts)
- The 3:1 ratio criterion (p. 358) for classifying adjectives
- Antonym pair structure with De Morgan consistency verification
- Verification theorems connecting polarity, standard type, and binding type

## Scale type note

Scale types here use @cite{kennedy-mcnally-2005} `Boundedness` values, which
match the Fragment lexicon. Sassoon's own modifier-distribution analysis
(Section 2.3, Table 4) reclassifies several adjectives: *good* and *dissimilar*
as total, *bad* and *similar* as partial. These reclassifications are noted in
comments but not encoded, since the correlational H3 test (r = 0.62, p < 0.013
for non-comparatives) is the paper's actual finding — per-adjective binary
predictions are our addition for verification purposes.
-/

namespace Phenomena.Gradability.Studies.Sassoon2013

open Semantics.Lexical.Adjective (DimensionBindingType conjunctiveBinding
  disjunctiveBinding deMorgan_conjunctive_disjunctive
  deMorgan_disjunctive_conjunctive predictedBinding)
open Semantics.Degree (interpretiveEconomy)
open Core.Scale (Boundedness)

-- ════════════════════════════════════════════════════
-- § 1. Multidimensional Adjective Data
-- ════════════════════════════════════════════════════

/-- An adjective in Sassoon's 18-item sample, classified along three axes. -/
structure MultidimAdj where
  form : String
  /-- Evaluative polarity: positive adjectives denote membership under a
      generalization across ALL dimensional properties; negative adjectives
      denote the existence of a counterexample to SOME dimensional standard.
      Distinct from scale-endpoint polarity (`AdjModifierEntry.isLowerEndpoint`):
      *empty* is lower-endpoint but evaluatively positive. -/
  isPositive : Bool
  /-- Scale structure classification (@cite{kennedy-mcnally-2005}). -/
  scaleType : Boundedness
  /-- Observed default binding type from exception-phrase corpus data (36a–c). -/
  binding : DimensionBindingType
  deriving Repr, DecidableEq

-- Conjunctive adjectives (36a): Conj/Disj ratio 3:1 or higher

def normal    : MultidimAdj := ⟨"normal",    true, .closed,       .conjunctive⟩
def typical   : MultidimAdj := ⟨"typical",   true, .closed,       .conjunctive⟩
def healthy   : MultidimAdj := ⟨"healthy",   true, .closed,       .conjunctive⟩
def familiar  : MultidimAdj := ⟨"familiar",  true, .lowerBounded, .conjunctive⟩

-- Disjunctive adjectives (36b): Disj/Conj ratio 3:1 or higher

def bad_      : MultidimAdj := ⟨"bad",       false, .open_,        .disjunctive⟩
def sick      : MultidimAdj := ⟨"sick",      false, .lowerBounded, .disjunctive⟩
def atypical  : MultidimAdj := ⟨"atypical",  false, .lowerBounded, .disjunctive⟩
def abnormal  : MultidimAdj := ⟨"abnormal",  false, .lowerBounded, .disjunctive⟩
def different : MultidimAdj := ⟨"different",  false, .lowerBounded, .disjunctive⟩

-- Mixed adjectives (36c): balanced conjunctivity and disjunctivity

def identical   : MultidimAdj := ⟨"identical",   true,  .closed, .mixed⟩
def similar_    : MultidimAdj := ⟨"similar",     true,  .open_,  .mixed⟩
def good_       : MultidimAdj := ⟨"good",        true,  .open_,  .mixed⟩
def intelligent : MultidimAdj := ⟨"intelligent",  true,  .open_,  .mixed⟩
def dissimilar  : MultidimAdj := ⟨"dissimilar",   false, .open_,  .mixed⟩
def worse_      : MultidimAdj := ⟨"worse",        false, .open_,  .mixed⟩
def unfamiliar  : MultidimAdj := ⟨"unfamiliar",   false, .closed, .mixed⟩

-- Comparatives (inherit binding from base adjective)

def healthier : MultidimAdj := ⟨"healthier", true,  .open_, .conjunctive⟩
def better_   : MultidimAdj := ⟨"better",    true,  .open_, .mixed⟩

def allAdjs : List MultidimAdj := [
  normal, typical, healthy, familiar,
  bad_, sick, atypical, abnormal, different,
  identical, similar_, good_, intelligent, dissimilar, worse_, unfamiliar,
  healthier, better_
]

theorem sample_size : allAdjs.length = 18 := rfl

-- ════════════════════════════════════════════════════
-- § 2. Corpus Data (Table 3) and 3:1 Criterion
-- ════════════════════════════════════════════════════

/-- Exception-phrase corpus data from Table 3. Each adjective has two counts:
    - `conj`: dimensional uses in **positive** contexts ("P except Dim")
    - `disj`: dimensional uses in **negative** contexts ("not P except Dim")

    The chi-square tests in the paper compare the [conj, disj] distribution
    between antonym pairs to test whether polarity predicts binding type. -/
structure ExceptData where
  adj : String
  conj : Nat
  disj : Nat
  deriving Repr

/-- Table 3 data. Values are raw counts of dimensional exception-phrase uses
    per adjective in positive vs. negative contexts. -/
def exceptData : List ExceptData := [
  -- Conjunctive adjectives (36a): conj ≫ disj
  ⟨"healthy",     54, 11⟩,
  ⟨"normal",      69, 10⟩,
  ⟨"typical",     54,  9⟩,
  ⟨"familiar",    45,  9⟩,
  ⟨"healthier",   35,  9⟩,
  -- Disjunctive adjectives (36b): disj ≫ conj
  ⟨"bad",          3, 55⟩,
  ⟨"sick",         2, 26⟩,
  ⟨"atypical",    19, 68⟩,
  ⟨"abnormal",     6, 20⟩,
  ⟨"different",   13, 40⟩,
  -- Mixed adjectives (36c): balanced
  ⟨"identical",   86, 49⟩,
  ⟨"similar",     80, 67⟩,
  ⟨"good",        24, 21⟩,
  ⟨"intelligent", 37, 41⟩,
  ⟨"dissimilar",  58, 83⟩,
  ⟨"unfamiliar",  15, 27⟩,
  -- Comparatives
  ⟨"better",      25, 25⟩,
  ⟨"worse",       20, 32⟩
]

/-- The 3:1 ratio criterion from p. 358: Sassoon classifies adjectives as
    conjunctive when the conj/disj ratio is "significantly larger," which
    she operationalizes as ≥ 3 times the other count. -/
def isStronglyConjunctive (d : ExceptData) : Bool := d.conj ≥ 3 * d.disj
def isStronglyDisjunctive (d : ExceptData) : Bool := d.disj ≥ 3 * d.conj

/-- Classification from 3:1 criterion: conjunctive, disjunctive, or mixed. -/
def classifyFromCorpus (d : ExceptData) : DimensionBindingType :=
  if isStronglyConjunctive d then .conjunctive
  else if isStronglyDisjunctive d then .disjunctive
  else .mixed

-- Verify the 3:1 criterion classifies each adjective correctly

theorem classify_healthy    : classifyFromCorpus ⟨"healthy",   54, 11⟩ = .conjunctive := rfl
theorem classify_normal     : classifyFromCorpus ⟨"normal",    69, 10⟩ = .conjunctive := rfl
theorem classify_typical    : classifyFromCorpus ⟨"typical",   54,  9⟩ = .conjunctive := rfl
theorem classify_familiar   : classifyFromCorpus ⟨"familiar",  45,  9⟩ = .conjunctive := rfl
theorem classify_healthier  : classifyFromCorpus ⟨"healthier", 35,  9⟩ = .conjunctive := rfl

theorem classify_bad        : classifyFromCorpus ⟨"bad",        3, 55⟩ = .disjunctive := rfl
theorem classify_sick       : classifyFromCorpus ⟨"sick",       2, 26⟩ = .disjunctive := rfl
theorem classify_atypical   : classifyFromCorpus ⟨"atypical",  19, 68⟩ = .disjunctive := rfl
theorem classify_abnormal   : classifyFromCorpus ⟨"abnormal",   6, 20⟩ = .disjunctive := rfl
theorem classify_different  : classifyFromCorpus ⟨"different",  13, 40⟩ = .disjunctive := rfl

theorem classify_identical  : classifyFromCorpus ⟨"identical",  86, 49⟩ = .mixed := rfl
theorem classify_similar    : classifyFromCorpus ⟨"similar",    80, 67⟩ = .mixed := rfl
theorem classify_good       : classifyFromCorpus ⟨"good",       24, 21⟩ = .mixed := rfl
theorem classify_intelligent : classifyFromCorpus ⟨"intelligent", 37, 41⟩ = .mixed := rfl
theorem classify_dissimilar : classifyFromCorpus ⟨"dissimilar", 58, 83⟩ = .mixed := rfl
theorem classify_unfamiliar : classifyFromCorpus ⟨"unfamiliar", 15, 27⟩ = .mixed := rfl
theorem classify_better     : classifyFromCorpus ⟨"better",     25, 25⟩ = .mixed := rfl
theorem classify_worse      : classifyFromCorpus ⟨"worse",      20, 32⟩ = .mixed := rfl

/-- All 18 adjectives: corpus classification matches assigned binding type. -/
theorem corpus_matches_classification :
    exceptData.all (fun d =>
      classifyFromCorpus d == (allAdjs.find? (fun a => a.form == d.adj) |>.map MultidimAdj.binding
        |>.getD .mixed)) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Antonym Pairs and De Morgan Consistency
-- ════════════════════════════════════════════════════

/-- Antonym pairs from the paper's sample. Each pair (positive, negative)
    should satisfy De Morgan consistency: if the positive is conjunctive,
    the negative should be disjunctive, and vice versa. Mixed adjectives
    are exempt (mixed.negate = mixed). -/
def antonymPairs : List (MultidimAdj × MultidimAdj) := [
  (healthy, sick),
  (normal, abnormal),
  (typical, atypical),
  (familiar, unfamiliar),
  (good_, bad_),
  (similar_, dissimilar),
  (identical, different)
]

/-- De Morgan consistency: the negative antonym's binding type matches
    `.negate` of the positive antonym's binding, or one of them is mixed
    (context-dependent, so not constrained by De Morgan). -/
def deMorganConsistent (pos neg : MultidimAdj) : Bool :=
  pos.binding == .mixed || neg.binding == .mixed ||
  neg.binding == pos.binding.negate

theorem antonyms_consistent :
    antonymPairs.all (fun (p, n) => deMorganConsistent p n) = true := rfl

-- Per-pair verification for explicitness

theorem healthy_sick_consistent   : deMorganConsistent healthy  sick      = true := rfl
theorem normal_abnormal_consistent : deMorganConsistent normal  abnormal  = true := rfl
theorem typical_atypical_consistent : deMorganConsistent typical atypical  = true := rfl
theorem familiar_unfamiliar_consistent : deMorganConsistent familiar unfamiliar = true := rfl
theorem good_bad_consistent       : deMorganConsistent good_   bad_      = true := rfl
theorem similar_dissimilar_consistent : deMorganConsistent similar_ dissimilar = true := rfl
theorem identical_different_consistent : deMorganConsistent identical different = true := rfl

-- ════════════════════════════════════════════════════
-- § 4. Comparative Inheritance
-- ════════════════════════════════════════════════════

/-- Comparatives inherit binding type from their base adjective (p. 360).
    *healthier* inherits conjunctive from *healthy*; *better* inherits
    mixed from *good*. -/
theorem healthier_inherits : healthier.binding = healthy.binding := rfl
theorem better_inherits    : better_.binding = good_.binding := rfl

/-- *worse* diverges from *bad*: bad is disjunctive, but worse is mixed.
    This is expected — comparative morphology changes scale structure
    (closed → open), which shifts the H3 prediction. -/
theorem worse_diverges : worse_.binding ≠ bad_.binding := by decide

-- ════════════════════════════════════════════════════
-- § 5. Hypothesis 2: Polarity predicts binding type
-- ════════════════════════════════════════════════════

/-! Under a negation theory of antonymy (@cite{heim-2006}, @cite{buring-2007}),
    if a positive adjective P is conjunctive (∀Q∈DIM: Q(x)), then its
    negative antonym ¬P is disjunctive (∃Q∈DIM: ¬Q(x)), by De Morgan's laws.
    The proof is in Theory.lean as `deMorgan_conjunctive_disjunctive`. -/

/-- Predicted binding type from evaluative polarity, assuming positive
    member of each antonym pair is conjunctive. -/
def predictedFromPolarity (isPositive : Bool) : DimensionBindingType :=
  if isPositive then .conjunctive else .disjunctive

/-- Hypothesis 2 is satisfied when the adjective is mixed (context-dependent)
    or when its binding matches the polarity prediction. -/
def hypothesis2Holds (a : MultidimAdj) : Bool :=
  a.binding == .mixed || a.binding == predictedFromPolarity a.isPositive

theorem hypothesis2_all : allAdjs.all hypothesis2Holds = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 6. Hypothesis 3: Standard type predicts binding type
-- ════════════════════════════════════════════════════

/-- Predicted binding type from scale structure via Interpretive Economy.
    Max-endpoint standard → conjunctive, min-endpoint → disjunctive,
    contextual → mixed. -/
def predictedFromStandard (b : Boundedness) : DimensionBindingType :=
  predictedBinding (interpretiveEconomy b)

theorem standard_closed_conjunctive :
    predictedFromStandard .closed = .conjunctive := rfl
theorem standard_upperBounded_conjunctive :
    predictedFromStandard .upperBounded = .conjunctive := rfl
theorem standard_lowerBounded_disjunctive :
    predictedFromStandard .lowerBounded = .disjunctive := rfl
theorem standard_open_mixed :
    predictedFromStandard .open_ = .mixed := rfl

def hypothesis3Holds (a : MultidimAdj) : Bool :=
  a.binding == predictedFromStandard a.scaleType

-- Hypothesis 3 confirmed: total → conjunctive
theorem hypothesis3_normal    : hypothesis3Holds normal    = true := rfl
theorem hypothesis3_typical   : hypothesis3Holds typical   = true := rfl
theorem hypothesis3_healthy   : hypothesis3Holds healthy   = true := rfl

-- Hypothesis 3 confirmed: partial → disjunctive
theorem hypothesis3_sick      : hypothesis3Holds sick      = true := rfl
theorem hypothesis3_atypical  : hypothesis3Holds atypical  = true := rfl
theorem hypothesis3_abnormal  : hypothesis3Holds abnormal  = true := rfl
theorem hypothesis3_different : hypothesis3Holds different = true := rfl

-- Hypothesis 3 confirmed: relative → mixed
theorem hypothesis3_similar    : hypothesis3Holds similar_    = true := rfl
theorem hypothesis3_good       : hypothesis3Holds good_       = true := rfl
theorem hypothesis3_intelligent : hypothesis3Holds intelligent = true := rfl
theorem hypothesis3_dissimilar : hypothesis3Holds dissimilar  = true := rfl
theorem hypothesis3_worse      : hypothesis3Holds worse_      = true := rfl

-- Counterexamples to H3 (K&M2005 scale types)
-- `identical` is closed (total → conjunctive) but observed mixed per (36c)
-- `familiar` is lowerBounded (partial → disjunctive) but observed conjunctive
-- `unfamiliar` is closed (total → conjunctive) but observed mixed
-- `bad` is open (relative → mixed) but observed disjunctive
-- `healthier` is open (relative → mixed) but inherits conjunctive from `healthy`
-- Under Sassoon's own modifier-based classification (Table 4), bad would be
-- partial (→ disjunctive), resolving this counterexample. But similar/good/
-- dissimilar gain new tensions under her classification.
theorem hypothesis3_identical_fails  : hypothesis3Holds identical  = false := rfl
theorem hypothesis3_familiar_fails   : hypothesis3Holds familiar   = false := rfl
theorem hypothesis3_unfamiliar_fails : hypothesis3Holds unfamiliar = false := rfl
theorem hypothesis3_bad_fails        : hypothesis3Holds bad_       = false := rfl
theorem hypothesis3_healthier_fails  : hypothesis3Holds healthier  = false := rfl

/-- H3 holds for 13 of 18 adjectives (72%) using K&M2005 scale types. -/
theorem hypothesis3_success_count :
    (allAdjs.filter hypothesis3Holds).length = 13 := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. De Morgan Chain: end-to-end
-- ════════════════════════════════════════════════════

/-! The full chain connecting Hypothesis 2 to the De Morgan theorems:

    1. *healthy* is conjunctive: `conjunctiveBinding healthDims x`
    2. Under negation theory of antonymy, *sick* ≈ ¬*healthy*
    3. By `deMorgan_conjunctive_disjunctive`:
       `!conjunctiveBinding healthDims x = disjunctiveBinding (neg healthDims) x`
    4. Therefore *sick* is disjunctive: QED

    We demonstrate this with a concrete 3-dimension health model. -/

structure HealthState where
  bp : Bool
  cholesterol : Bool
  lung : Bool
  deriving DecidableEq, Repr

def healthDims : List (HealthState → Bool) :=
  [HealthState.bp, HealthState.cholesterol, HealthState.lung]

/-- Dan: high on 2 dimensions, fails lung. -/
def dan : HealthState := ⟨true, true, false⟩

/-- Sam: meets all 3 standards. -/
def sam : HealthState := ⟨true, true, true⟩

theorem dan_not_healthy : conjunctiveBinding healthDims dan = false := rfl
theorem sam_healthy     : conjunctiveBinding healthDims sam = true := rfl

theorem dan_sick : disjunctiveBinding
    (healthDims.map fun d a => !d a) dan = true := rfl
theorem sam_not_sick : disjunctiveBinding
    (healthDims.map fun d a => !d a) sam = false := rfl

/-- End-to-end: "not healthy" and "sick" are equivalent under the
    negation theory of antonymy + De Morgan. -/
theorem not_healthy_iff_sick (s : HealthState) :
    (!conjunctiveBinding healthDims s) =
      disjunctiveBinding (healthDims.map fun d a => !d a) s :=
  deMorgan_conjunctive_disjunctive healthDims s

-- ════════════════════════════════════════════════════
-- § 8. Polarity Judgment Data (Table 2)
-- ════════════════════════════════════════════════════

/-- Polarity judgment on a 1–7 scale (1 = perfectly negative, 7 = perfectly
    positive). Mean from 20 AMT participants. -/
structure PolarityJudgment where
  adj : String
  mean : Float
  isPositive : Bool
  deriving Repr

def polarityData : List PolarityJudgment := [
  ⟨"healthy",     6.6,  true⟩,
  ⟨"normal",      5.65, true⟩,
  ⟨"typical",     4.2,  true⟩,
  ⟨"similar",     4.5,  true⟩,
  ⟨"identical",   4.15, true⟩,
  ⟨"good",        6.45, true⟩,
  ⟨"familiar",    5.8,  true⟩,
  ⟨"better",      6.3,  true⟩,
  ⟨"intelligent", 6.7,  true⟩,
  ⟨"healthier",   6.05, true⟩,
  ⟨"sick",        1.5,  false⟩,
  ⟨"abnormal",    1.8,  false⟩,
  ⟨"atypical",    3.2,  false⟩,
  ⟨"dissimilar",  2.8,  false⟩,
  ⟨"different",   3.4,  false⟩,
  ⟨"bad",         1.1,  false⟩,
  ⟨"unfamiliar",  2.6,  false⟩,
  ⟨"worse",       1.4,  false⟩
]

/-- All positive adjectives have mean > 4, all negative have mean < 4.
    Midpoint 4 cleanly separates the two groups. -/
theorem polarity_above_midpoint :
    polarityData.all fun j => if j.isPositive then j.mean > 4.0 else j.mean < 4.0 := by
  native_decide

end Phenomena.Gradability.Studies.Sassoon2013
