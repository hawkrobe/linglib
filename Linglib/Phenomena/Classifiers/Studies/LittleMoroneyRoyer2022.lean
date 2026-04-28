import Linglib.Core.Lexical.NounCategorization
import Linglib.Core.Mereology
import Linglib.Core.Tree
import Linglib.Phenomena.Classifiers.Typology
import Linglib.Phenomena.Classifiers.Studies.Chierchia1998
import Linglib.Phenomena.Classifiers.Studies.Sudo2016
import Linglib.Fragments.Mayan.Chol.Classifiers
import Linglib.Fragments.Shan.Classifiers
import Linglib.Theories.Semantics.Classifier.Basic

/-!
# Little, Moroney & Royer (2022)
@cite{little-moroney-royer-2022}

Classifiers can be for numerals *or* nouns: Two strategies for numeral
modification. *Glossa* 7(1). 1–35.

## Core Claim

Numeral classifiers form a heterogeneous class. Two families of theories —
classifier-for-numeral (CLF-for-NUM) and classifier-for-noun (CLF-for-N) —
are *both* correct, but for different languages:

- **Ch'ol** (Mayan): CLF-for-NUM — the classifier is a measure function
  required by the numeral.
- **Shan** (Kra-Dai): CLF-for-N — the classifier atomizes the noun
  denotation so the numeral can count.

## Four Predictions (Table 8)

The two strategies make divergent predictions about classifier distribution:

1. **(num)** Variation in whether a *numeral* requires a CLF → CLF-for-NUM
2. **(noun)** Variation in whether a *noun* requires a CLF → CLF-for-N
3. **(noun)** CLF found beyond numerals (quantifiers, demonstratives) → CLF-for-N
4. **(num)** CLF appears in counting (no noun present) → CLF-for-NUM

Ch'ol shows predictions 1 and 4; Shan shows predictions 2 and 3.

## Semantic Equivalence

Despite different derivational strategies, both languages derive the same
meaning for "two dogs": {ab, ac, bc} — the set of pluralities of two dogs.

## Architectural Note

CLF-for-NUM is formalized using `Mereology.QMOD` — the measure function
`Finset.card` produces a quantized predicate (`clfForNum_qua`).
CLF-for-N is formalized directly as atom-pair selection: `∃ d₁ d₂, d₁ ≠ d₂ ∧ s = {d₁, d₂}`.
The `ClassifierStrategy` enum in `Core.NounCategorization` captures the
typological parameter.

Note: `Mereology.atomize` cannot be applied to `Finset Dog` directly because
`Finset` has `∅` as a bottom element — `Mereology.Atom` (no proper part)
is only satisfied by `∅`, so `atomize(DOGS)` would be empty. The CLF-for-N
semantics is instead formalized at the element level: singletons `{d}` are
the atoms, and `clfForNounSem` selects 2-element unions of distinct atoms.
The extensional equivalence (`derivations_extensionally_equal`) bridges the
two via `Finset.card_eq_two`.
-/

open Phenomena.Classifiers

namespace LittleMoroneyRoyer2022

open Core.NounCategorization
open Typology
open Typology.NounCategorizationSystem
open Phenomena.Classifiers.Typology

-- ============================================================================
-- § 1: Language Profiles
-- ============================================================================

/-- Ch'ol noun categorization system: numeral classifier, CLF-for-NUM.
    @cite{bale-coon-2014} @cite{bale-et-al-2019}

    Key properties:
    - Classifiers are bound to the numeral (suffixes)
    - Only Mayan-based numerals (1–6) take classifiers; Spanish loans do not
    - Classifiers appear in counting contexts (no noun)
    - Plural marking *-ob* co-occurs with classifiers (ex. 30)
    - Classifiers are ungrammatical with quantifiers, demonstratives, modifiers (ex. 19) -/
def chol : NounCategorizationSystem :=
  { family := "Mayan"
  , classifierType := .numeralClassifier
  , scopes := [.numeralNP]  -- ONLY with numerals (ex. 19: *DEM-CLF, *ADJ-CLF)
  , assignment := .semantic
  , realizations := [.suffix]  -- Bound morphemes on numeral stem
  , hasAgreement := false
  , inventorySize := Fragments.Mayan.Chol.Classifiers.allClassifiers.length
  , isObligatory := true
  , hasUnmarkedDefault := true  -- -p'ej is default
  , preferredSemantics := collectSemantics Fragments.Mayan.Chol.Classifiers.allClassifiers
  , pluralClfCooccur := true  -- ex. 30: cha'-tyikil wiñik-ob 'two men' (CLF + PL)
  , source := "@cite{little-moroney-royer-2022}; @cite{bale-coon-2014}" }

/-- Shan noun categorization system: numeral classifier, CLF-for-N.
    @cite{moroney-2021}

    Key properties:
    - Classifiers are free morphemes derived from nominal elements
    - All numerals uniformly require classifiers (no idiosyncrasies)
    - Classifiers appear with quantifiers, demonstratives, relative clauses (ex. 42)
    - Classifiers degraded/unacceptable in counting contexts (exs. 48–49)
    - No plural–classifier co-occurrence -/
def shan : NounCategorizationSystem :=
  { family := "Kra-Dai"
  , classifierType := .numeralClassifier
  , scopes := [.numeralNP, .attributiveNP]  -- With numerals AND dems/quantifiers
  , assignment := .semantic
  , realizations := [.freeForm]  -- Free morphemes
  , hasAgreement := false
  , inventorySize := Fragments.Shan.Classifiers.allClassifiers.length
  , isObligatory := true
  , hasUnmarkedDefault := true  -- ʔǎn is default
  , preferredSemantics := collectSemantics Fragments.Shan.Classifiers.allClassifiers
  , pluralClfCooccur := false  -- CLF and PL in same projection (Borer 2005)
  , source := "@cite{little-moroney-royer-2022}; @cite{moroney-2021}" }

-- ============================================================================
-- § 2: Predictions (Table 8)
-- ============================================================================

/-- The four distributional predictions from the CLF-for-NUM vs CLF-for-N
    distinction (Table 2/7/8). -/
structure Predictions where
  /-- Prediction 1: Idiosyncrasies in whether a *numeral* requires a CLF.
      Expected for CLF-for-NUM (measure function may be built into numeral). -/
  numeralIdiosyncrasies : Bool
  /-- Prediction 2: Idiosyncrasies in whether a *noun* requires a CLF.
      Expected for CLF-for-N (some nouns may already denote atoms). -/
  nounIdiosyncrasies : Bool
  /-- Prediction 3: CLF found with the noun beyond numerals
      (quantifiers, demonstratives, relative clauses).
      Expected for CLF-for-N (CLF is for the noun, not the numeral). -/
  clfBeyondNumerals : Bool
  /-- Prediction 4: CLF appears in counting contexts (no noun present).
      Expected for CLF-for-NUM (CLF is required by the numeral itself). -/
  clfInCounting : Bool
  deriving Repr, BEq, DecidableEq

/-- Expected predictions for CLF-for-NUM languages. -/
def clfForNumPredictions : Predictions :=
  { numeralIdiosyncrasies := true
  , nounIdiosyncrasies := false
  , clfBeyondNumerals := false
  , clfInCounting := true }

/-- Expected predictions for CLF-for-N languages. -/
def clfForNounPredictions : Predictions :=
  { numeralIdiosyncrasies := false
  , nounIdiosyncrasies := true
  , clfBeyondNumerals := true
  , clfInCounting := false }

/-- Expected predictions for languages whose classifier system is the
    @cite{sudo-2016} blocking strategy: classifier semantics live with
    *numerals*, not nouns; the silent ∪-operator that lifts numerals to
    predicates is blocked by the lexical presence of classifiers.

    LMR's diagnostic battery applied to Sudo's framework:
    - **numeralIdiosyncrasies = false**: ∪ is uniformly blocked across
      all numerals; no per-numeral variation (contrast Ch'ol Mayan-vs-
      Spanish split, which Sudo's framework does not predict).
    - **nounIdiosyncrasies = false**: explanation lives in numerals, not
      nouns; uniform across the noun lexicon.
    - **clfBeyondNumerals = false**: classifiers exist *to lift numerals*
      to predicate type; they appear *with* numerals, not beyond them
      (contrast LMR's CLF-for-N prediction).
    - **clfInCounting = true**: the ∩-operator (Sudo eq. 24) maps the
      numeral+CL property back to type-n, so number-predicate uses like
      *juu-ni-nin-da* "the number is twelve people" (Sudo eq. 22a) are
      well-formed (contrast LMR's CLF-for-N prediction). -/
def sudoBlockingPredictions : Predictions :=
  { numeralIdiosyncrasies := false
  , nounIdiosyncrasies := false
  , clfBeyondNumerals := false
  , clfInCounting := true }

/-- Derive LMR's distributional predictions from any classifier strategy.
    This is the paper's core claim for `.forNumeral` and `.forNoun`;
    extended here to `.sudoBlocking` per @cite{sudo-2016}'s analysis. -/
def predictionsOf : ClassifierStrategy → Predictions
  | .forNumeral => clfForNumPredictions
  | .forNoun => clfForNounPredictions
  | .sudoBlocking => sudoBlockingPredictions

/-! ## §2b: LMR's per-language strategy assignments

@cite{little-moroney-royer-2022} assigns Ch'ol the CLF-for-NUM strategy
and Shan the CLF-for-N strategy. They are *consistent with* the
@cite{chierchia-1998} CLF-for-N assignment for Mandarin/Japanese (LMR
treat Sinitic and Japonic as CLF-for-N). Per-language assignments live
here (in this study file) rather than on `NounCategorizationSystem`. -/

/-- LMR's strategy assignment for Ch'ol: classifier is a measure function
    required by the numeral. -/
def cholStrategy : ClassifierStrategy := .forNumeral

/-- LMR's strategy assignment for Shan: classifier atomizes the noun
    denotation. -/
def shanStrategy : ClassifierStrategy := .forNoun

/-- Ch'ol predictions derived from LMR's CLF-for-NUM assignment. -/
def cholPredictions : Predictions := predictionsOf cholStrategy

/-- Shan predictions derived from LMR's CLF-for-N assignment. -/
def shanPredictions : Predictions := predictionsOf shanStrategy

-- ============================================================================
-- § 3: Prediction Verification
-- ============================================================================

/-- The CLF-for-NUM and CLF-for-N profiles are distinct — the two LMR
    strategies make genuinely different predictions on all four diagnostics. -/
theorem profiles_distinct :
    clfForNumPredictions ≠ clfForNounPredictions := by decide

/-- Ch'ol predictions follow from LMR's strategy assignment via `predictionsOf`. -/
theorem chol_predictions_from_strategy :
    predictionsOf cholStrategy = cholPredictions := rfl

/-- Shan predictions follow from LMR's strategy assignment via `predictionsOf`. -/
theorem shan_predictions_from_strategy :
    predictionsOf shanStrategy = shanPredictions := rfl

-- ============================================================================
-- § 3b: Cross-paper divergence on Japanese
-- ============================================================================

/-- @cite{chierchia-1998} and @cite{sudo-2016} disagree on Japanese's
    classifier strategy: Chierchia assigns `.forNoun`, Sudo assigns
    `.sudoBlocking`. Run through LMR's diagnostic battery, the two
    strategies make divergent empirical predictions: -/
theorem chierchia_sudo_diverge_on_predictions :
    predictionsOf Chierchia1998.japaneseStrategy ≠
      predictionsOf Sudo2016.japaneseStrategy := by decide

/-- The empirical wedge: under LMR's diagnostics, Chierchia's `.forNoun`
    and Sudo's `.sudoBlocking` agree on `numeralIdiosyncrasies = false`
    but diverge on the other three. The most decisive disagreement is
    `clfInCounting`: Sudo predicts `true` (citing eq. 22a — *juu-ni-nin-da*
    "the number is twelve people" is well-formed via the ∩-operator),
    Chierchia predicts `false`. Japanese empirically exhibits the Sudo
    pattern on this diagnostic. -/
theorem clfInCounting_distinguishes_chierchia_from_sudo :
    (predictionsOf Chierchia1998.japaneseStrategy).clfInCounting = false ∧
    (predictionsOf Sudo2016.japaneseStrategy).clfInCounting = true := ⟨rfl, rfl⟩

/-- Symmetric divergence on `clfBeyondNumerals`: Chierchia predicts `true`
    (CLF appears with quantifiers, demonstratives, relative clauses
    independent of numerals); Sudo predicts `false` (CLF exists *for*
    numerals, not beyond them). -/
theorem clfBeyondNumerals_distinguishes_chierchia_from_sudo :
    (predictionsOf Chierchia1998.japaneseStrategy).clfBeyondNumerals = true ∧
    (predictionsOf Sudo2016.japaneseStrategy).clfBeyondNumerals = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 4: Empirical Data
-- ============================================================================

/-- Grammaticality judgments for Ch'ol classifier distribution (§3.1, §4).
    Each datum records whether a CLF appears in a given syntactic context. -/
structure ClfDatum where
  language : String
  context : String
  clfPresent : Bool
  grammatical : Bool
  deriving Repr

/-- Ch'ol: CLF only with numerals and interrogative *jay-* 'how many'. -/
def cholData : List ClfDatum :=
  [ -- CLF with Mayan numeral: ✓ (ex. 16)
    { language := "Ch'ol", context := "Mayan numeral + CLF"
    , clfPresent := true, grammatical := true }
    -- CLF with Spanish numeral: ✗ (ex. 17)
  , { language := "Ch'ol", context := "Spanish numeral + CLF"
    , clfPresent := true, grammatical := false }
    -- CLF with quantifier 'many': ✗ (ex. 19a)
  , { language := "Ch'ol", context := "quantifier + CLF"
    , clfPresent := true, grammatical := false }
    -- CLF with demonstrative: ✗ (ex. 19c)
  , { language := "Ch'ol", context := "demonstrative + CLF"
    , clfPresent := true, grammatical := false }
    -- CLF in counting (no noun): ✓ (ex. 45)
  , { language := "Ch'ol", context := "counting (no noun)"
    , clfPresent := true, grammatical := true }
    -- CLF in number reference: ✓ (ex. 46)
  , { language := "Ch'ol", context := "number reference"
    , clfPresent := true, grammatical := true }
    -- CLF co-occurs with plural -ob: ✓ (ex. 30)
  , { language := "Ch'ol", context := "CLF + plural marking"
    , clfPresent := true, grammatical := true } ]

/-- Shan: CLF with numerals, quantifiers, demonstratives, relative clauses. -/
def shanData : List ClfDatum :=
  [ -- CLF with numeral: ✓ (ex. 21)
    { language := "Shan", context := "numeral + CLF"
    , clfPresent := true, grammatical := true }
    -- CLF with quantifier 'every': ✓ (ex. 42a)
  , { language := "Shan", context := "quantifier + CLF"
    , clfPresent := true, grammatical := true }
    -- CLF with demonstrative: ✓ (ex. 42b)
  , { language := "Shan", context := "demonstrative + CLF"
    , clfPresent := true, grammatical := true }
    -- CLF with relative clause: ✓ (ex. 42d)
  , { language := "Shan", context := "relative clause + CLF"
    , clfPresent := true, grammatical := true }
    -- CLF in counting: ? (degraded, ex. 48)
  , { language := "Shan", context := "counting (no noun)"
    , clfPresent := true, grammatical := false }
    -- CLF in number reference: ✗ (ex. 49)
  , { language := "Shan", context := "number reference"
    , clfPresent := true, grammatical := false } ]

-- ============================================================================
-- § 5: Plural Co-occurrence (§3.4)
-- ============================================================================

/-- @cite{little-moroney-royer-2022} §3.4 refine @cite{greenberg-1972}'s
    complementarity universal. The original says numeral classifiers and
    obligatory number marking are in complementary distribution. The
    refinement: this holds for CLF-for-N (where CLF and PL occupy the
    same functional projection) but *not* for CLF-for-NUM (where CLF is
    in a separate projection and can co-occur with PL).

    Ch'ol (CLF-for-NUM): cha'-tyikil wiñik-*ob* 'two-CLF men-PL' (ex. 30)
    Shan (CLF-for-N): *mǎa sǎam tǒ khǎw 'three CLF dogs PL' (unattested) -/
theorem greenberg_refined_by_strategy :
    -- CLF-for-NUM: plural CAN co-occur with CLF
    cholStrategy = .forNumeral ∧ chol.pluralClfCooccur = true ∧
    -- CLF-for-N: plural CANNOT co-occur with CLF
    shanStrategy = .forNoun ∧ shan.pluralClfCooccur = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 6: Scope Diagnostics
-- ============================================================================

/-- Prediction 3 (CLF beyond numerals) is derived from the system's scopes.
    CLF-for-N classifiers serve the noun, so they appear wherever the noun
    needs individuation — not just with numerals. -/
theorem clf_beyond_numerals_tracks_scopes :
    -- Ch'ol: no scopes beyond numeralNP → prediction 3 = false
    (chol.scopes.any (· != .numeralNP) = false) ∧
    -- Shan: has scopes beyond numeralNP → prediction 3 = true
    (shan.scopes.any (· != .numeralNP) = true) :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 7: Constituency (§5, derivation trees 51–52)
-- ============================================================================

section Constituency

open Core.Tree

/-- Ch'ol constituency (51): numeral and classifier form a constituent.
    [[cha'-kojty]_NumCLF [ts'i']_N]
    The numeral *cha'* first combines with the classifier *-kojty* to form
    a measure phrase, which then applies to the noun *ts'i'* 'dog'. -/
def cholTree : Tree Unit String :=
  .bin (.bin (.leaf "cha'") (.leaf "kojty")) (.leaf "ts'i'")

/-- Shan constituency (52): classifier and noun form a constituent.
    [[sǒŋ]_Num [[tǒ]_CLF [mǎa]_N]]
    The classifier *tǒ* first combines with the noun *mǎa* 'dog' to
    atomize it, then the numeral *sǒŋ* 'two' selects a 2-element sum. -/
def shanTree : Tree Unit String :=
  .bin (.leaf "sǒŋ") (.bin (.leaf "tǒ") (.leaf "mǎa"))

/-- The two derivation trees have different constituency despite both
    being binary branching over three terminals. In Ch'ol, the left
    daughter of the root is complex (Num+CLF); in Shan, the right
    daughter is complex (CLF+N).

    This structural difference is what generates the four distributional
    predictions: if Num+CLF is a constituent, the classifier is part of
    the numeral's semantics and appears wherever the numeral appears
    (counting, number reference). If CLF+N is a constituent, the
    classifier is part of the noun's semantics and appears wherever
    the noun needs individuation (quantifiers, demonstratives). -/
theorem constituency_differs : cholTree != shanTree := rfl

/-- Both trees have the same size (5 nodes each: 2 internal + 3 terminals).
    The difference is purely structural — which pairs branch together. -/
theorem same_size : cholTree.size = shanTree.size := rfl

end Constituency

-- ============================================================================
-- § 8: Semantic Derivation (§2.3, §5)
-- ============================================================================

section SemanticDerivation

/-- A finite domain of three atomic dogs: a, b, c. -/
inductive Dog where | a | b | c
  deriving DecidableEq, Repr

instance : Fintype Dog where
  elems := {.a, .b, .c}
  complete x := by cases x <;> simp

/-- CLF-for-NUM derivation: `Mereology.QMOD` applied to the dog domain.
    ⟦two-CLF⟧ = λP. QMOD(P, μ#, 2) where μ# = `Finset.card`.
    This uses `Mereology.QMOD` from `Core/Mereology.lean`:
      QMOD(R, μ, n) = λx. R(x) ∧ μ(x) = n -/
def clfForNumSem (s : Finset Dog) : Prop :=
  Mereology.QMOD (·.Nonempty : Finset Dog → Prop) Finset.card 2 s

/-- CLF-for-N derivation: atomize, then count.
    ⟦CLF⟧(⟦DOGS⟧) restricts to atoms (singletons), then
    ⟦TWO⟧ selects 2-element sums from the atomized set.
    The result: s is the union of exactly two distinct atoms. -/
def clfForNounSem (s : Finset Dog) : Prop :=
  ∃ d₁ d₂ : Dog, d₁ ≠ d₂ ∧ s = {d₁, d₂}

/-- The two derivation strategies are extensionally equivalent:
    QMOD(DOGS, μ#, 2) = {s | ∃ d₁ d₂, d₁ ≠ d₂ ∧ s = {d₁, d₂}}.
    This is the paper's key semantic result (§5): despite different
    compositional paths, both strategies produce the same denotation
    for "two dogs."

    The CLF-for-NUM path uses the measure constraint directly (QMOD);
    the CLF-for-N path atomizes then forms 2-element sums.
    `Finset.card_eq_two` provides the bridge: a finset has cardinality 2
    iff it's a pair of distinct elements. -/
theorem derivations_extensionally_equal (s : Finset Dog) :
    clfForNumSem s ↔ clfForNounSem s := by
  simp only [clfForNumSem, clfForNounSem, Mereology.QMOD]
  constructor
  · rintro ⟨_, hcard⟩
    exact Finset.card_eq_two.mp hcard
  · rintro ⟨d₁, d₂, hne, rfl⟩
    exact ⟨⟨d₁, Finset.mem_insert_self d₁ {d₂}⟩, Finset.card_pair hne⟩

/-- The full dog predicate (Nonempty) is cumulative: the union of two
    dog-pluralities is a dog-plurality. `Mereology.CUM` applied to
    `Finset Dog` with `⊔ = ∪`.

    Cumulativity is what forces classifier languages to need a classifier:
    counting over a CUM predicate is undefined until it's quantized.
    CLF-for-NUM uses QMOD to quantize directly; CLF-for-N atomizes first. -/
theorem dogs_cum : Mereology.CUM (·.Nonempty : Finset Dog → Prop) :=
  fun _ _ hx _ => hx.mono Finset.subset_union_left

/-- CLF-for-NUM creates a quantized predicate via QMOD: no proper
    subset of a 2-element set also has 2 elements.

    Proof: `y ⊂ x` implies `|y| < |x|` (`Finset.card_lt_card`),
    but both have card 2 — contradiction. This mirrors the general
    `Mereology.extMeasure_qua` pattern (QMOD by any extensive measure
    produces QUA), instantiated directly for `Finset.card`. -/
theorem clfForNum_qua : Mereology.QUA clfForNumSem := by
  intro x y hx hlt hy
  simp only [clfForNumSem, Mereology.QMOD] at hx hy
  exact absurd (Finset.card_lt_card hlt) (by omega)

/-- CLF-for-N also creates a quantized predicate: no proper subset of
    a pair of distinct dogs is also a pair of distinct dogs. Both
    strategies convert CUM predicates to QUA predicates — this is the
    semantic function of classifiers regardless of strategy.

    Proof: if `y ⊂ x` and both satisfy `clfForNounSem`, then by
    `derivations_extensionally_equal`, both have card 2. But `y ⊂ x`
    implies `|y| < |x|` — contradiction. -/
theorem clfForNoun_qua : Mereology.QUA clfForNounSem := by
  intro x y hx hlt hy
  have hx' := (derivations_extensionally_equal x).mpr hx
  have hy' := (derivations_extensionally_equal y).mpr hy
  simp only [clfForNumSem, Mereology.QMOD] at hx' hy'
  exact absurd (Finset.card_lt_card hlt) (by omega)

/-- Both strategies quantize: the semantic function of classifiers is to
    turn CUM predicates into QUA predicates, enabling counting. -/
theorem both_strategies_quantize :
    Mereology.QUA clfForNumSem ∧ Mereology.QUA clfForNounSem :=
  ⟨clfForNum_qua, clfForNoun_qua⟩

/-- Concrete witness: {a, b} is a two-dog plurality. -/
theorem ab_satisfies : clfForNumSem {.a, .b} :=
  ⟨⟨.a, Finset.mem_insert_self _ _⟩, Finset.card_pair (by decide)⟩

/-- Concrete witness: {a, c} is a two-dog plurality. -/
theorem ac_satisfies : clfForNumSem {.a, .c} :=
  ⟨⟨.a, Finset.mem_insert_self _ _⟩, Finset.card_pair (by decide)⟩

/-- Concrete witness: {b, c} is a two-dog plurality. -/
theorem bc_satisfies : clfForNumSem {.b, .c} :=
  ⟨⟨.b, Finset.mem_insert_self _ _⟩, Finset.card_pair (by decide)⟩

/-- Singletons are not two-dog pluralities: the measure constraint
    excludes them. This is why CLF-for-N atomization alone doesn't
    suffice — the numeral still needs to select the right cardinality. -/
theorem singleton_excluded (d : Dog) : ¬clfForNumSem {d} := by
  simp only [clfForNumSem, Mereology.QMOD]
  intro ⟨_, h⟩
  simp [Finset.card_singleton] at h

/-- The triple is not a two-dog plurality: QMOD excludes oversized sums. -/
theorem triple_excluded : ¬clfForNumSem {.a, .b, .c} := by
  simp only [clfForNumSem, Mereology.QMOD]
  intro ⟨_, h⟩
  simp [Finset.card_insert_of_notMem] at h

end SemanticDerivation

-- ============================================================================
-- § 9: Integration with Extended Typology
-- ============================================================================

/-- Extended system list including Ch'ol and Shan. -/
def allSystemsWithCholShan : List NounCategorizationSystem :=
  Typology.allSystems ++ [chol, shan]

/-- Ch'ol and Shan are both numeral classifier systems in Aikhenvald's
    typology, but have different classifier strategies.
    They agree on Aikhenvald's morphosyntactic classification but differ
    on the semantic level — illustrating that `ClassifierType` is too
    coarse to capture the CLF-for-NUM vs CLF-for-N distinction. -/
theorem same_aikhenvald_different_strategy :
    chol.classifierType = shan.classifierType ∧
    cholStrategy ≠ shanStrategy :=
  ⟨rfl, by decide⟩

/-- Sample-restricted: in the 7-language Aikhenvald sample plus Ch'ol
    and Shan, every classifier-type language lacks agreement. -/
theorem sample_no_agreement_with_chol_shan :
    (allSystemsWithCholShan.filter (isClassifierType ·.classifierType)).all
      (!·.hasAgreement) = true := by decide

/-- @cite{chierchia-1998}'s NMP predicts CLF-for-N for [+arg, -pred] languages
    (Mandarin, Japanese). Shan is also CLF-for-N per @cite{little-moroney-royer-2022},
    despite being Kra-Dai not Sino-Tibetan — the strategy is independent of
    the NMP parameter. Ch'ol is CLF-for-NUM, which @cite{chierchia-1998} does not
    predict (Ch'ol is not a [+arg, -pred] language in the NMP typology).

    This connects the two classifier study files: Chierchia predicts the
    strategy for Mandarin/Japanese; Little et al. provide the diagnostic
    framework that confirms it and extends it to new languages. -/
theorem shan_agrees_with_chierchia_clf_for_noun :
    shanStrategy = Chierchia1998.mandarinStrategy ∧
    shanStrategy = Chierchia1998.japaneseStrategy :=
  ⟨rfl, rfl⟩

/-- Ch'ol's CLF-for-NUM strategy differs from the Chierchia-predicted
    CLF-for-N found in Mandarin and Japanese. This is the paper's main
    typological contribution: not all numeral classifier languages use
    the same semantic strategy. -/
theorem chol_differs_from_chierchia_languages :
    cholStrategy ≠ Chierchia1998.mandarinStrategy :=
  by decide

-- ============================================================================
-- § 10: Bridge to Unified Classifier Semantics
-- ============================================================================

/-- The unified `classifierDenot` correctly dispatches based on strategy.

    - CLF-for-N → `clfForNoun` (= `atomize`)
    - CLF-for-NUM → `clfForNum` (= `QMOD`)

    This confirms that the typological enum in `Core.NounCategorization`
    is structurally connected to semantic content, not just a label. -/
theorem strategy_dispatch_forNoun :
    Semantics.Classifier.classifierDenot
      Core.NounCategorization.ClassifierStrategy.forNoun
      (fun (_ : Finset Dog) => True) (fun _ => 0) 0
    = Semantics.Classifier.clfForNoun (fun (_ : Finset Dog) => True) := rfl

/-- The local `clfForNumSem` IS `QMOD` from `Core.Mereology`: both compute
    `R(x) ∧ μ(x) = n` with `μ = Finset.card` and `n = 2`. The unified
    `clfForNum` specializes `QMOD` to `ℚ`; the local definition uses `ℕ`
    directly. Both reduce to `QMOD`. -/
theorem clfForNum_agrees_with_local (s : Finset Dog) :
    clfForNumSem s ↔
      Mereology.QMOD (·.Nonempty : Finset Dog → Prop) Finset.card 2 s :=
  Iff.rfl

end LittleMoroneyRoyer2022
