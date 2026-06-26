import Linglib.Morphology.MorphRule
import Linglib.Syntax.Negation

/-!
# Japanese Negation Fragment
[miestamo-2005] [haspelmath-2013] [dryer-haspelmath-2013]

Japanese expresses standard negation with the suffix *-nai* on the verb
stem. This is **asymmetric** negation of type A/Fin+A/Cat: the negative
form differs from the affirmative both in finiteness properties and in
category marking.

## Key asymmetries

1. **A/Fin**: The negative suffix *-nai* conjugates as an i-adjective,
   not as a verb. The lexical verb loses its finite inflection and
   appears as a stem (continuative/mizenkei form).

2. **A/Cat**: Past tense in the negative is formed differently:
   - Affirmative past: stem + *-ta* (e.g., *tabe-ta* 'ate')
   - Negative past: stem + *-naka-tta* (e.g., *tabe-naka-tta* 'didn't eat')

   The negative past uses the *-nai* → *-nakatta* i-adjective past,
   NOT the verbal past *-ta* directly on the stem.

## Paradigm (*taberu* 'eat')

| Form | Affirmative | Negative |
|------|-------------|----------|
| Nonpast | *tabe-ru* | *tabe-nai* |
| Past | *tabe-ta* | *tabe-naka-tta* |
| Gerund | *tabe-te* | *tabe-naku-te* |
| Conditional | *tabe-reba* | *tabe-nake-reba* |
-/

namespace Japanese.Negation

open Morphology (MorphCategory)
open Syntax.Negation

/-- *-nai* — Japanese's negative verbal suffix.
    Attaches to the verb stem (mizenkei/continuative form) and itself
    inflects as an i-adjective: *tabe-nai* (NPST), *tabe-naka-tta* (PST),
    *tabe-naku-te* (GER). The shift of TAM marking from the stem to the
    *-nai* suffix is the A/Fin+A/Cat asymmetry captured by
    `japaneseNegDistribution` below. -/
def negSuffix : NegMarkerEntry :=
  { form := "-nai"
  , morphemeType := .affix
  , position := .morphological }

/-- The Japanese negation system: a single verbal affix with rich
    morphological redistribution (see `japaneseNegDistribution`).
    The Fragment-side joint consumed by `Studies/Dryer2013Negation.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "jpn" [negSuffix]

/-- A Japanese negation paradigm entry. -/
structure NegParadigmEntry where
  formLabel : String
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  deriving Repr, BEq, Inhabited

/-- Paradigm for *taberu* 'eat' (ichidan/vowel-stem verb). -/
def taberuParadigm : List NegParadigmEntry :=
  [ { formLabel := "nonpast"
    , affirmative := "taberu", negative := "tabenai"
    , glossAff := "eat.NPST", glossNeg := "eat.NEG" }
  , { formLabel := "past"
    , affirmative := "tabeta", negative := "tabenakatta"
    , glossAff := "eat.PST", glossNeg := "eat.NEG.PST" }
  , { formLabel := "gerund"
    , affirmative := "tabete", negative := "tabenakute"
    , glossAff := "eat.GER", glossNeg := "eat.NEG.GER" }
  , { formLabel := "conditional"
    , affirmative := "tabereba", negative := "tabenakereba"
    , glossAff := "eat.COND", glossNeg := "eat.NEG.COND" }
  , { formLabel := "volitional"
    , affirmative := "tabeyō", negative := "tabenai darō"
    , glossAff := "eat.VOL", glossNeg := "eat.NEG PROB" }
  ]

/-- Paradigm for *yomu* 'read' (godan/consonant-stem verb).
    Shows the stem-final consonant alternation. -/
def yomuParadigm : List NegParadigmEntry :=
  [ { formLabel := "nonpast"
    , affirmative := "yomu", negative := "yomanai"
    , glossAff := "read.NPST", glossNeg := "read.NEG" }
  , { formLabel := "past"
    , affirmative := "yonda", negative := "yomanakatta"
    , glossAff := "read.PST", glossNeg := "read.NEG.PST" }
  ]

/-- Which morphological categories are affected by negation.
    In the affirmative, tense is marked directly on the verb stem.
    In the negative, tense is marked on the *-nai* suffix (i-adjective inflection),
    not on the verb stem. -/
structure NegInflDistribution where
  /-- Categories on verb stem in affirmative -/
  affirmativeOnStem : List MorphCategory
  /-- Categories on verb stem in negative -/
  negativeOnStem : List MorphCategory
  /-- Categories on the negative suffix -/
  negativeOnSuffix : List MorphCategory
  deriving Repr, BEq

def japaneseNegDistribution : NegInflDistribution :=
  { affirmativeOnStem := [.tense, .aspect, .mood, .agreement .subj]
  , negativeOnStem := [.aspect]
  , negativeOnSuffix := [.negation, .tense, .mood] }

/-! ## Verification -/

theorem taberu_paradigm_size : taberuParadigm.length = 5 := by decide
theorem yomu_paradigm_size : yomuParadigm.length = 2 := by decide

/-- The negative past form is *tabenakatta* — built on the negative stem,
    not the affirmative past *tabeta*. -/
theorem neg_past_form :
    (taberuParadigm.filter (·.formLabel == "past")).head!.negative
      = "tabenakatta" := by decide

/-- The distribution shows that tense moves from stem to suffix under negation. -/
theorem tense_moves_to_suffix :
    japaneseNegDistribution.affirmativeOnStem.contains .tense = true ∧
    japaneseNegDistribution.negativeOnStem.contains .tense = false ∧
    japaneseNegDistribution.negativeOnSuffix.contains .tense = true := by
  decide

/-- Japanese negation profile (WALS Ch 112-115 + Greco/JinKoenig fields). -/
def negationProfile : Syntax.Negation.NegationProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finAndCat
  , negIndefinite := some .cooccur
  , negMarkers := ["-nai", "-nakat-"]
  , negIsHead := none
  , enAttested := none }

end Japanese.Negation
