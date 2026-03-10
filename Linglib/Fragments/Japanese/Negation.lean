import Linglib.Core.Lexical.MorphRule

/-!
# Japanese Negation Fragment
@cite{miestamo-2005} @cite{dryer-haspelmath-2013}

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

namespace Fragments.Japanese.Negation

open Core.Morphology (MorphCategory)

/-- The Japanese negative suffix. -/
def negSuffix : String := "-nai"

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
  { affirmativeOnStem := [.tense, .aspect, .mood, .agreement]
  , negativeOnStem := [.aspect]
  , negativeOnSuffix := [.negation, .tense, .mood] }

/-! ## Verification -/

theorem negSuffix_is_nai : negSuffix = "-nai" := rfl
theorem taberu_paradigm_size : taberuParadigm.length = 5 := by native_decide
theorem yomu_paradigm_size : yomuParadigm.length = 2 := by native_decide

private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The verb stem in negative forms differs from affirmative — asymmetry
    is visible: negative past *tabenakatta* does not contain the affirmative
    past suffix *-ta* directly on the stem. -/
theorem neg_past_differs_from_aff_past :
    let affPast := (taberuParadigm.filter (·.formLabel == "past")).head!
    let negPast := affPast.negative
    negPast = "tabenakatta" ∧ hasSubstr negPast "nakatta" = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- All negative forms contain the negative morpheme *na*. -/
theorem all_neg_contain_na :
    taberuParadigm.all (fun e => hasSubstr e.negative "na") = true := by
  native_decide

/-- The distribution shows that tense moves from stem to suffix under negation. -/
theorem tense_moves_to_suffix :
    japaneseNegDistribution.affirmativeOnStem.contains .tense = true ∧
    japaneseNegDistribution.negativeOnStem.contains .tense = false ∧
    japaneseNegDistribution.negativeOnSuffix.contains .tense = true := by
  native_decide

end Fragments.Japanese.Negation
