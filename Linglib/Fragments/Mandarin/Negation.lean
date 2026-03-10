import Linglib.Core.Lexical.Word
import Linglib.Fragments.Mandarin.AspectComparison

/-!
# Mandarin Negation Fragment
@cite{miestamo-2005} @cite{dryer-haspelmath-2013} @cite{zhao-2025}

Mandarin Chinese has two standard negation particles:

| Particle | Domain | Symmetric? |
|----------|--------|------------|
| 不 *bù* | General (non-perfective) | Yes |
| 没(有) *méi(yǒu)* | Perfective / existential | No (A/Fin) |

## SymAsy: Symmetric and Asymmetric

WALS classifies Mandarin as **both** symmetric and asymmetric:

- **Symmetric**: 不 *bù* negation simply adds the particle before the verb,
  with no structural change. Available across tenses and moods.

- **Asymmetric (A/Fin)**: 没(有) *méi(yǒu)* is restricted to perfective/
  existential contexts and introduces a finiteness-like change: it is
  incompatible with certain aspect markers (e.g., 了 *le* perfective).
  The *bù*/*méi* split itself constitutes an asymmetry — the choice of
  negator depends on aspect, unlike in the affirmative.

## Connection to AspectComparison

The *méi(yǒu)* entry connects to `Fragments.Mandarin.AspectComparison`,
where it is formalized as a cross-domain particle (negative perfective /
not-exceed-threshold).
-/

namespace Fragments.Mandarin.Negation

/-- The general negation particle. -/
def buParticle : String := "bù"

/-- The perfective/existential negation particle. -/
def meiParticle : String := "méi"

/-- The full form of perfective negation. -/
def meiyouParticle : String := "méi-yǒu"

/-- A Mandarin negation example. -/
structure NegExample where
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  /-- Which negation particle is used -/
  negator : String
  /-- Is this construction symmetric (neg = aff + neg marker, no other change)? -/
  symmetric : Bool
  deriving Repr, BEq

/-- 不 *bù* + present/habitual: symmetric. -/
def buPresent : NegExample :=
  { affirmative := "tā chī", negative := "tā bù chī"
  , glossAff := "3SG eat", glossNeg := "3SG NEG eat"
  , negator := "bù", symmetric := true }

/-- 不 *bù* + stative: symmetric. -/
def buStative : NegExample :=
  { affirmative := "tā gāo", negative := "tā bù gāo"
  , glossAff := "3SG tall", glossNeg := "3SG NEG tall"
  , negator := "bù", symmetric := true }

/-- 不 *bù* + future/modal: symmetric. -/
def buFuture : NegExample :=
  { affirmative := "tā huì lái", negative := "tā bù huì lái"
  , glossAff := "3SG will come", glossNeg := "3SG NEG will come"
  , negator := "bù", symmetric := true }

/-- 没(有) *méi(yǒu)* + perfective: asymmetric.
    The perfective marker 了 *le* is dropped under negation. -/
def meiPerfective : NegExample :=
  { affirmative := "tā chī le", negative := "tā méi chī"
  , glossAff := "3SG eat PFV", glossNeg := "3SG NEG.PFV eat"
  , negator := "méi", symmetric := false }

/-- 没(有) *méi(yǒu)* + existential: asymmetric.
    有 *yǒu* 'have/exist' can only be negated with 没, not 不. -/
def meiExistential : NegExample :=
  { affirmative := "tā yǒu qián", negative := "tā méi-yǒu qián"
  , glossAff := "3SG have money", glossNeg := "3SG NEG-have money"
  , negator := "méi-yǒu", symmetric := false }

def allExamples : List NegExample :=
  [buPresent, buStative, buFuture, meiPerfective, meiExistential]

/-- Which negation particle applies in which aspectual context. -/
structure NegatorDistribution where
  context : String
  negator : String
  deriving Repr, BEq

def negatorContexts : List NegatorDistribution :=
  [ { context := "non-perfective / habitual", negator := "bù" }
  , { context := "stative", negator := "bù" }
  , { context := "modal / future", negator := "bù" }
  , { context := "perfective", negator := "méi(yǒu)" }
  , { context := "existential", negator := "méi(yǒu)" }
  ]

/-! ## Verification -/

theorem buParticle_is_bu : buParticle = "bù" := rfl
theorem meiParticle_is_mei : meiParticle = "méi" := rfl

theorem all_examples_count : allExamples.length = 5 := by native_decide

/-- The *bù* constructions are symmetric; the *méi* constructions are not. -/
theorem bu_symmetric_mei_asymmetric :
    (allExamples.filter (·.negator == "bù")).all (·.symmetric) = true ∧
    (allExamples.filter (fun e => e.negator == "méi" || e.negator == "méi-yǒu")).all
      (fun e => !e.symmetric) = true := by
  exact ⟨by native_decide, by native_decide⟩

/-- 3 symmetric + 2 asymmetric constructions = SymAsy. -/
theorem symasy_distribution :
    (allExamples.filter (·.symmetric)).length = 3 ∧
    (allExamples.filter (fun e => !e.symmetric)).length = 2 := by
  exact ⟨by native_decide, by native_decide⟩

/-! ## Bridge to AspectComparison

The *méi-yǒu* entry in `AspectComparison` formalizes the same particle
as a cross-domain negative perfective. -/

theorem meiyou_matches_aspect_comparison :
    Fragments.Mandarin.AspectComparison.meiyou.hanzi = "没有" ∧
    Fragments.Mandarin.AspectComparison.meiyou.pinyin = "méi-yǒu" :=
  ⟨rfl, rfl⟩

end Fragments.Mandarin.Negation
