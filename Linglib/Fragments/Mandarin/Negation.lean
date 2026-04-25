import Linglib.Core.Lexical.NegMarker
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

open Core.Lexical.NegMarker

/-- 不 *bù* — the general non-perfective negation particle.
    Used with imperfective, stative, modal, and future contexts;
    excluded from perfective and existential. Symmetric: simply adds
    to the verb without further structural change. -/
def bu : NegMarkerEntry :=
  { form := "bù"
  , morphemeType := .particle
  , position := .preverbal }

/-- 没 *méi* (long form 没有 *méi-yǒu*) — the perfective/existential
    negation particle. Asymmetric: incompatible with the perfective
    aspect marker 了 *le*; required as the negator of 有 *yǒu* 'have'.
    The choice between *bù* and *méi* is aspect-conditioned. -/
def mei : NegMarkerEntry :=
  { form := "méi"
  , morphemeType := .particle
  , position := .preverbal }

/-- The Mandarin negation system: two aspect-conditioned markers.
    *bù* (default, non-perfective) listed first per the ordering
    convention in `NegationSystem`; *méi* second. The Fragment-side
    joint consumed by `Phenomena/Negation/Typology.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "cmn" [bu, mei]

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

-- ════════════════════════════════════════════════════
-- Expletive Negation Markers
-- ════════════════════════════════════════════════════

/-! ## Expletive Negation
@cite{jin-koenig-2021}

Mandarin EN negators show striking **trigger-class covariation**: different
trigger classes select different expletive negators, and the choice is
semantically motivated.

| Trigger class | EN negator      | Gloss              | Note                     |
|---------------|-----------------|---------------------|--------------------------|
| FEAR          | 别 *bié*        | don't (imperative)  | Neither 不 nor 没 allowed |
| FEAR          | 不要 *búyào*    | not-want (imp.)     | Neither 不 nor 没 allowed |
| REGRET        | 不该 *bùgāi*   | shouldn't (deontic) | Must include deontic modal|
| COMPLAIN      | 不该 *bùgāi*   | shouldn't (deontic) | Must include deontic modal|
| DENY          | 不 *bù*        | NEG (general)       | Standard negator         |
| BEFORE        | 不 *bù*        | NEG (general)       | Via 以前 *yǐqián*          |
| ALMOST        | 没 *méi*       | NEG (perfective)    | Via 差点儿 *chàdiǎnr*        |

The imperative negators *bié*/*búyào* for FEAR connect to the
desiderative semantics: fear activates the desire for ¬p, and the
imperative form lexicalizes the prohibition component.

The deontic negator *bùgāi* for REGRET/COMPLAIN connects to the
behavioral-standards semantics: the negative inference is that
¬p is consistent with X's standards, i.e., p *shouldn't* have happened.
-/

/-- Mandarin imperative negation particle (used as EN for FEAR). -/
def bieParticle : String := "bié"

/-- Mandarin imperative negation 'not-want' (used as EN for FEAR). -/
def buyaoParticle : String := "búyào"

/-- Mandarin deontic negation 'shouldn't' (used as EN for REGRET/COMPLAIN). -/
def bugaiParticle : String := "bùgāi"

/-- An expletive negation marker and its trigger context. -/
structure ENTriggerNegator where
  /-- The trigger class label (from @cite{jin-koenig-2021} Table 5) -/
  triggerClass : String
  /-- Mandarin trigger lexical item -/
  triggerForm : String
  /-- EN negator form (pinyin) -/
  enNegatorForm : String
  /-- EN negator gloss -/
  enNegatorGloss : String
  deriving Repr, BEq

/-- EN trigger-negator pairings from @cite{jin-koenig-2021}, Table 5
    and §6.1–6.4. -/
def enTriggerNegators : List ENTriggerNegator :=
  [ { triggerClass := "FEAR", triggerForm := "pà"
    , enNegatorForm := "bié", enNegatorGloss := "don't (imperative)" }
  , { triggerClass := "AVOID", triggerForm := "bìmiǎn"
    , enNegatorForm := "bù/méi(yǒu)", enNegatorGloss := "NEG (general/perfective)" }
  , { triggerClass := "REGRET", triggerForm := "hòuhuǐ"
    , enNegatorForm := "bùgāi", enNegatorGloss := "shouldn't (deontic)" }
  , { triggerClass := "COMPLAIN", triggerForm := "bàoyuan"
    , enNegatorForm := "bùgāi", enNegatorGloss := "shouldn't (deontic)" }
  , { triggerClass := "DENY", triggerForm := "fǒurèn"
    , enNegatorForm := "bù", enNegatorGloss := "NEG (general)" }
  , { triggerClass := "BEFORE", triggerForm := "yǐqián"
    , enNegatorForm := "bù", enNegatorGloss := "NEG (general)" }
  , { triggerClass := "ALMOST", triggerForm := "chàdiǎnr"
    , enNegatorForm := "méi", enNegatorGloss := "NEG (perfective)" } ]

/-- FEAR triggers use imperative negators, not the standard
    *bù* or *méi*. This connects to the desiderative semantics:
    fear activates desire for ¬p, and imperative negation lexicalizes
    prohibition (@cite{jin-koenig-2021}, §6.1.1, ex. 14). -/
theorem fear_uses_imperative_neg :
    (enTriggerNegators.filter (·.triggerClass == "FEAR")).all
      (·.enNegatorForm == "bié") = true := by native_decide

/-- REGRET/COMPLAIN triggers use the deontic negator *bùgāi* 'shouldn't'.
    This connects to the behavioral-standards semantics: ¬p is consistent
    with X's standards → p *shouldn't* have happened
    (@cite{jin-koenig-2021}, §6.1.2). -/
theorem regret_uses_deontic_neg :
    (enTriggerNegators.filter (fun e =>
      e.triggerClass == "REGRET" || e.triggerClass == "COMPLAIN")).all
      (·.enNegatorForm == "bùgāi") = true := by native_decide

end Fragments.Mandarin.Negation
