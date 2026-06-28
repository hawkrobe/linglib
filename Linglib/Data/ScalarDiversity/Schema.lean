import Mathlib.Data.Rat.Defs

/-!
# Scalar-diversity data schema

Typed schema for per-scale scalar-inference data, the home of the canonical
matrix behind [van-tiel-geurts-2016] (and reusable by later scalar-diversity
studies). Generated rows live in `Data/ScalarDiversity/<Paper>.lean`, emitted
from the canonical `<Paper>.json` by `scripts/gen_scalardiversity.py`.

This is substrate: it imports nothing from `Linglib/`. Consumers (the paper's
study file, `Studies/Ronai2024`) import the generated module.

## Main definitions
* `GrammaticalClass` — open vs closed lexical class of a scale's members.
* `ScaleDatum` — one scale's nine measured columns (SI rates, cloze rates,
  frequency ratio, LSA relatedness, semantic distance, boundedness).
-/

namespace VanTielEtAl2016

/-- Grammatical category of a scale's members. The open/closed split (closed =
    smaller alternative set) is one operationalisation of scale *availability*. -/
inductive GrammaticalClass where
  | adjective
  | adverb
  | auxiliaryVerb
  | mainVerb
  | quantifier
  deriving DecidableEq, Repr, Inhabited

/-- Whether a scale's members are from a closed grammatical class (quantifiers,
    auxiliaries) — predicted, on the availability hypothesis, to be more available. -/
def GrammaticalClass.isClosedClass : GrammaticalClass → Bool
  | .quantifier => true
  | .auxiliaryVerb => true
  | _ => false

/-- One scale's measured data ([van-tiel-geurts-2016], Table 3). SI rates from
    the two inference experiments, the two availability proxies measured per
    scale (cloze mention rates, frequency ratio, LSA relatedness) and the two
    distinctness measures (semantic distance, boundedness). -/
structure ScaleDatum where
  /-- Weaker scalar term (α). -/
  weakerTerm : String
  /-- Stronger scalar term (β). -/
  strongerTerm : String
  /-- Grammatical category. -/
  category : GrammaticalClass
  /-- SI rate in Experiment 1 (neutral content, %). -/
  siRateExp1 : Nat
  /-- SI rate in Experiment 2 (non-neutral content, %). -/
  siRateExp2 : Nat
  /-- Cloze task: % mentioning the stronger term (Exp 3, neutral, lenient). -/
  clozeNeutral : Option Nat
  /-- Cloze task: % mentioning the stronger term (Exp 3, non-neutral, lenient). -/
  clozeNonNeutral : Option Nat
  /-- Log ratio of weaker-to-stronger term frequencies (`none` = not measured). -/
  freqRatio : Option ℚ
  /-- LSA semantic relatedness in `[0,1]` (`none` = not available). -/
  lsaRelatedness : Option ℚ
  /-- Mean semantic distance rating (1–7 scale, Exp 4). -/
  semanticDistance : ℚ
  /-- Whether the stronger term denotes a scale endpoint (a *bounded* scale). -/
  bounded : Bool
  deriving Repr

end VanTielEtAl2016
