import Linglib.Syntax.Negation

/-!
# Hixkaryana Negation Fragment
[miestamo-2005] [haspelmath-2013] [dryer-haspelmath-2013]

Hixkaryana (Carib; Brazil) expresses standard negation with the suffix
*-hira* on the verb. Negation is **asymmetric (A/Fin)**: the negative
suffix deverbalizes the lexical verb, and a non-negative copula takes
over as the finite element.

## Example

| | Affirmative | Negative |
|---|---|---|
| Immediate past | *amryeki* 'I hunted' | *amryeki-hira w-ah-ko* 'hunt-NEG 1SUBJ-be-IMM.PST' |

The deverbalization + copula pattern is a clear case of A/Fin asymmetry:
the lexical verb loses its finiteness under negation, and a copula verb
becomes the finite element carrying person/tense marking.
-/

namespace Hixkaryana.Negation

open Syntax.Negation

/-- *-hira* — Hixkaryana's standard negation suffix.
    Deverbalizes the lexical verb (A/Fin asymmetry); a copula then takes
    over as the finite element. -/
def hira : NegMarkerEntry :=
  { form := "-hira"
  , morphemeType := .affix
  , position := .morphological }

/-- The Hixkaryana negation system: a single deverbalizing suffix.
    The Fragment-side joint consumed by `Studies/Dryer2013Negation.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "hix" [hira]

/-- A Hixkaryana negation example. -/
structure NegExample where
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  /-- Does this construction use a copula as the finite element? -/
  copulaFinite : Bool
  /-- Is this construction symmetric? -/
  symmetric : Bool
  deriving Repr, BEq

/-- Immediate past: deverbalization + copula. -/
def immPast : NegExample :=
  { affirmative := "amryeki"
  , negative := "amryeki-hira w-ah-ko"
  , glossAff := "hunt.1SG.IMM.PST"
  , glossNeg := "hunt-NEG 1SUBJ-be-IMM.PST"
  , copulaFinite := true
  , symmetric := false }

def allExamples : List NegExample := [immPast]

/-! ## Verification -/

theorem all_examples_count : allExamples.length = 1 := by decide

/-- All constructions are asymmetric. -/
theorem all_asymmetric :
    allExamples.all (fun e => !e.symmetric) = true := by
  decide

/-- Negation introduces a copula as the finite element. -/
theorem copula_as_finite :
    allExamples.all (·.copulaFinite) = true := by
  decide

/-- Hixkaryana negation profile (WALS Ch 112-115 + Greco/JinKoenig fields). -/
def negationProfile : Syntax.Negation.NegationProfile :=
  { language := "Hixkaryana"
  , iso := "hix"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , negIndefinite := Option.none
  , negMarkers := ["-hira"]
  , negIsHead := none
  , enAttested := none }

end Hixkaryana.Negation
