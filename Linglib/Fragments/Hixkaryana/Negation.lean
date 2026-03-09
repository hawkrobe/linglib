import Linglib.Core.Lexical.Word

/-!
# Hixkaryana Negation Fragment
@cite{miestamo-2005} @cite{dryer-haspelmath-2013}

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

namespace Fragments.Hixkaryana.Negation

/-- The standard negation suffix. -/
def negSuffix : String := "-hira"

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

theorem negSuffix_is_hira : negSuffix = "-hira" := rfl

theorem all_examples_count : allExamples.length = 1 := by native_decide

/-- All constructions are asymmetric. -/
theorem all_asymmetric :
    allExamples.all (fun e => !e.symmetric) = true := by
  native_decide

/-- Negation introduces a copula as the finite element. -/
theorem copula_as_finite :
    allExamples.all (·.copulaFinite) = true := by
  native_decide

private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- All negative examples contain the suffix *-hira*. -/
theorem all_negative_contain_hira :
    allExamples.all (fun e => hasSubstr e.negative "-hira") = true := by
  native_decide

end Fragments.Hixkaryana.Negation
