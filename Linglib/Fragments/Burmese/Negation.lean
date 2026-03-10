import Linglib.Core.Lexical.Word

/-!
# Burmese Negation Fragment
@cite{miestamo-2005} @cite{dryer-haspelmath-2013}

Burmese expresses standard negation with a circumfix: prefix *ma-* on
the verb and suffix *-bu* replacing the TAM markers of the affirmative.

## Always asymmetric (A/Cat)

Burmese negation is always **asymmetric**: the negative suffix *-bu*
replaces the TAM (tense-aspect-mood) markers used in the affirmative,
neutralizing TAM distinctions. This is **paradigmatic asymmetry**: the
negative paradigm has fewer formal distinctions than the affirmative.

## Paradigm (*sa* 'eat')

| Construction | Affirmative | Negative |
|-------------|-------------|----------|
| Realis | *sa-deh* | *ma-sa-bu* |
| Irrealis | *sa-meh* | *ma-sa-bu* |
| Future | *sa-laimeh* | *ma-sa-bu* |

The affirmative distinguishes realis (*-deh*), irrealis (*-meh*), and
future (*-laimeh*), but the negative collapses all three to *ma-...-bu*.
-/

namespace Fragments.Burmese.Negation

/-- The Burmese negative prefix. -/
def negPrefix : String := "ma-"

/-- The Burmese negative suffix (replaces TAM markers). -/
def negSuffix : String := "-bu"

/-- A Burmese negation paradigm entry showing TAM neutralization. -/
structure NegParadigmEntry where
  tamLabel : String
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  deriving Repr, BEq

/-- Paradigm for *sa* 'eat'. -/
def saParadigm : List NegParadigmEntry :=
  [ { tamLabel := "realis"
    , affirmative := "sa-deh", negative := "ma-sa-bu"
    , glossAff := "eat-REAL", glossNeg := "NEG-eat-NEG" }
  , { tamLabel := "irrealis"
    , affirmative := "sa-meh", negative := "ma-sa-bu"
    , glossAff := "eat-IRR", glossNeg := "NEG-eat-NEG" }
  , { tamLabel := "future"
    , affirmative := "sa-laimeh", negative := "ma-sa-bu"
    , glossAff := "eat-FUT", glossNeg := "NEG-eat-NEG" }
  ]

/-- Which TAM categories are available in affirmative vs negative. -/
structure TAMAvailability where
  /-- TAM distinctions available in affirmative -/
  affirmativeTAM : List String
  /-- TAM distinctions available in negative -/
  negativeTAM : List String
  deriving Repr, BEq

def burmeseTAM : TAMAvailability :=
  { affirmativeTAM := ["realis", "irrealis", "future"]
  , negativeTAM := ["general negative"] }

/-! ## Verification -/

theorem negPrefix_is_ma : negPrefix = "ma-" := rfl
theorem negSuffix_is_bu : negSuffix = "-bu" := rfl
theorem sa_paradigm_size : saParadigm.length = 3 := by native_decide

/-- All negative forms are identical: TAM is neutralized. -/
theorem tam_neutralized :
    let negForms := saParadigm.map (·.negative)
    negForms.all (· == "ma-sa-bu") = true := by
  native_decide

/-- The affirmative has 3 distinct TAM forms; the negative has 1. -/
theorem paradigmatic_asymmetry :
    burmeseTAM.affirmativeTAM.length = 3 ∧
    burmeseTAM.negativeTAM.length = 1 := by
  exact ⟨rfl, rfl⟩

/-- All affirmative forms are distinct (3 TAM contrasts). -/
theorem affirmative_forms_distinct :
    let affForms := saParadigm.map (·.affirmative)
    affForms.length = 3 ∧ affForms.eraseDups.length = 3 := by
  exact ⟨rfl, by native_decide⟩

private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- All negative forms contain the circumfix *ma-...-bu*. -/
theorem all_neg_circumfix :
    saParadigm.all (fun e =>
      hasSubstr e.negative "ma-" && hasSubstr e.negative "-bu") = true := by
  native_decide

end Fragments.Burmese.Negation
