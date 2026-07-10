import Linglib.Syntax.Negation

/-!
# Burmese Negation Fragment
[miestamo-2005] [haspelmath-2013] [dryer-haspelmath-2013]

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

namespace Burmese.Negation

open Syntax.Negation

/-- The Burmese negative prefix. Component of the bipartite *ma-...-bu*
    circumfix; see `circumfix` for the substrate-typed entry. -/
def negPrefix : String := "ma-"

/-- The Burmese negative suffix (replaces TAM markers). Component of the
    bipartite *ma-...-bu* circumfix. -/
def negSuffix : String := "-bu"

/-- *ma-...-bu* — Burmese's bipartite negation circumfix.
    The prefix attaches to the verb stem; the suffix replaces the
    affirmative TAM markers (realis *-deh*, irrealis *-meh*, future
    *-laimeh*), neutralizing TAM distinctions. WALS classifies Burmese
    as `.doubleNegation` (Ch 112A). -/
def circumfix : NegMarkerEntry :=
  { form := "ma-...-bu"
  , morphemeType := .doubleNeg
  , position := .discontinuous }

/-- The Burmese negation system: a single bipartite circumfix.
    The Fragment-side joint consumed by `Studies/Dryer2013Negation.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "mya" [circumfix]

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

theorem sa_paradigm_size : saParadigm.length = 3 := by decide

/-- All negative forms are identical: TAM is neutralized. -/
theorem tam_neutralized :
    let negForms := saParadigm.map (·.negative)
    negForms.all (· == "ma-sa-bu") = true := by
  decide

/-- The affirmative has 3 distinct TAM forms; the negative has 1. -/
theorem paradigmatic_asymmetry :
    burmeseTAM.affirmativeTAM.length = 3 ∧
    burmeseTAM.negativeTAM.length = 1 := by
  exact ⟨rfl, rfl⟩

/-- All affirmative forms are distinct (3 TAM contrasts). -/
theorem affirmative_forms_distinct :
    let affForms := saParadigm.map (·.affirmative)
    affForms.length = 3 ∧ affForms.eraseDups.length = 3 := by
  exact ⟨rfl, by decide⟩

end Burmese.Negation
