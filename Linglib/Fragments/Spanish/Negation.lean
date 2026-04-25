import Linglib.Core.Lexical.NegMarker

/-!
# Spanish Negation Fragment
@cite{miestamo-2005} @cite{haspelmath-2013} @cite{dryer-haspelmath-2013}
@cite{zanuttini-1997}

Spanish expresses standard negation with the preverbal particle *no*.
Negation is **symmetric**: adding *no* introduces no structural changes
to the clause — no finiteness change, no TAM restrictions, no paradigmatic
gaps.

## Examples

| Tense | Affirmative | Negative |
|-------|-------------|----------|
| Present | *Juan come* | *Juan no come* |
| Preterite | *Juan comió* | *Juan no comió* |
| Imperfect | *Juan comía* | *Juan no comía* |
| Future | *Juan comerá* | *Juan no comerá* |
| Subjunctive | *que Juan coma* | *que Juan no coma* |

## Negative concord (n-words)

Spanish has position-dependent negative concord (WALS Ch 115: mixed):
- Preverbal n-words preclude *no*: *Nadie vino* 'Nobody came'
- Postverbal n-words require *no*: *No vi nada* 'NEG saw nothing'

The pattern parallels Italian (*nessuno*/*non*). N-word lexemes —
*nadie*, *nada*, *nunca*, *ninguno* — live in the sibling
`Fragments/Spanish/PolarityItems.lean` per the operator/lexical-reactive
split documented in `Core/Lexical/NegMarker.lean`. The
`NegConcordExample` data below illustrates the marker's interaction with
the n-word system at the sentence level (operator-side typology).
-/

namespace Fragments.Spanish.Negation

open Core.Lexical.NegMarker

/-- *no* — Spanish's standard preverbal negation particle.
    A free word, syntactically immediately preverbal:
    *Juan **no** come* 'Juan doesn't eat'. -/
def no : NegMarkerEntry :=
  { form := "no"
  , morphemeType := .particle
  , position := .preverbal }

/-- The Spanish negation system: a single preverbal particle.
    The Fragment-side joint consumed by `Phenomena/Negation/Typology.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "spa" [no]

/-- A Spanish negation example. -/
structure NegExample where
  affirmative : String
  negative : String
  gloss : String
  tenseLabel : String
  deriving Repr, BEq

def present : NegExample :=
  { affirmative := "Juan come"
  , negative := "Juan no come"
  , gloss := "Juan eats / Juan NEG eats"
  , tenseLabel := "present" }

def preterite : NegExample :=
  { affirmative := "Juan comió"
  , negative := "Juan no comió"
  , gloss := "Juan ate / Juan NEG ate"
  , tenseLabel := "preterite" }

def imperfect : NegExample :=
  { affirmative := "Juan comía"
  , negative := "Juan no comía"
  , gloss := "Juan ate.IMPF / Juan NEG ate.IMPF"
  , tenseLabel := "imperfect" }

def future : NegExample :=
  { affirmative := "Juan comerá"
  , negative := "Juan no comerá"
  , gloss := "Juan will.eat / Juan NEG will.eat"
  , tenseLabel := "future" }

def subjunctive : NegExample :=
  { affirmative := "que Juan coma"
  , negative := "que Juan no coma"
  , gloss := "that Juan eat.SUBJ / that Juan NEG eat.SUBJ"
  , tenseLabel := "subjunctive" }

def allExamples : List NegExample :=
  [present, preterite, imperfect, future, subjunctive]

/-- A negative concord example showing the position-dependent pattern. -/
structure NegConcordExample where
  sentence : String
  translation : String
  hasNo : Bool
  nwordPosition : String
  deriving Repr, BEq

/-- Preverbal n-word: *no* absent. -/
def preverbalNadie : NegConcordExample :=
  { sentence := "Nadie vino"
  , translation := "Nobody came"
  , hasNo := false
  , nwordPosition := "preverbal" }

/-- Postverbal n-word: *no* required. -/
def postverbalNada : NegConcordExample :=
  { sentence := "No vi nada"
  , translation := "I didn't see anything"
  , hasNo := true
  , nwordPosition := "postverbal" }

/-! ## Verification -/

/-- All five tenses are available under negation (no paradigmatic gaps). -/
theorem all_tenses_available : allExamples.length = 5 := by native_decide

private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- All negative examples contain *no*. -/
theorem all_negative_contain_no :
    allExamples.all (fun e => hasSubstr e.negative " no ") = true := by
  native_decide

end Fragments.Spanish.Negation
