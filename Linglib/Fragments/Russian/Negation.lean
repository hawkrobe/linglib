import Linglib.Core.Lexical.NegMarker

/-!
# Russian Negation Fragment
@cite{miestamo-2005} @cite{haspelmath-2013} @cite{dryer-haspelmath-2013}

Russian expresses standard negation with the preverbal particle *не* (*ne*).
Negation is **symmetric**: adding *не* introduces no structural changes —
no finiteness change, no TAM restrictions, no paradigmatic gaps.

## Negative concord (Ch 115)

Russian has obligatory negative concord (WALS: co-occur):
- *Никто не пришёл* 'Nobody NEG came' = 'Nobody came'
- *Ничего не видел* 'Nothing NEG saw' = '(I) saw nothing'

N-words of the *ни-* series always co-occur with predicate negation *не*.
The lexical-reactive side — `никто`, `ничего`, `никогда`, `кто-либо`, etc. —
lives in `Fragments/Russian/PolarityItems.lean` per the operator/lexical-
reactive split documented in `Core/Lexical/NegMarker.lean`. The
`NegConcordExample` data below illustrates the marker's NC behavior at
the sentence level, which is operator-side typology consumed by
`Phenomena/Negation/Studies/Miestamo2005.lean`.
-/

namespace Fragments.Russian.Negation

open Core.Lexical.NegMarker

/-- *не* — Russian's standard preverbal negation particle.
    A free word, syntactically immediately preverbal. -/
def ne : NegMarkerEntry :=
  { form := "не"
  , morphemeType := .particle
  , position := .preverbal }

/-- The Russian negation system: a single preverbal particle.
    The Fragment-side joint consumed by `Phenomena/Negation/Typology.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "rus" [ne]

/-- A Russian negation example. -/
structure NegExample where
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  tenseLabel : String
  deriving Repr, BEq

/-- Present tense. -/
def present : NegExample :=
  { affirmative := "Он ест"
  , negative := "Он не ест"
  , glossAff := "3SG eat.PRS"
  , glossNeg := "3SG NEG eat.PRS"
  , tenseLabel := "present" }

/-- Past tense. -/
def past : NegExample :=
  { affirmative := "Он ел"
  , negative := "Он не ел"
  , glossAff := "3SG eat.PST.M"
  , glossNeg := "3SG NEG eat.PST.M"
  , tenseLabel := "past" }

/-- Future (periphrastic). -/
def future : NegExample :=
  { affirmative := "Он будет есть"
  , negative := "Он не будет есть"
  , glossAff := "3SG will eat.INF"
  , glossNeg := "3SG NEG will eat.INF"
  , tenseLabel := "future" }

/-- Imperative. -/
def imperative : NegExample :=
  { affirmative := "Ешь!"
  , negative := "Не ешь!"
  , glossAff := "eat.IMP.2SG"
  , glossNeg := "NEG eat.IMP.2SG"
  , tenseLabel := "imperative" }

def allExamples : List NegExample := [present, past, future, imperative]

/-- A negative concord example. -/
structure NegConcordExample where
  sentence : String
  translation : String
  nword : String
  nwordGloss : String
  deriving Repr, BEq

/-- *Никто не пришёл* — obligatory negative concord. -/
def nikto : NegConcordExample :=
  { sentence := "Никто не пришёл"
  , translation := "Nobody came"
  , nword := "никто"
  , nwordGloss := "nobody" }

/-- *Ничего не видел* — obligatory negative concord. -/
def nichego : NegConcordExample :=
  { sentence := "Ничего не видел"
  , translation := "(I) saw nothing"
  , nword := "ничего"
  , nwordGloss := "nothing.GEN" }

/-- *Никогда не приходил* — obligatory negative concord. -/
def nikogda : NegConcordExample :=
  { sentence := "Никогда не приходил"
  , translation := "(He) never came"
  , nword := "никогда"
  , nwordGloss := "never" }

def allConcordExamples : List NegConcordExample := [nikto, nichego, nikogda]

/-! ## Verification -/

private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

theorem ne_form : ne.form = "не" := rfl

theorem all_examples_count : allExamples.length = 4 := by native_decide

/-- All negative examples contain *не* (or sentence-initial *Не*). -/
theorem all_negative_contain_ne :
    allExamples.all (fun e =>
      hasSubstr e.negative "не" || hasSubstr e.negative "Не") = true := by
  native_decide

/-- All negative concord examples contain *не* alongside the n-word. -/
theorem all_concord_contain_ne :
    allConcordExamples.all (fun e => hasSubstr e.sentence "не") = true := by
  native_decide

/-- All n-words begin with *ни-*. -/
theorem all_nwords_ni_prefix :
    allConcordExamples.all (fun e => e.nword.startsWith "ни") = true := by
  native_decide

end Fragments.Russian.Negation
