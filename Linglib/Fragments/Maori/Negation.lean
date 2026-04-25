import Linglib.Core.Lexical.NegMarker

/-!
# Maori Negation Fragment
@cite{miestamo-2005} @cite{haspelmath-2013} @cite{dryer-haspelmath-2013}

Maori expresses standard negation with the word *kāhore* (also written
*kaahore*). WALS classifies the negator's morpheme type as **wordUnclear** —
in this isolating language, it is unclear whether *kāhore* is a verb or a
particle.

## Asymmetric A/Fin

WALS classifies Maori negation as **asymmetric (A/Fin)**: the negator
functions as a quasi-auxiliary that changes the finiteness structure.
In the affirmative, the lexical verb is preceded by a TAM particle
(e.g., *kei te* progressive). Under negation, *kāhore* takes the
position of the TAM particle and the verb appears in a nominalized
form with *e...ana* or bare.

## Examples

| | Affirmative | Negative |
|---|---|---|
| Progressive | *Kei te kai ia* | *Kāhore ia e kai ana* |
| Past | *I kai ia* | *Kāhore ia i kai* |
-/

namespace Fragments.Maori.Negation

open Core.Lexical.NegMarker

/-- *kāhore* — Maori's standard sentential negation word.
    WALS Ch 112A classifies this as `.wordUnclear` — in Maori's isolating
    morphology, *kāhore* could be analyzed as a verb or a particle.
    Functions as a quasi-auxiliary that takes the TAM-particle position. -/
def kahore : NegMarkerEntry :=
  { form := "kāhore"
  , morphemeType := .wordUnclear
  , position := .preverbal }

/-- The Maori negation system: a single quasi-auxiliary word.
    The Fragment-side joint consumed by `Phenomena/Negation/Typology.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "mri" [kahore]

/-- A Maori negation example. -/
structure NegExample where
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  tamLabel : String
  /-- Is this construction symmetric? -/
  symmetric : Bool
  deriving Repr, BEq

/-- Progressive: *Kei te kai ia* → *Kāhore ia e kai ana*. Asymmetric:
    TAM particle replaced by negator, verb nominalized. -/
def progressive : NegExample :=
  { affirmative := "Kei te kai ia"
  , negative := "Kāhore ia e kai ana"
  , glossAff := "PROG eat 3SG"
  , glossNeg := "NEG 3SG TAM eat PROG"
  , tamLabel := "progressive"
  , symmetric := false }

/-- Past: *I kai ia* → *Kāhore ia i kai*. Asymmetric:
    negator replaces TAM position. -/
def past : NegExample :=
  { affirmative := "I kai ia"
  , negative := "Kāhore ia i kai"
  , glossAff := "PST eat 3SG"
  , glossNeg := "NEG 3SG PST eat"
  , tamLabel := "past"
  , symmetric := false }

def allExamples : List NegExample := [progressive, past]

/-! ## Verification -/

theorem all_examples_count : allExamples.length = 2 := by native_decide

/-- All constructions are asymmetric (A/Fin). -/
theorem all_asymmetric :
    allExamples.all (fun e => !e.symmetric) = true := by
  native_decide

private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- All negative examples contain the negator *Kāhore*. -/
theorem all_negative_contain_kahore :
    allExamples.all (fun e => hasSubstr e.negative "Kāhore") = true := by
  native_decide

end Fragments.Maori.Negation
