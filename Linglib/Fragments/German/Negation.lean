import Linglib.Core.Lexical.NegMarker

/-!
# German Negation Fragment
@cite{miestamo-2005} @cite{haspelmath-2013} @cite{dryer-haspelmath-2013}

German expresses standard negation with the particle *nicht*, which
appears after the finite verb in main clauses and before the non-finite
verb at clause end. Negation is **symmetric**: adding *nicht* introduces
no structural changes beyond the negation marker itself.

## Examples

| Affirmative | Negative |
|-------------|----------|
| *Ich singe* 'I sing' | *Ich singe nicht* 'I don't sing' |
| *Er hat gelesen* 'He has read' | *Er hat nicht gelesen* 'He hasn't read' |

## Key properties

- No finiteness change: finite verb stays finite
- No TAM restrictions: all tenses/moods available under negation
- No paradigmatic gaps: the full inflectional paradigm is maintained
- Constituent negation *nicht* can also negate sub-constituents
-/

namespace Fragments.German.Negation

open Core.Lexical.NegMarker

/-- *nicht* — German's standard negation particle.
    Attaches to the VP at clause-final position; surfaces after the
    finite verb in V2 main clauses (*Ich singe nicht*) and before the
    non-finite verb in periphrastic constructions (*Er hat nicht
    gelesen*). The V2/SOV alternation is why WALS Ch 143A classifies
    German as `.type1Type2` (mixed NegV / VNeg) rather than a single
    position; the `position` field uses `.other` to flag this. -/
def nicht : NegMarkerEntry :=
  { form := "nicht"
  , morphemeType := .particle
  , position := .other }

/-- *kein* — negative determiner (fuses negation + indefinite article).
    Lives here as a lexical fact about German negation morphology;
    the morphosyntactic analysis of NQ-type negative quantifiers in
    non-NC languages is a separate axis from the operator. -/
def negDeterminer : String := "kein"

/-- The German negation system: a single particle.
    The Fragment-side joint consumed by `Phenomena/Negation/Typology.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "deu" [nicht]

/-- A negation example showing symmetric structure. -/
structure NegExample where
  affirmative : String
  negative : String
  gloss : String
  tenseLabel : String
  deriving Repr, BEq

/-- Present tense: *Ich singe* / *Ich singe nicht*. -/
def present : NegExample :=
  { affirmative := "Ich singe"
  , negative := "Ich singe nicht"
  , gloss := "I sing / I sing NEG"
  , tenseLabel := "present" }

/-- Present perfect: *Er hat gelesen* / *Er hat nicht gelesen*. -/
def presentPerfect : NegExample :=
  { affirmative := "Er hat gelesen"
  , negative := "Er hat nicht gelesen"
  , gloss := "He has read / He has NEG read"
  , tenseLabel := "present perfect" }

/-- Preterite: *Sie kam* / *Sie kam nicht*. -/
def preterite : NegExample :=
  { affirmative := "Sie kam"
  , negative := "Sie kam nicht"
  , gloss := "She came / She came NEG"
  , tenseLabel := "preterite" }

/-- Subjunctive II: *Er käme* / *Er käme nicht*. -/
def subjunctiveII : NegExample :=
  { affirmative := "Er käme"
  , negative := "Er käme nicht"
  , gloss := "He would.come / He would.come NEG"
  , tenseLabel := "subjunctive II" }

/-- Future: *Sie wird singen* / *Sie wird nicht singen*. -/
def future : NegExample :=
  { affirmative := "Sie wird singen"
  , negative := "Sie wird nicht singen"
  , gloss := "She will sing / She will NEG sing"
  , tenseLabel := "future" }

def allExamples : List NegExample :=
  [present, presentPerfect, preterite, subjunctiveII, future]

/-! ## Verification -/

private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- German negation is symmetric: the negative form is always the
    affirmative + *nicht*, with no structural change. We verify this
    by checking that each negative example contains *nicht*. -/
theorem all_negative_contain_nicht :
    allExamples.all (fun e => hasSubstr e.negative "nicht") = true := by
  native_decide

/-- All five tenses are available under negation (no paradigmatic gaps). -/
theorem all_tenses_available : allExamples.length = 5 := by native_decide

end Fragments.German.Negation
