import Linglib.Fragments.English.Predicates.Verbal

/-!
# French Predicate Lexicon Fragment

French causative predicates, centered on the *faire* causative.
Song (1996) classifies *faire* as a COMPACT causative with free morpheme
realization: the causative and effect verbs form a tight syntactic unit
despite being separate words.

"Je ferai lire le livre à Nicole" = "I will make Nicole read the book"
(faire + infinitive = single predicate for case marking purposes)

## References

- Song, J. J. (1996). Causatives and Causation. Longman. §5.1
- Kayne, R. (1975). French Syntax. MIT Press. (faire-infinitive)
-/

namespace Fragments.French.Predicates

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ControlType)
open NadathurLauer2020.Builder (CausativeBuilder)

/-- faire — COMPACT causative (free morpheme).

    "faire + infinitive" forms a tight syntactic unit (Kayne 1975):
    the causee is marked with *à* (dative) when the embedded verb is
    transitive, and with accusative when intransitive.

    Song (1996): COMPACT type, free morpheme realization. -/
def faire : VerbEntry where
  form := "faire"
  form3sg := "fait"
  formPast := "fit"
  formPastPart := "fait"
  formPresPart := "faisant"
  complementType := .smallClause  -- faire + bare infinitive
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .make

/-- laisser — permissive causative ("let").

    "laisser + infinitive" = permissive causation (barrier removal).
    "Je l'ai laissé partir" = "I let him leave" -/
def laisser : VerbEntry where
  form := "laisser"
  form3sg := "laisse"
  formPast := "laissa"
  formPastPart := "laissé"
  formPresPart := "laissant"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .enable

/-- French *faire* uses `.make` builder. -/
theorem faire_is_make :
    faire.causativeBuilder = some .make := rfl

/-- French *laisser* uses `.enable` builder (permissive). -/
theorem laisser_is_enable :
    laisser.causativeBuilder = some .enable := rfl

/-- *faire* and *laisser* have different builders (make vs enable). -/
theorem faire_laisser_different :
    faire.causativeBuilder ≠ laisser.causativeBuilder := by decide

def allVerbs : List VerbEntry := [faire, laisser]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.French.Predicates
