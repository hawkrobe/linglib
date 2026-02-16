import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

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

open Core.Verbs
open NadathurLauer2020.Builder (CausativeBuilder)

/-- French verb entry: extends VerbCore with French inflectional paradigm. -/
structure FrenchVerbEntry extends VerbCore where
  /-- 3sg present -/
  form3sg : String
  /-- Passé simple -/
  formPasse : String
  /-- Participe passé -/
  formPartPasse : String
  /-- Participe présent -/
  formPartPres : String
  deriving Repr, BEq

/-- faire — COMPACT causative (free morpheme). -/
def faire : FrenchVerbEntry where
  form := "faire"
  form3sg := "fait"
  formPasse := "fit"
  formPartPasse := "fait"
  formPartPres := "faisant"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .make

/-- laisser — permissive causative ("let"). -/
def laisser : FrenchVerbEntry where
  form := "laisser"
  form3sg := "laisse"
  formPasse := "laissa"
  formPartPasse := "laissé"
  formPartPres := "laissant"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
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

def allVerbs : List FrenchVerbEntry := [faire, laisser]

def lookup (form : String) : Option FrenchVerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.French.Predicates
