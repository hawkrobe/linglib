import Linglib.Fragments.English.Predicates.Verbal

/-!
# Turkish Predicate Lexicon Fragment

Turkish predicates relevant to Qing et al. (2025). Properties like
C-distributivity and NVP class are DERIVED from the `attitudeBuilder` field.
-/

namespace Fragments.Turkish.Predicates

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ThetaRole ControlType PreferentialBuilder AttitudeBuilder)
open IntensionalSemantics.Attitude.Preferential (AttitudeValence NVPClass)

/-- "kork-" — fear (Class 2: C-distributive, negative, takes questions with symmetric interpretation). -/
def kork : VerbEntry where
  form := "kork-"
  form3sg := "korkuyor"
  formPast := "korktu"
  formPastPart := "korkmuş"
  formPresPart := "korkan"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/-- "um-" — hope (Class 3: C-distributive, positive, anti-rogative). -/
def um : VerbEntry where
  form := "um-"
  form3sg := "umuyor"
  formPast := "umdu"
  formPastPart := "ummuş"
  formPresPart := "uman"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- "merak et-" — wonder/be curious (rogative, non-preferential). -/
def merakEt : VerbEntry where
  form := "merak et-"
  form3sg := "merak ediyor"
  formPast := "merak etti"
  formPastPart := "merak etmiş"
  formPresPart := "merak eden"
  complementType := .question
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  takesQuestionBase := true

/-- "endişelen-" — worry (Class 1: non-C-distributive). -/
def endiselen : VerbEntry where
  form := "endişelen-"
  form3sg := "endişeleniyor"
  formPast := "endişelendi"
  formPastPart := "endişelenmiş"
  formPresPart := "endişelenen"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)

def allVerbs : List VerbEntry := [kork, um, merakEt, endiselen]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Turkish.Predicates
