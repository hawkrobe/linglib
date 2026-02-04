import Linglib.Fragments.English.Predicates.Verbal

/-!
# Mandarin Predicate Lexicon Fragment

Mandarin predicates relevant to Qing et al. (2025). Properties like
C-distributivity and NVP class are DERIVED from the `attitudeBuilder` field.
-/

namespace Fragments.Mandarin.Predicates

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ThetaRole ControlType PreferentialBuilder AttitudeBuilder)
open Montague.Verb.Attitude.Preferential (AttitudeValence NVPClass)

/-- 期待 "qidai" — look forward to (Class 1: positive, non-C-distributive, takes questions). -/
def qidai : VerbEntry where
  form := "qidai"
  form3sg := "qidai"
  formPast := "qidai"
  formPastPart := "qidai"
  formPresPart := "qidai"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.relevanceBased .positive))

/-- 担心 "danxin" — worry (Class 1: negative, non-C-distributive). -/
def danxin : VerbEntry where
  form := "danxin"
  form3sg := "danxin"
  formPast := "danxin"
  formPastPart := "danxin"
  formPresPart := "danxin"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)

/-- 希望 "xiwang" — hope (Class 3: positive, C-distributive, anti-rogative). -/
def xiwang : VerbEntry where
  form := "xiwang"
  form3sg := "xiwang"
  formPast := "xiwang"
  formPastPart := "xiwang"
  formPresPart := "xiwang"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- 害怕 "haipa" — fear (Class 2: negative, C-distributive, takes questions). -/
def haipa : VerbEntry where
  form := "haipa"
  form3sg := "haipa"
  formPast := "haipa"
  formPastPart := "haipa"
  formPresPart := "haipa"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

def allVerbs : List VerbEntry := [qidai, danxin, xiwang, haipa]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Mandarin.Predicates
