import Linglib.Fragments.English.Predicates.Verbal

/-!
# Japanese Predicate Lexicon Fragment

Japanese predicates relevant to Qing et al. (2025). Properties like
C-distributivity and NVP class are DERIVED from the `attitudeBuilder` field.
-/

namespace Fragments.Japanese.Predicates

open Fragments.English.Predicates.Verbal (VerbEntry VerbClass ComplementType ThetaRole ControlType PreferentialBuilder AttitudeBuilder)
open IntensionalSemantics.Attitude.Preferential (AttitudeValence NVPClass)

/-- 楽しみ "tanosimi" — looking forward to (Class 1: positive, non-C-distributive). -/
def tanosimi : VerbEntry where
  form := "tanosimi"
  form3sg := "tanosimi da"
  formPast := "tanosimi datta"
  formPastPart := "tanosimi"
  formPresPart := "tanosimi"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.relevanceBased .positive))

/-- 恐れ "osore" — fear (Class 2: negative, C-distributive). -/
def osore : VerbEntry where
  form := "osore"
  form3sg := "osoreru"
  formPast := "osoreta"
  formPastPart := "osorete"
  formPresPart := "osoreteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/-- 期待 "kitai" — expect/hope (Class 3: positive, C-distributive, anti-rogative). -/
def kitai : VerbEntry where
  form := "kitai"
  form3sg := "kitai suru"
  formPast := "kitai shita"
  formPastPart := "kitai shite"
  formPresPart := "kitai shiteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- 心配 "shinpai" — worry (Class 1: non-C-distributive). -/
def shinpai : VerbEntry where
  form := "shinpai"
  form3sg := "shinpai suru"
  formPast := "shinpai shita"
  formPastPart := "shinpai shite"
  formPresPart := "shinpai shiteiru"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)

def allVerbs : List VerbEntry := [tanosimi, osore, kitai, shinpai]

def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (·.form == form)

end Fragments.Japanese.Predicates
