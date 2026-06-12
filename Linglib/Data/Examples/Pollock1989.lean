import Linglib.Data.Examples.Schema

/-!
# `Pollock1989` — typed example data

Auto-generated from `Linglib/Data/Examples/Pollock1989.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pollock1989.Examples`.
-/

namespace Pollock1989.Examples

open Data.Examples

def ex_p01 : LinguisticExample :=
  { id := "pollock1989_ex_p01"
    source := ⟨"pollock-1989", "UNVERIFIED (3b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Aime-t-il Marie?"
    discourseSegments := []
    glossedTokens := []
    translation := "Does he love Marie?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "inversion"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p01. French lexical verb inverts with the subject (V-to-I-to-C)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p02 : LinguisticExample :=
  { id := "pollock1989_ex_p02"
    source := ⟨"pollock-1989", "UNVERIFIED (3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Likes he Mary?"
    discourseSegments := []
    glossedTokens := []
    translation := "Likes he Mary?"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "inversion"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p02. English lexical verb cannot invert with the subject (*V-to-C)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p03 : LinguisticExample :=
  { id := "pollock1989_ex_p03"
    source := ⟨"pollock-1989", "UNVERIFIED (4b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jean embrasse souvent Marie"
    discourseSegments := []
    glossedTokens := []
    translation := "Jean often kisses Marie"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "adverb"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p03. French lexical verb raises past the adverb (V > Adv)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p04 : LinguisticExample :=
  { id := "pollock1989_ex_p04"
    source := ⟨"pollock-1989", "UNVERIFIED (4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John kisses often Mary"
    discourseSegments := []
    glossedTokens := []
    translation := "John kisses often Mary"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "adverb"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p04. English lexical verb cannot raise past the adverb (*V > Adv)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p05 : LinguisticExample :=
  { id := "pollock1989_ex_p05"
    source := ⟨"pollock-1989", "UNVERIFIED (4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John often kisses Mary"
    discourseSegments := []
    glossedTokens := []
    translation := "John often kisses Mary"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "adverb"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "false")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p05. English adverb precedes the in-situ lexical verb (Adv > V)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p06 : LinguisticExample :=
  { id := "pollock1989_ex_p06"
    source := ⟨"pollock-1989", "UNVERIFIED (4d)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jean souvent embrasse Marie"
    discourseSegments := []
    glossedTokens := []
    translation := "Jean often kisses Marie"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "adverb"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "false")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p06. French adverb cannot precede the lexical verb (*Adv > V; V must raise)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p07 : LinguisticExample :=
  { id := "pollock1989_ex_p07"
    source := ⟨"pollock-1989", "UNVERIFIED (2b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jean n'aime pas Marie"
    discourseSegments := []
    glossedTokens := []
    translation := "Jean does not love Marie"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "negation"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p07. French lexical verb raises past negation (V > Neg)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p08 : LinguisticExample :=
  { id := "pollock1989_ex_p08"
    source := ⟨"pollock-1989", "UNVERIFIED (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John likes not Mary"
    discourseSegments := []
    glossedTokens := []
    translation := "John likes not Mary"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "negation"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p08. English lexical verb cannot raise past negation (*V > Neg)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p09 : LinguisticExample :=
  { id := "pollock1989_ex_p09"
    source := ⟨"pollock-1989", "UNVERIFIED (5b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mes amis aiment tous Marie"
    discourseSegments := []
    glossedTokens := []
    translation := "My friends all love Marie"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "floatingQ"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p09. French lexical verb raises past the floating quantifier (V > FQ)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p10 : LinguisticExample :=
  { id := "pollock1989_ex_p10"
    source := ⟨"pollock-1989", "UNVERIFIED (5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My friends love all Mary"
    discourseSegments := []
    glossedTokens := []
    translation := "My friends love all Mary"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "floatingQ"), ("verb_type", "lexical"), ("v_precedes_diagnostic", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p10. English lexical verb cannot raise past the floating quantifier (*V > FQ)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p11 : LinguisticExample :=
  { id := "pollock1989_ex_p11"
    source := ⟨"pollock-1989", "UNVERIFIED auxiliary raising (no quoted example number)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has often eaten pizza"
    discourseSegments := []
    glossedTokens := []
    translation := "John has often eaten pizza"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "adverb"), ("verb_type", "auxiliary"), ("v_precedes_diagnostic", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p11. English auxiliary raises past the adverb (Aux > Adv), patterning with French lexical verbs."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_p12 : LinguisticExample :=
  { id := "pollock1989_ex_p12"
    source := ⟨"pollock-1989", "UNVERIFIED auxiliary raising (no quoted example number)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John often has eaten pizza"
    discourseSegments := []
    glossedTokens := []
    translation := "John often has eaten pizza"
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "adverb"), ("verb_type", "auxiliary"), ("v_precedes_diagnostic", "false")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex_p12. English adverb before the auxiliary is marginal (Aux should raise)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_p01, ex_p02, ex_p03, ex_p04, ex_p05, ex_p06, ex_p07, ex_p08, ex_p09, ex_p10, ex_p11, ex_p12]

end Pollock1989.Examples
