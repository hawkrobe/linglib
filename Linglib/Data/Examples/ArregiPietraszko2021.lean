import Linglib.Data.Examples.Schema

/-!
# `ArregiPietraszko2021` — typed example data

Auto-generated from `Linglib/Data/Examples/ArregiPietraszko2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ArregiPietraszko2021.Examples`.
-/

namespace ArregiPietraszko2021.Examples

open Data.Examples

def ex27 : LinguisticExample :=
  { id := "arregipietraszko2021_ex27"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (36c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where does Sue eat fish?"
    discourseSegments := []
    glossedTokens := []
    translation := "Where does Sue eat fish?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "question"), ("verb_type", "lexical"), ("do_support", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex27. Do-support in a wh-question with a lexical verb."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30 : LinguisticExample :=
  { id := "arregipietraszko2021_ex30"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (37c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where is Sue eating fish?"
    discourseSegments := []
    glossedTokens := []
    translation := "Where is Sue eating fish?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "question"), ("verb_type", "auxiliary"), ("do_support", "false")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex30. Auxiliary inverts directly — no do-support."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex31 : LinguisticExample :=
  { id := "arregipietraszko2021_ex31"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (37c), starred variant"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where does Sue be eating fish?"
    discourseSegments := []
    glossedTokens := []
    translation := "Where does Sue be eating fish?"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "question"), ("verb_type", "auxiliary"), ("do_support", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex31. Do-support with an auxiliary is ungrammatical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32 : LinguisticExample :=
  { id := "arregipietraszko2021_ex32"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue does not eat fish"
    discourseSegments := []
    glossedTokens := []
    translation := "Sue does not eat fish"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "negation"), ("verb_type", "lexical"), ("do_support", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex32. Do-support in sentential negation with a lexical verb."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex33 : LinguisticExample :=
  { id := "arregipietraszko2021_ex33"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (36a), starred variant"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue not eats fish"
    discourseSegments := []
    glossedTokens := []
    translation := "Sue not eats fish"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "negation"), ("verb_type", "lexical"), ("do_support", "false")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex33. Lexical verb cannot raise past negation; omitting do-support is ungrammatical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex34 : LinguisticExample :=
  { id := "arregipietraszko2021_ex34"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue is not eating fish"
    discourseSegments := []
    glossedTokens := []
    translation := "Sue is not eating fish"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "negation"), ("verb_type", "auxiliary"), ("do_support", "false")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex34. Auxiliary raises past negation — no do-support."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex35 : LinguisticExample :=
  { id := "arregipietraszko2021_ex35"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (37a), starred variant"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue does not be eating fish"
    discourseSegments := []
    glossedTokens := []
    translation := "Sue does not be eating fish"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "negation"), ("verb_type", "auxiliary"), ("do_support", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex35. Do-support with an auxiliary is ungrammatical even under negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38 : LinguisticExample :=
  { id := "arregipietraszko2021_ex38"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED VP-ellipsis discussion (no example number)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She runs faster than he does"
    discourseSegments := []
    glossedTokens := []
    translation := "She runs faster than he does"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "vpEllipsis"), ("verb_type", "lexical"), ("do_support", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex38. VP ellipsis strands tense; do-support with a lexical verb."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39 : LinguisticExample :=
  { id := "arregipietraszko2021_ex39"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue DOES eat fish"
    discourseSegments := []
    glossedTokens := []
    translation := "Sue DOES eat fish"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "verum"), ("verb_type", "lexical"), ("do_support", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex39. Verum focus with do-support on a lexical verb."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40 : LinguisticExample :=
  { id := "arregipietraszko2021_ex40"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She IS eating fish"
    discourseSegments := []
    glossedTokens := []
    translation := "She IS eating fish"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "verum"), ("verb_type", "auxiliary"), ("do_support", "false")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex40. Verum focus with an auxiliary — no do-support."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41 : LinguisticExample :=
  { id := "arregipietraszko2021_ex41"
    source := ⟨"arregi-pietraszko-2021", "UNVERIFIED (37b), starred variant"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She DOES be eating fish"
    discourseSegments := []
    glossedTokens := []
    translation := "She DOES be eating fish"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "verum"), ("verb_type", "auxiliary"), ("do_support", "true")]
    comment := "Migrated from Phenomena/WordOrder/SubjectAuxInversion.lean ex41. Do-support with an auxiliary is ungrammatical even for verum focus."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex27, ex30, ex31, ex32, ex33, ex34, ex35, ex38, ex39, ex40, ex41]

end ArregiPietraszko2021.Examples
