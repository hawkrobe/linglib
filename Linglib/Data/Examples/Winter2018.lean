module

public import Linglib.Data.Examples.Schema

/-!
# `Winter2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Winter2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Winter2018.Examples`.
-/

@[expose] public section

namespace Winter2018.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "winter2018_1"
    source := ⟨"winter-2018", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue dated Dan."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Dan dated Sue.", .acceptable)]
    readings := []
    paperFeatures := [("predicate", "date"), ("property", "symmetric")]
    comment := "A symmetric binary predicate: the two orders are equivalent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "winter2018_2"
    source := ⟨"winter-2018", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue and Dan dated."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "date"), ("alternation", "plain")]
    comment := "The collective alternate of (1a), a plain reciprocal."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "winter2018_3"
    source := ⟨"winter-2018", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue and Dan hugged."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("alternation", "non-plain")]
    comment := "The collective alternate of a non-symmetric binary predicate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "winter2018_4"
    source := ⟨"winter-2018", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue hugged Dan and Dan hugged Sue."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("inference", "does not entail Sue and Dan hugged")]
    comment := "Two unidirectional hugs at different times do not make a collective hug."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "winter2018_5"
    source := ⟨"winter-2018", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A, B and C agreed."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "agree"), ("inference", "one shared opinion")]
    comment := "The collective is stronger than pairwise binary predications: the members share one opinion."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "winter2018_6"
    source := ⟨"winter-2018", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A agreed with B, and B agreed with C, and C agreed with A."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "agree"), ("inference", "possibly three opinions")]
    comment := "Pairwise agreement allows a different opinion for each pair."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "winter2018_7"
    source := ⟨"winter-2018", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The drunk embraced the lamppost."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("The lamppost embraced the drunk.", .unacceptable)]
    readings := []
    paperFeatures := [("predicate", "embrace"), ("property", "non-symmetric")]
    comment := "Subject and object cannot be exchanged."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "winter2018_8"
    source := ⟨"winter-2018", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue and Dan hugged."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("scenario", "(39)"), ("truth", "does not follow")]
    comment := "Not entailed by (38) under scenario (39)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "winter2018_9"
    source := ⟨"winter-2018", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue hugged Dan and Dan hugged Sue."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("scenario", "(39)"), ("truth", "true")]
    comment := "True under scenario (39): Sue hugged Dan while he slept, then he hugged her while she slept."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "winter2018_10"
    source := ⟨"winter-2018", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue hugged Dan and Dan hugged Sue simultaneously."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "hug"), ("inference", "entails Sue and Dan hugged")]
    comment := "With simultaneity the bidirectional hugs yield the collective."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "winter2018_11"
    source := ⟨"winter-2018", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue and Dan broke up."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "break up"), ("inference", "does not entail Sue broke up with Dan")]
    comment := "The instigator may have been Dan alone."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "winter2018_12"
    source := ⟨"winter-2018", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue broke up with Dan."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "break up"), ("inference", "entails Sue and Dan broke up")]
    comment := "One direction of the binary predicate yields the collective."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13 : LinguisticExample :=
  { id := "winter2018_13"
    source := ⟨"winter-2018", "(47)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "morrissey makir et hod-ma'alata, ve-hi makira oto"
    discourseSegments := []
    glossedTokens := [("morrissey", "Morrissey"), ("makir", "know-MASC.SG"), ("et", "ACC"), ("hod-ma'alata", "her-majesty"), ("ve-hi", "and-she"), ("makira", "know-FEM.SG"), ("oto", "him")]
    translation := "Morrissey knows Her Majesty, and she knows him"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "makir"), ("inference", "does not entail (48)")]
    comment := "Mutual acquaintance in the sense of having heard of each other."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "winter2018_14"
    source := ⟨"winter-2018", "(48)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "morrissey ve-hod-ma'alata makirim"
    discourseSegments := []
    glossedTokens := [("morrissey", "Morrissey"), ("ve-hod-ma'alata", "and-her-majesty"), ("makirim", "know-MASC.PL")]
    translation := "Morrissey and Her Majesty are acquainted with each other"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "makir"), ("reading", "collective only")]
    comment := "The intransitive form is unambiguously collective and entails personal acquaintance."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14]

end Winter2018.Examples
