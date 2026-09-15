import Linglib.Data.Examples.Schema

/-!
# `White2014` — typed example data

Auto-generated from `Linglib/Data/Examples/White2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace White2014.Examples`.
-/

namespace White2014.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "white2014_1"
    source := ⟨"white-2014", "poster (1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John remembered that he took the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite"), ("inference", "presupposes John took the trash out")]
    comment := "Factive with a finite complement; the same holds of didn't forget."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "white2014_2"
    source := ⟨"white-2014", "poster (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John remembered to take the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("inference", "entails John took the trash out")]
    comment := "Implicative with a nonfinite complement: the positive actuality entailment."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "white2014_3"
    source := ⟨"white-2014", "poster (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John forgot to take the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("inference", "entails John didn't take the trash out")]
    comment := "The negative actuality entailment; the same holds of didn't remember."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "white2014_4"
    source := ⟨"white-2014", "poster (3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John remembered that he was supposed to take the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite with overt modal"), ("inference", "presupposes John was supposed to take the trash out")]
    comment := "The overt modal in the finite complement gives the modalized presupposition of (2)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "white2014_5"
    source := ⟨"white-2014", "poster (5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John had to stay home from work during the government shutdown."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "strongly implicates John stayed home")]
    comment := "An actuality entailment of a root modal under perfective aspect."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "white2014_6"
    source := ⟨"white-2014", "poster (6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John remembered that he was supposed to take the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite with overt modal"), ("inference", "does not entail John took the trash out")]
    comment := "No actuality entailment: the finite complement binds its own event."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "white2014_7"
    source := ⟨"white-2014", "poster (15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary asked John to fill the bird feeder. He did so, and the next week, she asked again. John remembered to fill the feeder again."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "again"), ("reading", "restructured")]
    comment := "Again over a filling event that occurred: evidence that remember restructures."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "white2014_8"
    source := ⟨"white-2014", "poster (15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary asked John to fill the bird feeder. He remembered that he was supposed to, but didn't. The next week, she asked again and John again remembered to fill the feeder."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "again"), ("reading", "restructured")]
    comment := "Again cannot pick up a remembering whose filling event did not occur."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "white2014_9"
    source := ⟨"white-2014", "poster (16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A different student remembered to read every paper."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "inverse scope"), ("scope", "every over a")]
    comment := "Inverse scope of every out of the nonfinite complement is available."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "white2014_10"
    source := ⟨"white-2014", "poster (16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A different person remembered that he read every paper."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "inverse scope"), ("scope", "every over a")]
    comment := "No inverse scope out of the finite complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "white2014_11"
    source := ⟨"white-2014", "poster (17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John remembered to read every paper Bill did."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "antecedent-contained deletion"), ("ellipsis", "matrix or embedded")]
    comment := "Antecedent-contained deletion can target the matrix with the nonfinite complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "white2014_12"
    source := ⟨"white-2014", "poster (17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John remembered that he read every paper Bill did."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "antecedent-contained deletion"), ("ellipsis", "embedded only")]
    comment := "With the finite complement the deletion can target only the embedded clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12]

end White2014.Examples
