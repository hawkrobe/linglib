import Linglib.Data.Examples.Schema

/-!
# `Rett2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Rett2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rett2015.Examples`.
-/

namespace Rett2015.Examples

open Data.Examples

def positive_tall : LinguisticExample :=
  { id := "rett2015_positive_tall"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is tall."
    discourseSegments := []
    glossedTokens := []
    translation := "Adam is tall."
    context := "Presupposes Adam's height exceeds the standard for tallness."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "positive"), ("polarity", "positive"), ("evaluative", "true")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def positive_short : LinguisticExample :=
  { id := "rett2015_positive_short"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is short."
    discourseSegments := []
    glossedTokens := []
    translation := "Adam is short."
    context := "Presupposes Adam's height is below the standard for shortness."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "positive"), ("polarity", "negative"), ("evaluative", "true")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def comparative_tall : LinguisticExample :=
  { id := "rett2015_comparative_tall"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is taller than Doug."
    discourseSegments := []
    glossedTokens := []
    translation := "Adam is taller than Doug."
    context := "True even if both Adam and Doug are short."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "comparative"), ("polarity", "positive"), ("evaluative", "false")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def comparative_short : LinguisticExample :=
  { id := "rett2015_comparative_short"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is shorter than Doug."
    discourseSegments := []
    glossedTokens := []
    translation := "Adam is shorter than Doug."
    context := "True even if both Adam and Doug are tall."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "comparative"), ("polarity", "negative"), ("evaluative", "false")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def equative_tall : LinguisticExample :=
  { id := "rett2015_equative_tall"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is as tall as Doug."
    discourseSegments := []
    glossedTokens := []
    translation := "Adam is as tall as Doug."
    context := "Does not presuppose that either is tall."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "equative"), ("polarity", "positive"), ("evaluative", "false")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def equative_short : LinguisticExample :=
  { id := "rett2015_equative_short"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is as short as Doug."
    discourseSegments := []
    glossedTokens := []
    translation := "Adam is as short as Doug."
    context := "Presupposes both Adam and Doug are short."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "equative"), ("polarity", "negative"), ("evaluative", "true")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mp_tall : LinguisticExample :=
  { id := "rett2015_mp_tall"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Adam is 6ft tall."
    discourseSegments := []
    glossedTokens := []
    translation := "Adam is 6ft tall."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "measurePhrase"), ("polarity", "positive"), ("evaluative", "false")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mp_short : LinguisticExample :=
  { id := "rett2015_mp_short"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Adam is 4ft short."
    discourseSegments := []
    glossedTokens := []
    translation := "Adam is 4ft short."
    context := "Measure phrases do not combine with negative-polar adjectives."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "measurePhrase"), ("polarity", "negative")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def question_tall : LinguisticExample :=
  { id := "rett2015_question_tall"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How tall is Adam?"
    discourseSegments := []
    glossedTokens := []
    translation := "How tall is Adam?"
    context := "Felicitous regardless of Adam's height."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degreeQuestion"), ("polarity", "positive"), ("evaluative", "false")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def question_short : LinguisticExample :=
  { id := "rett2015_question_short"
    source := ⟨"rett-2015", "Table 3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How short is Adam?"
    discourseSegments := []
    glossedTokens := []
    translation := "How short is Adam?"
    context := "Presupposes Adam is short."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degreeQuestion"), ("polarity", "negative"), ("evaluative", "true")]
    comment := "Evaluativity of relative adjectives by construction and antonym polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [positive_tall, positive_short, comparative_tall, comparative_short, equative_tall, equative_short, mp_tall, mp_short, question_tall, question_short]

end Rett2015.Examples
