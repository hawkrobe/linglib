module

public import Linglib.Data.Examples.Schema

/-!
# `White2014` — typed example data

Auto-generated from `Linglib/Data/Examples/White2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace White2014.Examples`.
-/

@[expose] public section

namespace White2014.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "white2014_1"
    source := ⟨"white-2014", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered that he took the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite"), ("inference", "presupposes (2)")]
    comment := "Factive with a finite complement: (2) survives negation, questioning and conditional antecedents (3)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "white2014_2"
    source := ⟨"white-2014", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to take the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("inference", "entails (2)")]
    comment := "Implicative with a control infinitive: (2) is entailed but not presupposed (4)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "white2014_3"
    source := ⟨"white-2014", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo took out the trash."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "the embedded content")]
    comment := "Implied by both sentences of (1), as a presupposition of (1a) and an entailment of (1b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "white2014_4"
    source := ⟨"white-2014", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo didn't remember that he took the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite"), ("test", "negation"), ("inference", "still implies (2)")]
    comment := "The embedded content of the finite complement is inert under negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "white2014_5"
    source := ⟨"white-2014", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo didn't remember to take the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "negation"), ("inference", "implies the negation of (2)")]
    comment := "Negation interacts with the embedded content: the negative implicative entailment."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "white2014_6"
    source := ⟨"white-2014", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo hoped to take out the trash."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hope"), ("complement", "infinitive")]
    comment := "A nonfactive verb with a control infinitive: factivity and implicativity are distributionally independent of finiteness."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "white2014_7"
    source := ⟨"white-2014", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It turned out that Bo took out the trash."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "turn out"), ("complement", "finite")]
    comment := "An implicative verb with a finite complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "white2014_8"
    source := ⟨"white-2014", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered that he had to take the trash out."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite with overt modal"), ("inference", "presupposes (7b)")]
    comment := "Presupposes that Bo had to take the trash out, as (1b) does: the presuppositional modality of the infinitive is that of an overt modal."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "white2014_9"
    source := ⟨"white-2014", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to clean the kitchen, even though he wasn't allowed to."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "denial of obligation")]
    comment := "The presuppositional modality cannot be denied with the infinitive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "white2014_10"
    source := ⟨"white-2014", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered that he cleaned the kitchen, even though he wasn't allowed to."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite"), ("test", "denial of obligation")]
    comment := "No presuppositional modality with the finite complement, so it is not encoded in the verb."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "white2014_11"
    source := ⟨"white-2014", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to go to the store and that Jo asked him to grab cereal."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "coordination")]
    comment := "Remember distributes over a control complement and a that-clause, against an ambiguity between two verbs."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "white2014_12"
    source := ⟨"white-2014", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to wash the dishes and Jo, that the dog needed a walk."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "gapping")]
    comment := "Gapping across the two complement types."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13 : LinguisticExample :=
  { id := "white2014_13"
    source := ⟨"white-2014", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo wasn't supposed to go to the store."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "In the context of (9a)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "detachability")]
    comment := "The modalized presupposition is not detachable from the first conjunct of (9a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "white2014_14"
    source := ⟨"white-2014", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered to fill the bird feeder."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "again")]
    comment := "The sentence whose restructuring the again test probes."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "white2014_15"
    source := ⟨"white-2014", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again remembered that he had to fill the feeder."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Jo told Bo to fill the bird feeder. He remembered this but didn't fill it. The next week, she asked again."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite"), ("test", "again"), ("previous", "remembering only")]
    comment := "Matrix again is felicitous without a previous filling: it modifies only the remembering."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "white2014_16"
    source := ⟨"white-2014", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again remembered that he had to fill the feeder."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Jo told Bo to fill the bird feeder. He forgot this, but noticed it was empty and filled it anyway. She told him to again the next week."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite"), ("test", "again"), ("previous", "filling only")]
    comment := "Infelicitous without a previous remembering."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "white2014_17"
    source := ⟨"white-2014", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again remembered to fill the feeder."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Jo told Bo to fill the bird feeder. He remembered that he had to, but didn't. The next week, she asked again."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "again"), ("previous", "remembering only")]
    comment := "Infelicitous without a previous filling: the embedded event is accessible from the matrix."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "white2014_18"
    source := ⟨"white-2014", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again remembered to fill the feeder."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Jo told Bo to fill the bird feeder. He forgot this, but noticed it was empty and filled it anyway. She told him to again the next week."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "infinitive"), ("test", "again"), ("previous", "filling only")]
    comment := "Infelicitous without a previous remembering too: again modifies the compound event."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19 : LinguisticExample :=
  { id := "white2014_19"
    source := ⟨"white-2014", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo again hoped to get a ticket."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Bo hoped to get a ticket to Jo's show. He couldn't, but when Jo came again..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hope"), ("test", "again"), ("previous", "hoping only")]
    comment := "Hope to patterns with remember that: no semantic restructuring."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20 : LinguisticExample :=
  { id := "white2014_20"
    source := ⟨"white-2014", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bo remembered that he had to take out the trash, but he didn't end up doing it."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "finite with overt modal"), ("inference", "no actuality entailment")]
    comment := "A modalized presupposition alone does not yield an actuality entailment."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "white2014_21"
    source := ⟨"white-2014", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jo hoped to get coal in her stocking and that it would be inky black."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hope"), ("test", "coordination")]
    comment := "Hope also coordinates a control complement with a that-clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21]

end White2014.Examples
