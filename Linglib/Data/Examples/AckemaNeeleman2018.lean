import Linglib.Data.Examples.Schema

/-!
# `AckemaNeeleman2018` — typed example data

Auto-generated from `Linglib/Data/Examples/AckemaNeeleman2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AckemaNeeleman2018.Examples`.
-/

namespace AckemaNeeleman2018.Examples

open Data.Examples

def ex_2a : LinguisticExample :=
  { id := "ackemaneeleman2018_2a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It seems that Mary has left for Paris."
    discourseSegments := []
    glossedTokens := []
    translation := "It seems that Mary has left for Paris."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "third")]
    comment := "Expletive pronouns are third person: only DIST can deliver an empty output set."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2b : LinguisticExample :=
  { id := "ackemaneeleman2018_2b"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is raining again in Edinburgh."
    discourseSegments := []
    glossedTokens := []
    translation := "It is raining again in Edinburgh."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "third")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20a : LinguisticExample :=
  { id := "ackemaneeleman2018_20a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I can't believe your luck!"
    discourseSegments := []
    glossedTokens := []
    translation := "I can't believe your luck!"
    context := "John discovers he has a winning lottery ticket and talks to himself."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "self-talk"), ("roles", "i and u co-incide")]
    comment := "The same individual bears the speaker and addressee roles; possible because the features carry no negative values."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21a : LinguisticExample :=
  { id := "ackemaneeleman2018_21a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I can't believe your luck! If we hurry, we can still collect the money today."
    discourseSegments := ["I can't believe your luck!", "If we hurry, we can still collect the money today."]
    glossedTokens := []
    translation := "I can't believe your luck! If we hurry, we can still collect the money today."
    context := "John discovers he has a winning lottery ticket and talks to himself."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "self-talk"), ("person", "first plural")]
    comment := "A first person plural cannot refer to the speaker and the addressee-guise of the same individual."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "ackemaneeleman2018_24"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It seems that Vitesse won."
    discourseSegments := []
    glossedTokens := []
    translation := "It seems that Vitesse won."
    context := ""
    judgment := .acceptable
    alternatives := [("It seem that Vitesse won.", .ungrammatical), ("I seem that Vitesse won.", .ungrammatical), ("You seem that Vitesse won.", .ungrammatical)]
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "third singular")]
    comment := "Expletives are third person singular: plural is undefined on the empty set."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25 : LinguisticExample :=
  { id := "ackemaneeleman2018_25"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (25)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Nog jaren is naar een oplossing gezocht."
    discourseSegments := []
    glossedTokens := [("Nog", "still"), ("jaren", "years"), ("is", "be.3SG"), ("naar", "for"), ("een", "a"), ("oplossing", "solution"), ("gezocht", "searched")]
    translation := "People searched for a solution for many years."
    context := ""
    judgment := .acceptable
    alternatives := [("Nog jaren ben naar een oplossing gezocht.", .ungrammatical), ("Nog jaren bent naar een oplossing gezocht.", .ungrammatical), ("Nog jaren zijn naar een oplossing gezocht.", .ungrammatical)]
    readings := []
    paperFeatures := [("phenomenon", "default agreement"), ("construction", "impersonal passive")]
    comment := "Default agreement in the absence of an agreeing argument is third person singular."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30 : LinguisticExample :=
  { id := "ackemaneeleman2018_30"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (30)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Men schijnt dat men regent."
    discourseSegments := []
    glossedTokens := [("Men", "one"), ("schijnt", "seems"), ("dat", "that"), ("men", "one"), ("regent", "rains")]
    translation := "It seems that it rains."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("pronoun", "featureless impersonal")]
    comment := "The featureless pronoun refers to the whole input set, which has two obligatory members, so it cannot be a dummy."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_2a, ex_2b, ex_20a, ex_21a, ex_24, ex_25, ex_30]

end AckemaNeeleman2018.Examples
