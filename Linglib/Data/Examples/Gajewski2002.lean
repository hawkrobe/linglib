import Linglib.Data.Examples.Schema

/-!
# `Gajewski2002` — typed example data

Auto-generated from `Linglib/Data/Examples/Gajewski2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gajewski2002.Examples`.
-/

namespace Gajewski2002.Examples

open Data.Examples

def ex4c : LinguisticExample :=
  { id := "gajewski2002_ex4c"
    source := ⟨"barwise-cooper-1981", "(4c)"⟩
    reportedIn := some ⟨"gajewski-2002", "(4c)"⟩
    language := "stan1293"
    primaryText := "There was everyone in the room."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "every"), ("grammatical", "no")]
    comment := "A strong quantifier in a there-sentence, the Definiteness Restriction of Milsark and Barwise and Cooper; its logical skeleton receives 1 under every assignment."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30a : LinguisticExample :=
  { id := "gajewski2002_ex30a"
    source := ⟨"gajewski-2002", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is every new student."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "every"), ("grammatical", "no")]
    comment := "The logical skeleton [there [are [every n1]]] is an L-tautology: every element of the domain of properties is a subset of the domain of individuals."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5a : LinguisticExample :=
  { id := "gajewski2002_ex5a"
    source := ⟨"barwise-cooper-1981", "(5a)"⟩
    reportedIn := some ⟨"gajewski-2002", "(5a)"⟩
    language := "stan1293"
    primaryText := "There is a wolf at the door."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "some"), ("grammatical", "yes")]
    comment := "A weak quantifier in a there-sentence."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5c : LinguisticExample :=
  { id := "gajewski2002_ex5c"
    source := ⟨"barwise-cooper-1981", "(5c)"⟩
    reportedIn := some ⟨"gajewski-2002", "(5c)"⟩
    language := "stan1293"
    primaryText := "There was someone in the room."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "there"), ("determiner", "some"), ("grammatical", "yes")]
    comment := "The skeleton [there [are [some n1]]] is false when the variable is assigned the empty set and true otherwise, so it is not L-analytic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11a_every : LinguisticExample :=
  { id := "gajewski2002_ex11a_every"
    source := ⟨"von-fintel-1993", "(11a)"⟩
    reportedIn := some ⟨"gajewski-2002", "(11a)"⟩
    language := "stan1293"
    primaryText := "Every student but Bill passed the exam."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "every"), ("grammatical", "yes")]
    comment := "A but-exceptive on a positive universal; its skeleton is contingent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11a_no : LinguisticExample :=
  { id := "gajewski2002_ex11a_no"
    source := ⟨"von-fintel-1993", "(11a)"⟩
    reportedIn := some ⟨"gajewski-2002", "(11a)"⟩
    language := "stan1293"
    primaryText := "No student but Bill passed the exam."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "no"), ("grammatical", "yes")]
    comment := "A but-exceptive on a negative universal; its skeleton is contingent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11b : LinguisticExample :=
  { id := "gajewski2002_ex11b"
    source := ⟨"von-fintel-1993", "(11b)"⟩
    reportedIn := some ⟨"gajewski-2002", "(11b)"⟩
    language := "stan1293"
    primaryText := "Some students but Bill passed the exam."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "exceptive"), ("determiner", "some"), ("grammatical", "no")]
    comment := "A but-exceptive on a left-upward-monotone determiner: the least-exception schema is a contradiction under every assignment with a nonempty exception set."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex34a : LinguisticExample :=
  { id := "gajewski2002_ex34a"
    source := ⟨"gajewski-2002", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every woman is a woman."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "everyIs"), ("determiner", "every"), ("grammatical", "yes")]
    comment := "A garden-variety tautology whose skeleton replaces the two occurrences of woman by distinct variables, so it is not L-analytic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex34b : LinguisticExample :=
  { id := "gajewski2002_ex34b"
    source := ⟨"gajewski-2002", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is smoking and John is not smoking."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "andNot"), ("determiner", "none"), ("grammatical", "yes")]
    comment := "A garden-variety contradiction whose skeleton has two distinct propositional variables, so it is not L-analytic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex4c, ex30a, ex5a, ex5c, ex11a_every, ex11a_no, ex11b, ex34a, ex34b]

end Gajewski2002.Examples
