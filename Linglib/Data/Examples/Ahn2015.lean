import Linglib.Data.Examples.Schema

/-!
# `Ahn2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Ahn2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ahn2015.Examples`.
-/

namespace Ahn2015.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "ahn2015_1"
    source := ⟨"ahn-2015", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John came to the party too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("focus", "John")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "ahn2015_2"
    source := ⟨"ahn-2015", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't come to the party either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative"), ("focus", "John")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "ahn2015_3"
    source := ⟨"ahn-2015", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We're going to Philly either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5_too : LinguisticExample :=
  { id := "ahn2015_5_too"
    source := ⟨"rullmann-2003", "(5)"⟩
    reportedIn := some ⟨"ahn-2015", "(5)"⟩
    language := "stan1293"
    primaryText := "John washed the dishes. He shouldn't do the laundry too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("antecedent", "positive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5_either : LinguisticExample :=
  { id := "ahn2015_5_either"
    source := ⟨"rullmann-2003", "(5)"⟩
    reportedIn := some ⟨"ahn-2015", "(5)"⟩
    language := "stan1293"
    primaryText := "John washed the dishes. He shouldn't do the laundry either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative"), ("antecedent", "positive")]
    comment := "A negative host with a positive antecedent: the anaphor's antecedent must be false."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "ahn2015_9"
    source := ⟨"ahn-2015", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't leave either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "ahn2015_10"
    source := ⟨"ahn-2015", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "ahn2015_11"
    source := ⟨"ahn-2015", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is almost finished either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive"), ("operator", "almost")]
    comment := "Rullmann's licensing condition wrongly predicts almost, which implies the host is false, to license either."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "ahn2015_12"
    source := ⟨"kripke-2009", "(12)"⟩
    reportedIn := some ⟨"ahn-2015", "(12)"⟩
    language := "stan1293"
    primaryText := "John is having dinner in New York tonight too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Uttered out of the blue; it is common knowledge that many people dine in New York every night."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("focus", "John")]
    comment := "An existential presupposition would be satisfied, yet too is infelicitous without a salient antecedent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "ahn2015_15"
    source := ⟨"kripke-2009", "(15)"⟩
    reportedIn := some ⟨"ahn-2015", "(15)"⟩
    language := "stan1293"
    primaryText := "If John is coming to the party, the boss will come too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("distinctness", "John and the boss must be distinct")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "ahn2015_23"
    source := ⟨"ahn-2015", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't visit Boston. Bill didn't visit Boston too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "negative"), ("scope", "negation below too")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "ahn2015_24"
    source := ⟨"ahn-2015", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue bought some books. (But) Mary didn't buy them too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "negative"), ("scope", "negation above too")]
    comment := "Asserts ¬(q ∧ p); with q true from the discourse, ¬p follows."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26a : LinguisticExample :=
  { id := "ahn2015_26a"
    source := ⟨"ahn-2015", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary went to the shop, but it is not the case that somebody went there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "none"), ("test", "Abrusán entailment")]
    comment := "From Abrusán 2014."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26b : LinguisticExample :=
  { id := "ahn2015_26b"
    source := ⟨"ahn-2015", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary went to the shop, but it is not the case that somebody went there as well."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "as well"), ("test", "Abrusán entailment")]
    comment := "From Abrusán 2014."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29 : LinguisticExample :=
  { id := "ahn2015_29"
    source := ⟨"ahn-2015", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't know if Mary is in the elevator. But if John is in the elevator too, we will go over the weight limit."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("polarity", "positive"), ("antecedent", "not presupposed")]
    comment := "The additive meaning is not presupposed: the question at hand is the conjunction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_32 : LinguisticExample :=
  { id := "ahn2015_32"
    source := ⟨"ahn-2015", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't leave either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Discourse antecedent or context entailing that Bill didn't leave."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative"), ("focus", "John")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_41 : LinguisticExample :=
  { id := "ahn2015_41"
    source := ⟨"ahn-2015", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive")]
    comment := "O over the alternatives of the disjunction yields a contradiction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_43 : LinguisticExample :=
  { id := "ahn2015_43"
    source := ⟨"ahn-2015", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't leave either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "negative")]
    comment := "Under negation the disjunction entails every alternative; exhaustification is vacuous."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_45 : LinguisticExample :=
  { id := "ahn2015_45"
    source := ⟨"ahn-2015", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is almost finished either."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("polarity", "positive"), ("operator", "almost")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_5_too, ex_5_either, ex_9, ex_10, ex_11, ex_12, ex_15, ex_23, ex_24, ex_26a, ex_26b, ex_29, ex_32, ex_41, ex_43, ex_45]

end Ahn2015.Examples
