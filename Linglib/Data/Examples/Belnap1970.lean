import Linglib.Data.Examples.Schema

/-!
# `Belnap1970` — typed example data

Auto-generated from `Linglib/Data/Examples/Belnap1970.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Belnap1970.Examples`.
-/

namespace Belnap1970.Examples

open Data.Examples

def ex_11 : LinguisticExample :=
  { id := "belnap1970_11"
    source := ⟨"belnap-1970", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All crows are black."
    discourseSegments := []
    glossedTokens := []
    translation := "All crows are black."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("quantified conditional assertion: consider the crows — each one is black", .acceptable)]
    paperFeatures := [("form", "A"), ("assertive iff", "there are crows")]
    comment := "Asserts nothing about crowhood: the content is the conjunction of 't is black' for the crows t."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "belnap1970_12"
    source := ⟨"belnap-1970", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some crows are black."
    discourseSegments := []
    glossedTokens := []
    translation := "Some crows are black."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("consider the crows: some of them are black", .acceptable)]
    paperFeatures := [("form", "I"), ("assertive iff", "there are crows")]
    comment := "The freshman rendering ∃x(if Cx then Bx) comes out right under conditional assertion."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unicorns_a : LinguisticExample :=
  { id := "belnap1970_unicorns_a"
    source := ⟨"belnap-1970", "p. 8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some unicorns are animals."
    discourseSegments := []
    glossedTokens := []
    translation := "Some unicorns are animals."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("status", "nonassertive"), ("diagnostic", "I-conversion")]
    comment := "Nonassertive: no unicorns. Its converse is plain false — conversion preserves truth, not assertiveness."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unicorns_b : LinguisticExample :=
  { id := "belnap1970_unicorns_b"
    source := ⟨"belnap-1970", "p. 8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some animals are unicorns."
    discourseSegments := []
    glossedTokens := []
    translation := "Some animals are unicorns."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("status", "false"), ("diagnostic", "I-conversion")]
    comment := "Assertive (there are animals) and false."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def johns_children : LinguisticExample :=
  { id := "belnap1970_johns_children"
    source := ⟨"belnap-1970", "p. 8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some of John's children are asleep."
    discourseSegments := []
    glossedTokens := []
    translation := "Some of John's children are asleep."
    context := "John has no children."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("status", "nonassertive"), ("diagnostic", "I-conversion")]
    comment := "Nonassertive in this context, while 'Some sleepers are children of John's' is false."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def barbara : LinguisticExample :=
  { id := "belnap1970_barbara"
    source := ⟨"belnap-1970", "p. 8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of Alan's birds are black."
    discourseSegments := []
    glossedTokens := []
    translation := "All of Alan's birds are black."
    context := "Major: all crows are black. Minor: all of Alan's birds are crows."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "Barbara conclusion"), ("asymmetry", "the major alone implies the conclusion")]
    comment := "When the minor is true, major and conclusion are both assertive, and the major's content implies the conclusion's."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def biscuits : LinguisticExample :=
  { id := "belnap1970_biscuits"
    source := ⟨"belnap-1970", "p. 11"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are biscuits on the sideboard if you want some."
    discourseSegments := []
    glossedTokens := []
    translation := "There are biscuits on the sideboard if you want some."
    context := "There are no biscuits, and you don't want any."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("status", "plain false, not nonassertive")]
    comment := "Not a conditional assertion: falsity survives a false antecedent — the biscuit conditional is something else."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def frank_james : LinguisticExample :=
  { id := "belnap1970_frank_james"
    source := ⟨"belnap-1970", "p. 9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If my name is Frank James, I have never beaten my wife."
    discourseSegments := []
    glossedTokens := []
    translation := "If my name is Frank James, I have never beaten my wife."
    context := "A reply to: If your name is Frank James, have you stopped beating your wife?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "conditional denial of a conditional question's presupposition")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def wages : LinguisticExample :=
  { id := "belnap1970_wages"
    source := ⟨"belnap-1970", "p. 11"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wages were high throughout the 1960's."
    discourseSegments := []
    glossedTokens := []
    translation := "Wages were high throughout the 1960's."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "summarizing an empirical regularity without explanatory force")]
    comment := "Quantified conditional assertion limits a law's scope without asserting a connection between antecedent and consequent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_11, ex_12, unicorns_a, unicorns_b, johns_children, barbara, biscuits, frank_james, wages]

end Belnap1970.Examples
