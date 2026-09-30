module

public import Linglib.Data.Examples.Schema

/-!
# `Lassiter2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Lassiter2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Lassiter2015.Examples`.
-/

@[expose] public section

namespace Lassiter2015.Examples

open Data.Examples

def ex4 : LinguisticExample :=
  { id := "lassiter2015_ex4"
    source := ⟨"lassiter-2015", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam is as likely to win the lottery as anyone else is."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A lottery with a million tickets; three siblings, Sam, Mary and Sue, buy two tickets each, and nobody else buys more than two."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ ψ_i for each i")]
    comment := "True, since Sam holds as many tickets as anyone; the starting point of the iterated disjunction puzzle." }

def ex8 : LinguisticExample :=
  { id := "lassiter2015_ex8"
    source := ⟨"lassiter-2015", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is as likely that Sam will win as it is that Mary or Sue will win."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The same lottery."
    judgment := .unacceptable
    alternatives := []
    readings := [("φ ⪰ (ψ ∨ χ)", .unacceptable), ("φ ⪰ ψ ∧ φ ⪰ χ", .acceptable)]
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ (ψ ∨ χ)")]
    comment := "False on the reading equivalent to (9): Mary and Sue hold four tickets together against Sam's two; the conjunctive reading of the disjunction in a comparative complement is set aside." }

def ex9 : LinguisticExample :=
  { id := "lassiter2015_ex9"
    source := ⟨"lassiter-2015", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is as likely that Sam will win as it is that one of his sisters will win."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The same lottery."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ (ψ ∨ χ)")]
    comment := "Unambiguously false; the reading (8) shares." }

def ex12 : LinguisticExample :=
  { id := "lassiter2015_ex12"
    source := ⟨"lassiter-2015", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is as likely that Sam will win as it is that Mary, Sue, Tom, Alice, Bob, Hank or Murray will."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The lottery, with five more people holding two tickets each."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("form", "φ ⪰ (ψ₁ ∨ … ∨ ψ₇)")]
    comment := "Iterating the puzzle; feeding each conclusion back as a premise reaches (14), that Sam is as likely to win as not." }

def ex33c : LinguisticExample :=
  { id := "lassiter2015_ex33c"
    source := ⟨"lassiter-2015", "(33c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is as likely that Sam will win (and Mary and Sue will not) as it is that either Mary or Sue will win (and Sam will not)."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The lottery with three siblings."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.4"), ("form", "(φ ∧ ¬ψ ∧ ¬χ) ⪰ ((¬φ ∧ ψ ∧ ¬χ) ∨ (¬φ ∧ ¬ψ ∧ χ))")]
    comment := "The modified disjunction puzzle's conclusion: as invalid as (8), yet valid for the revised comparative possibility once the alternatives are stated as disjoint." }

def ex35 : LinguisticExample :=
  { id := "lassiter2015_ex35"
    source := ⟨"lassiter-2015", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If φ must be the case, then φ is more likely than ¬φ."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.5"), ("pattern", "must to more likely than not")]
    comment := "Intuitively obvious, weaker than (3); invalid when the m-lifting is combined with Kratzer's semantics for must." }

def ex48 : LinguisticExample :=
  { id := "lassiter2015_ex48"
    source := ⟨"lassiter-2015", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is exactly as likely that Sam will go to the movies as it is that he will either go to school or go to the movies."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Sam might go to school, but he is somewhat more likely to cut class and go to the movies."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("measure", "symmetric fuzzy")]
    comment := "Compatible with a symmetric fuzzy measure for likely; clearly wrong unless going to school is impossible, which the equal-shares axiom enforces." }

def ex50 : LinguisticExample :=
  { id := "lassiter2015_ex50"
    source := ⟨"lassiter-2015", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are exactly three times as likely to throw an odd number as you are to throw a two."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "You are about to throw a fair die."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("modifier", "ratio")]
    comment := "Ratio modifiers are acceptable with likely, as with adjectives on additive scales." }

def ex51 : LinguisticExample :=
  { id := "lassiter2015_ex51"
    source := ⟨"lassiter-2015", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are exactly twice as likely to draw a jack as you are to draw a red queen."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "You are about to draw a card at random from a well-shuffled pack."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("modifier", "ratio")]
    comment := "" }

def ex53 : LinguisticExample :=
  { id := "lassiter2015_ex53"
    source := ⟨"lassiter-2015", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is exactly three times as tall as Bill is."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("modifier", "ratio"), ("scale", "additive")]
    comment := "The paper prints the variants tall, old and heavy with a single check mark." }

def ex54 : LinguisticExample :=
  { id := "lassiter2015_ex54"
    source := ⟨"lassiter-2015", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is exactly three times as angry as Bill is."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("modifier", "ratio"), ("scale", "non-additive")]
    comment := "Printed with two question marks, with the variants hungry and lecherous; ratio modifiers resist adjectives on non-additive scales." }

def ex56 : LinguisticExample :=
  { id := "lassiter2015_ex56"
    source := ⟨"lassiter-2015", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam must be at home. Therefore it is much more likely that Sam is at home than it is that he is not at home."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("pattern", "must to much more likely than not")]
    comment := "Clearly valid; none of the bridging rules BR1–BR3 validates it, and the quantificational and strong probabilistic auxiliaries do." }

def ex62 : LinguisticExample :=
  { id := "lassiter2015_ex62"
    source := ⟨"lassiter-2015", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[T]he 1880 census shows her living with mom, two brothers and herdaughter … So David [the father] must have died before 1880."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "An online genealogy discussion; David is the father."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("issue", "weakness of must")]
    comment := "The conclusion is presented as the best explanation of the evidence, not as the only possibility: a marital split would be an obvious alternative." }

def ex65a : LinguisticExample :=
  { id := "lassiter2015_ex65a"
    source := ⟨"lassiter-2015", "(65a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yale is more likely to win the NCAA basketball championship than Harvard is."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A year in which Yale is a much better team than Harvard, and the odds against either winning are astronomical."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "more likely than to might")]
    comment := "" }

def ex65b : LinguisticExample :=
  { id := "lassiter2015_ex65b"
    source := ⟨"lassiter-2015", "(65b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yale might win the NCAA basketball championship."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The same year."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "more likely than to might")]
    comment := "Not obviously inferable from (65a); if the inference fails, the weak probabilistic auxiliaries are favoured." }

def all : List LinguisticExample := [ex4, ex8, ex9, ex12, ex33c, ex35, ex48, ex50, ex51, ex53, ex54, ex56, ex62, ex65a, ex65b]

end Lassiter2015.Examples
