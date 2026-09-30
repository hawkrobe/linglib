module

public import Linglib.Data.Examples.Schema

/-!
# `Alsop2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Alsop2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Alsop2024.Examples`.
-/

@[expose] public section

namespace Alsop2024.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "alsop2024_1a"
    source := ⟨"alsop-2024", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may read any book."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("exclusiveness", .acceptable)]
    paperFeatures := [("logicalForm", "∀x ∈ De [book(x) → ◇read(you,x)]")]
    comment := "(2) You may read just Book A is the exclusiveness reading; Menéndez-Benito and Dayal take it to be entailed, Alsop to be a robust implicature." }

def ex_3 : LinguisticExample :=
  { id := "alsop2024_3"
    source := ⟨"alsop-2024", "(3)"⟩
    reportedIn := some ⟨"szabolcsi-2019", ""⟩
    language := "stan1293"
    primaryText := "Any bishop may meet a bishop."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("predicate", "symmetric"), ("state", "only2")]
    comment := "(4) Bishop A may be the only bishop who meets a bishop can never be true, so the Viability Constraint wrongly predicts infelicity." }

def ex_5a : LinguisticExample :=
  { id := "alsop2024_5a"
    source := ⟨"alsop-2024", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane didn't buy any shirts."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("any", "npi"), ("environment", "negation")]
    comment := "" }

def ex_5b : LinguisticExample :=
  { id := "alsop2024_5b"
    source := ⟨"alsop-2024", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tom thanked every guest who brought any drinks."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("any", "npi"), ("environment", "restrictorOfEvery")]
    comment := "" }

def ex_6a : LinguisticExample :=
  { id := "alsop2024_6a"
    source := ⟨"alsop-2024", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carrie read any book."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("any", "fci"), ("environment", "episodic")]
    comment := "" }

def ex_6b : LinguisticExample :=
  { id := "alsop2024_6b"
    source := ⟨"alsop-2024", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carrie may read any book."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("any", "fci"), ("environment", "possibilityModal")]
    comment := "" }

def ex_6c : LinguisticExample :=
  { id := "alsop2024_6c"
    source := ⟨"alsop-2024", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carrie must read any book."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("any", "fci"), ("environment", "necessityModal")]
    comment := "" }

def ex_17 : LinguisticExample :=
  { id := "alsop2024_17"
    source := ⟨"alsop-2024", "(17)"⟩
    reportedIn := some ⟨"menendez-benito-2010", ""⟩
    language := "stan1293"
    primaryText := "In Canasta, you can take any of the cards in the discard pile when you have two cards that match its top card."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "(16) The Canasta scenario: when a player has two cards that match the top card of the discard pile, she has two options: take all the cards in the discard pile, or take no card from it. Those are her only two options."
    judgment := .marginal
    alternatives := []
    readings := [("literal", .acceptable), ("exclusiveness", .unacceptable)]
    paperFeatures := [("state", "only2")]
    comment := "Menéndez-Benito judges it unambiguously false; the dialogue (18) — A: Is it true that in Canasta, you can take any of the cards in the discard pile when you have two cards that match its top card? B: Technically yes…but if you take one card from the discard pile, you must take all of them — shows it literally true." }

def ex_19 : LinguisticExample :=
  { id := "alsop2024_19"
    source := ⟨"alsop-2024", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Annie: Can I take any of these cats? Shelter employee: Technically yes…but they're siblings, so if you take one, you're required to take them all."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The local animal shelter has a strict policy of not separating animals from their siblings. Annie goes to the shelter to adopt a cat, and walks into one room with three cats inside."
    judgment := .acceptable
    alternatives := []
    readings := [("literal", .acceptable), ("exclusiveness", .unacceptable)]
    paperFeatures := [("state", "only2")]
    comment := "Judged less natural but acceptable, true and non-contradictory by the author and three further speakers (fn. 6)." }

def ex_20a : LinguisticExample :=
  { id := "alsop2024_20a"
    source := ⟨"alsop-2024", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any bishop may gather with other bishops."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("predicate", "symmetric"), ("state", "only2")]
    comment := "Does not implicate that Bishop A may be the only bishop who gathers with other bishops." }

def ex_20b : LinguisticExample :=
  { id := "alsop2024_20b"
    source := ⟨"alsop-2024", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any bishop may converse with another bishop."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("predicate", "symmetric"), ("state", "only2")]
    comment := "" }

def ex_20c : LinguisticExample :=
  { id := "alsop2024_20c"
    source := ⟨"alsop-2024", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any bishop may pair up with another bishop."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("predicate", "symmetric"), ("state", "only2")]
    comment := "" }

def ex_21b : LinguisticExample :=
  { id := "alsop2024_21b"
    source := ⟨"alsop-2024", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We may take any class."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "You are a graduate student only required to take one class per semester. You ask: What classes are we allowed to take in our first year?"
    judgment := .acceptable
    alternatives := []
    readings := [("exclusiveness", .acceptable)]
    paperFeatures := []
    comment := "Implicates that we may take Semantics without taking another class." }

def ex_22b : LinguisticExample :=
  { id := "alsop2024_22b"
    source := ⟨"alsop-2024", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We may take any class."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "You are an undergraduate student required to take four classes per semester. You ask: What classes are we allowed to take in our first year?"
    judgment := .acceptable
    alternatives := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("state", "only2")]
    comment := "The undergraduate's certainty about the courseload blocks the exclusiveness implicature; only the Only 2 state remains." }

def ex_23 : LinguisticExample :=
  { id := "alsop2024_23"
    source := ⟨"alsop-2024", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt any cat here… But if you adopt a cat, you also have to adopt its siblings."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Annie goes to the shelter to adopt a cat; the shelter employee speaks."
    judgment := .acceptable
    alternatives := []
    readings := [("exclusiveness", .unacceptable)]
    paperFeatures := [("implicature", "cancelled"), ("state", "only2")]
    comment := "The expectation that each cat can be adopted on its own is felicitously denied after the fact." }

def ex_24a : LinguisticExample :=
  { id := "alsop2024_24a"
    source := ⟨"alsop-2024", "(24a)"⟩
    reportedIn := some ⟨"dayal-2013", ""⟩
    language := "stan1293"
    primaryText := "Bill may read any of these books."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Out of the blue."
    judgment := .acceptable
    alternatives := []
    readings := [("not every", .questionable)]
    paperFeatures := [("prior", "uniform")]
    comment := "Dayal: Bill is unambiguously permitted to read all the books at once; Alsop: out of the blue this is left open." }

def ex_25b : LinguisticExample :=
  { id := "alsop2024_25b"
    source := ⟨"alsop-2024", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We may take any class."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "You are a part-time student who is forbidden from taking more than one class in a semester. Your university offers hundreds of classes each semester. You ask: What classes are we allowed to take in our first year?"
    judgment := .acceptable
    alternatives := []
    readings := [("not two", .acceptable), ("not three", .acceptable), ("not every", .acceptable)]
    paperFeatures := [("state", "only1")]
    comment := "The listener's prior knowledge, not the utterance, rules out taking more than one class." }

def ex_26a : LinguisticExample :=
  { id := "alsop2024_26a"
    source := ⟨"alsop-2024", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anyone and everyone is welcome to come."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anyAndEvery")]
    comment := "The second conjunct adds that there is no limit to the number of individuals who may come." }

def ex_26b : LinguisticExample :=
  { id := "alsop2024_26b"
    source := ⟨"alsop-2024", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We welcome any and all questions."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anyAndEvery")]
    comment := "" }

def ex_27a : LinguisticExample :=
  { id := "alsop2024_27a"
    source := ⟨"alsop-2024", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We reserve the right to refuse to serve anyone."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A restaurant sign."
    judgment := .acceptable
    alternatives := [("We reserve the right to refuse to serve anyone and everyone.", .unacceptable)]
    readings := []
    paperFeatures := []
    comment := "(27b) is infelicitous: the conjoined universal rules in the scenario of refusing everyone, which world knowledge rules out." }

def ex_28 : LinguisticExample :=
  { id := "alsop2024_28"
    source := ⟨"alsop-2024", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may have any of these souvenirs… In fact, you may even have all of them."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "You are one of three siblings. Your mother returns from a business trip with three souvenirs and presents them to just you first."
    judgment := .acceptable
    alternatives := []
    readings := [("not every", .unacceptable)]
    paperFeatures := [("implicature", "cancelled")]
    comment := "The not two and not every implicatures are robust from the prior but felicitously denied." }

def ex_31_mayS : LinguisticExample :=
  { id := "alsop2024_31_mayS"
    source := ⟨"alsop-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take Semantics."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The toy example: the domain of classes is {Semantics, Phonology}; the QUD is which classes the listener may take."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("utterance", "mayS"), ("parses", "3")]
    comment := "Parses (32a–c)." }

def ex_31_mayP : LinguisticExample :=
  { id := "alsop2024_31_mayP"
    source := ⟨"alsop-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take Phonology."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The toy example: the domain of classes is {Semantics, Phonology}; the QUD is which classes the listener may take."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("utterance", "mayP"), ("parses", "3")]
    comment := "Parses (33a–c)." }

def ex_31_mayAny : LinguisticExample :=
  { id := "alsop2024_31_mayAny"
    source := ⟨"alsop-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take any class."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The toy example: the domain of classes is {Semantics, Phonology}; the QUD is which classes the listener may take."
    judgment := .acceptable
    alternatives := []
    readings := [("exclusiveness", .acceptable), ("not every", .questionable)]
    paperFeatures := [("utterance", "mayAny"), ("parses", "2"), ("prior", "uniform")]
    comment := "Parses (34a) (Szabolcsi) and (34b) (Dayal); (42a) the exclusiveness implicature, (43a) the not every implicature, absent at a uniform prior." }

def ex_31_mayEvery : LinguisticExample :=
  { id := "alsop2024_31_mayEvery"
    source := ⟨"alsop-2024", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may take every class."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The toy example: the domain of classes is {Semantics, Phonology}; the QUD is which classes the listener may take."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("utterance", "mayEvery"), ("parses", "4")]
    comment := "Parses (35a–d), with both scopes of the universal." }

def ex_44 : LinguisticExample :=
  { id := "alsop2024_44"
    source := ⟨"alsop-2024", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris: Can I choose any of those chores? Grandmother: Technically yes—in fact, you must do all of them."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Chris spends the summer at his grandmother's house; on his first day she shows him a list of chores she has written down."
    judgment := .acceptable
    alternatives := []
    readings := [("literal", .acceptable), ("exclusiveness", .unacceptable), ("may but not must", .unacceptable)]
    paperFeatures := [("revisedViabilityConstraint", "cancelled")]
    comment := "Denies the scalar implicature the Revised Viability Constraint requires; outside the model." }

def all : List LinguisticExample := [ex_1a, ex_3, ex_5a, ex_5b, ex_6a, ex_6b, ex_6c, ex_17, ex_19, ex_20a, ex_20b, ex_20c, ex_21b, ex_22b, ex_23, ex_24a, ex_25b, ex_26a, ex_26b, ex_27a, ex_28, ex_31_mayS, ex_31_mayP, ex_31_mayAny, ex_31_mayEvery, ex_44]

end Alsop2024.Examples
