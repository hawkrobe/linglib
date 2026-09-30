module

public import Linglib.Data.Examples.Schema

/-!
# `Barker1995` — typed example data

Auto-generated from `Linglib/Data/Examples/Barker1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Barker1995.Examples`.
-/

@[expose] public section

namespace Barker1995.Examples

open Data.Examples

def ch2_39c : LinguisticExample :=
  { id := "barker1995_ch2_39c"
    source := ⟨"barker-1995", "Ch. 2 (39c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John's child."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "uniqueness")]
    comment := "Patterns with the definite (39b): refers to a uniquely determined entity." }

def ch2_44b : LinguisticExample :=
  { id := "barker1995_ch2_44b"
    source := ⟨"barker-1995", "Ch. 2 (44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John's children yesterday."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "maximality")]
    comment := "The plural possessive describes only the maximal set of John's children." }

def ch2_46 : LinguisticExample :=
  { id := "barker1995_ch2_46"
    source := ⟨"barker-1995", "Ch. 2 (46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People are sitting in my seat!"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Richard serves coffee at 4; seats are first-come-first-served; Tom arrives late to a full office."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "uniqueness relative to cases")]
    comment := "Uniqueness without a specific referent: unique relative to each occasion, not absolutely." }

def ch2_47b : LinguisticExample :=
  { id := "barker1995_ch2_47b"
    source := ⟨"barker-1995", "Ch. 2 (47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I hate it when my shoes get wet."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "uniqueness relative to cases")]
    comment := "No particular pair of shoes: unique and maximal per situation, varying across cases." }

def ch2_50a : LinguisticExample :=
  { id := "barker1995_ch2_50a"
    source := ⟨"barker-1995", "Ch. 2 (50a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John's child today."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Neutral context; the child has not been mentioned."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "novel reference"), ("possession", "lexical")]
    comment := "A lexical possessive introduces a novel referent: the kinship relation is familiar." }

def ch2_50b : LinguisticExample :=
  { id := "barker1995_ch2_50b"
    source := ⟨"barker-1995", "Ch. 2 (50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John's human today."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Neutral context; the person has not been mentioned."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "novel reference"), ("possession", "extrinsic")]
    comment := "An extrinsic possessive cannot introduce a novel referent: the relation is too vague." }

def ch2_53a : LinguisticExample :=
  { id := "barker1995_ch2_53a"
    source := ⟨"barker-1995", "Ch. 2 (53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John's car yesterday."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Neutral context."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "novel reference"), ("possession", "conventional")]
    comment := "Cars are conventionally owned, so the relation counts as familiar — only on the ownership reading." }

def ch2_53b : LinguisticExample :=
  { id := "barker1995_ch2_53b"
    source := ⟨"barker-1995", "Ch. 2 (53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John's bus yesterday."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Neutral context."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "novel reference"), ("possession", "extrinsic")]
    comment := "Busses are not conventionally possessed; the extrinsic relation is not resolvable." }

def ch4_1 : LinguisticExample :=
  { id := "barker1995_ch4_1"
    source := ⟨"barker-1995", "Ch. 4 (1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most students' cars are old and decrepit."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "proportion")]
    comment := "The Tony-and-Simona scenario: what counts as a counterexample tracks how instances group into cases." }

def ch4_6 : LinguisticExample :=
  { id := "barker1995_ch4_6"
    source := ⟨"barker-1995", "Ch. 4 (6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three students' dogs were barking last night until 2 AM."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "asymmetric quantification")]
    comment := "Requires three students, not three dogs: the possessor description dominates." }

def ch4_7 : LinguisticExample :=
  { id := "barker1995_ch4_7"
    source := ⟨"barker-1995", "Ch. 4 (7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most people's favorite color is blue."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Simona favors red, Tony green, Lola, Max and Sandy blue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "asymmetric quantification")]
    comment := "True in the model (8): counts people, never colors — no possessee-dominant reading." }

def ch4_10 : LinguisticExample :=
  { id := "barker1995_ch4_10"
    source := ⟨"barker-1995", "Ch. 4 (10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three students' apartment burned down last night."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "proportion")]
    comment := "A single jointly-possessed apartment yields at most one case, clashing with the three-case presupposition." }

def ch4_11 : LinguisticExample :=
  { id := "barker1995_ch4_11"
    source := ⟨"barker-1995", "Ch. 4 (11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most planets' rings are made of ice."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Nine planets; only Saturn, Neptune and Uranus have rings; Saturn's and Neptune's are icy."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "narrowing")]
    comment := "True and felicitous: quantification ranges only over the ringed planets — the domain narrowing problem." }

def ch4_12c : LinguisticExample :=
  { id := "barker1995_ch4_12c"
    source := ⟨"barker-1995", "Ch. 4 (12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every woman's dream is to become a merchant marine."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "narrowing")]
    comment := "Quantifies only over women who have a dream: narrowing with every." }

def ch4_62 : LinguisticExample :=
  { id := "barker1995_ch4_62"
    source := ⟨"barker-1995", "Ch. 4 (62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most younger students' favorite teachers smile at them often."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "perspective paradox")]
    comment := "Feels like a generalization about students or about teachers, with no truth-conditional difference." }

def ch4_63 : LinguisticExample :=
  { id := "barker1995_ch4_63"
    source := ⟨"barker-1995", "Ch. 4 (63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most kindergarten teachers' children obey them."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "lexical vs extrinsic")]
    comment := "Kinship reading (their own children) or extrinsic reading (their students); the relation holds constant across the quantification." }

def ch4_72 : LinguisticExample :=
  { id := "barker1995_ch4_72"
    source := ⟨"barker-1995", "Ch. 4 (72)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most graduate students' longer papers are about English."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "perspective paradox")]
    comment := "Uniqueness forces maximal paper-sums, so pair-cases and student-cases coincide: one instance per case." }

def all : List LinguisticExample := [ch2_39c, ch2_44b, ch2_46, ch2_47b, ch2_50a, ch2_50b, ch2_53a, ch2_53b, ch4_1, ch4_6, ch4_7, ch4_10, ch4_11, ch4_12c, ch4_62, ch4_63, ch4_72]

end Barker1995.Examples
