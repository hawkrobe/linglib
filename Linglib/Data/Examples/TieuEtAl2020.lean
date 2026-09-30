module

public import Linglib.Data.Examples.Schema

/-!
# `TieuEtAl2020` — typed example data

Auto-generated from `Linglib/Data/Examples/TieuEtAl2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TieuEtAl2020.Examples`.
-/

@[expose] public section

namespace TieuEtAl2020.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "tieuetal2020_1a"
    source := ⟨"tieu-etal-2020", "(1a), (13), (21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed giraffes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("more than one giraffe", .acceptable)]
    paperFeatures := [("polarity", "positive")] }

def ex_2a : LinguisticExample :=
  { id := "tieuetal2020_2a"
    source := ⟨"tieu-etal-2020", "(2a), (16), (23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not more than one giraffe", .unacceptable), ("not a single giraffe", .acceptable)]
    paperFeatures := [("polarity", "negative")] }

def ex_3a : LinguisticExample :=
  { id := "tieuetal2020_3a"
    source := ⟨"tieu-etal-2020", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If there are books on Stephen's desk, Robin should lock the door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "downward")] }

def ex_4a : LinguisticExample :=
  { id := "tieuetal2020_4a"
    source := ⟨"tieu-etal-2020", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Are there books on Stephen's desk?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "downward")] }

def ex_8 : LinguisticExample :=
  { id := "tieuetal2020_8"
    source := ⟨"tieu-etal-2020", "(8), (18), (26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes, because she fed only one!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative")] }

def ex_14 : LinguisticExample :=
  { id := "tieuetal2020_14"
    source := ⟨"tieu-etal-2020", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed exactly one giraffe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive")] }

def ex_17 : LinguisticExample :=
  { id := "tieuetal2020_17"
    source := ⟨"tieu-etal-2020", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed exactly one giraffe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative")] }

def ex_27a : LinguisticExample :=
  { id := "tieuetal2020_27a"
    source := ⟨"tieu-etal-2020", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed giraffes."
    glossedTokens := []
    context := "Emily fed exactly one giraffe."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("n_acted_on", "one")] }

def ex_27b : LinguisticExample :=
  { id := "tieuetal2020_27b"
    source := ⟨"tieu-etal-2020", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes."
    glossedTokens := []
    context := "Emily fed exactly one giraffe."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("n_acted_on", "one")] }

def ex_29a : LinguisticExample :=
  { id := "tieuetal2020_29a"
    source := ⟨"tieu-etal-2020", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed some of the giraffes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("not all of the giraffes", .acceptable)]
    paperFeatures := [("polarity", "positive")] }

def exp1_positive : LinguisticExample :=
  { id := "tieuetal2020_exp1_positive"
    source := ⟨"tieu-etal-2020", "(35), Experiment 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed pigs."
    glossedTokens := []
    context := "Emily is visiting the zoo and feeds exactly one pig."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("polarity", "positive"), ("n_acted_on", "one")] }

def exp1_negative : LinguisticExample :=
  { id := "tieuetal2020_exp1_negative"
    source := ⟨"tieu-etal-2020", "(43), Experiment 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes."
    glossedTokens := []
    context := "Emily feeds exactly one giraffe."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("polarity", "negative"), ("n_acted_on", "one")] }

def exp2_si : LinguisticExample :=
  { id := "tieuetal2020_exp2_si"
    source := ⟨"tieu-etal-2020", "(47), Experiment 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lion carried some of the apples!"
    glossedTokens := []
    context := "Lion carried all of the apples."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("polarity", "positive"), ("inference", "scalar")] }

def exp3_positive_plural : LinguisticExample :=
  { id := "tieuetal2020_exp3_positive_plural"
    source := ⟨"tieu-etal-2020", "(54), Experiment 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Koala bought pears."
    glossedTokens := []
    context := "Koala bought exactly one pear."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("polarity", "positive"), ("n_acted_on", "one"), ("task", "ternary_reward"), ("preferred_reward", "intermediate")] }

def exp3_negative_plural : LinguisticExample :=
  { id := "tieuetal2020_exp3_negative_plural"
    source := ⟨"tieu-etal-2020", "(54), Experiment 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Koala didn't buy pears."
    glossedTokens := []
    context := "Koala bought exactly one pear."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("polarity", "negative"), ("n_acted_on", "one"), ("task", "ternary_reward"), ("preferred_reward", "minimal")] }

def all : List LinguisticExample := [ex_1a, ex_2a, ex_3a, ex_4a, ex_8, ex_14, ex_17, ex_27a, ex_27b, ex_29a, exp1_positive, exp1_negative, exp2_si, exp3_positive_plural, exp3_negative_plural]

end TieuEtAl2020.Examples
