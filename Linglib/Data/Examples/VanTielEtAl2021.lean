import Linglib.Data.Examples.Schema

/-!
# `VanTielEtAl2021` — typed example data

Auto-generated from `Linglib/Data/Examples/VanTielEtAl2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanTielEtAl2021.Examples`.
-/

namespace VanTielEtAl2021.Examples

open Data.Examples

def frame : LinguisticExample :=
  { id := "vantieletal2021_frame"
    source := ⟨"van-tiel-franke-sauerland-2021", "Exp. 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "— of the circles are red."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A display of 432 red or black circles; the participant completes the frame with a quantity word, numerals discouraged."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("task", "production"), ("words", "17 quantity words, 87% of the data")]
    comment := "The production frame of Experiments 1a and 1b, whose production probabilities show gradience and focality."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all_inference : LinguisticExample :=
  { id := "vantieletal2021_all_inference"
    source := ⟨"van-tiel-franke-sauerland-2021", "monotonicity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All guests ate salmon. → All guests ate fish."
    discourseSegments := ["All guests ate salmon.", "All guests ate fish."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("monotonicity", "increasing"), ("inference", "sets to supersets")]
    comment := "A monotone-increasing quantity word licenses the inference from a set to its supersets; Experiment 2 classified the 17 words by such arguments."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def no_inference : LinguisticExample :=
  { id := "vantieletal2021_no_inference"
    source := ⟨"van-tiel-franke-sauerland-2021", "monotonicity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No guest ate fish. → No guest ate salmon."
    discourseSegments := ["No guest ate fish.", "No guest ate salmon."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("monotonicity", "decreasing"), ("inference", "sets to subsets")]
    comment := "A monotone-decreasing quantity word licenses the inference from a set to its subsets; few, hardly any, less than half, none and very few were so classified."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def some_good : LinguisticExample :=
  { id := "vantieletal2021_some_good"
    source := ⟨"van-tiel-franke-sauerland-2021", "argumentativity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some people liked the food, which is good."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("word", "some"), ("argumentative direction", "positive")]
    comment := "Some and few differ in argumentative direction, a consideration the models abstract away from."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def some_bad : LinguisticExample :=
  { id := "vantieletal2021_some_bad"
    source := ⟨"van-tiel-franke-sauerland-2021", "argumentativity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some people liked the food, which is bad."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("word", "some"), ("argumentative direction", "positive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def few_bad : LinguisticExample :=
  { id := "vantieletal2021_few_bad"
    source := ⟨"van-tiel-franke-sauerland-2021", "argumentativity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few people liked the food, which is bad."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("word", "few"), ("argumentative direction", "negative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def few_good : LinguisticExample :=
  { id := "vantieletal2021_few_good"
    source := ⟨"van-tiel-franke-sauerland-2021", "argumentativity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Few people liked the food, which is good."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("word", "few"), ("argumentative direction", "negative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [frame, all_inference, no_inference, some_good, some_bad, few_bad, few_good]

end VanTielEtAl2021.Examples
