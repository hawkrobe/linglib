import Linglib.Data.Examples.Schema

/-!
# `HofmeisterSag2010` — typed example data

Auto-generated from `Linglib/Data/Examples/HofmeisterSag2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HofmeisterSag2010.Examples`.
-/

namespace HofmeisterSag2010.Examples

open Data.Examples

def ex42a : LinguisticExample :=
  { id := "hofmeistersag2010_ex42a"
    source := ⟨"hofmeister-sag-2010", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which man saw the girl in the bar on California Avenue?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("factor", "locality"), ("dependency", "subject")]
    comment := "Judged more acceptable than the object question (42b): the filler integrates at the next word."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex42b : LinguisticExample :=
  { id := "hofmeistersag2010_ex42b"
    source := ⟨"hofmeister-sag-2010", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which man did the girl in the bar on California Avenue see?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("factor", "locality"), ("dependency", "object")]
    comment := "Three discourse referents are identified while the filler is held in memory."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex43 : LinguisticExample :=
  { id := "hofmeistersag2010_ex43"
    source := ⟨"hofmeister-sag-2010", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The consultant who (we/Donald Trump/the chairman/a chairman) called advised wealthy companies."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("factor", "referential load")]
    comment := "Warren and Gibson's contrast: definite NPs and names inside the dependency slow reading at the retrieval site relative to pronouns."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44a : LinguisticExample :=
  { id := "hofmeistersag2010_ex44a"
    source := ⟨"hofmeister-sag-2010", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has she forgotten that he dragged her to a movie on Christmas Eve?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("factor", "clause boundary"), ("complementizer", "that")]
    comment := "Kluender and Kutas's contrast: the declarative complement is rated highest."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44b : LinguisticExample :=
  { id := "hofmeistersag2010_ex44b"
    source := ⟨"hofmeister-sag-2010", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has she forgotten if he dragged her to a movie on Christmas Eve?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("factor", "clause boundary"), ("complementizer", "if")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44c : LinguisticExample :=
  { id := "hofmeistersag2010_ex44c"
    source := ⟨"hofmeister-sag-2010", "(44c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has she forgotten who he dragged to a movie on Christmas Eve?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("factor", "clause boundary"), ("complementizer", "who")]
    comment := "The interrogative complement is rated lowest, with no filler crossing the boundary."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45a : LinguisticExample :=
  { id := "hofmeistersag2010_ex45a"
    source := ⟨"hofmeister-sag-2010", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The diplomat contacted the dictator who the activist looking for more contributions encouraged to preserve natural habitats and resources."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("factor", "filler complexity"), ("filler", "simple")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45b : LinguisticExample :=
  { id := "hofmeistersag2010_ex45b"
    source := ⟨"hofmeister-sag-2010", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The diplomat contacted the ruthless military dictator who the activist looking for more contributions encouraged to preserve natural habitats and resources."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("factor", "filler complexity"), ("filler", "complex")]
    comment := "Hofmeister's finding: the richer filler is read faster from the subcategorizing verb on."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46 : LinguisticExample :=
  { id := "hofmeistersag2010_ex46"
    source := ⟨"hofmeister-sag-2010", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which politician did you read reports that we had impeached?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.5"), ("island", "complexNP")]
    comment := "A dependency into a complex NP processes three nominal references and crosses a clause boundary."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48_bareDef : LinguisticExample :=
  { id := "hofmeistersag2010_ex48_bareDef"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw who Emma doubted the report that we had captured in the nationwide FBI manhunt."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "bare"), ("islandNP", "definite")]
    comment := "Experiment 1 item; the which-N conditions are read faster from the complementizer on and rated higher, and NP type has only weak, local effects."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48_barePl : LinguisticExample :=
  { id := "hofmeistersag2010_ex48_barePl"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw who Emma doubted reports that we had captured in the nationwide FBI manhunt."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "bare"), ("islandNP", "plural")]
    comment := "Experiment 1 item; the which-N conditions are read faster from the complementizer on and rated higher, and NP type has only weak, local effects."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48_bareIndef : LinguisticExample :=
  { id := "hofmeistersag2010_ex48_bareIndef"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw who Emma doubted a report that we had captured in the nationwide FBI manhunt."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "bare"), ("islandNP", "indefinite")]
    comment := "Experiment 1 item; the which-N conditions are read faster from the complementizer on and rated higher, and NP type has only weak, local effects."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48_whichDef : LinguisticExample :=
  { id := "hofmeistersag2010_ex48_whichDef"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw which convict Emma doubted the report that we had captured in the nationwide FBI manhunt."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "whichN"), ("islandNP", "definite")]
    comment := "Experiment 1 item; the which-N conditions are read faster from the complementizer on and rated higher, and NP type has only weak, local effects."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48_whichPl : LinguisticExample :=
  { id := "hofmeistersag2010_ex48_whichPl"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw which convict Emma doubted reports that we had captured in the nationwide FBI manhunt."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "whichN"), ("islandNP", "plural")]
    comment := "Experiment 1 item; the which-N conditions are read faster from the complementizer on and rated higher, and NP type has only weak, local effects."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48_whichIndef : LinguisticExample :=
  { id := "hofmeistersag2010_ex48_whichIndef"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw which convict Emma doubted a report that we had captured in the nationwide FBI manhunt."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "complexNP"), ("filler", "whichN"), ("islandNP", "indefinite")]
    comment := "Experiment 1 item; the which-N conditions are read faster from the complementizer on and rated higher, and NP type has only weak, local effects."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48_baseline : LinguisticExample :=
  { id := "hofmeistersag2010_ex48_baseline"
    source := ⟨"hofmeister-sag-2010", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw which convict Emma doubted that we had captured in the nationwide FBI manhunt."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("experiment", "1"), ("island", "none"), ("filler", "whichN")]
    comment := "The non-island baseline of Experiment 1, rated higher than every island condition."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex49_bare : LinguisticExample :=
  { id := "hofmeistersag2010_ex49_bare"
    source := ⟨"hofmeister-sag-2010", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did Albert learn whether they dismissed after the annual performance review?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Albert learned that the managers dismissed the employee with poor sales after the annual performance review."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("experiment", "2"), ("island", "embeddedQuestion"), ("filler", "bare")]
    comment := "Experiment 2 item; the which-N question is read as fast as the baseline after the embedded verb, the bare one slower."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex49_which : LinguisticExample :=
  { id := "hofmeistersag2010_ex49_which"
    source := ⟨"hofmeister-sag-2010", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which employee did Albert learn whether they dismissed after the annual performance review?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Albert learned that the managers dismissed the employee with poor sales after the annual performance review."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("experiment", "2"), ("island", "embeddedQuestion"), ("filler", "whichN")]
    comment := "Experiment 2 item; the which-N question is read as fast as the baseline after the embedded verb, the bare one slower."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex49_baseline : LinguisticExample :=
  { id := "hofmeistersag2010_ex49_baseline"
    source := ⟨"hofmeister-sag-2010", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did Albert learn that they dismissed after the annual performance review?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Albert learned that the managers dismissed the employee with poor sales after the annual performance review."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("experiment", "2"), ("island", "none"), ("filler", "bare")]
    comment := "Experiment 2 item; the which-N question is read as fast as the baseline after the embedded verb, the bare one slower."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex42a, ex42b, ex43, ex44a, ex44b, ex44c, ex45a, ex45b, ex46, ex48_bareDef, ex48_barePl, ex48_bareIndef, ex48_whichDef, ex48_whichPl, ex48_whichIndef, ex48_baseline, ex49_bare, ex49_which, ex49_baseline]

end HofmeisterSag2010.Examples
