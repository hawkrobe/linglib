import Linglib.Data.Examples.Schema

/-!
# `HalleVauxWolfe2000` — typed example data

Auto-generated from `Linglib/Data/Examples/HalleVauxWolfe2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HalleVauxWolfe2000.Examples`.
-/

namespace HalleVauxWolfe2000.Examples

open Data.Examples

def ex44a : LinguisticExample :=
  { id := "hallevauxwolfe2000_ex44a"
    source := ⟨"halle-vaux-wolfe-2000", "(44a)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "dʲekʲhʲinʲ"
    discourseSegments := []
    glossedTokens := []
    translation := "I would see"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("phenomenon", "dorsalAssimilation")]
    comment := "The palatalised coronal nasal before assimilation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44a_ii : LinguisticExample :=
  { id := "hallevauxwolfe2000_ex44a-ii"
    source := ⟨"halle-vaux-wolfe-2000", "(44a-ii)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "dʲekʲhʲiŋʲ gan eː"
    discourseSegments := []
    glossedTokens := []
    translation := "I would see without it"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("phenomenon", "dorsalAssimilation")]
    comment := "The nasal assimilates the dorsal primary articulation of the following g but keeps its own palatalisation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44b : LinguisticExample :=
  { id := "hallevauxwolfe2000_ex44b"
    source := ⟨"halle-vaux-wolfe-2000", "(44b)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "dʲiːlən"
    discourseSegments := []
    glossedTokens := []
    translation := "a diary"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("phenomenon", "dorsalAssimilation")]
    comment := "The plain coronal nasal before assimilation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44b_ii : LinguisticExample :=
  { id := "hallevauxwolfe2000_ex44b-ii"
    source := ⟨"halle-vaux-wolfe-2000", "(44b-ii)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "dʲiːləŋgʲiːvʲrʲi"
    discourseSegments := []
    glossedTokens := []
    translation := "a winter's diary"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("phenomenon", "dorsalAssimilation")]
    comment := "The plain nasal assimilates the dorsal articulation of the following palatalised gʲ but not its palatalisation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex44a, ex44a_ii, ex44b, ex44b_ii]

end HalleVauxWolfe2000.Examples
