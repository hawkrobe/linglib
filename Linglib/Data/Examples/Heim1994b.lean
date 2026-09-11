import Linglib.Data.Examples.Schema

/-!
# `Heim1994b` — typed example data

Auto-generated from `Linglib/Data/Examples/Heim1994b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heim1994b.Examples`.
-/

namespace Heim1994b.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "heim1994b_ex1"
    source := ⟨"heim-1994", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students called."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "0"), ("question", "which students called")]
    comment := "Exhaustive and de dicto: false when John is agnostic about a non-caller, or does not know that a caller is a student."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6 : LinguisticExample :=
  { id := "heim1994b_ex6"
    source := ⟨"heim-1994", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows who called."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("question", "who called")]
    comment := "Entails (1) only on the de re reading; Karttunen predicts the entailment except when no student called."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex17 : LinguisticExample :=
  { id := "heim1994b_ex17"
    source := ⟨"heim-1994", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows the answer to the question which students called."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")]
    comment := "Has a weaker reading than (1), on which (18) is valid: 'answer' can mean the answer in the first sense."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex18 : LinguisticExample :=
  { id := "heim1994b_ex18"
    source := ⟨"heim-1994", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows that Bill and Sue called. That Bill and Sue called happens to be the answer to the question which students called. So John knows the answer to the question which students called."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")]
    comment := "Valid on the weak reading of (17)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex19 : LinguisticExample :=
  { id := "heim1994b_ex19"
    source := ⟨"heim-1994", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't find your house."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")]
    comment := "Ambiguous in the same way as (17): Partee's example."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex20a : LinguisticExample :=
  { id := "heim1994b_ex20a"
    source := ⟨"heim-1994", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I identified the culprit."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex20b : LinguisticExample :=
  { id := "heim1994b_ex20b"
    source := ⟨"heim-1994", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I identified the striped animal in your drawing."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21 : LinguisticExample :=
  { id := "heim1994b_ex21"
    source := ⟨"heim-1994", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students are identical with themselves."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7"), ("gs", "John knows what students there are"), ("generalizedKarttunen", "John knows whether there are students")]
    comment := "A universally necessary property: the two analyses diverge, and neither captures the trivial knowledge intuitively ascribed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex24 : LinguisticExample :=
  { id := "heim1994b_ex24"
    source := ⟨"heim-1994", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which students live with their actual spouses."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7"), ("gs", "false when John believes Sue not to be a student"), ("generalizedKarttunen", "true")]
    comment := "Living with is symmetric, so Bill's and Sue's propositions coincide; Groenendijk and Stokhof predict the right falsity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1, ex6, ex17, ex18, ex19, ex20a, ex20b, ex21, ex24]

end Heim1994b.Examples
