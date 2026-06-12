import Linglib.Data.Examples.Schema

/-!
# `Westergaard2009` — typed example data

Auto-generated from `Linglib/Data/Examples/Westergaard2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Westergaard2009.Examples`.
-/

namespace Westergaard2009.Examples

open Data.Examples

def ex20 : LinguisticExample :=
  { id := "westergaard2009_ex20"
    source := ⟨"westergaard-2009", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What will you bring to the party?"
    discourseSegments := []
    glossedTokens := []
    translation := "What will you bring to the party?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause_type", "whQuestion"), ("inverted", "true")]
    comment := "Verified against the PDF (Ch. 2 §3.1). English residual V2: subject-auxiliary inversion in wh-questions."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21 : LinguisticExample :=
  { id := "westergaard2009_ex21"
    source := ⟨"westergaard-2009", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you seen her today?"
    discourseSegments := []
    glossedTokens := []
    translation := "Have you seen her today?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause_type", "yesNoQuestion"), ("inverted", "true")]
    comment := "Verified against the PDF (Ch. 2 §3.1). English residual V2: subject-auxiliary inversion in yes/no-questions."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23 : LinguisticExample :=
  { id := "westergaard2009_ex23"
    source := ⟨"henry-1997", "p. 275"⟩
    reportedIn := some ⟨"westergaard-2009", "(23)"⟩
    language := "stan1293"
    primaryText := "They asked me was I going to the party."
    discourseSegments := []
    glossedTokens := []
    translation := "They asked me was I going to the party."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variety", "Belfast English"), ("clause_type", "embeddedQuestion"), ("inverted", "true")]
    comment := "Verified against the Westergaard PDF (Ch. 2 §3.1). Belfast English V2 in embedded yes/no-questions."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex24 : LinguisticExample :=
  { id := "westergaard2009_ex24"
    source := ⟨"henry-1997", "p. 274"⟩
    reportedIn := some ⟨"westergaard-2009", "(24)"⟩
    language := "stan1293"
    primaryText := "Bring you that with you!"
    discourseSegments := []
    glossedTokens := []
    translation := "Bring you that with you!"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("variety", "Belfast English"), ("clause_type", "imperative"), ("inverted", "true")]
    comment := "Verified against the Westergaard PDF (Ch. 2 §3.1). Belfast English V2 in imperatives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex20, ex21, ex23, ex24]

end Westergaard2009.Examples
