module

public import Linglib.Data.Examples.Schema

/-!
# `Khoo2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Khoo2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Khoo2015.Examples`.
-/

@[expose] public section

namespace Khoo2015.Examples

open Data.Examples

def control : LinguisticExample :=
  { id := "khoo2015_control"
    source := ⟨"khoo-2015", "Section II"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jim is at home right now."
    discourseSegments := []
    glossedTokens := []
    translation := "Jim is at home right now."
    context := "A non-modal assertion in the control vignette; participants rated on a 7-point scale either whether what the speaker said is false or whether they would respond 'No, ...'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def modal : LinguisticExample :=
  { id := "khoo2015_modal"
    source := ⟨"khoo-2015", "Section II"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fat Tony might be dead."
    discourseSegments := []
    glossedTokens := []
    translation := "Fat Tony might be dead."
    context := "Smith, having examined evidence consistent with Fat Tony's death, asserts the epistemic might-claim; Beth knows Fat Tony is alive; participants rated on a 7-point scale either whether what Smith said is false or whether they would respond 'No, ...'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [control, modal]

end Khoo2015.Examples
