import Linglib.Data.Examples.Schema

/-!
# `Hofmann2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Hofmann2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hofmann2025.Examples`.
-/

namespace Hofmann2025.Examples

open Data.Examples

def veridical_basic : LinguisticExample :=
  { id := "hofmann2025_veridical_basic"
    source := ⟨"hofmann-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary owns a car. It is red."
    discourseSegments := ["Mary owns a car.", "It is red."]
    glossedTokens := []
    translation := "Mary owns a car. It is red."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Hofmann 2025 (1a), §1.1. Veridical antecedent + veridical anaphor context = felicitous baseline. antecedentStatus=veridical, anaphorCtx=veridical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def negated_basic : LinguisticExample :=
  { id := "hofmann2025_negated_basic"
    source := ⟨"hofmann-2025", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't own a car. It is red."
    discourseSegments := ["Mary doesn't own a car.", "It is red."]
    glossedTokens := []
    translation := "Mary doesn't own a car. It is red."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Hofmann 2025 (1b), §1.1. Counterfactual (negated) antecedent + veridical anaphor context = infelicitous (the # in the original notation marks felicity failure on the anaphor). antecedentStatus=counterfactual, anaphorCtx=veridical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def double_negation : LinguisticExample :=
  { id := "hofmann2025_double_negation"
    source := ⟨"krahmer-muskens-1995", "(5)"⟩
    reportedIn := some ⟨"hofmann-2025", "(2a)/(42a)"⟩
    language := "stan1293"
    primaryText := "It's not true that there isn't a bathroom. It is upstairs."
    discourseSegments := ["It's not true that there isn't a bathroom.", "It is upstairs."]
    glossedTokens := []
    translation := "It's not true that there isn't a bathroom. It is upstairs."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Double-negation counterexample to nested update: the bathroom referent survives despite living inside a negated context. Originally Krahmer & Muskens 1995 (5); cited in Hofmann 2025 §1.2 as one of four canonical counterexamples to the standard view that negation blocks anaphora. antecedentStatus=veridical (after double negation), anaphorCtx=veridical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def modal_subordination : LinguisticExample :=
  { id := "hofmann2025_modal_subordination"
    source := ⟨"frank-1996", "(8a)"⟩
    reportedIn := some ⟨"hofmann-2025", "(2d)/(42d)"⟩
    language := "stan1293"
    primaryText := "Fred didn't buy a microwave oven. He wouldn't know what to do with it."
    discourseSegments := ["Fred didn't buy a microwave oven.", "He wouldn't know what to do with it."]
    glossedTokens := []
    translation := "Fred didn't buy a microwave oven. He wouldn't know what to do with it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Modal subordination (Roberts 1989, attributed to Frank 1996 (8a) by Hofmann 2025): the microwave referent is accessible to the modal anaphor `wouldn't…with it` despite the antecedent being negated. The anaphor's nonveridical context licenses the otherwise-blocked accessibility. antecedentStatus=counterfactual, anaphorCtx=nonveridical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def counterfactual_modal : LinguisticExample :=
  { id := "hofmann2025_counterfactual_modal"
    source := ⟨"hofmann-2025", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary doesn't own a car. It would be parked outside."
    discourseSegments := ["Mary doesn't own a car.", "It would be parked outside."]
    glossedTokens := []
    translation := "Mary doesn't own a car. It would be parked outside."
    context := ""
    judgment := .acceptable
    alternatives := [("Mary doesn't own a car. It is parked outside.", .unacceptable)]
    readings := []
    paperFeatures := []
    comment := "Hofmann 2025 (6b), §1.4. Counterfactual antecedent + nonveridical anaphor context (`would`) = felicitous, in contrast to (6a) where the same antecedent with a veridical anaphor (`is`) is infelicitous. The within-example contrast (alternatives field) records the (6a) variant as the failed alternative. antecedentStatus=counterfactual, anaphorCtx=nonveridical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [veridical_basic, negated_basic, double_negation, modal_subordination, counterfactual_modal]

end Hofmann2025.Examples
