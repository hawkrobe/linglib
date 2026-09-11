import Linglib.Data.Examples.Schema

/-!
# `HawkinsEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/HawkinsEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HawkinsEtAl2025.Examples`.
-/

namespace HawkinsEtAl2025.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "hawkinsetal2025_ex1"
    source := ⟨"hawkins-etal-2025", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Quinn: Do you take Visa or Mastercard? Rickie: Yes, we take Visa. ?? Quinn: Yeah, sure I already knew that!"
    discourseSegments := ["Quinn: Do you take Visa or Mastercard?", "Rickie: Yes, we take Visa.", "?? Quinn: Yeah, sure I already knew that!"]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2a"), ("response", "safe")]
    comment := "Knowing that Visa is taken settles the disjunctive question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2 : LinguisticExample :=
  { id := "hawkinsetal2025_ex2"
    source := ⟨"hawkins-etal-2025", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Quinn: Do you take Visa or Mastercard? Rickie: No, but we take American Express. Quinn: Yeah, sure I already knew that!"
    discourseSegments := ["Quinn: Do you take Visa or Mastercard?", "Rickie: No, but we take American Express.", "Quinn: Yeah, sure I already knew that!"]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2a"), ("response", "unsafe")]
    comment := "Knowing about American Express leaves the question open."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex3 : LinguisticExample :=
  { id := "hawkinsetal2025_ex3"
    source := ⟨"hawkins-etal-2025", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Quinn: Do you accept American Express? Rickie: Yes, we accept American Express and … [exhaustive list]."
    discourseSegments := ["Quinn: Do you accept American Express?", "Rickie: Yes, we accept American Express and … [exhaustive list]."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3a"), ("question", "specific"), ("target", "available"), ("response", "exhaustive")]
    comment := "The least likely site of an exhaustive list: (4) ≥ (5) > (3)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4 : LinguisticExample :=
  { id := "hawkinsetal2025_ex4"
    source := ⟨"hawkins-etal-2025", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Quinn: Do you accept American Express? Rickie: No, we accept … [exhaustive list]."
    discourseSegments := ["Quinn: Do you accept American Express?", "Rickie: No, we accept … [exhaustive list]."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3a"), ("question", "specific"), ("target", "unavailable"), ("response", "exhaustive")]
    comment := "Model rate of exhaustive lists 0.75."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5 : LinguisticExample :=
  { id := "hawkinsetal2025_ex5"
    source := ⟨"hawkins-etal-2025", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Quinn: Do you accept credit cards? Rickie: Yes, we accept … [exhaustive list]."
    discourseSegments := ["Quinn: Do you accept credit cards?", "Rickie: Yes, we accept … [exhaustive list]."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3a"), ("question", "general"), ("response", "exhaustive")]
    comment := "Model rate of exhaustive lists 0.66."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6 : LinguisticExample :=
  { id := "hawkinsetal2025_ex6"
    source := ⟨"hawkins-etal-2025", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are a bartender in a hotel bar. The bar serves only soda, iced coffee and Chardonnay. A woman walks in. She says: Do you have iced tea?"
    discourseSegments := ["You are a bartender in a hotel bar. The bar serves only soda, iced coffee and Chardonnay.", "A woman walks in. She says: Do you have iced tea?"]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3b"), ("competitor", "iced coffee"), ("sameCategory", "soda"), ("otherCategory", "Chardonnay")]
    comment := "Predicted ordering of responses: competitor > taciturn ≥ same category > exhaustive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7 : LinguisticExample :=
  { id := "hawkinsetal2025_ex7"
    source := ⟨"hawkins-etal-2025", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Context 1 (sleepover): Your friend is having a sleepover with some friends on the weekend. They are preparing everything for the guests since they don't host many guests very often. You have the following items at home that you could spare for some time: some bubble wrap, a pillow, a sleeping bag and a carpet. Your friend asks: Do you have a blanket?"
    discourseSegments := ["Context 1 (sleepover): Your friend is having a sleepover with some friends on the weekend. They are preparing everything for the guests since they don't host many guests very often. You have the following items at home that you could spare for some time: some bubble wrap, a pillow, a sleeping bag and a carpet.", "Your friend asks: Do you have a blanket?"]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3c"), ("competitor", "sleeping bag"), ("mostSimilar", "pillow"), ("otherCategory", "carpet")]
    comment := "The contextually relevant competitor is mentioned more than the most similar option."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8 : LinguisticExample :=
  { id := "hawkinsetal2025_ex8"
    source := ⟨"hawkins-etal-2025", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Context 2 (transportation): Your roommate is moving to another apartment and is packing her things. She has a large mirror that she needs to pack for transportation. You have the following items at home that you could spare for some time: some bubble wrap, a pillow, a sleeping bag and a carpet. She asks: Do you have a blanket?"
    discourseSegments := ["Context 2 (transportation): Your roommate is moving to another apartment and is packing her things. She has a large mirror that she needs to pack for transportation. You have the following items at home that you could spare for some time: some bubble wrap, a pillow, a sleeping bag and a carpet.", "She asks: Do you have a blanket?"]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3c"), ("competitor", "bubble wrap"), ("mostSimilar", "pillow"), ("otherCategory", "carpet")]
    comment := "The same question and options as (7) with the other competitor relevant."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def icedtea : LinguisticExample :=
  { id := "hawkinsetal2025_icedtea"
    source := ⟨"hawkins-etal-2025", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Customer: Do you have iced tea? Barista: No, but we have iced coffee."
    discourseSegments := ["Customer: Do you have iced tea?", "Barista: No, but we have iced coffee."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("response", "competitor")]
    comment := "The question signals a goal: something cold and caffeinated."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bbq : LinguisticExample :=
  { id := "hawkinsetal2025_bbq"
    source := ⟨"hawkins-etal-2025", "§4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Will we have BBQ in the park? A: Chances of rain are 90%."
    discourseSegments := ["Q: Will we have BBQ in the park?", "A: Chances of rain are 90%."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("response", "relevant, non-resolving")]
    comment := "Relevance that shifts the likelihood of a world state without resolving the question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, icedtea, bbq]

end HawkinsEtAl2025.Examples
