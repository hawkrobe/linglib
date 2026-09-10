import Linglib.Data.Examples.Schema

/-!
# `Grove2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Grove2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Grove2022.Examples`.
-/

namespace Grove2022.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "grove2022_1"
    source := ⟨"grove-2022", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Theo has a brother, he'll bring his wetsuit."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes that Theo has a wetsuit", .acceptable), ("presupposes that Theo has a wetsuit if he has a brother", .questionable)]
    paperFeatures := [("section", "2.1"), ("phenomenon", "provisoProblem"), ("trigger", "his wetsuit"), ("filter", "conditional")]
    comment := "What one tends to accommodate is the unconditional presupposition; the satisfaction account predicts the conditional one."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "grove2022_2"
    source := ⟨"grove-2022", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Theo is a scuba diver, he'll bring his wetsuit."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes that Theo has a wetsuit if he is a scuba diver", .acceptable)]
    paperFeatures := [("section", "2"), ("phenomenon", "provisoProblem"), ("trigger", "his wetsuit"), ("filter", "conditional")]
    comment := "The conditional presupposition is relatively clear here."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "grove2022_6"
    source := ⟨"heim-1992", "(6)"⟩
    reportedIn := some ⟨"grove-2022", "(6)"⟩
    language := "stan1293"
    primaryText := "John: I am already in bed. Mary: My parents think I am also in bed."
    discourseSegments := ["John: I am already in bed.", "Mary: My parents think I am also in bed."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes that John is in bed", .acceptable), ("presupposes that Mary's parents think John is in bed", .questionable)]
    paperFeatures := [("section", "2.1"), ("phenomenon", "trappedTrigger"), ("trigger", "also"), ("filter", "think")]
    comment := "Heim's (1992) example: the utterance is consistent with the parents' ignorance of John's claim."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "grove2022_7"
    source := ⟨"grove-2022", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was limping earlier; I don't know why. Maybe he has a stress fracture. I don't know if he plays any sports, but if he has a stress fracture, then he'll stop running cross-country now."
    discourseSegments := ["John was limping earlier; I don't know why.", "Maybe he has a stress fracture.", "I don't know if he plays any sports, but if he has a stress fracture, then he'll stop running cross-country now."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "provisoProblem"), ("trigger", "stop"), ("filter", "conditional")]
    comment := "Mandelkern's judgment: odd because the unconditional presupposition that John runs cross-country conflicts with the assertion of ignorance."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "grove2022_8"
    source := ⟨"grove-2022", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw John limping earlier. If he has a stress fracture, then I assume that he runs cross-country. Indeed, if he has a stress fracture, then he'll stop running cross-country now."
    discourseSegments := ["I saw John limping earlier.", "If he has a stress fracture, then I assume that he runs cross-country.", "Indeed, if he has a stress fracture, then he'll stop running cross-country now."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "conditionalReadingContext"), ("trigger", "stop"), ("filter", "conditional")]
    comment := "Felicitous and does not imply that John runs cross-country: the conditional presupposition is available in context."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "grove2022_9"
    source := ⟨"grove-2022", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We're going scuba diving later, and I don't know if Theo owns a wetsuit. But it seems that everyone who has a brother got a wetsuit for Christmas. So, if Theo has a brother, he'll bring his wetsuit."
    discourseSegments := ["We're going scuba diving later, and I don't know if Theo owns a wetsuit.", "But it seems that everyone who has a brother got a wetsuit for Christmas.", "So, if Theo has a brother, he'll bring his wetsuit."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "conditionalReadingContext"), ("trigger", "his wetsuit"), ("filter", "conditional")]
    comment := "A context in which (1) is understood with the conditional inference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22 : LinguisticExample :=
  { id := "grove2022_22"
    source := ⟨"grove-2022", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo believes he lost his wetsuit."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("presupposes that Theo has a wetsuit, his wetsuit de re", .acceptable), ("presupposes that Theo believes he has a wetsuit, his wetsuit de dicto", .acceptable)]
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "believe")]
    comment := "The global presupposition coincides with the de re reading and the local one with the de dicto reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "grove2022_23"
    source := ⟨"grove-2022", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo believes he has a wetsuit, and he believes he lost his wetsuit."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "believe")]
    comment := "Most easily understood as presupposition-free: the local presupposition is satisfied."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "grove2022_24"
    source := ⟨"grove-2022", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo believes he has a wetsuit. He hopes his wetsuit is dry."
    discourseSegments := ["Theo believes he has a wetsuit.", "He hopes his wetsuit is dry."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "hope")]
    comment := "The second sentence's presupposition of belief is satisfied by the first."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25 : LinguisticExample :=
  { id := "grove2022_25"
    source := ⟨"grove-2022", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo has a wetsuit, and he believes he lost his wetsuit."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "believe")]
    comment := "The presupposition of (22) is satisfied by a context in which Theo has a wetsuit."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26 : LinguisticExample :=
  { id := "grove2022_26"
    source := ⟨"grove-2022", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Theo has a wetsuit. He hopes his wetsuit is dry."
    discourseSegments := ["Theo has a wetsuit.", "He hopes his wetsuit is dry."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("phenomenon", "attitude"), ("trigger", "his wetsuit"), ("filter", "hope")]
    comment := "The presupposition of the second sentence of (24) is satisfied by a context in which Theo has a wetsuit."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_6, ex_7, ex_8, ex_9, ex_22, ex_23, ex_24, ex_25, ex_26]

end Grove2022.Examples
