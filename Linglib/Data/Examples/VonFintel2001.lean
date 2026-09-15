import Linglib.Data.Examples.Schema

/-!
# `VonFintel2001` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintel2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintel2001.Examples`.
-/

namespace VonFintel2001.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "vonfintel2001_1"
    source := ⟨"geis-zwicky-1971", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(1)"⟩
    language := "stan1293"
    primaryText := "If you mow the lawn, I'll give you five dollars."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("perfection: no five dollars without mowing", .questionable), ("strengthening: the five dollars are not free for the taking", .acceptable)]
    paperFeatures := [("inference", "conditional perfection"), ("flavor", "bouletic")]
    comment := "Geis and Zwicky's invited inference; Lilje's addressee may still ask whether cleaning the garage would earn the money."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "vonfintel2001_2"
    source := ⟨"geis-zwicky-1971", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(2)"⟩
    language := "stan1293"
    primaryText := "If John leans out of that window any further, he'll fall."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "conditional perfection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "vonfintel2001_3"
    source := ⟨"geis-zwicky-1971", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(3)"⟩
    language := "stan1293"
    primaryText := "If you disturb me tonight, I won't let you go to the movies tomorrow."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "conditional perfection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "vonfintel2001_4"
    source := ⟨"geis-zwicky-1971", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(4)"⟩
    language := "stan1293"
    primaryText := "If you heat iron in a fire, it turns red."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "conditional perfection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "vonfintel2001_6"
    source := ⟨"lilje-1972", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(6)"⟩
    language := "stan1293"
    primaryText := "If it doesn't say 'Goodyear', it isn't Polyglas."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("perfection", .unacceptable), ("strengthening: the object is not necessarily not Polyglas", .acceptable)]
    paperFeatures := [("inference", "no perfection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "vonfintel2001_7"
    source := ⟨"lilje-1972", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(7)"⟩
    language := "stan1293"
    primaryText := "If this cactus grows native to Idaho, then it's not an Astrophytum."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "An information-seeking dialogue on whether the cactus is an Astrophytum."
    judgment := .acceptable
    alternatives := []
    readings := [("perfection", .unacceptable), ("strengthening: it is not settled that the cactus is not an Astrophytum", .acceptable)]
    paperFeatures := [("inference", "no perfection"), ("question", "information-seeking")]
    comment := "A speaker who has just learned the antecedent may utter it to show how the conclusion was reached."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "vonfintel2001_8"
    source := ⟨"lilje-1972", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(8)"⟩
    language := "stan1293"
    primaryText := "If you scratch on the eight-ball, then you lost the game."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("perfection", .unacceptable)]
    paperFeatures := [("inference", "no perfection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "vonfintel2001_9"
    source := ⟨"lilje-1972", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(9)"⟩
    language := "stan1293"
    primaryText := "If the axioms aren't consistent with each other, then every WFF in the system is a theorem."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("perfection", .unacceptable)]
    paperFeatures := [("inference", "no perfection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "vonfintel2001_10"
    source := ⟨"boer-lycan-1973", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(10)"⟩
    language := "stan1293"
    primaryText := "If John quits, he will be replaced."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("perfection", .unacceptable), ("strengthening: it is not settled that John will be replaced", .acceptable)]
    paperFeatures := [("inference", "no perfection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "vonfintel2001_11"
    source := ⟨"von-fintel-2001", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you get a \"B\" on your next history test, I will give you $5."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Uttered by the wealthy aunt of an uninspired C-average high school student."
    judgment := .acceptable
    alternatives := []
    readings := [("perfection: the student must avoid an A", .unacceptable), ("strengthening: no $5 for another C", .acceptable)]
    paperFeatures := [("inference", "no perfection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17a : LinguisticExample :=
  { id := "vonfintel2001_17a"
    source := ⟨"von-fintel-2001", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "not only warm but hot"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("not only some but all", .acceptable), ("not only John but John and Mary", .acceptable)]
    readings := []
    paperFeatures := [("test", "not only α but β"), ("scale", "same monotonicity")]
    comment := "Evidence for Matsumoto's monotonicity condition on Horn scales."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17b : LinguisticExample :=
  { id := "vonfintel2001_17b"
    source := ⟨"von-fintel-2001", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "not only some but some and not all"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := [("not only John but only John", .unacceptable), ("not only John but John and not Mary", .unacceptable)]
    readings := []
    paperFeatures := [("test", "not only α but β"), ("scale", "mixed monotonicity")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def seat : LinguisticExample :=
  { id := "vonfintel2001_seat"
    source := ⟨"cornulier-1983", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "p. 9"⟩
    language := "stan1293"
    primaryText := "One is allowed to sit in this seat if one is disabled or one is older than 70."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A sign on public transportation."
    judgment := .acceptable
    alternatives := []
    readings := [("perfection: only the disabled or the over-70 may sit here", .acceptable)]
    paperFeatures := [("inference", "conditional perfection"), ("presumption", "exhaustivity")]
    comment := "The utterance situation suggests that other sufficient conditions would have been mentioned."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p14_2 : LinguisticExample :=
  { id := "vonfintel2001_p14_2"
    source := ⟨"groenendijk-stokhof-1984", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(2) p. 14"⟩
    language := "stan1293"
    primaryText := "Q: Who left the party early? A: Robin and Hilary left the party early."
    discourseSegments := ["Who left the party early?", "Robin and Hilary left the party early."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("exhaustive: Robin and Hilary and nobody else", .acceptable)]
    paperFeatures := [("answer", "exhaustive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p15_3 : LinguisticExample :=
  { id := "vonfintel2001_p15_3"
    source := ⟨"groenendijk-stokhof-1984", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(3) p. 15"⟩
    language := "stan1293"
    primaryText := "Q: Will Robin come to the party? A: If there is vegetarian food Robin will come to the party."
    discourseSegments := ["Will Robin come to the party?", "If there is vegetarian food Robin will come to the party."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("exhaustive: Robin comes only if there is vegetarian food", .acceptable)]
    paperFeatures := [("answer", "exhaustive"), ("inference", "conditional perfection")]
    comment := "A conditional answer to a yes/no question, read as the answer to under which conditions Robin comes."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p17_4a : LinguisticExample :=
  { id := "vonfintel2001_p17_4a"
    source := ⟨"von-fintel-2001", "(4) p. 17"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Will you give me $5 if I mow the lawn for you? A: Sure, I will give you $5 if you mow the lawn."
    discourseSegments := ["Will you give me $5 if I mow the lawn for you?", "Sure, I will give you $5 if you mow the lawn."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Q: Will the TV work if it is humid? A: Yes, the TV will work if it is humid.", .acceptable)]
    readings := [("perfection", .unacceptable)]
    paperFeatures := [("question", "yes/no conditional"), ("inference", "no perfection")]
    comment := "Exhaustivity applies vacuously to a yes-answer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p17_5 : LinguisticExample :=
  { id := "vonfintel2001_p17_5"
    source := ⟨"von-fintel-2001", "(5) p. 17"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: John is in Amherst today. B: If he is in Amherst, he'll be home late tonight."
    discourseSegments := ["John is in Amherst today.", "If he is in Amherst, he'll be home late tonight."]
    glossedTokens := []
    translation := ""
    context := "Implicit question: what of current interest follows from John's being in Amherst today?"
    judgment := .acceptable
    alternatives := []
    readings := [("perfection: he is home late only if in Amherst", .unacceptable)]
    paperFeatures := [("question", "consequences of an antecedent"), ("inference", "no perfection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p17_6 : LinguisticExample :=
  { id := "vonfintel2001_p17_6"
    source := ⟨"von-fintel-2001", "(6) p. 17"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Where around here can I buy Italian newspapers? A: You can get them at Out of Town News in Harvard Square."
    discourseSegments := ["Where around here can I buy Italian newspapers?", "You can get them at Out of Town News in Harvard Square."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("exhaustive", .unacceptable)]
    paperFeatures := [("question", "mention-some")]
    comment := "One convenient place is enough; a teenager asking how to earn five dollars is answered likewise without perfection."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "vonfintel2001_18"
    source := ⟨"von-fintel-2001", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Will you be upset if I call you at home tonight? A: I will be upset if you call me after midnight."
    discourseSegments := ["Will you be upset if I call you at home tonight?", "I will be upset if you call me after midnight."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("relativized perfection: a call before midnight will not upset her about its time", .acceptable), ("full perfection: nothing but a call after midnight upsets her", .unacceptable)]
    paperFeatures := [("inference", "relativized perfection"), ("question", "antecedents from a narrow set")]
    comment := "An insult during a call before midnight is not excluded; modeled after an example of Irene Heim's."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_17a, ex_17b, seat, p14_2, p15_3, p17_4a, p17_5, p17_6, ex_18]

end VonFintel2001.Examples
