module

public import Linglib.Data.Examples.Schema

/-!
# `VanRooy2003` — typed example data

Auto-generated from `Linglib/Data/Examples/VanRooy2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanRooy2003.Examples`.
-/

@[expose] public section

namespace VanRooy2003.Examples

open Data.Examples

def ex_3 : LinguisticExample :=
  { id := "vanrooy2003_3"
    source := ⟨"van-rooy-2003", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who is Muhammed Ali?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("referential: that man over there", .acceptable), ("descriptive: the greatest boxer ever", .acceptable)]
    paperFeatures := [("type", "identification question")]
    comment := "Which method of identification resolves the question depends on the decision problem."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "vanrooy2003_12"
    source := ⟨"van-rooy-2003", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where can I buy an Italian newspaper?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The questioner wants a newspaper and can walk to the station or to the palace; in one world both sell it."
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some: at least at the station", .acceptable)]
    paperFeatures := [("type", "mention-some"), ("regions", "{u,w},{v,w}")]
    comment := "The partial answer resolves the decision problem: the actions induce overlapping propositions, not a partition."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "vanrooy2003_14"
    source := ⟨"van-rooy-2003", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who, for example, came to the party?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "explicitly non-exhaustive")]
    comment := "Completely answered without the exhaustive list: the meaning of a question need not be a partition."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "vanrooy2003_15"
    source := ⟨"van-rooy-2003", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows where he can buy an Italian newspaper."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "embedded mention-some")]
    comment := "True when John knows one relevant place: resolvedness is context-dependent within the semantics."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "vanrooy2003_16"
    source := ⟨"van-rooy-2003", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who will come to the concert?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "contextual domain")]
    comment := "Neither a full enumeration nor mention-some: the domain is the people the questioner cares about."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "vanrooy2003_17"
    source := ⟨"van-rooy-2003", "(17)"⟩
    reportedIn := some ⟨"karttunen-1977", ""⟩
    language := "stan1293"
    primaryText := "Who dates Mary?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "contextual domain")]
    comment := "Karttunen's argument against partitions dissolves once the domain is contextually limited."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18b : LinguisticExample :=
  { id := "vanrooy2003_18b"
    source := ⟨"van-rooy-2003", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many meters can you jump?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "degree question"), ("optimal value", "maximal")]
    comment := "The maximal value is the most informative true answer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19 : LinguisticExample :=
  { id := "vanrooy2003_19"
    source := ⟨"van-rooy-2003", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In how many seconds can you run the 100 meters?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "degree question"), ("optimal value", "minimal")]
    comment := "The minimal value is the most informative true answer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "vanrooy2003_21"
    source := ⟨"van-rooy-2003", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where do you live?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complete address, to send a letter", .acceptable), ("the city, to decide on a visit", .acceptable)]
    paperFeatures := [("type", "granularity")]
    comment := "The level of granularity of the resolving answer depends on the decision problem."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22 : LinguisticExample :=
  { id := "vanrooy2003_22"
    source := ⟨"van-rooy-2003", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who killed spiderman?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Either John or Bill did it, and the killer wears a blue or a green mask; who wears which is unknown."
    judgment := .acceptable
    alternatives := []
    readings := [("by name: {{u,v},{w,x}}", .acceptable), ("by mask: {{u,w},{v,x}}", .acceptable)]
    paperFeatures := [("type", "conceptual cover")]
    comment := "The partition depends on which concepts resolve the decision problem, without fixing a conceptual cover in advance."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "vanrooy2003_23"
    source := ⟨"van-rooy-2003", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who is who?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "The spiderman scenario of (22)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "conceptual cover")]
    comment := "The identity is informative only across incompatible concepts, giving the four-cell partition."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "vanrooy2003_24"
    source := ⟨"van-rooy-2003", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many meters can't you jump?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("type", "degree question"), ("optimal value", "undefined")]
    comment := "Odd at first: with jumping high preferred there is no best number of meters one cannot jump; reversing the preferences yields the first such number."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25 : LinguisticExample :=
  { id := "vanrooy2003_25"
    source := ⟨"van-rooy-2003", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How tall can a polar bear be?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Asked by an artist making a life-size sculpture of a polar bear."
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [("type", "degree question"), ("reading", "mention-some")]
    comment := "A degree question with a mention-some reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_3, ex_12, ex_14, ex_15, ex_16, ex_17, ex_18b, ex_19, ex_21, ex_22, ex_23, ex_24, ex_25]

end VanRooy2003.Examples
