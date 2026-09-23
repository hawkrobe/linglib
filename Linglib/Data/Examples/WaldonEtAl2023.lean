module

public import Linglib.Data.Examples.Schema

/-!
# `WaldonEtAl2023` — typed example data

Auto-generated from `Linglib/Data/Examples/WaldonEtAl2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WaldonEtAl2023.Examples`.
-/

@[expose] public section

namespace WaldonEtAl2023.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "waldonetal2023_1"
    source := ⟨"hart-1958", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(1)"⟩
    language := "stan1293"
    primaryText := "A legal rule forbids you to take a vehicle into the public park."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("puzzle", "Hart's vehicle rule")]
    comment := "Hart's no-vehicles-in-the-park rule; whether a bicycle, roller skates or a toy car count as vehicles is what the rule leaves open."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def rule : LinguisticExample :=
  { id := "waldonetal2023_rule"
    source := ⟨"waldon-etal-2023", "§3.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No electronic devices are allowed in the theater."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("rule", "prohibition"), ("artifactNoun", "electronic device")]
    comment := "The rule of Figure 1, read in the goal-neutral condition and with the goals of limiting light, limiting noise and preventing recordings."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4a : LinguisticExample :=
  { id := "waldonetal2023_4a"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(4a)"⟩
    language := "stan1293"
    primaryText := "This tree is a pine in some respects."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := [("This tree is a pine in most respects.", .unacceptable), ("This tree is a pine in every respect.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "dimensional"), ("nounType", "natural kind")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4b : LinguisticExample :=
  { id := "waldonetal2023_4b"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(4b)"⟩
    language := "stan1293"
    primaryText := "This place is a church in some respects."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "dimensional"), ("nounType", "artifact")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4c : LinguisticExample :=
  { id := "waldonetal2023_4c"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(4c)"⟩
    language := "stan1293"
    primaryText := "This place is safe in some respects."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "dimensional"), ("nounType", "multidimensional adjective")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5a : LinguisticExample :=
  { id := "waldonetal2023_5a"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(5a)"⟩
    language := "stan1293"
    primaryText := "This tree is more a pine than that one."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := [("This tree is more a pine than an oak.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "degree"), ("nounType", "natural kind")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5b : LinguisticExample :=
  { id := "waldonetal2023_5b"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(5b)"⟩
    language := "stan1293"
    primaryText := "This place is more a church than that one."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := [("This place is more a church than an art gallery.", .questionable)]
    readings := []
    paperFeatures := [("construction", "degree"), ("nounType", "artifact")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5c : LinguisticExample :=
  { id := "waldonetal2023_5c"
    source := ⟨"sassoon-fadlon-2017", ""⟩
    reportedIn := some ⟨"waldon-etal-2023", "(5c)"⟩
    language := "stan1293"
    primaryText := "This place is more safe than that one."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degree"), ("nounType", "multidimensional adjective")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "waldonetal2023_7"
    source := ⟨"waldon-etal-2023", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This tree is taller than that one."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("This tree is taller than it is wide.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "degree"), ("nounType", "single-dimensional adjective")]
    comment := "Not context sensitive: the comparative orders two degrees."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10a : LinguisticExample :=
  { id := "waldonetal2023_10a"
    source := ⟨"waldon-etal-2023", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every vehicle is prohibited from the park."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "quantificational"), ("parameters", "F, W, s")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11a : LinguisticExample :=
  { id := "waldonetal2023_11a"
    source := ⟨"waldon-etal-2023", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This object is more of a vehicle than that one."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "degree"), ("parameters", "F, W project")]
    comment := "Context sensitivity persists in the artifact noun comparative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16a : LinguisticExample :=
  { id := "waldonetal2023_16a"
    source := ⟨"waldon-etal-2023", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No electronic devices are allowed in the theater. By the way: for our purposes, a flashlight counts as an electronic device."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "meta-linguistic negotiation")]
    comment := "What counts as a member of the category is up for negotiation, as a threshold is for a gradable adjective."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16b : LinguisticExample :=
  { id := "waldonetal2023_16b"
    source := ⟨"waldon-etal-2023", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Get me a long ladder. By the way: for our purposes, 20 feet counts as long for a ladder."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "meta-linguistic negotiation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16c : LinguisticExample :=
  { id := "waldonetal2023_16c"
    source := ⟨"waldon-etal-2023", "(16c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put all the bottles of Heineken in the fridge. By the way: for our purposes, nothing that my neighbors bought for their party counts as a bottle of Heineken."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "meta-linguistic negotiation"), ("analysis", "domain restriction")]
    comment := "Domain restriction to the salient bottles is available, but what counts as a bottle of Heineken is not negotiated."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, rule, ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_5c, ex_7, ex_10a, ex_11a, ex_16a, ex_16b, ex_16c]

end WaldonEtAl2023.Examples
