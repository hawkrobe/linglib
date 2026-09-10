import Linglib.Data.Examples.Schema

/-!
# `GartnerGyuris2017` — typed example data

Auto-generated from `Linglib/Data/Examples/GartnerGyuris2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GartnerGyuris2017.Examples`.
-/

namespace GartnerGyuris2017.Examples

open Data.Examples

def gg2017_1 : LinguisticExample :=
  { id := "gg2017_1"
    source := ⟨"gartner-gyuris-2017", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is it sunny outside?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A enters S's windowless office in a manifestly dripping wet raincoat."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "English V1"), ("form", "PPQ"), ("dimension", "evidential"), ("value", "-")]
    comment := "A positive polar question is infelicitous under compelling evidence against p."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gg2017_2a : LinguisticExample :=
  { id := "gg2017_2a"
    source := ⟨"gartner-gyuris-2017", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Didn't John go to the party?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "S has just learned that A hosted a party last night but has no idea who did or should have attended."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "English V1"), ("form", "IN-NPQ"), ("dimension", "epistemic"), ("value", "%")]
    comment := "A negative polar question conveys the speaker's expectation that p, so it is odd without one."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gg2017_2b : LinguisticExample :=
  { id := "gg2017_2b"
    source := ⟨"gartner-gyuris-2017", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did John not go to the party?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "S has just learned that A hosted a party last night but has no idea who did or should have attended."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "English V1"), ("form", "IN-NPQ"), ("dimension", "epistemic"), ("value", "%")]
    comment := "As (2a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gg2017_8_neg : LinguisticExample :=
  { id := "gg2017_8_neg"
    source := ⟨"gartner-gyuris-2017", "(8)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Süt-e a nap?"
    discourseSegments := []
    glossedTokens := [("Süt-e", "shine-Q"), ("a", "the"), ("nap", "sun")]
    translation := "Is it sunny?"
    context := "A enters S's windowless office in a manifestly dripping wet raincoat."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Hungarian e"), ("form", "PPQ"), ("dimension", "evidential"), ("value", "-")]
    comment := "The e-interrogative's evidential anti-bias: infelicitous under compelling evidence against p."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gg2017_8_pos : LinguisticExample :=
  { id := "gg2017_8_pos"
    source := ⟨"gartner-gyuris-2017", "(8)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Süt-e a nap?"
    discourseSegments := []
    glossedTokens := [("Süt-e", "shine-Q"), ("a", "the"), ("nap", "sun")]
    translation := "Is it sunny?"
    context := "A comes in with dark sunglasses, T-shirt, shorts, a straw hat and suntan lotion, humming a song about sunshine."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Hungarian e"), ("form", "PPQ"), ("dimension", "evidential"), ("value", "+")]
    comment := "The e-interrogative's evidential anti-bias: infelicitous under compelling evidence for p too."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gg2017_9a : LinguisticExample :=
  { id := "gg2017_9a"
    source := ⟨"gartner-gyuris-2017", "(9a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Nincs-e itt egy francia étterem?"
    discourseSegments := []
    glossedTokens := [("Nincs-e", "not.is-Q"), ("itt", "here"), ("egy", "a"), ("francia", "French"), ("étterem", "restaurant")]
    translation := "Isn't there a French restaurant here?"
    context := "S and A stand in front of a billboard in a small village saying that the last restaurant there has just closed for good."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Hungarian e"), ("form", "ON-NPQ"), ("dimension", "evidential"), ("value", "-")]
    comment := "The e-interrogative expressing an outside-negation question keeps the anti-bias."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gg2017_9b : LinguisticExample :=
  { id := "gg2017_9b"
    source := ⟨"gartner-gyuris-2017", "(9b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Nincs-e itt egy étterem?"
    discourseSegments := []
    glossedTokens := [("Nincs-e", "not.is-Q"), ("itt", "here"), ("egy", "a"), ("étterem", "restaurant")]
    translation := "Isn't there a restaurant here?"
    context := "The billboard announces the opening of several new restaurants in the village."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Hungarian e"), ("form", "ON-NPQ"), ("dimension", "evidential"), ("value", "+")]
    comment := "As (9a), under compelling evidence for p."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [gg2017_1, gg2017_2a, gg2017_2b, gg2017_8_neg, gg2017_8_pos, gg2017_9a, gg2017_9b]

end GartnerGyuris2017.Examples
