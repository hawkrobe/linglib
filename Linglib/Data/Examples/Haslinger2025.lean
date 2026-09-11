import Linglib.Data.Examples.Schema

/-!
# `Haslinger2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Haslinger2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Haslinger2025.Examples`.
-/

namespace Haslinger2025.Examples

open Data.Examples

def ch1_6a : LinguisticExample :=
  { id := "haslinger2025_ch1_6a"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The doors are open."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "lower"), ("precision", "lower")]
    comment := "The simpler member: a definite plural with potential for imprecision."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch1_6b : LinguisticExample :=
  { id := "haslinger2025_ch1_6b"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the doors are open."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "higher"), ("precision", "higher")]
    comment := "The more complex member: not blocked despite its complexity, because it is more precise."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch1_7a : LinguisticExample :=
  { id := "haslinger2025_ch1_7a"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann owns 100 cars."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "lower"), ("precision", "lower")]
    comment := "A round bare numeral, imprecise in the right context."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch1_7b : LinguisticExample :=
  { id := "haslinger2025_ch1_7b"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann owns exactly 100 cars."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "higher"), ("precision", "higher")]
    comment := "The modified numeral: more complex and more precise."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch1_8a : LinguisticExample :=
  { id := "haslinger2025_ch1_8a"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[DEF [all doors]] [are open]"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "higher"), ("precision", "lower"), ("hypothetical", "yes")]
    comment := "The hypothetical inverse pattern, an imprecise expression built by adding structure to the precise one: blocked in almost all contexts by No Needless Manner Violations, hence unattested."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch1_8b : LinguisticExample :=
  { id := "haslinger2025_ch1_8b"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[all doors] [are open]"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "lower"), ("precision", "higher"), ("hypothetical", "yes")]
    comment := "The hypothetical inverse pattern's precise member, simpler than its imprecise counterpart."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch1_9a : LinguisticExample :=
  { id := "haslinger2025_ch1_9a"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ann and Bert have red hair."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "lower"), ("precision", "lower")]
    comment := "A conjunction with a homogeneity gap but no non-maximal reading: potential for imprecision that Inference Preservation blocks."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch1_9b : LinguisticExample :=
  { id := "haslinger2025_ch1_9b"
    source := ⟨"haslinger-2025-diss", "Ch. 1, (9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Both Ann and Bert have red hair."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "1"), ("phenomenon", "complexityPrecision"), ("complexity", "higher"), ("precision", "higher")]
    comment := "The gap-less counterpart, with extra material."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch2_19 : LinguisticExample :=
  { id := "haslinger2025_ch2_19"
    source := ⟨"haslinger-2025-diss", "Ch. 2, (19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Look, this guy owns 100 cars."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A new tax was introduced to discourage rich people from collecting cars. The tax rate per car increases if someone owns 10 or more cars, and increases yet again for people who own 100 or more. Ann is looking at the tax paperwork of someone who claims to own 98 cars."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "2"), ("phenomenon", "numeralImprecision"), ("scenario", "carsExact"), ("actualValue", "98")]
    comment := "CARS(EXACT): the salient issue is the tax rate, which separates 98 from 100, so the exact construal is the only relevant one and the utterance is rejected."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch2_20 : LinguisticExample :=
  { id := "haslinger2025_ch2_20"
    source := ⟨"haslinger-2025-diss", "Ch. 2, (20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Look, this guy owns 100 cars."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Ann just read a newspaper report on how insanely rich Sam Bankman-Fried is. Among other things, the report claims that he owns 98 Teslas for his personal use."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "2"), ("phenomenon", "numeralImprecision"), ("scenario", "carsInexact"), ("actualValue", "98")]
    comment := "CARS(INEXACT): for the issue of extreme wealth 98 and 100 fall together, and the inexact construal makes the utterance acceptable."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch2_164a : LinguisticExample :=
  { id := "haslinger2025_ch2_164a"
    source := ⟨"haslinger-2025-diss", "Ch. 2, (164a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bei diesem Spiel hat heute jeder 200 Münzen gesammelt."
    discourseSegments := []
    glossedTokens := []
    translation := "In this game, everyone collected 200 coins today."
    context := "On a TV game show, there is a game in which participants have to collect 200 coins in a very brief time interval. Participants that achieve a count of exactly 200 win €250. Participants that come very close to that number, but do not meet the goal exactly, receive €50. Today all ten participants managed to collect amounts that come close to 200 (195, 198, 203, 205, 199 etc.) and therefore won €50. After the show, the producer wants to know how the individual games went. Her assistant points at the coins and says:"
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "2"), ("phenomenon", "numeralImprecision"), ("scenario", "gameShow")]
    comment := "False on the exact construal, true on the inexact one; most consultants accept exactly one of (164a) and (164b), disagreeing on which, so round numerals show no homogeneity gap."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch2_164b : LinguisticExample :=
  { id := "haslinger2025_ch2_164b"
    source := ⟨"haslinger-2025-diss", "Ch. 2, (164b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bei diesem Spiel hat heute niemand 200 Münzen gesammelt."
    discourseSegments := []
    glossedTokens := []
    translation := "In this game, nobody collected 200 coins today."
    context := "On a TV game show, there is a game in which participants have to collect 200 coins in a very brief time interval. Participants that achieve a count of exactly 200 win €250. Participants that come very close to that number, but do not meet the goal exactly, receive €50. Today all ten participants managed to collect amounts that come close to 200 (195, 198, 203, 205, 199 etc.) and therefore won €50. After the show, the producer wants to know how the individual games went. Her assistant points at the coins and says:"
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "2"), ("phenomenon", "numeralImprecision"), ("scenario", "gameShow")]
    comment := "True on the exact construal, false on the inexact one."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch6_8a : LinguisticExample :=
  { id := "haslinger2025_ch6_8a"
    source := ⟨"haslinger-2025-diss", "Ch. 6, (8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "150"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("phenomenon", "roundness"), ("roundnessScale", "tens")]
    comment := "A numeral on the conventionalized scale of tens, which permits imprecision."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch6_8b : LinguisticExample :=
  { id := "haslinger2025_ch6_8b"
    source := ⟨"haslinger-2025-diss", "Ch. 6, (8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "152"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("phenomenon", "roundness"), ("roundnessScale", "units")]
    comment := "A numeral off that scale, whose alternatives include 150: no imprecision."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch6_9a : LinguisticExample :=
  { id := "haslinger2025_ch6_9a"
    source := ⟨"haslinger-2025-diss", "Ch. 6, (9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's 10:45."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("phenomenon", "roundness"), ("roundnessScale", "quarterHours")]
    comment := "A clock time on the quarter-hour scale: acceptable exact and inexact."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch6_9b : LinguisticExample :=
  { id := "haslinger2025_ch6_9b"
    source := ⟨"haslinger-2025-diss", "Ch. 6, (9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's 10:46."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("chapter", "6"), ("phenomenon", "roundness"), ("roundnessScale", "minutes")]
    comment := "A clock time off that scale: acceptable exact, unacceptable inexact."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch7_19b : LinguisticExample :=
  { id := "haslinger2025_ch7_19b"
    source := ⟨"haslinger-2025-diss", "Ch. 7, (19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bert, Claire and Dora were there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Bert was there.", .acceptable)]
    readings := []
    paperFeatures := [("chapter", "7"), ("phenomenon", "conjunctionMaximality")]
    comment := "The precise truth conditions entail each conjunct alternative, so Inference Preservation admits only the maximal construal."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ch1_6a, ch1_6b, ch1_7a, ch1_7b, ch1_8a, ch1_8b, ch1_9a, ch1_9b, ch2_19, ch2_20, ch2_164a, ch2_164b, ch6_8a, ch6_8b, ch6_9a, ch6_9b, ch7_19b]

end Haslinger2025.Examples
