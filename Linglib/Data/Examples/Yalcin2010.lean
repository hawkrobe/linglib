module

public import Linglib.Data.Examples.Schema

/-!
# `Yalcin2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Yalcin2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Yalcin2010.Examples`.
-/

@[expose] public section

namespace Yalcin2010.Examples

open Data.Examples

def die_p1 : LinguisticExample :=
  { id := "yalcin2010_die_p1"
    source := ⟨"yalcin-2010", "(P1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Probably, a number below 9 came up."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A fair twelve-sided die, with the sides numbered one to twelve, has been rolled."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "E1"), ("probability", "8/12")]
    comment := "First premise of the Conjunctivitis counterexample: eight of the twelve faces."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def die_p2 : LinguisticExample :=
  { id := "yalcin2010_die_p2"
    source := ⟨"yalcin-2010", "(P2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Probably, a number above 4 came up."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A fair twelve-sided die, with the sides numbered one to twelve, has been rolled."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "E1"), ("probability", "8/12")]
    comment := "Second premise, by parity with (P1); the paper notes a tendency to read it as modally subordinate to (P1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def die_c : LinguisticExample :=
  { id := "yalcin2010_die_c"
    source := ⟨"yalcin-2010", "(C)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Probably, a number above 4 and below 9 came up."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A fair twelve-sided die, with the sides numbered one to twelve, has been rolled."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "E1"), ("probability", "4/12")]
    comment := "The conclusion speakers are not tempted to accept: four of the twelve faces, refuting Conjunctivitis under the probability-space semantics."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8 : LinguisticExample :=
  { id := "yalcin2010_ex8"
    source := ⟨"yalcin-2010", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The coin probably landed heads."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A fair coin has been biased with a thin piece of tape, so that it is just slightly more likely to land heads than tails, and flipped."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6"), ("reading", "appreciably more likely than not")]
    comment := "Suggests that heads is appreciably more likely than not; the probability-space semantics with the threshold one half does not predict the judgment, motivating a relative-adjective threshold."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex9 : LinguisticExample :=
  { id := "yalcin2010_ex9"
    source := ⟨"yalcin-2010", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone probably lost the lottery."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("probably > everyone", .acceptable), ("everyone > probably", .unacceptable)]
    paperFeatures := [("section", "7"), ("principle", "epistemic containment")]
    comment := "Only the wide-scope reading of probably is available, although the narrow-scope one would be the more plausible claim."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex17 : LinguisticExample :=
  { id := "yalcin2010_ex17"
    source := ⟨"yalcin-2010", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John imagines that it is raining but that he doesn't know it is raining."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "8"), ("embedding", "imagine")]
    comment := "Imagining a Moore-paradoxical proposition is odd but the sentence is not defective."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex18 : LinguisticExample :=
  { id := "yalcin2010_ex18"
    source := ⟨"yalcin-2010", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John imagines that it is raining but it is not likely that it is raining."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "8"), ("embedding", "imagine")]
    comment := "Marked, unlike (17): the probability operator does not behave like a knowledge ascription under verbs of imagination."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex19 : LinguisticExample :=
  { id := "yalcin2010_ex19"
    source := ⟨"yalcin-2010", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Probably, Sally is likely to be at the party."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "8"), ("phenomenon", "modal concord")]
    comment := "Iterated probability operators are odd, and when not odd often vacuous."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [die_p1, die_p2, die_c, ex8, ex9, ex17, ex18, ex19]

end Yalcin2010.Examples
