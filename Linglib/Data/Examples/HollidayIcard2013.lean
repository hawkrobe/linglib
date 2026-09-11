import Linglib.Data.Examples.Schema

/-!
# `HollidayIcard2013` — typed example data

Auto-generated from `Linglib/Data/Examples/HollidayIcard2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HollidayIcard2013.Examples`.
-/

namespace HollidayIcard2013.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "hollidayicard2013_ex1"
    source := ⟨"holliday-icard-2013", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is at least as likely that one of Brazil or Qatar will win the World Cup as it is that one of the U.S. or Qatar will win the World Cup."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7"), ("axiom", "A"), ("form", "(φ ∨ χ) ⩾ (ψ ∨ χ)")]
    comment := "Intuitively equivalent to (2): the motivation for qualitative additivity, the axiom A of the logic FA."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2 : LinguisticExample :=
  { id := "hollidayicard2013_ex2"
    source := ⟨"holliday-icard-2013", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is at least as likely that Brazil will win the World Cup as it is that the U.S. will win the World Cup."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7"), ("axiom", "A"), ("form", "φ ⩾ ψ")]
    comment := "The shared disjunct Qatar cancels; a preliminary Mechanical Turk study found unanimous agreement with the equivalence (footnote 14)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex3 : LinguisticExample :=
  { id := "hollidayicard2013_ex3"
    source := ⟨"holliday-icard-2013", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is more likely that one of Argentina or England will win the World Cup than it is that one of China or Denmark will win."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "10.1"), ("axiom", "Scott4"), ("form", "{a, e} ≻ {c, d}")]
    comment := "One of the four Kraft–Pratt–Seidenberg comparisons: jointly consistent with FA but with no finitely additive measure. The paper doubts that speakers find the combination inconsistent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4 : LinguisticExample :=
  { id := "hollidayicard2013_ex4"
    source := ⟨"holliday-icard-2013", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is more likely that one of Brazil or China will win than it is that one of Argentina or Denmark will win."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "10.1"), ("axiom", "Scott4"), ("form", "{b, c} ≻ {a, d}")]
    comment := "One of the four Kraft–Pratt–Seidenberg comparisons: jointly consistent with FA but with no finitely additive measure. The paper doubts that speakers find the combination inconsistent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5 : LinguisticExample :=
  { id := "hollidayicard2013_ex5"
    source := ⟨"holliday-icard-2013", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is more likely that Denmark will win than it is that one of Argentina or China will win."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "10.1"), ("axiom", "Scott4"), ("form", "{d} ≻ {a, c}")]
    comment := "One of the four Kraft–Pratt–Seidenberg comparisons: jointly consistent with FA but with no finitely additive measure. The paper doubts that speakers find the combination inconsistent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6 : LinguisticExample :=
  { id := "hollidayicard2013_ex6"
    source := ⟨"holliday-icard-2013", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is more likely that one of Argentina, China, or Denmark will win than it is that one of Brazil or England will win."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "10.1"), ("axiom", "Scott4"), ("form", "{a, c, d} ≻ {b, e}")]
    comment := "One of the four Kraft–Pratt–Seidenberg comparisons: jointly consistent with FA but with no finitely additive measure. The paper doubts that speakers find the combination inconsistent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1, ex2, ex3, ex4, ex5, ex6]

end HollidayIcard2013.Examples
