import Linglib.Data.Examples.Schema

/-!
# `Elliott2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Elliott2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Elliott2025.Examples`.
-/

namespace Elliott2025.Examples

open Data.Examples

def ex_6 : LinguisticExample :=
  { id := "elliott2025_6"
    source := ⟨"elliott-2025", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three boys gathered."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1")]
    comment := "A numeral expression composes with a collective predicate, as the predicative theory of numerals predicts."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "elliott2025_7"
    source := ⟨"elliott-2025", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three boys are singing or dancing."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Boys b1 and b2 are only singing, b3 is only dancing, and no other boys are singing or dancing."
    judgment := .acceptable
    alternatives := []
    readings := [("distributive scope over the disjunction", .acceptable)]
    paperFeatures := [("section", "2.1")]
    comment := "True in the context: the covert distributivity operator quantifies over the atomic parts."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "elliott2025_10"
    source := ⟨"elliott-2025", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Less than three boys sneezed."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Three boys sneezed."
    judgment := .acceptable
    alternatives := []
    readings := [("true in the context", .unacceptable)]
    paperFeatures := [("section", "2.2.1")]
    comment := "The classical predicative entry wrongly predicts truth, since a two-boy part of the sneezers sneezed: van Benthem's problem."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "elliott2025_12"
    source := ⟨"elliott-2025", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Less than three boys sneezed."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "No boys sneezed."
    judgment := .acceptable
    alternatives := []
    readings := [("true in the context", .acceptable)]
    paperFeatures := [("section", "2.2.2")]
    comment := "Intuitively true, but the classical predicative entry requires a sneezing plurality of boys: the existential entailment problem."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_47 : LinguisticExample :=
  { id := "elliott2025_47"
    source := ⟨"elliott-2025", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If two relatives of mine die, I'll inherit a house."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > if..then > Dist", .acceptable), ("∃ > Dist > if..then", .unacceptable)]
    paperFeatures := [("section", "5")]
    comment := "The existential component of the numeral takes exceptional scope out of the antecedent; the distributive component stays inside."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_48a : LinguisticExample :=
  { id := "elliott2025_48a"
    source := ⟨"elliott-2025", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If all relatives of mine die, I'll inherit a house."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∀ > if..then", .unacceptable)]
    paperFeatures := [("section", "5")]
    comment := "No exceptional scope: all relatives of mine denotes a singleton, so existential raising over it is scopeless and universal force stays inside the antecedent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_48b : LinguisticExample :=
  { id := "elliott2025_48b"
    source := ⟨"elliott-2025", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If no relatives of mine die, I'll inherit a house."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("no > if..then", .unacceptable)]
    paperFeatures := [("section", "5")]
    comment := "No exceptional scope: no relatives of mine denotes the wholly negative group."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_50 : LinguisticExample :=
  { id := "elliott2025_50"
    source := ⟨"elliott-2025", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If James bets on exactly two numbers, he'll win this round (I just don't know which two)."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "James plays a two-ball roulette variant, betting on any two numbers and winning if both balls land on them; the croupier has rigged the wheel so the balls land on two predetermined numbers."
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > if..then (exceptional existential scope)", .acceptable)]
    paperFeatures := [("section", "5")]
    comment := "Contrary to the received view on modified numerals, the exceptional existential scope reading the theory predicts is available; the judgment was checked with about ten speakers."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_51a : LinguisticExample :=
  { id := "elliott2025_51a"
    source := ⟨"elliott-2025", "(51a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some boy gathered."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1")]
    comment := "A collective predicate needs a semantically plural DP, which the singular predicative theory does not yet distinguish."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_51b : LinguisticExample :=
  { id := "elliott2025_51b"
    source := ⟨"elliott-2025", "(51b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some boys gathered."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1")]
    comment := "The plural DP composes with the collective predicate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_6, ex_7, ex_10, ex_12, ex_47, ex_48a, ex_48b, ex_50, ex_51a, ex_51b]

end Elliott2025.Examples
