import Linglib.Data.Examples.Schema

/-!
# `Iatridou2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Iatridou2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Iatridou2000.Examples`.
-/

namespace Iatridou2000.Examples

open Data.Examples

def ex1a : LinguisticExample :=
  { id := "iatridou2000_ex1a"
    source := ⟨"iatridou-2000", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish I had a car."
    discourseSegments := []
    glossedTokens := []
    translation := "I wish I had a car."
    context := "Present counterfactual wish. Conveys: I don't have a car now. Past morphology (`had`) but present-time reference."
    judgment := .acceptable
    alternatives := []
    readings := [("present-CF (car absent now)", .acceptable)]
    paperFeatures := []
    comment := "Iatridou 2000 ex (1a), Linguistic Inquiry 31(2) p. 232. First of the (1a)/(1b) wishes pair. The grammatical past-tense morpheme contributes counterfactuality (about the present), not temporal precedence — Iatridou's central exclusion-feature claim."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex1b : LinguisticExample :=
  { id := "iatridou2000_ex1b"
    source := ⟨"iatridou-2000", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish I had had a car when I was a student."
    discourseSegments := []
    glossedTokens := []
    translation := "I wish I had had a car when I was a student."
    context := "Past counterfactual wish. Conveys: I didn't have a car then (student days). Says nothing about whether I have a car now. Past-on-past morphology (`had had`) — the doubling encodes BOTH counterfactuality AND past temporal reference."
    judgment := .acceptable
    alternatives := []
    readings := [("past-CF (no car as student)", .acceptable)]
    paperFeatures := []
    comment := "Iatridou 2000 ex (1b), p. 232. Second of the wishes pair. The contrast (1a)/(1b) motivates separating the counterfactuality-marking past morpheme from the temporal past morpheme."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2a : LinguisticExample :=
  { id := "iatridou2000_ex2a"
    source := ⟨"iatridou-2000", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he were smart, he would be rich."
    discourseSegments := []
    glossedTokens := []
    translation := "If he were smart, he would be rich."
    context := "Present counterfactual conditional. Conveys: he is not smart AND he is not rich. Past morphology (`were`, `would`) with present reference."
    judgment := .acceptable
    alternatives := []
    readings := [("present-CF (he is not smart and not rich)", .acceptable)]
    paperFeatures := []
    comment := "Iatridou 2000 ex (2a), p. 232. Canonical present counterfactual conditional. Iatridou's own (2a) uses `If he were smart`; the generic `If John were here` / `If John were taller` form is widely cited but not verbatim from the paper."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2b : LinguisticExample :=
  { id := "iatridou2000_ex2b"
    source := ⟨"iatridou-2000", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he had been smart, he would have been rich."
    discourseSegments := []
    glossedTokens := []
    translation := "If he had been smart, he would have been rich."
    context := "Past counterfactual conditional. Conveys: he was not smart (in general or on one specific occasion) AND he was not rich. Past-perfect morphology (`had been`, `would have been`) encodes BOTH counterfactuality AND past reference."
    judgment := .acceptable
    alternatives := []
    readings := [("past-CF (he was not smart and not rich)", .acceptable)]
    paperFeatures := []
    comment := "Iatridou 2000 ex (2b), p. 232. Past-CF counterpart to (2a). The (2a)/(2b) contrast — like (1a)/(1b) — diagnostics the exclusion-feature analysis: one past morpheme for counterfactuality (excludes the actual world), a second past morpheme for past tense (excludes the present)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1a, ex1b, ex2a, ex2b]

end Iatridou2000.Examples
