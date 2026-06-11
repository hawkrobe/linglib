import Linglib.Data.Examples.Schema

/-!
# `Musan1995` — typed example data

Auto-generated from `Linglib/Data/Examples/Musan1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Musan1995.Examples`.
-/

namespace Musan1995.Examples

open Data.Examples

def ex2a : LinguisticExample :=
  { id := "musan1995_ex2a"
    source := ⟨"musan-1995", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gregory was silent."
    discourseSegments := []
    glossedTokens := []
    translation := "Gregory was silent."
    context := "Past tense with a stage-level predicate (`silent`). Does NOT implicate that Gregory is dead — silence is a temporary state; the sentence is felicitous regardless of Gregory's current existence."
    judgment := .acceptable
    alternatives := []
    readings := [("no-lifetime-implicature (stage-level)", .acceptable)]
    paperFeatures := []
    comment := "Musan 1995 (dissertation) ex (2a) p. 11, Introduction. First half of the (2a)/(2b) minimal pair that establishes the lifetime-effects diagnostic: stage-level predicates do not implicate the subject's death."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2b : LinguisticExample :=
  { id := "musan1995_ex2b"
    source := ⟨"musan-1995", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gregory was from America."
    discourseSegments := []
    glossedTokens := []
    translation := "Gregory was from America."
    context := "Past tense with an individual-level predicate (`from America` — a permanent origin/property). IMPLICATES that Gregory is dead. The lifetime effect: past tense + individual-level predicate → subject's lifetime has ended."
    judgment := .acceptable
    alternatives := []
    readings := [("lifetime-implicature (Gregory is dead)", .acceptable)]
    paperFeatures := []
    comment := "Musan 1995 ex (2b) p. 11. Second half of the minimal pair. The implicature is not part of the truth conditions but a strong inference from past tense + individual-level predicate composition. Central to the dissertation's argument that NP temporal interpretation depends on the predicate's lexical aspect."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex2a, ex2b]

end Musan1995.Examples
