import Linglib.Data.Examples.Schema

/-!
# `Wurmbrand2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Wurmbrand2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wurmbrand2014.Examples`.
-/

namespace Wurmbrand2014.Examples

open Data.Examples

def ex1a : LinguisticExample :=
  { id := "wurmbrand2014_ex1a"
    source := ⟨"wurmbrand-2014", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo decided to read a book."
    discourseSegments := []
    glossedTokens := []
    translation := "Leo decided to read a book."
    context := "Future-irrealis infinitive: the reading is future of the deciding. No tense morphology on the complement; the future orientation comes from `decide`'s lexical semantics (woll-like operator selected by the matrix verb)."
    judgment := .acceptable
    alternatives := []
    readings := [("future-irrealis (reading after deciding)", .acceptable)]
    paperFeatures := []
    comment := "Wurmbrand 2014 ex (1a), LI 45(3) p. 403–404. First diagnostic in her classification of infinitival tense — future irrealis with `decide` (and the `want` class more generally)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex1b : LinguisticExample :=
  { id := "wurmbrand2014_ex1b"
    source := ⟨"wurmbrand-2014", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believes Julia to be a princess."
    discourseSegments := []
    glossedTokens := []
    translation := "Leo believes Julia to be a princess."
    context := "Propositional (NOW-anchored) infinitive: the believing time and Julia-being-a-princess time coincide. Simultaneous, not future-shifted."
    judgment := .acceptable
    alternatives := []
    readings := [("propositional (Julia princess at believing time)", .acceptable)]
    paperFeatures := []
    comment := "Wurmbrand 2014 ex (1b), p. 403. Second class in her classification: propositional infinitives anchor to the matrix's NOW."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2a : LinguisticExample :=
  { id := "wurmbrand2014_ex2a"
    source := ⟨"wurmbrand-2014", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo decided to bring the toys tomorrow."
    discourseSegments := []
    glossedTokens := []
    translation := "Leo decided to bring the toys tomorrow."
    context := "Future-irrealis infinitive with episodic interpretation: the bringing is at a specific future time (tomorrow relative to the deciding)."
    judgment := .acceptable
    alternatives := []
    readings := [("episodic-future (bringing tomorrow-relative-to-deciding)", .acceptable)]
    paperFeatures := []
    comment := "Wurmbrand 2014 ex (2a), p. 404. Diagnoses that future-irrealis infinitives admit episodic readings."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2b : LinguisticExample :=
  { id := "wurmbrand2014_ex2b"
    source := ⟨"wurmbrand-2014", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believed Julia to bring the toys right then."
    discourseSegments := []
    glossedTokens := []
    translation := "Leo believed Julia to bring the toys right then."
    context := "Propositional infinitive + episodic adverbial. The bare infinitive does NOT admit an episodic reading; needs the progressive (`to be bringing`) instead."
    judgment := .ungrammatical
    alternatives := [("Leo believed Julia to be bringing the toys right then.", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "Wurmbrand 2014 ex (2b), p. 404. Diagnoses that propositional infinitives BLOCK bare episodic readings — needs the progressive. The contrast (2a)/(2b) is the cornerstone of her propositional vs future-irrealis classification."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1a, ex1b, ex2a, ex2b]

end Wurmbrand2014.Examples
