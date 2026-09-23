module

public import Linglib.Data.Examples.Schema

/-!
# `RosaArnold2017` — typed example data

Auto-generated from `Linglib/Data/Examples/RosaArnold2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RosaArnold2017.Examples`.
-/

@[expose] public section

namespace RosaArnold2017.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "rosaarnold2017_1a"
    source := ⟨"rosa-arnold-2017", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The butler blamed the chauffeur because he..."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("murdered someone", .acceptable)]
    paperFeatures := [("verbType", "implicitCausality"), ("expected", "stimulus")]
    comment := "Implicit causality: the stimulus, the chauffeur, is the expected continuation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1b : LinguisticExample :=
  { id := "rosaarnold2017_1b"
    source := ⟨"rosa-arnold-2017", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The butler impressed the chauffeur because he..."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("figured out the case", .acceptable)]
    paperFeatures := [("verbType", "implicitCausality"), ("expected", "stimulus")]
    comment := "Implicit causality: the stimulus, the butler, is the expected continuation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2a : LinguisticExample :=
  { id := "rosaarnold2017_2a"
    source := ⟨"rosa-arnold-2017", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The butler gave the threatening note to the chauffeur and he..."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("turned it in to the police", .acceptable)]
    paperFeatures := [("verbType", "transfer"), ("expected", "goal")]
    comment := "Transfer of possession: the goal, the chauffeur, is the expected continuation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2b : LinguisticExample :=
  { id := "rosaarnold2017_2b"
    source := ⟨"rosa-arnold-2017", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The butler received a ticking bomb from the chauffeur and he..."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("chucked it into the river", .acceptable)]
    paperFeatures := [("verbType", "transfer"), ("expected", "goal")]
    comment := "Transfer of possession with the goal as subject: the butler is the expected continuation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3a : LinguisticExample :=
  { id := "rosaarnold2017_3a"
    source := ⟨"rosa-arnold-2017", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sir Barnes got a backrub from Lady Mannerly."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "goal"), ("gram", "subject")]
    comment := "Goal continuation, subject position: the continued character is the goal and the subject. The underlined character is the one the next picture continues."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3b : LinguisticExample :=
  { id := "rosaarnold2017_3b"
    source := ⟨"rosa-arnold-2017", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lady Mannerly gave a backrub to Sir Barnes."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "goal"), ("gram", "nonsubject")]
    comment := "Goal continuation, nonsubject position. The underlined character is the one the next picture continues."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4a : LinguisticExample :=
  { id := "rosaarnold2017_4a"
    source := ⟨"rosa-arnold-2017", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The chef handed a cookbook to the maid."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "source"), ("gram", "subject")]
    comment := "Source continuation, subject position. The underlined character is the one the next picture continues."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4b : LinguisticExample :=
  { id := "rosaarnold2017_4b"
    source := ⟨"rosa-arnold-2017", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The maid took a cookbook from the chef."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "source"), ("gram", "nonsubject")]
    comment := "Source continuation, nonsubject position. The underlined character is the one the next picture continues."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4a, ex_4b]

end RosaArnold2017.Examples
