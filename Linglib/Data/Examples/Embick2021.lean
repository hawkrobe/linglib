import Linglib.Data.Examples.Schema

/-!
# `Embick2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Embick2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Embick2021.Examples`.
-/

namespace Embick2021.Examples

open Data.Examples

def ex_6c : LinguisticExample :=
  { id := "embick2021_6c"
    source := ⟨"embick-2021", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's destruction of the city"
    discourseSegments := []
    glossedTokens := []
    translation := "John's destruction of the city"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "DESTROY"), ("rootClass", "agentive"), ("construction", "derivedNominal"), ("h1", "n"), ("h1exp", "-tion")]
    comment := "Agentive reading of the possessor."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6d : LinguisticExample :=
  { id := "embick2021_6d"
    source := ⟨"embick-2021", "(6d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's destroying the city"
    discourseSegments := []
    glossedTokens := []
    translation := "John's destroying the city"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "DESTROY"), ("rootClass", "agentive"), ("construction", "gerund"), ("h1", "v"), ("h1exp", ""), ("h2", "voice"), ("h2exp", ""), ("h3", "n"), ("h3exp", "-ing")]
    comment := "Agentive reading of the possessor."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7c : LinguisticExample :=
  { id := "embick2021_7c"
    source := ⟨"embick-2021", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's growth of tomatoes"
    discourseSegments := []
    glossedTokens := []
    translation := "John's growth of tomatoes"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "GROW"), ("rootClass", "nonagentive"), ("construction", "derivedNominal"), ("h1", "n"), ("h1exp", "-th")]
    comment := "Agentive reading of the possessor."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7d : LinguisticExample :=
  { id := "embick2021_7d"
    source := ⟨"embick-2021", "(7d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John's growing tomatoes"
    discourseSegments := []
    glossedTokens := []
    translation := "John's growing tomatoes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "GROW"), ("rootClass", "nonagentive"), ("construction", "gerund"), ("h1", "v"), ("h1exp", ""), ("h2", "voice"), ("h2exp", ""), ("h3", "n"), ("h3exp", "-ing")]
    comment := "Agentive reading of the possessor."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bent : LinguisticExample :=
  { id := "embick2021_bent"
    source := ⟨"embick-2021", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "bent"
    discourseSegments := []
    glossedTokens := []
    translation := "bent"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "BEND"), ("construction", "inflected"), ("h1", "v"), ("h1exp", ""), ("h2", "T"), ("h2exp", "-t")]
    comment := "Root-determined allomorphy of a noncyclic head outside the categorizer (structure 15)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def broken : LinguisticExample :=
  { id := "embick2021_broken"
    source := ⟨"embick-2021", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "broken"
    discourseSegments := []
    glossedTokens := []
    translation := "broken"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "BREAK"), ("construction", "inflected"), ("h1", "v"), ("h1exp", ""), ("h2", "aspect"), ("h2exp", "-en")]
    comment := "Root-determined allomorphy of a noncyclic head outside the categorizer (structure 15)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_6c, ex_6d, ex_7c, ex_7d, bent, broken]

end Embick2021.Examples
