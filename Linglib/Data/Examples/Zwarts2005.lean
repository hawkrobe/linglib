module

public import Linglib.Data.Examples.Schema

/-!
# `Zwarts2005` — typed example data

Auto-generated from `Linglib/Data/Examples/Zwarts2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zwarts2005.Examples`.
-/

@[expose] public section

namespace Zwarts2005.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "zwarts2005_1a"
    source := ⟨"zwarts-2005", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex swam for an hour"
    discourseSegments := []
    glossedTokens := []
    translation := "Alex swam for an hour"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "atelic")]
    comment := "The in-adverbial is out: a manner of motion verb alone is atelic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1b : LinguisticExample :=
  { id := "zwarts2005_1b"
    source := ⟨"zwarts-2005", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex swam to the beach in an hour"
    discourseSegments := []
    glossedTokens := []
    translation := "Alex swam to the beach in an hour"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "telic"), ("preposition", "to")]
    comment := "The for-adverbial is out: the goal phrase makes the sentence telic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1c : LinguisticExample :=
  { id := "zwarts2005_1c"
    source := ⟨"zwarts-2005", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex swam towards the beach for an hour"
    discourseSegments := []
    glossedTokens := []
    translation := "Alex swam towards the beach for an hour"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "atelic"), ("preposition", "towards")]
    comment := "The in-adverbial is out: the comparative phrase leaves the sentence atelic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12a : LinguisticExample :=
  { id := "zwarts2005_12a"
    source := ⟨"zwarts-2005", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex ran away from the accident"
    discourseSegments := []
    glossedTokens := []
    translation := "Alex ran away from the accident"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "away from")]
    comment := "Can be telic although the phrase specifies no endpoint."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23a : LinguisticExample :=
  { id := "zwarts2005_23a"
    source := ⟨"zwarts-2005", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex ran to the house in a minute"
    discourseSegments := []
    glossedTokens := []
    translation := "Alex ran to the house in a minute"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "telic"), ("preposition", "to")]
    comment := "Bounded but not quantized: a path to the house has proper subpaths to the house."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23b : LinguisticExample :=
  { id := "zwarts2005_23b"
    source := ⟨"zwarts-2005", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex walked over the bridge in two minutes"
    discourseSegments := []
    glossedTokens := []
    translation := "Alex walked over the bridge in two minutes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "telic"), ("preposition", "over")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23c : LinguisticExample :=
  { id := "zwarts2005_23c"
    source := ⟨"zwarts-2005", "(23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex crawled out of the room in three minutes"
    discourseSegments := []
    glossedTokens := []
    translation := "Alex crawled out of the room in three minutes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "telic"), ("preposition", "out of")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30a : LinguisticExample :=
  { id := "zwarts2005_30a"
    source := ⟨"zwarts-2005", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex walk to the capitol"
    discourseSegments := []
    glossedTokens := []
    translation := "Alex walk to the capitol"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "to")]
    comment := "The verb phrase whose weak goal denotation (30c) is cumulative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_1c, ex_12a, ex_23a, ex_23b, ex_23c, ex_30a]

end Zwarts2005.Examples
