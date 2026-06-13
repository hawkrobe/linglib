import Linglib.Data.Examples.Schema

/-!
# `Gunlogson2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Gunlogson2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gunlogson2001.Examples`.
-/

namespace Gunlogson2001.Examples

open Data.Examples

def falling_decl : LinguisticExample :=
  { id := "gunlogson2001_falling_decl"
    source := ⟨"gunlogson-2001", "falling declarative"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's raining."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intonation", "falling"), ("speaker_commits", "true"), ("attributed_to_addressee", "false")]
    comment := "Gunlogson's signature minimal pair: a falling declarative commits the speaker to its content."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def rising_decl : LinguisticExample :=
  { id := "gunlogson2001_rising_decl"
    source := ⟨"gunlogson-2001", "rising declarative"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's raining?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intonation", "rising"), ("speaker_commits", "false"), ("attributed_to_addressee", "true")]
    comment := "Same words, rising intonation: the speaker does not commit; the content is attributed to the addressee, inviting confirmation or denial."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [falling_decl, rising_decl]

end Gunlogson2001.Examples
