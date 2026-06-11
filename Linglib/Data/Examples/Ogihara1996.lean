import Linglib.Data.Examples.Schema

/-!
# `Ogihara1996` — typed example data

Auto-generated from `Linglib/Data/Examples/Ogihara1996.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ogihara1996.Examples`.
-/

namespace Ogihara1996.Examples

open Data.Examples

def ex2a : LinguisticExample :=
  { id := "ogihara1996_ex2a"
    source := ⟨"ogihara-1996", "(2a)"⟩
    reportedIn := none
    language := "jpan1234"
    primaryText := "Taroo-wa Hanako-ga byooki-da to it-ta."
    discourseSegments := []
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byooki-da", "be.sick-PRES"), ("to", "COMP"), ("it-ta", "say-PAST")]
    translation := "Taro said that Hanako was sick [at that time]."
    context := "Past matrix + PRESENT embedded → simultaneous reading. In non-SOT Japanese, the embedded clause uses present (`-da`) to express simultaneity with the saying time; the embedded clause's tense is interpreted relative to speech time, so PRESENT here is anchored to the saying time via attitude-context shift, not to speech time."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (Hanako sick at saying time)", .acceptable), ("shifted (Hanako sick before saying)", .ungrammatical)]
    paperFeatures := []
    comment := "Ogihara 1996 ex (2a), Chapter 1 §1.2 p. 11. Half of the minimal pair (2a)/(2b) — the embedded PRESENT form. Together with (2b) below, motivates Ogihara's analysis: embedded tense in Japanese is absolute, so PRESENT delivers simultaneity (via attitude shift) and PAST delivers strict backward shift."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex2b : LinguisticExample :=
  { id := "ogihara1996_ex2b"
    source := ⟨"ogihara-1996", "(2b)"⟩
    reportedIn := none
    language := "jpan1234"
    primaryText := "Taroo-wa Hanako-ga byookidat-ta to it-ta."
    discourseSegments := []
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byookidat-ta", "be.sick-PAST"), ("to", "COMP"), ("it-ta", "say-PAST")]
    translation := "Taro said that Hanako had been sick."
    context := "Past matrix + PAST embedded → ONLY shifted reading. Hanako's sickness strictly precedes the saying. No simultaneous reading is available — sharply diagnostic of non-SOT Japanese vs SOT English."
    judgment := .acceptable
    alternatives := []
    readings := [("shifted (Hanako sick before saying)", .acceptable), ("simultaneous (Hanako sick at saying time)", .ungrammatical)]
    paperFeatures := []
    comment := "Ogihara 1996 ex (2b), Chapter 1 §1.2 p. 11. The other half of the minimal pair. With English-style SOT, the embedded past should admit a simultaneous reading; its unavailability here is Ogihara's main empirical hook."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex19d : LinguisticExample :=
  { id := "ogihara1996_ex19d"
    source := ⟨"ogihara-1996", "(19d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He said that Mary had been reading books yesterday."
    discourseSegments := []
    glossedTokens := []
    translation := "He said that Mary had been reading books yesterday."
    context := "English past perfect under past matrix. The adverbial `yesterday` denotes a definite past interval and restricts the embedded event's temporal location — solid evidence that the perfect can be used as a preterit."
    judgment := .acceptable
    alternatives := []
    readings := [("Mary's reading at yesterday (definite past)", .acceptable)]
    paperFeatures := []
    comment := "Ogihara 1996 ex (19d), Chapter 1 §1.4 p. 12. Part of the (18a-d)/(19a-d) discussion arguing the perfect can be a preterit. The adverbial-licensing argument: definite-past adverbials like `yesterday` co-occur with the perfect, showing the perfect doesn't always require an open interval up to reference time."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex2a, ex2b, ex19d]

end Ogihara1996.Examples
