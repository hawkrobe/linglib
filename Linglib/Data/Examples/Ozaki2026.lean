import Linglib.Data.Examples.Schema

/-!
# `Ozaki2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Ozaki2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ozaki2026.Examples`.
-/

namespace Ozaki2026.Examples

open Data.Examples

def ex1_acc : LinguisticExample :=
  { id := "ozaki2026_ex1_acc"
    source := ⟨"ozaki-2026", "(1)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga mura-o hanare-ta."
    discourseSegments := []
    glossedTokens := []
    translation := "Taro left the village."
    context := "The source of the departure verb marked accusative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "acc"), ("diagnostic", "alternation")]
    comment := "Taro-NOM village-ACC leave-PAST"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex1_abl : LinguisticExample :=
  { id := "ozaki2026_ex1_abl"
    source := ⟨"ozaki-2026", "(1)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga mura-kara hanare-ta."
    discourseSegments := []
    glossedTokens := []
    translation := "Taro left the village."
    context := "The source of the departure verb marked ablative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "abl"), ("diagnostic", "alternation")]
    comment := "Taro-NOM village-from leave-PAST"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex9_acc : LinguisticExample :=
  { id := "ozaki2026_ex9_acc"
    source := ⟨"ozaki-2026", "(9)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-wa suguni eki-o deta ga, Hanako-wa suguni denakatta."
    discourseSegments := []
    glossedTokens := []
    translation := "Taro exited the station quickly, but Hanako didn't exit the station quickly."
    context := "Ellipsis of the accusative source under the overt adjunct suguni 'quickly': the continuation (10), 'Hanako exited the ticket gate quickly, but she took time to exit the station', is not contradictory, so the elided-source reading is available and the source is an argument by the generalization of Funakoshi (2016)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "deru"), ("marking", "acc"), ("diagnostic", "ellipsis")]
    comment := "Taro-TOP quickly station-ACC exited but Hanako-TOP quickly didn't.exit"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex9_abl : LinguisticExample :=
  { id := "ozaki2026_ex9_abl"
    source := ⟨"ozaki-2026", "(9)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-wa suguni eki-kara deta ga, Hanako-wa suguni denakatta."
    discourseSegments := []
    glossedTokens := []
    translation := "Taro exited the station quickly, but Hanako didn't exit the station quickly."
    context := "Ellipsis of the ablative source under the overt adjunct suguni 'quickly'; the continuation (10) is not contradictory, so the source is an argument whatever its marking."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "deru"), ("marking", "abl"), ("diagnostic", "ellipsis")]
    comment := "Taro-TOP quickly station-from exited but Hanako-TOP quickly didn't.exit"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13_acc : LinguisticExample :=
  { id := "ozaki2026_ex13_acc"
    source := ⟨"ozaki-2026", "(13)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mura-o Taro-wa Hanako-ga hanareta to itta."
    discourseSegments := []
    glossedTokens := []
    translation := "Taro said Hanako left the village."
    context := "Long-distance scrambling of the accusative source out of the embedded clause, available to arguments but not adjuncts (Saito 1985)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "acc"), ("diagnostic", "scrambling")]
    comment := "village-ACC Taro-TOP Hanako-NOM left COMP said"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13_abl : LinguisticExample :=
  { id := "ozaki2026_ex13_abl"
    source := ⟨"ozaki-2026", "(13)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mura-kara Taro-wa Hanako-ga hanareta to itta."
    discourseSegments := []
    glossedTokens := []
    translation := "Taro said Hanako left the village."
    context := "Long-distance scrambling of the ablative source out of the embedded clause."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "abl"), ("diagnostic", "scrambling")]
    comment := "village-from Taro-TOP Hanako-NOM left COMP said"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex14 : LinguisticExample :=
  { id := "ozaki2026_ex14"
    source := ⟨"ozaki-2026", "(14)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sono mura-ga Taro-ni hanare-rare-ta."
    discourseSegments := []
    glossedTokens := []
    translation := "That village was left by Taro."
    context := "The passive with dative marking on the leaver: an indirect passive, the construction available to unaccusatives, not a direct passive."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "none"), ("diagnostic", "indirect_passive")]
    comment := "that village-NOM Taro-DAT leave-PASS-PAST"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex20 : LinguisticExample :=
  { id := "ozaki2026_ex20"
    source := ⟨"ozaki-2026", "(20)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sono mura-ga Taro-niyotte hanare-rare-ta."
    discourseSegments := []
    glossedTokens := []
    translation := "That village was left by Taro."
    context := "The direct passive, diagnosed by niyotte in place of the dative marker (Jo and Seo 2023), which only a verb with thematic Voice can undergo."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "none"), ("diagnostic", "direct_passive")]
    comment := "that village-NOM Taro-NIYOTTE leave-PASS-PAST"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26_acc : LinguisticExample :=
  { id := "ozaki2026_ex26_acc"
    source := ⟨"ozaki-2026", "(26)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Nani-o Taro-wa mura-o hanare-teir-u no?"
    discourseSegments := []
    glossedTokens := []
    translation := "Why is Taro leaving the village?"
    context := "The accusative wh-adjunct nani-o 'what-ACC' in its 'why' reading (Kurafuji 1997), available with unergatives and transitives but not with unaccusatives."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "acc"), ("diagnostic", "nani_o")]
    comment := "what-ACC Taro-TOP village-ACC leave-PROG-PRES Q"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex26_abl : LinguisticExample :=
  { id := "ozaki2026_ex26_abl"
    source := ⟨"ozaki-2026", "(26)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Nani-o Taro-wa mura-kara hanare-teir-u no?"
    discourseSegments := []
    glossedTokens := []
    translation := "Why is Taro leaving the village?"
    context := "The accusative wh-adjunct in its 'why' reading with the ablative source: unavailable as with unaccusatives."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hanareru"), ("marking", "abl"), ("diagnostic", "nani_o")]
    comment := "what-ACC Taro-TOP village-from leave-PROG-PRES Q"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1_acc, ex1_abl, ex9_acc, ex9_abl, ex13_acc, ex13_abl, ex14, ex20, ex26_acc, ex26_abl]

end Ozaki2026.Examples
