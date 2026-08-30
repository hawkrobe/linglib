import Linglib.Data.Examples.Schema

/-!
# `Belth2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Belth2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Belth2026.Examples`.
-/

namespace Belth2026.Examples

open Data.Examples

def ex_53a : LinguisticExample :=
  { id := "belth2026_53a"
    source := ⟨"belth-2026", "(53a)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "nav-alis"
    discourseSegments := []
    glossedTokens := [("nav-alis", "naval")]
    translation := "naval"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "default l: tier-preceding consonant not lateral")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_53b1 : LinguisticExample :=
  { id := "belth2026_53b1"
    source := ⟨"belth-2026", "(53b)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "popul-aris"
    discourseSegments := []
    glossedTokens := [("popul-aris", "popular")]
    translation := "popular"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-aris"), ("analysis", "dissimilation from tier-adjacent stem l")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_53b2 : LinguisticExample :=
  { id := "belth2026_53b2"
    source := ⟨"belth-2026", "(53b)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "lun-aris"
    discourseSegments := []
    glossedTokens := [("lun-aris", "lunar")]
    translation := "lunar"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-aris"), ("analysis", "dissimilation across the coronal n")]
    comment := "Rule (54) predicts *lunalis here (the tier-preceding consonant is non-lateral n): a residual error the Tolerance Principle absorbs."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_53c : LinguisticExample :=
  { id := "belth2026_53c"
    source := ⟨"belth-2026", "(53c)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "flor-alis"
    discourseSegments := []
    glossedTokens := [("flor-alis", "floral")]
    translation := "floral"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "blocked by intervening r")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_53d1 : LinguisticExample :=
  { id := "belth2026_53d1"
    source := ⟨"belth-2026", "(53d)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "pluvi-alis"
    discourseSegments := []
    glossedTokens := [("pluvi-alis", "rainy")]
    translation := "rainy"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "blocked by an intervening non-coronal consonant")]
    comment := "The non-coronal blocker stays on the tier, hiding the stem l from the suffix liquid."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_53d2 : LinguisticExample :=
  { id := "belth2026_53d2"
    source := ⟨"belth-2026", "(53d)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "leg-alis"
    discourseSegments := []
    glossedTokens := [("leg-alis", "legal")]
    translation := "legal"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "blocked by intervening g")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_46 : LinguisticExample :=
  { id := "belth2026_46"
    source := ⟨"belth-2026", "(46)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "dal-lar-ın / yer-ler-in / ip-ler-in"
    discourseSegments := []
    glossedTokens := [("dal-lar-ın", "branch-PL-GEN"), ("yer-ler-in", "place-PL-GEN"), ("ip-ler-in", "rope-PL-GEN")]
    translation := "of the branches / of the places / of the ropes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "backness harmony"), ("tier", "vowels")]
    comment := "Affix vowels harmonize with the preceding vowel across intervening consonants."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_47 : LinguisticExample :=
  { id := "belth2026_47"
    source := ⟨"belth-2026", "(47)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "ip-in / jüz-ün / kız-ın / buz-un"
    discourseSegments := []
    glossedTokens := [("ip-in", "rope-GEN"), ("jüz-ün", "face-GEN"), ("kız-ın", "girl-GEN"), ("buz-un", "ice-GEN")]
    translation := "of the rope / of the face / of the girl / of the ice"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "secondary rounding harmony"), ("target", "high vowels only")]
    comment := "High affix vowels copy both backness and rounding from the preceding vowel of any height."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_51 : LinguisticExample :=
  { id := "belth2026_51"
    source := ⟨"belth-2026", "(51)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "pöytä-nä / pouta-na / koti-na / velje-nä"
    discourseSegments := []
    glossedTokens := [("pöytä-nä", "table-ESS"), ("pouta-na", "fine.weather-ESS"), ("koti-na", "home-ESS"), ("velje-nä", "road-ESS")]
    translation := "as a table / as fine weather / as a home / as a road"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "backness harmony"), ("neutral vowels", "i, e off the tier"), ("default", "front when only neutral vowels precede")]
    comment := "koti-na: harmony passes over the neutral i; velje-nä: the Elsewhere default fires."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_53a, ex_53b1, ex_53b2, ex_53c, ex_53d1, ex_53d2, ex_46, ex_47, ex_51]

end Belth2026.Examples
