module

public import Linglib.Data.Examples.Schema

/-!
# `Belth2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Belth2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Belth2026.Examples`.
-/

@[expose] public section

namespace Belth2026.Examples

def ex_53a : Datum :=
  { id := "belth2026_53a"
    source := ⟨"belth-2026", "(53a)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "nav-alis"
    glossedTokens := [("nav-alis", "naval")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "default l: tier-preceding consonant not lateral")] }

def ex_53b1 : Datum :=
  { id := "belth2026_53b1"
    source := ⟨"belth-2026", "(53b)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "popul-aris"
    glossedTokens := [("popul-aris", "popular")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-aris"), ("analysis", "dissimilation from tier-adjacent stem l")] }

def ex_53b2 : Datum :=
  { id := "belth2026_53b2"
    source := ⟨"belth-2026", "(53b)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "lun-aris"
    glossedTokens := [("lun-aris", "lunar")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-aris"), ("analysis", "dissimilation across the coronal n")] }

def ex_53c : Datum :=
  { id := "belth2026_53c"
    source := ⟨"belth-2026", "(53c)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "flor-alis"
    glossedTokens := [("flor-alis", "floral")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "blocked by intervening r")] }

def ex_53d1 : Datum :=
  { id := "belth2026_53d1"
    source := ⟨"belth-2026", "(53d)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "pluvi-alis"
    glossedTokens := [("pluvi-alis", "rainy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "blocked by an intervening non-coronal consonant")] }

def ex_53d2 : Datum :=
  { id := "belth2026_53d2"
    source := ⟨"belth-2026", "(53d)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "leg-alis"
    glossedTokens := [("leg-alis", "legal")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "blocked by intervening g")] }

def ex_46 : Datum :=
  { id := "belth2026_46"
    source := ⟨"belth-2026", "(46)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "dal-lar-ın / yer-ler-in / ip-ler-in"
    glossedTokens := [("dal-lar-ın", "branch-PL-GEN"), ("yer-ler-in", "place-PL-GEN"), ("ip-ler-in", "rope-PL-GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "backness harmony"), ("tier", "vowels")] }

def ex_47 : Datum :=
  { id := "belth2026_47"
    source := ⟨"belth-2026", "(47)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "ip-in / jüz-ün / kız-ın / buz-un"
    glossedTokens := [("ip-in", "rope-GEN"), ("jüz-ün", "face-GEN"), ("kız-ın", "girl-GEN"), ("buz-un", "ice-GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "secondary rounding harmony"), ("target", "high vowels only")] }

def ex_51 : Datum :=
  { id := "belth2026_51"
    source := ⟨"belth-2026", "(51)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "pöytä-nä / pouta-na / koti-na / velje-nä"
    glossedTokens := [("pöytä-nä", "table-ESS"), ("pouta-na", "fine.weather-ESS"), ("koti-na", "home-ESS"), ("velje-nä", "road-ESS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "backness harmony"), ("neutral vowels", "i, e off the tier"), ("default", "front when only neutral vowels precede")] }

def all : List Datum := [ex_53a, ex_53b1, ex_53b2, ex_53c, ex_53d1, ex_53d2, ex_46, ex_47, ex_51]

end Belth2026.Examples
