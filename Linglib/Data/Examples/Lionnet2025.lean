module

public import Linglib.Data.Examples.Schema

/-!
# `Lionnet2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Lionnet2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Lionnet2025.Examples`.
-/

@[expose] public section

namespace Lionnet2025.Examples

open Data.Examples

def ex11 : LinguisticExample :=
  { id := "lionnet2025_ex11"
    source := ⟨"shintani-paita-1990b", "p. 19"⟩
    reportedIn := some ⟨"lionnet-2025", "(11)"⟩
    language := "dumb1241"
    primaryText := "ꜜɳi ꜜmwa ꜜɳii ꜜme"
    glossedTokens := [("ꜜɳi", "3PL.SBJ"), ("ꜜmwa", "PFV"), ("ꜜɳii", "say"), ("ꜜme", "that")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("underlying", "ꜜɳi ꜜmwa ꜜɳii ꜜme"), ("surface", "(ꜜ)ɳi ꜜmwa ꜜɳii ꜜme"), ("levels", "4 3 2 1")] }

def ex13a : LinguisticExample :=
  { id := "lionnet2025_ex13a"
    source := ⟨"rivierre-1973", "p. 132"⟩
    reportedIn := some ⟨"lionnet-2025", "(13a)"⟩
    language := "dumb1241"
    primaryText := "ko te ꜜbeɽu-ɽe"
    glossedTokens := [("ko", "1SG.SBJ"), ("te", "DESCR"), ("ꜜbeɽu-ɽe", "swim-ACT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("underlying", "ko te ꜜbeɽu-ɽe"), ("surface", "ko te ꜜbeɽu-ɽe"), ("levels", "4 4 3 2.5 2.5")] }

def ex13b : LinguisticExample :=
  { id := "lionnet2025_ex13b"
    source := ⟨"rivierre-1973", "p. 132"⟩
    reportedIn := some ⟨"lionnet-2025", "(13b)"⟩
    language := "dumb1241"
    primaryText := "ko te ꜜbeɽu-ɽe"
    glossedTokens := [("ko", "1SG.SBJ"), ("te", "DESCR"), ("ꜜbeɽu-ɽe", "swim-ACT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("underlying", "ko te ꜜbeɽu-ɽe"), ("surface", "ko ꜛte ꜜbeɽu-ɽe"), ("levels", "4 5 2.5 2 2")] }

def ex19 : LinguisticExample :=
  { id := "lionnet2025_ex19"
    source := ⟨"rivierre-1973", "p. 126"⟩
    reportedIn := some ⟨"lionnet-2025", "(19)"⟩
    language := "dumb1241"
    primaryText := "ꜜtaa dɪɪ bee"
    glossedTokens := [("ꜜtaa", "one"), ("dɪɪ", "small"), ("bee", "fish")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("underlying", "ꜜtaa dɪɪ bee"), ("surface", "(ꜜ)taa dɪɪ bee"), ("levels", "4 4 4")] }

def ex20 : LinguisticExample :=
  { id := "lionnet2025_ex20"
    source := ⟨"rivierre-1973", "p. 128"⟩
    reportedIn := some ⟨"lionnet-2025", "(20)"⟩
    language := "dumb1241"
    primaryText := "ꜜtaa bee pwi + ꜛ%"
    glossedTokens := [("ꜜtaa", "one"), ("bee", "fish"), ("pwi", "cooked")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("underlying", "ꜜtaa bee pwi + ꜛ%"), ("surface", "(ꜜ)taa bee ꜛ%pwi"), ("levels", "4 4 5")] }

def ex30 : LinguisticExample :=
  { id := "lionnet2025_ex30"
    source := ⟨"rivierre-1973", "p. 127"⟩
    reportedIn := some ⟨"lionnet-2025", "(30)"⟩
    language := "dumb1241"
    primaryText := "ko te tɪɪ-ɽe kuɽe"
    glossedTokens := [("ko", "1SG.SBJ"), ("te", "DESCR"), ("tɪɪ-ɽe", "look.at-ACT"), ("kuɽe", "bush")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.5"), ("underlying", "ko te tɪɪ-ɽe kuɽe"), ("surface", "ko te tɪɪ-ɽe kuɽe"), ("levels", "4 4 4 4 4")] }

def ex32 : LinguisticExample :=
  { id := "lionnet2025_ex32"
    source := ⟨"rivierre-1973", "p. 125"⟩
    reportedIn := some ⟨"lionnet-2025", "(32)"⟩
    language := "dumb1241"
    primaryText := "goo ꜜmie"
    glossedTokens := [("goo", "plant.sp"), ("ꜜmie", "wet")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.5"), ("underlying", "goo ꜜmie"), ("surface", "ꜛgoo ꜜmie"), ("levels", "5 3")] }

def ex33 : LinguisticExample :=
  { id := "lionnet2025_ex33"
    source := ⟨"rivierre-1973", "p. 125"⟩
    reportedIn := some ⟨"lionnet-2025", "(33)"⟩
    language := "dumb1241"
    primaryText := "ꜜgoo ꜜmie"
    glossedTokens := [("ꜜgoo", "tree"), ("ꜜmie", "wet")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.5"), ("underlying", "ꜜgoo ꜜmie"), ("surface", "(ꜜ)goo ꜜmie"), ("levels", "4 3")] }

def ex53a : LinguisticExample :=
  { id := "lionnet2025_ex53a"
    source := ⟨"rivierre-1973", "p. 144"⟩
    reportedIn := some ⟨"lionnet-2025", "(53a)"⟩
    language := "dumb1241"
    primaryText := "koꜜo kwɛ-ɽe"
    glossedTokens := [("koꜜo", "place"), ("kwɛ-ɽe", "dance-ACT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.7"), ("underlying", "koꜜo kwɛ-ɽe"), ("surface", "ꜛkoo ꜜkwɛ-ɽe"), ("levels", "5 4")] }

def ex53b : LinguisticExample :=
  { id := "lionnet2025_ex53b"
    source := ⟨"rivierre-1973", "p. 144"⟩
    reportedIn := some ⟨"lionnet-2025", "(53b)"⟩
    language := "dumb1241"
    primaryText := "koꜜo ꜜkwe-ɽe"
    glossedTokens := [("koꜜo", "place"), ("ꜜkwe-ɽe", "eat-ACT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.7"), ("underlying", "koꜜo ꜜkwe-ɽe"), ("surface", "ꜛkoo ꜜꜜkwe-ɽe"), ("levels", "5 3")] }

def ex56a : LinguisticExample :=
  { id := "lionnet2025_ex56a"
    source := ⟨"rivierre-1973", "pp. 140–141"⟩
    reportedIn := some ⟨"lionnet-2025", "(56a)"⟩
    language := "dumb1241"
    primaryText := "ʈa-uɽu"
    glossedTokens := [("ʈa-uɽu", "with.hand-cut")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.9"), ("underlying", "ʈa-uɽu"), ("surface", "ʈa-uɽu")] }

def ex56b : LinguisticExample :=
  { id := "lionnet2025_ex56b"
    source := ⟨"rivierre-1973", "pp. 140–141"⟩
    reportedIn := some ⟨"lionnet-2025", "(56b)"⟩
    language := "dumb1241"
    primaryText := "ʈa-ꜜtie"
    glossedTokens := [("ʈa-ꜜtie", "with.hand-tear")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.9"), ("underlying", "ʈa-ꜜtie"), ("surface", "ꜜʈa-ꜜtie")] }

def ex57 : LinguisticExample :=
  { id := "lionnet2025_ex57"
    source := ⟨"rivierre-1973", "p. 141"⟩
    reportedIn := some ⟨"lionnet-2025", "(57)"⟩
    language := "dumb1241"
    primaryText := "ko te ʈa-ꜜtie-ɽe"
    glossedTokens := [("ko", "1SG.SBJ"), ("te", "DESCR"), ("ʈa-", "with.hand-"), ("ꜜtie", "tear"), ("-ɽe", "-ACT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.9"), ("underlying", "ko te ʈa-ꜜtie-ɽe"), ("surface", "ko ꜛte ꜜʈa-ꜜtie-ɽe"), ("levels", "4 4.5 4 3 3 3")] }

def ex18 : LinguisticExample :=
  { id := "lionnet2025_ex18"
    source := ⟨"rivierre-1973", "p. 147"⟩
    reportedIn := some ⟨"lionnet-2025", "(18)"⟩
    language := "nucl1484"
    primaryText := "ꜜɳe ꜜmwa ꜜve"
    glossedTokens := [("ꜜɳe", "3PL.SBJ"), ("ꜜmwa", "PFV"), ("ꜜve", "go")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("underlying", "ꜜɳe ꜜmwa ꜜve"), ("surface", "(ꜜ)ɳe ꜜmwaꜛa ꜜve")] }

def ex22 : LinguisticExample :=
  { id := "lionnet2025_ex22"
    source := ⟨"rivierre-1973", "p. 132"⟩
    reportedIn := some ⟨"lionnet-2025", "(22)"⟩
    language := "nucl1484"
    primaryText := "dɛɳu a ɳa + ꜜ%"
    glossedTokens := [("dɛɳu", "jaw"), ("a", "REL"), ("ɳa", "up")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("underlying", "dɛɳu a ɳa + ꜜ%"), ("surface", "dɛɳu ꜛa ꜜ%ɳa"), ("levels", "4 4 4.5 3")] }

def ex24 : LinguisticExample :=
  { id := "lionnet2025_ex24"
    source := ⟨"rivierre-1973", "p. 127"⟩
    reportedIn := some ⟨"lionnet-2025", "(24)"⟩
    language := "nucl1484"
    primaryText := "jaa ɲĩ + ꜜ%"
    glossedTokens := [("jaa", "juice"), ("ɲĩ", "coconut")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("underlying", "jaa ɲĩ + ꜜ%"), ("surface", "ꜛɟaa ꜜ%ɲĩ"), ("levels", "5 4")] }

def ex25 : LinguisticExample :=
  { id := "lionnet2025_ex25"
    source := ⟨"rivierre-1973", "p. 127"⟩
    reportedIn := some ⟨"lionnet-2025", "(25)"⟩
    language := "nucl1484"
    primaryText := "jaa ꜜɲĩ + ꜜ%"
    glossedTokens := [("jaa", "juice"), ("ꜜɲĩ", "breast")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("underlying", "jaa ꜜɲĩ + ꜜ%"), ("surface", "ꜛɟaa ꜜꜜ%ɲĩ"), ("levels", "5 3.5")] }

def ex26 : LinguisticExample :=
  { id := "lionnet2025_ex26"
    source := ⟨"rivierre-1973", "p. 132"⟩
    reportedIn := some ⟨"lionnet-2025", "(26)"⟩
    language := "nucl1484"
    primaryText := "dɛɳʊ a mii + ꜜ%"
    glossedTokens := [("dɛɳʊ", "jaw"), ("a", "REL"), ("mii", "low")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("underlying", "dɛɳʊ a mii + ꜜ%"), ("surface", "dɛɳʊ a mii"), ("levels", "4 4 4 4")] }

def ex28 : LinguisticExample :=
  { id := "lionnet2025_ex28"
    source := ⟨"rivierre-1973", "p. 135"⟩
    reportedIn := some ⟨"lionnet-2025", "(28)"⟩
    language := "nucl1484"
    primaryText := "ꜜtẽẽ-ꜜẽ nõ bɛꜜtĩĩ ku + ꜜ%"
    glossedTokens := [("ꜜtẽẽ-ꜜẽ", "girl-PROX"), ("nõ", "grill"), ("bɛꜜtĩĩ", "three"), ("ku", "yam")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("underlying", "ꜜtẽẽ-ꜜẽ nõ bɛꜜtĩĩ ku + ꜜ%"), ("surface", "(ꜜ)tẽẽ-ꜜẽ nõ ꜛbɛꜜtĩĩ ku"), ("levels", "5 4 4 5 3 3")] }

def ex38 : LinguisticExample :=
  { id := "lionnet2025_ex38"
    source := ⟨"rivierre-1973", "p. 146"⟩
    reportedIn := some ⟨"lionnet-2025", "(38)"⟩
    language := "nucl1484"
    primaryText := "ꜜcĩĩbu ꜜmwã ꜜku mwoɽo + ꜜ%"
    glossedTokens := [("ꜜcĩĩbu", "rat"), ("ꜜmwã", "PFV"), ("ꜜku", "flee"), ("mwoɽo", "alive")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.6"), ("underlying", "ꜜcĩĩbu ꜜmwã ꜜku mwoɽo + ꜜ%"), ("surface", "(ꜜ)cĩĩꜛbu ꜜmwã ꜜku ꜛmwoꜜ%ɽo"), ("levels", "4 5 4 3 4 3")] }

def ex52 : LinguisticExample :=
  { id := "lionnet2025_ex52"
    source := ⟨"rivierre-1973", "p. 143"⟩
    reportedIn := some ⟨"lionnet-2025", "(52)"⟩
    language := "nucl1484"
    primaryText := "yaꜜa ꜜmẽ geꜜe ꜜmẽ ɲaꜜi"
    glossedTokens := [("yaꜜa", "NEG"), ("ꜜmẽ", "that"), ("geꜜe", "1PL.EXCL.SBJ"), ("ꜜmẽ", "FUT"), ("ɲaꜜi", "arrive")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.7"), ("underlying", "yaꜜa ꜜmẽ geꜜe ꜜmẽ ɲaꜜi"), ("surface", "ꜛyaa ꜜꜜmẽ ꜛgee ꜜꜜmẽ ꜛɲaꜜi"), ("levels", "5 3 5 3 4 3")] }

def ex62 : LinguisticExample :=
  { id := "lionnet2025_ex62"
    source := ⟨"rivierre-1973", "p. 134"⟩
    reportedIn := some ⟨"lionnet-2025", "(62)"⟩
    language := "nucl1484"
    primaryText := "gu ꜜcapɛ ꜜpaɳaa ꜜko ɲʊ ꜜwii to"
    glossedTokens := [("gu", "2SG.SBJ"), ("ꜜcapɛ", "raise"), ("ꜜpaɳaa", "mast"), ("ꜜko", "on"), ("ɲʊ", "boat"), ("ꜜwii", "down"), ("to", "there")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("underlying", "gu ꜜcapɛ ꜜpaɳaa ꜜko ɲʊ ꜜwii to"), ("surface", "ꜛgu ꜜcaꜛpɛ ꜜpaꜛɳaa ꜜko ꜛɲʊ ꜜwii to"), ("levels", "5 4 4.5 3 3.5 2 2.5 1.5 1.5")] }

def all : List LinguisticExample := [ex11, ex13a, ex13b, ex19, ex20, ex30, ex32, ex33, ex53a, ex53b, ex56a, ex56b, ex57, ex18, ex22, ex24, ex25, ex26, ex28, ex38, ex52, ex62]

end Lionnet2025.Examples
