module

public import Linglib.Data.Examples.Schema

/-!
# `Hanink2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Hanink2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hanink2021.Examples`.
-/

@[expose] public section

namespace Hanink2021.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "hanink2021_ex1"
    source := ⟨"hanink-2021", "(1)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "gí: pélew ʔ-íʔiw-i"
    glossedTokens := [("gí:", "3.NOM"), ("pélew", "jackrabbit"), ("ʔ-íʔiw-i", "3/3-eat-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("phenomenon", "pronoun"), ("idxForm", "gi"), ("case", "nominative")] }

def ex2 : LinguisticExample :=
  { id := "hanink2021_ex2"
    source := ⟨"hanink-2021", "(2)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hádi-gi pélew Mú:biʔ-i"
    glossedTokens := [("hádi-gi", "DIST-IDX.NOM"), ("pélew", "jackrabbit"), ("Mú:biʔ-i", "3.run-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("phenomenon", "demonstrative"), ("idxForm", "gi")] }

def ex3 : LinguisticExample :=
  { id := "hanink2021_ex3"
    source := ⟨"hanink-2021", "(3)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "t'é:liwhu šáwlamhu ʔló:t ʔ-í:gi-yi-š-gi ʔwáʔ ʔ-éʔ-i"
    glossedTokens := [("t'é:liwhu", "man"), ("šáwlamhu", "girl"), ("ʔló:t", "yesterday"), ("ʔ-í:gi-yi-š-gi", "3-see-IND-DS-IDX.NOM"), ("ʔwáʔ", "here"), ("ʔ-éʔ-i", "3-be-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("phenomenon", "internallyHeadedRelative"), ("idxForm", "gi"), ("case", "nominative")] }

def ex19 : LinguisticExample :=
  { id := "hanink2021_ex19"
    source := ⟨"hanink-2021", "(19)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mušé:gew ʔ-lémiʔ-giš-uwaʔ-ášaʔ-aʔ"
    glossedTokens := [("mušé:gew", "bear"), ("ʔ-lémiʔ-giš-uwaʔ-ášaʔ-aʔ", "3-gather.food-DUR-hence-PROSP-DEP")]
    context := "First line of the story, setting the scene."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "bareNoun"), ("reading", "indefinite")] }

def ex20 : LinguisticExample :=
  { id := "hanink2021_ex20"
    source := ⟨"hanink-2021", "(20)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "dí:be wa-dášiw-i"
    glossedTokens := [("dí:be", "sun"), ("wa-dášiw-i", "STAT-shine-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "bareNoun"), ("reading", "unique")] }

def ex21 : LinguisticExample :=
  { id := "hanink2021_ex21"
    source := ⟨"hanink-2021", "(21)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "lák'aʔ t'é:liwhu ʔwáʔ ʔ-éʔ-i t'é:liwhu ʔ-émlu-yé:biʔ-i"
    glossedTokens := [("lák'aʔ", "one"), ("t'é:liwhu", "man"), ("ʔwáʔ", "here"), ("ʔ-éʔ-i", "3-be-IND"), ("t'é:liwhu", "man"), ("ʔ-émlu-yé:biʔ-i", "3-eat-come-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "bareNoun"), ("reading", "anaphoric"), ("idxForm", "null")] }

def ex22 : LinguisticExample :=
  { id := "hanink2021_ex22"
    source := ⟨"hanink-2021", "(22)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔlót súkuʔ l-í:gi-yi Adele gí:-saʔ súkuʔ ʔ-í:gi-yi"
    glossedTokens := [("ʔlót", "yesterday"), ("súkuʔ", "dog"), ("l-í:gi-yi", "1/3-see-IND"), ("Adele", "Adele"), ("gí:-saʔ", "3.PRO-also"), ("súkuʔ", "dog"), ("ʔ-í:gi-yi", "3/3-see-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "bareNoun"), ("reading", "anaphoric"), ("idxForm", "null"), ("case", "accusative")] }

def ex23 : LinguisticExample :=
  { id := "hanink2021_ex23"
    source := ⟨"hanink-2021", "(23)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hádigi daláʔak behéziŋ k'-éʔ-i"
    glossedTokens := [("hádigi", "that"), ("daláʔak", "mountain"), ("behéziŋ", "small"), ("k'-éʔ-i", "3-be-IND")]
    context := "Pointing at the mountain."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "demonstrative")] }

def ex25a : LinguisticExample :=
  { id := "hanink2021_ex25a"
    source := ⟨"hanink-2021", "(25a)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hádi-gi pélew Mú:biʔ-i"
    glossedTokens := [("hádi-gi", "DIST-GI"), ("pélew", "jackrabbit"), ("Mú:biʔ-i", "3.come.running-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "demonstrative"), ("deixis", "distal")] }

def ex25b : LinguisticExample :=
  { id := "hanink2021_ex25b"
    source := ⟨"hanink-2021", "(25b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wídi-gi pélew Mú:biʔ-i"
    glossedTokens := [("wídi-gi", "PROX-GI"), ("pélew", "jackrabbit"), ("Mú:biʔ-i", "3.come.running-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "demonstrative"), ("deixis", "proximal")] }

def ex27 : LinguisticExample :=
  { id := "hanink2021_ex27"
    source := ⟨"hanink-2021", "(27)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "Eddy ʔwáʔ ʔ-éʔ-é:s-i ʔi-š-ŋa gé: l-í:gi k'-éʔ-i"
    glossedTokens := [("Eddy", "Eddy"), ("ʔwáʔ", "here"), ("ʔ-éʔ-é:s-i", "3-be-NEG-IND"), ("ʔi-š-ŋa", "IND-DS-but"), ("gé:", "3.ACC"), ("l-í:gi", "1/3-see"), ("k'-éʔ-i", "3-be-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "pronoun"), ("idxForm", "ge"), ("case", "accusative")] }

def ex41 : LinguisticExample :=
  { id := "hanink2021_ex41"
    source := ⟨"hanink-2021", "(41)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "dáwligaŋa m-í:gi-aʔy-i-š-ge lé:-saʔ l-í:gi-yi"
    glossedTokens := [("dáwligaŋa", "movie"), ("m-í:gi-aʔy-i-š-ge", "2/3-see-INT.PST-IND-DS-IDX.ACC"), ("lé:-saʔ", "1.PRO-also"), ("l-í:gi-yi", "1/3-see-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "internallyHeadedRelative"), ("idxForm", "ge"), ("case", "accusative")] }

def ex45 : LinguisticExample :=
  { id := "hanink2021_ex45"
    source := ⟨"hanink-2021", "(45)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mé:hu géwe ʔ-í:gi-yi-š-ge lé:-saʔ l-í:gi-yi"
    glossedTokens := [("mé:hu", "boy"), ("géwe", "coyote"), ("ʔ-í:gi-yi-š-ge", "3/3-see-IND-DS-IDX.ACC"), ("lé:-saʔ", "1.PRO-also"), ("l-í:gi-yi", "1-see-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "internallyHeadedRelative"), ("idxForm", "ge"), ("case", "accusative")] }

def ex46 : LinguisticExample :=
  { id := "hanink2021_ex46"
    source := ⟨"hanink-2021", "(46)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "di-tulíc'ik-lu di-gum-c'í:ge-yi"
    glossedTokens := [("di-tulíc'ik-lu", "1-finger-INST"), ("di-gum-c'í:ge-yi", "1-REFL-scratch-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "postposition")] }

def ex47 : LinguisticExample :=
  { id := "hanink2021_ex47"
    source := ⟨"hanink-2021", "(47)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "gó:beʔ l-émeʔ-áŋaw-i-∅-ge-lu di-p'ím-eweʔ-giš-i"
    glossedTokens := [("gó:beʔ", "coffee"), ("l-émeʔ-áŋaw-i-∅-ge-lu", "1-drink-well-IND-SS-IDX.ACC-INST"), ("di-p'ím-eweʔ-giš-i", "1-go.out-hence-DUR-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("phenomenon", "postposition"), ("idxForm", "ge")] }

def ex50 : LinguisticExample :=
  { id := "hanink2021_ex50"
    source := ⟨"hanink-2021", "(50)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "t'ánu démlu sú:biʔ-i-š-ge di-sú:dɨm-i-š-gi wayúʔuš-áŋaw-i"
    glossedTokens := [("t'ánu", "people"), ("démlu", "food"), ("sú:biʔ-i-š-ge", "3/3.bring-IND-DS-IDX.ACC"), ("di-sú:dɨm-i-š-gi", "1/3-look.at-IND-DS-IDX.NOM"), ("wayúʔuš-áŋaw-i", "3.smell-good-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "islandInsensitivity")] }

def ex51 : LinguisticExample :=
  { id := "hanink2021_ex51"
    source := ⟨"hanink-2021", "(51)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "daʔmóʔmoʔ gó:beʔ ʔ-ímeʔ-i-š-ge l-í:gi-yi-∅-ge lé:-saʔ l-émeʔ-ašaʔ-i"
    glossedTokens := [("daʔmóʔmoʔ", "woman"), ("gó:beʔ", "coffee"), ("ʔ-ímeʔ-i-š-ge", "drink-IND-DS-IDX.ACC"), ("l-í:gi-yi-∅-ge", "1/3-see-IND-SS-IDX.ACC"), ("lé:-saʔ", "1.PRO-also"), ("l-émeʔ-ašaʔ-i", "1/3-drink-PROSP-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "islandInsensitivity")] }

def ex53 : LinguisticExample :=
  { id := "hanink2021_ex53"
    source := ⟨"hanink-2021", "(53)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "k'ák'aʔ dá: gé:gel-i-š-ge yá:m-aʔ"
    glossedTokens := [("k'ák'aʔ", "heron"), ("dá:", "there"), ("gé:gel-i-š-ge", "3.sit-IND-DS-IDX.ACC"), ("yá:m-aʔ", "3/3.speak-DEP")]
    context := "A bear is looking for her cubs, and comes to a river."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "restrictiveness"), ("reading", "existential")] }

def ex54 : LinguisticExample :=
  { id := "hanink2021_ex54"
    source := ⟨"hanink-2021", "(54)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "súkuʔ baŋáya ʔ-éʔ-i-š-ge daʔmóʔmoʔ bóŋi-yi-š-gi p'á:š-ug-i"
    glossedTokens := [("súkuʔ", "dog"), ("baŋáya", "outside"), ("ʔ-éʔ-i-š-ge", "3-be-IND-DS-IDX.ACC"), ("daʔmóʔmoʔ", "woman"), ("bóŋi-yi-š-gi", "3/3.call-IND-DS-IDX.NOM"), ("p'á:š-ug-i", "3.enter-hither-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "restrictiveness")] }

def ex56 : LinguisticExample :=
  { id := "hanink2021_ex56"
    source := ⟨"hanink-2021", "(56)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "Adele gawá:yɨʔ gaʔlám-i-š-gi Múʔuš-úweʔ-i"
    glossedTokens := [("Adele", "Adele"), ("gawá:yɨʔ", "horse"), ("gaʔlám-i-š-gi", "3/3.like-IND-DS-IDX.NOM"), ("Múʔuš-úweʔ-i", "3.run-hence-IND")]
    context := "You ask what is going on. Someone responds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "internallyHeadedRelative")] }

def ex91 : LinguisticExample :=
  { id := "hanink2021_ex91"
    source := ⟨"hanink-2021", "(91)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "daʔmoʔmóʔmoʔ p'á:š-ug-i-š-ge di-sú:dɨm-i"
    glossedTokens := [("daʔmoʔmóʔmoʔ", "woman.R"), ("p'á:š-ug-i-š-ge", "3.enter-hither-IND-DS-IDX.ACC"), ("di-sú:dɨm-i", "1/3-look.at-IND")]
    context := ""
    judgment := .acceptable
    alternatives := [("daʔmoʔmóʔmoʔ p'á:š-ug-i-š-ge-w di-sú:dɨm-i", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.5"), ("phenomenon", "noFeatureTransmission")] }

def ex96 : LinguisticExample :=
  { id := "hanink2021_ex96"
    source := ⟨"hanink-2021", "(96)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔló:t Adele hádi-gi mé:hu ʔ-í:gi-yi-š-gi ʔwáʔ ʔ-éʔ-i"
    glossedTokens := [("ʔló:t", "yesterday"), ("Adele", "Adele"), ("hádi-gi", "DIST-IDX.NOM"), ("mé:hu", "boy"), ("ʔ-í:gi-yi-š-gi", "3/3-see-IND-DS-IDX.NOM"), ("ʔwáʔ", "here"), ("ʔ-éʔ-i", "3-be-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("phenomenon", "indefinitenessRestriction")] }

def ex98 : LinguisticExample :=
  { id := "hanink2021_ex98"
    source := ⟨"hanink-2021", "(98)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "dak'uláŋaʔ míʔle-w gawá:yɨʔ baŋáya gúm-úweʔ-i-š-ge di-sú:dɨm-i"
    glossedTokens := [("dak'uláŋaʔ", "cowboy"), ("míʔle-w", "all-AN.PL"), ("gawá:yɨʔ", "horse"), ("baŋáya", "outside"), ("gúm-úweʔ-i-š-ge", "3/3.take.out-hence-IND-DS-IDX.ACC"), ("di-sú:dɨm-i", "1/3-look.at-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("phenomenon", "quantifiedHead")] }

def ex102 : LinguisticExample :=
  { id := "hanink2021_ex102"
    source := ⟨"hanink-2021", "(102)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔiŋa baŋáya gawá:yɨʔ míʔle-w-ŋa gúm-úweʔ-é:s-i"
    glossedTokens := [("ʔiŋa", "but"), ("baŋáya", "outside"), ("gawá:yɨʔ", "horse"), ("míʔle-w-ŋa", "all-PL-NC"), ("gúm-úweʔ-é:s-i", "3/3.take.out-hence-NEG-IND")]
    context := "Uttered after (98)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("phenomenon", "quantifiedHead")] }

def ex103 : LinguisticExample :=
  { id := "hanink2021_ex103"
    source := ⟨"hanink-2021", "(103)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "míʔle-w dak'uláŋaʔ gawá:yɨʔ baŋáya gúm-úweʔ-i-š-ge di-sú:dɨm-i"
    glossedTokens := [("míʔle-w", "all-AN.PL"), ("dak'uláŋaʔ", "cowboy"), ("gawá:yɨʔ", "horse"), ("baŋáya", "outside"), ("gúm-úweʔ-i-š-ge", "3/3.take.out-hence-IND-DS-IDX.ACC"), ("di-sú:dɨm-i", "1/3-look.at-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("phenomenon", "quantifiedHead")] }

def ex104 : LinguisticExample :=
  { id := "hanink2021_ex104"
    source := ⟨"hanink-2021", "(104)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔum-wagayáyʔ-i-š-ge di-dámal-i"
    glossedTokens := [("ʔum-wagayáyʔ-i-š-ge", "2-talk-IND-DS-IDX.ACC"), ("di-dámal-i", "1/3-hear-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("phenomenon", "perceptionReading")] }

def ex105 : LinguisticExample :=
  { id := "hanink2021_ex105"
    source := ⟨"hanink-2021", "(105)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "w-álag-éweʔ-i-š-ge l-í:gi-yi"
    glossedTokens := [("w-álag-éweʔ-i-š-ge", "STAT-shine-hence-IND-DS-IDX.ACC"), ("l-í:gi-yi", "1/3-see-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("phenomenon", "perceptionReading")] }

def ex120a : LinguisticExample :=
  { id := "hanink2021_ex120a"
    source := ⟨"hanink-2021", "(120a)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "gé-ši l-í:gi-yi"
    glossedTokens := [("gé-ši", "IDX.ACC-DU"), ("l-í:gi-yi", "1-see-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "pronounConcord"), ("number", "dual")] }

def ex120b : LinguisticExample :=
  { id := "hanink2021_ex120b"
    source := ⟨"hanink-2021", "(120b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "gé-w l-í:gi-yi"
    glossedTokens := [("gé-w", "IDX.ACC-PL"), ("l-í:gi-yi", "1-see-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "pronounConcord"), ("number", "plural")] }

def ex121a : LinguisticExample :=
  { id := "hanink2021_ex121a"
    source := ⟨"hanink-2021", "(121a)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "míʔle-ši t'elí:liwhu"
    glossedTokens := [("míʔle-ši", "all-DU"), ("t'elí:liwhu", "man.R")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "modifierConcord"), ("number", "dual")] }

def ex121b : LinguisticExample :=
  { id := "hanink2021_ex121b"
    source := ⟨"hanink-2021", "(121b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hésgil-ši di-ʔisá:sa"
    glossedTokens := [("hésgil-ši", "two-DU"), ("di-ʔisá:sa", "1-older.sister.R")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "modifierConcord"), ("number", "dual")] }

def ex122a : LinguisticExample :=
  { id := "hanink2021_ex122a"
    source := ⟨"hanink-2021", "(122a)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "t'é:k'e-w dílek"
    glossedTokens := [("t'é:k'e-w", "many-PL"), ("dílek", "duck")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "modifierConcord"), ("number", "plural")] }

def ex122b : LinguisticExample :=
  { id := "hanink2021_ex122b"
    source := ⟨"hanink-2021", "(122b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "hélme-w di-wic'úc'uk"
    glossedTokens := [("hélme-w", "three-PL"), ("di-wic'úc'uk", "1.POSS-younger.sister")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3"), ("phenomenon", "modifierConcord"), ("number", "plural")] }

def all : List LinguisticExample := [ex1, ex2, ex3, ex19, ex20, ex21, ex22, ex23, ex25a, ex25b, ex27, ex41, ex45, ex46, ex47, ex50, ex51, ex53, ex54, ex56, ex91, ex96, ex98, ex102, ex103, ex104, ex105, ex120a, ex120b, ex121a, ex121b, ex122a, ex122b]

end Hanink2021.Examples
