import Linglib.Data.Examples.Schema

/-!
# `ChatzikyriakidisEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/ChatzikyriakidisEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ChatzikyriakidisEtAl2025.Examples`.
-/

namespace ChatzikyriakidisEtAl2025.Examples

open Data.Examples

def hobNob : LinguisticExample :=
  { id := "chatzikyriakidisetal2025_hobNob"
    source := ⟨"geach-1967", "the Hob-Nob sentence"⟩
    reportedIn := some ⟨"chatzikyriakidis-etal-2025", "§2.3.2"⟩
    language := "stan1293"
    primaryText := "Hob thinks a witch has blighted Bob's mare, and Nob wonders whether she (the same witch) killed Cob's sow."
    discourseSegments := []
    glossedTokens := []
    translation := "Hob thinks a witch has blighted Bob's mare, and Nob wonders whether she (the same witch) killed Cob's sow."
    context := "No witch need exist, and Hob and Nob need not be aware of each other's attitudes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Geach's intentional identity puzzle: anaphoric relatedness across the belief states of different agents without a requirement that the kind of individual the agents believe in actually exist (Chatzikyriakidis et al. 2025, §2.3.2). The parenthetical '(the same witch)' is part of the sentence as the Element quotes it and forces the same-witch reading that constitutes the puzzle. Edelberg 1986's detective variants, whose conjuncts resist reversal, are the key additional data in this literature; not yet recorded here."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [hobNob]

end ChatzikyriakidisEtAl2025.Examples
