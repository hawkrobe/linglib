import Linglib.Data.Examples.Schema

/-!
# `DeoThomas2025` — typed example data

Auto-generated from `Linglib/Data/Examples/DeoThomas2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DeoThomas2025.Examples`.
-/

namespace DeoThomas2025.Examples

open Data.Examples

def complement_exclusion_vacation : LinguisticExample :=
  { id := "deothomas2025_complement_exclusion_vacation"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.1 — complement exclusion"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She just went to Spain and Portugal"
    discourseSegments := []
    glossedTokens := []
    translation := "She just went to Spain and Portugal"
    context := "Where did Mary go for her vacation this year?"
    judgment := .acceptable
    alternatives := [("She only went to Spain and Portugal", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "complementExclusion"), ("only_ok", "true"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean complementExclusion_vacation. Inference: Mary did not go to any country other than Spain and Portugal. The alternatives field carries the #only substitution test (here felicitous)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def rank_order_intern : LinguisticExample :=
  { id := "deothomas2025_rank_order_intern"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.1 — rank order"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is just an intern"
    discourseSegments := []
    glossedTokens := []
    translation := "She is just an intern"
    context := "What is Mary's job at the hospital?"
    judgment := .acceptable
    alternatives := [("She is only an intern", .acceptable)]
    readings := []
    paperFeatures := [("flavor", "rankOrder"), ("only_ok", "true"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean rankOrder_intern. Inference: Mary is nothing more senior than an intern."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def emphatic_amazing : LinguisticExample :=
  { id := "deothomas2025_emphatic_amazing"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.2 — emphatic"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The food was just amazing!"
    discourseSegments := []
    glossedTokens := []
    translation := "The food was just amazing!"
    context := "How good was the food?"
    judgment := .acceptable
    alternatives := [("#The food was only amazing!", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "emphatic"), ("only_ok", "false"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean emphatic_amazing. Inference: the degree of goodness exceeds contextual expectations."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def emphatic_enormous : LinguisticExample :=
  { id := "deothomas2025_emphatic_enormous"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.2 — emphatic"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Empire State Building is just gigantic!"
    discourseSegments := []
    glossedTokens := []
    translation := "The Empire State Building is just gigantic!"
    context := "How big is the Empire State Building?"
    judgment := .acceptable
    alternatives := [("#The Empire State Building is only gigantic!", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "emphatic"), ("only_ok", "false"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean emphatic_enormous. Inference: the size exceeds what the speaker expected to be relevant."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def precisifying_eq_full : LinguisticExample :=
  { id := "deothomas2025_precisifying_eq_full"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.3 — precisifying (equality)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tank is just full"
    discourseSegments := []
    glossedTokens := []
    translation := "The tank is just full"
    context := "How full is the tank?"
    judgment := .acceptable
    alternatives := [("#The tank is only full", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "precisifyingEquality"), ("only_ok", "false"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean precisifying_eq_full. Inference: the tank is full at the highest level of precision (= exactly full)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def precisifying_prox_older : LinguisticExample :=
  { id := "deothomas2025_precisifying_prox_older"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.3 — precisifying (proximity)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fafen is just older than Siri"
    discourseSegments := []
    glossedTokens := []
    translation := "Fafen is just older than Siri"
    context := "How much older than Siri is Fafen?"
    judgment := .acceptable
    alternatives := [("#Fafen is only older than Siri", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity"), ("only_ok", "false"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean precisifying_prox_older. Inference: Fafen is older by the smallest relevant amount (= barely/slightly)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def precisifying_temporal : LinguisticExample :=
  { id := "deothomas2025_precisifying_temporal"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.3 — precisifying (temporal proximity)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My sister just got here"
    discourseSegments := []
    glossedTokens := []
    translation := "My sister just got here"
    context := "When did your sister get here?"
    judgment := .acceptable
    alternatives := [("#My sister only got here", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "precisifyingProximity"), ("only_ok", "false"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean precisifying_temporal. Inference: the arrival was at the finest temporal granularity (= just now)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def minsuff_cat : LinguisticExample :=
  { id := "deothomas2025_minsuff_cat"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.4 — minimal sufficiency"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Just one cat will make Patrick happy"
    discourseSegments := []
    glossedTokens := []
    translation := "Just one cat will make Patrick happy"
    context := "What is sufficient for Patrick to be happy?"
    judgment := .acceptable
    alternatives := [("#Only one cat will make Patrick happy", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "minimalSufficiency"), ("only_ok", "false"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean minSuff_cat. Inference: one cat is causally sufficient; nothing less is needed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def minsuff_gpa : LinguisticExample :=
  { id := "deothomas2025_minsuff_gpa"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.4 — minimal sufficiency"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Just a 3.5 GPA is sufficient for Jason to stay in the program"
    discourseSegments := []
    glossedTokens := []
    translation := "Just a 3.5 GPA is sufficient for Jason to stay in the program"
    context := "What GPA is sufficient to stay in the program?"
    judgment := .acceptable
    alternatives := [("#Only a 3.5 GPA is sufficient for Jason to stay in the program", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "minimalSufficiency"), ("only_ok", "false"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean minSuff_gpa. Inference: 3.5 is the minimum sufficient GPA; nothing less works."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unexplanatory_lamp : LinguisticExample :=
  { id := "deothomas2025_unexplanatory_lamp"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.5 — unexplanatory"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was sitting there and the lamp just broke!"
    discourseSegments := []
    glossedTokens := []
    translation := "I was sitting there and the lamp just broke!"
    context := "Why is the lamp broken?"
    judgment := .acceptable
    alternatives := [("#I was sitting there and the lamp only broke!", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "unexplanatory"), ("only_ok", "false"), ("context_type", "qualityFail")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean unexplanatory_lamp. Inference: the speaker can identify no explanation for the lamp's breaking."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unexplanatory_mangoes : LinguisticExample :=
  { id := "deothomas2025_unexplanatory_mangoes"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.5 — unexplanatory"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I just had extra mangoes"
    discourseSegments := []
    glossedTokens := []
    translation := "I just had extra mangoes"
    context := "Why did you make mango-mousse cake?"
    judgment := .acceptable
    alternatives := [("#I only had extra mangoes", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "unexplanatory"), ("only_ok", "false"), ("context_type", "qualityFail")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean unexplanatory_mangoes. Inference: there is no stronger explanation than having extra mangoes."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unelaboratory_dog : LinguisticExample :=
  { id := "deothomas2025_unelaboratory_dog"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.6 — unelaboratory"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fido is just a dog"
    discourseSegments := []
    glossedTokens := []
    translation := "Fido is just a dog"
    context := "What kind of dog is Fido?"
    judgment := .acceptable
    alternatives := [("#Fido is only a dog", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "unelaboratory"), ("only_ok", "false"), ("context_type", "relevanceFail")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean unelaboratory_dog. Inference: no further elaboration is needed or relevant."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unelaboratory_proton : LinguisticExample :=
  { id := "deothomas2025_unelaboratory_proton"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.6 — unelaboratory"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A proton is just a hydrogen atom without an electron"
    discourseSegments := []
    glossedTokens := []
    translation := "A proton is just a hydrogen atom without an electron"
    context := "What is a proton?"
    judgment := .acceptable
    alternatives := [("#A proton is only a hydrogen atom without an electron", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "unelaboratory"), ("only_ok", "false"), ("context_type", "relevanceFail")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean unelaboratory_proton. Inference: no more elaboration is needed to define a proton."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unelaboratory_mad : LinguisticExample :=
  { id := "deothomas2025_unelaboratory_mad"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.6 — unelaboratory"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I am just mad"
    discourseSegments := []
    glossedTokens := []
    translation := "I am just mad"
    context := "Why are you mad?"
    judgment := .acceptable
    alternatives := [("#I am only mad", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "unelaboratory"), ("only_ok", "false"), ("context_type", "relevanceFail")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean unelaboratory_mad. Inference: the speaker is not mad at anyone in particular."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def counterexp_texting : LinguisticExample :=
  { id := "deothomas2025_counterexp_texting"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.7 — counterexpectational"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He started seeing an ex-girlfriend and just stopped texting me"
    discourseSegments := []
    glossedTokens := []
    translation := "He started seeing an ex-girlfriend and just stopped texting me"
    context := "What happened to your relationship?"
    judgment := .acceptable
    alternatives := [("#He started seeing an ex-girlfriend and only stopped texting me", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "counterexpectational"), ("only_ok", "false"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean counterexp_texting. Inference: the subject referent failed to adhere to norms."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def counterexp_wafer : LinguisticExample :=
  { id := "deothomas2025_counterexp_wafer"
    source := ⟨"deo-thomas-2025", "UNVERIFIED §2.7 — counterexpectational"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The priest gave Charlotte her communion wafer and she just ate it!"
    discourseSegments := []
    glossedTokens := []
    translation := "The priest gave Charlotte her communion wafer and she just ate it!"
    context := "What happened at the church?"
    judgment := .acceptable
    alternatives := [("#The priest gave Charlotte her communion wafer and she only ate it!", .unacceptable)]
    readings := []
    paperFeatures := [("flavor", "counterexpectational"), ("only_ok", "false"), ("context_type", "answerable")]
    comment := "Migrated from Phenomena/Focus/Exclusives.lean counterexp_wafer. Inference: Charlotte behaved in a way inconsistent with Catholic norms."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [complement_exclusion_vacation, rank_order_intern, emphatic_amazing, emphatic_enormous, precisifying_eq_full, precisifying_prox_older, precisifying_temporal, minsuff_cat, minsuff_gpa, unexplanatory_lamp, unexplanatory_mangoes, unelaboratory_dog, unelaboratory_proton, unelaboratory_mad, counterexp_texting, counterexp_wafer]

end DeoThomas2025.Examples
