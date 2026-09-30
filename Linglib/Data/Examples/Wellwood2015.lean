module

public import Linglib.Data.Examples.Schema

/-!
# `Wellwood2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Wellwood2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wellwood2015.Examples`.
-/

@[expose] public section

namespace Wellwood2015.Examples

open Data.Examples

def felicity_mass : LinguisticExample :=
  { id := "wellwood2015_felicity_mass"
    source := ⟨"wellwood-2015", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al bought more coffee than Bill did."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun")]
    comment := "Mass-noun nominal comparative; VOLUME or WEIGHT dimension available." }

def felicity_count : LinguisticExample :=
  { id := "wellwood2015_felicity_count"
    source := ⟨"wellwood-2015", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al has more idea than Bill does."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("category", "countNoun")]
    comment := "Singular count noun anomalous under much-comparison." }

def felicity_atelic : LinguisticExample :=
  { id := "wellwood2015_felicity_atelic"
    source := ⟨"wellwood-2015", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al ran more than Bill did."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "atelicVP")]
    comment := "Atelic VP verbal comparative; DURATION or DISTANCE dimension available." }

def felicity_telic : LinguisticExample :=
  { id := "wellwood2015_felicity_telic"
    source := ⟨"wellwood-2015", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al graduated high school more than Bill did."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("category", "telicVP")]
    comment := "Telic VP anomalous under much-comparison." }

def felicity_ga : LinguisticExample :=
  { id := "wellwood2015_felicity_ga"
    source := ⟨"wellwood-2015", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al's coffee is hotter than Bill's is."
    discourseSegments := []
    glossedTokens := []
    translation := "Al's coffee is hotter than Bill's."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj")]
    comment := "Gradable adjective comparative; TEMPERATURE dimension." }

def felicity_nonga : LinguisticExample :=
  { id := "wellwood2015_felicity_nonga"
    source := ⟨"wellwood-2015", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This piece of wood is more wooden than that one is."
    discourseSegments := []
    glossedTokens := []
    translation := "This piece of wood is more wooden than that one."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("category", "nonGradableAdj")]
    comment := "Non-gradable adjective anomalous under comparison." }

def dim_82a_hotter : LinguisticExample :=
  { id := "wellwood2015_dim_82a_hotter"
    source := ⟨"wellwood-2015", "ex. (82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "hotter"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("measuredDomain", "state"), ("dimension", "temperature"), ("intensive", "true")]
    comment := "GA measuring states: intensive dimension." }

def dim_82b_harder : LinguisticExample :=
  { id := "wellwood2015_dim_82b_harder"
    source := ⟨"wellwood-2015", "ex. (82b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "harder"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("measuredDomain", "state"), ("dimension", "hardness"), ("intensive", "true")]
    comment := "GA measuring states: intensive dimension." }

def dim_83a_more_coffee : LinguisticExample :=
  { id := "wellwood2015_dim_83a_more_coffee"
    source := ⟨"wellwood-2015", "ex. (83a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "more coffee"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun"), ("measuredDomain", "entity"), ("dimension", "volume"), ("intensive", "false")]
    comment := "Mass noun measuring entities: extensive dimension." }

def dim_83b_more_plastic : LinguisticExample :=
  { id := "wellwood2015_dim_83b_more_plastic"
    source := ⟨"wellwood-2015", "ex. (83b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "more plastic"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun"), ("measuredDomain", "entity"), ("dimension", "weight"), ("intensive", "false")]
    comment := "Mass noun measuring entities: extensive dimension." }

def dim_84a_fuller : LinguisticExample :=
  { id := "wellwood2015_dim_84a_fuller"
    source := ⟨"wellwood-2015", "ex. (84a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fuller"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("measuredDomain", "entity"), ("dimension", "volume"), ("intensive", "false")]
    comment := "Reversal: GA but extensive, because the measured domain is entities." }

def dim_84b_heavier : LinguisticExample :=
  { id := "wellwood2015_dim_84b_heavier"
    source := ⟨"wellwood-2015", "ex. (84b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "heavier"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("measuredDomain", "entity"), ("dimension", "weight"), ("intensive", "false")]
    comment := "Reversal: GA but extensive, because the measured domain is entities." }

def dim_85a_more_heat : LinguisticExample :=
  { id := "wellwood2015_dim_85a_more_heat"
    source := ⟨"wellwood-2015", "ex. (85a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "more heat"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun"), ("measuredDomain", "state"), ("dimension", "temperature"), ("intensive", "true")]
    comment := "Reversal: noun but intensive, because the measured domain is states." }

def dim_85b_more_firmness : LinguisticExample :=
  { id := "wellwood2015_dim_85b_more_firmness"
    source := ⟨"wellwood-2015", "ex. (85b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "more firmness"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "massNoun"), ("measuredDomain", "state"), ("dimension", "hardness"), ("intensive", "true")]
    comment := "Reversal: noun but intensive, because the measured domain is states." }

def dim_89a_sped_up : LinguisticExample :=
  { id := "wellwood2015_dim_89a_sped_up"
    source := ⟨"wellwood-2015", "ex. (89a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "sped up more"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "atelicVP"), ("measuredDomain", "state"), ("dimension", "speed"), ("intensive", "true")]
    comment := "Reversal: verb but intensive, because the measured domain is states." }

def dim_87a_drove : LinguisticExample :=
  { id := "wellwood2015_dim_87a_drove"
    source := ⟨"wellwood-2015", "ex. (87a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "drove more"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("category", "atelicVP"), ("measuredDomain", "event"), ("dimension", "distance"), ("intensive", "false")]
    comment := "Atelic VP measuring events: extensive dimension." }

def very_ga : LinguisticExample :=
  { id := "wellwood2015_very_ga"
    source := ⟨"wellwood-2015", "(118)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al wasn't very intelligent."
    discourseSegments := []
    glossedTokens := []
    translation := "very hot"
    context := ""
    judgment := .acceptable
    alternatives := [("Al wasn't very much intelligent.", .ungrammatical)]
    readings := []
    paperFeatures := [("category", "gradableAdj"), ("requiresOvertMuch", "false")]
    comment := "GAs host covert much, so very combines directly." }

def very_noun : LinguisticExample :=
  { id := "wellwood2015_very_noun"
    source := ⟨"wellwood-2015", "(117a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al didn't eat very much soup."
    discourseSegments := []
    glossedTokens := []
    translation := "very much coffee"
    context := ""
    judgment := .acceptable
    alternatives := [("Al didn't eat very soup.", .ungrammatical)]
    readings := []
    paperFeatures := [("category", "massNoun"), ("requiresOvertMuch", "true")]
    comment := "Nouns need overt much for very." }

def very_verb : LinguisticExample :=
  { id := "wellwood2015_very_verb"
    source := ⟨"wellwood-2015", "(117b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al didn't run very much."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Al didn't run very.", .ungrammatical)]
    readings := []
    paperFeatures := [("category", "atelicVP"), ("requiresOvertMuch", "true")]
    comment := "Verbs need overt much for very; much follows the verb." }

def shift_104_rock : LinguisticExample :=
  { id := "wellwood2015_shift_104_rock"
    source := ⟨"wellwood-2015", "(104a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al found more rock than Bill did."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Al found more rocks than Bill did.", .acceptable)]
    readings := []
    paperFeatures := [("shift", "numberMorphology")]
    comment := "Mass 'more rock': WEIGHT/VOLUME, *NUMBER. Plural 'more rocks': *WEIGHT/*VOLUME, NUMBER. The plural shifts mass to count, restricting measurement to NUMBER." }

def shift_105_run : LinguisticExample :=
  { id := "wellwood2015_shift_105_run"
    source := ⟨"wellwood-2015", "(105a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Al ran in the park more than Bill did."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Al ran to the park more than Bill did.", .acceptable)]
    readings := []
    paperFeatures := [("shift", "telicization")]
    comment := "Atelic 'ran in the park more': DISTANCE/DURATION/NUMBER. Telic 'ran to the park more': *DISTANCE/*DURATION, NUMBER. The directional PP telicizes, restricting measurement to NUMBER." }

def all : List LinguisticExample := [felicity_mass, felicity_count, felicity_atelic, felicity_telic, felicity_ga, felicity_nonga, dim_82a_hotter, dim_82b_harder, dim_83a_more_coffee, dim_83b_more_plastic, dim_84a_fuller, dim_84b_heavier, dim_85a_more_heat, dim_85b_more_firmness, dim_89a_sped_up, dim_87a_drove, very_ga, very_noun, very_verb, shift_104_rock, shift_105_run]

end Wellwood2015.Examples
