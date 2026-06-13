import Linglib.Data.Examples.Schema

/-!
# `CohenErteschikShir2002` — typed example data

Auto-generated from `Linglib/Data/Examples/CohenErteschikShir2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CohenErteschikShir2002.Examples`.
-/

namespace CohenErteschikShir2002.Examples

open Data.Examples

def boys_brave : LinguisticExample :=
  { id := "cohenerteschikshir2002_boys_brave"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Boys are brave."
    discourseSegments := []
    glossedTokens := []
    translation := "Boys are brave."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .unacceptable)]
    paperFeatures := [("predicate_level", "individual")]
    comment := "Migrated from Phenomena/Generics/BarePlurals.lean boysAreBrave. I-level predicate forces the generic reading of the bare plural subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def italians_good_looking : LinguisticExample :=
  { id := "cohenerteschikshir2002_italians_good_looking"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Italians are good-looking."
    discourseSegments := []
    glossedTokens := []
    translation := "Italians are good-looking."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .unacceptable)]
    paperFeatures := [("predicate_level", "individual")]
    comment := "Migrated from Phenomena/Generics/BarePlurals.lean italiansGoodLooking. I-level predicate; no existential reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def lawyers_intelligent : LinguisticExample :=
  { id := "cohenerteschikshir2002_lawyers_intelligent"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lawyers are intelligent."
    discourseSegments := []
    glossedTokens := []
    translation := "Lawyers are intelligent."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .unacceptable)]
    paperFeatures := [("predicate_level", "individual")]
    comment := "Migrated from Phenomena/Generics/BarePlurals.lean lawyersIntelligent. I-level predicate forces the generic reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def boys_present : LinguisticExample :=
  { id := "cohenerteschikshir2002_boys_present"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Boys are present."
    discourseSegments := []
    glossedTokens := []
    translation := "Boys are present."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("predicate_level", "stage"), ("locative_status", "argument")]
    comment := "Migrated from Phenomena/Generics/BarePlurals.lean boysArePresent. S-level predicate with a locative ARGUMENT licenses the existential reading ('there are boys here')."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def firemen_available : LinguisticExample :=
  { id := "cohenerteschikshir2002_firemen_available"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Firemen are available."
    discourseSegments := []
    glossedTokens := []
    translation := "Firemen are available."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("predicate_level", "stage"), ("locative_status", "argument")]
    comment := "Migrated from Phenomena/Generics/BarePlurals.lean firemenAvailable. S-level predicate with an implicit locative argument (for some task/location)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def soldiers_arrived : LinguisticExample :=
  { id := "cohenerteschikshir2002_soldiers_arrived"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Soldiers arrived."
    discourseSegments := []
    glossedTokens := []
    translation := "Soldiers arrived."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("predicate_level", "stage"), ("locative_status", "argument")]
    comment := "Migrated from Phenomena/Generics/BarePlurals.lean soldiersArrived. Motion verb with an implicit goal argument; existential reading available."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [boys_brave, italians_good_looking, lawyers_intelligent, boys_present, firemen_available, soldiers_arrived]

end CohenErteschikShir2002.Examples
