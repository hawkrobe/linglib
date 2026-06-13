import Linglib.Data.Examples.Schema

/-!
# `Gasparri2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Gasparri2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gasparri2025.Examples`.
-/

namespace Gasparri2025.Examples

open Data.Examples

def ruth_dancer : LinguisticExample :=
  { id := "gasparri2025_ruth_dancer"
    source := ⟨"gasparri-2025", "UNVERIFIED ex. 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ruth is a dancer."
    discourseSegments := []
    glossedTokens := []
    translation := "Ruth is a dancer."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("token", .acceptable), ("generic", .questionable)]
    paperFeatures := [("subject_type", "bare_name"), ("licensor", "none")]
    comment := "Migrated from Phenomena/Generics/BareNames.lean ruth_dancer. Bare singular name without a licensor: the token reading is fine, the generic reading ('people called Ruth are dancers') is degraded — generic recalcitrance."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def the_tiger_striped : LinguisticExample :=
  { id := "gasparri2025_the_tiger_striped"
    source := ⟨"gasparri-2025", "UNVERIFIED ex. 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tiger is striped."
    discourseSegments := []
    glossedTokens := []
    translation := "The tiger is striped."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("token", .acceptable), ("generic", .acceptable)]
    paperFeatures := [("subject_type", "definite_common"), ("licensor", "none")]
    comment := "Migrated from Phenomena/Generics/BareNames.lean the_tiger_striped. Ordinary definite singular: generic reading available without any licensor — the baseline bare names fail to match."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruth_good_grades : LinguisticExample :=
  { id := "gasparri2025_ruth_good_grades"
    source := ⟨"gasparri-2025", "UNVERIFIED ex. 21"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the numbers, Ruth has good grades in biology."
    discourseSegments := []
    glossedTokens := []
    translation := "According to the numbers, Ruth has good grades in biology."
    context := "Naming-convention context: statistical generalization over people called Ruth."
    judgment := .acceptable
    alternatives := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject_type", "bare_name"), ("licensor", "generic_context")]
    comment := "Migrated from Phenomena/Generics/BareNames.lean ruth_good_grades. A naming-convention context licenses the generic reading of the bare singular name."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def tristan_extinct : LinguisticExample :=
  { id := "gasparri2025_tristan_extinct"
    source := ⟨"gasparri-2025", "UNVERIFIED ex. 34-35"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tristan is extinct."
    discourseSegments := []
    glossedTokens := []
    translation := "Tristan is extinct."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := [("token", .questionable), ("generic", .questionable)]
    paperFeatures := [("subject_type", "bare_name"), ("licensor", "kind_level_pred")]
    comment := "Migrated from Phenomena/Generics/BareNames.lean tristan_extinct. Bare singular names resist kind-level predicates even though those select for kinds."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def quoted_tristan_extinct : LinguisticExample :=
  { id := "gasparri2025_quoted_tristan_extinct"
    source := ⟨"gasparri-2025", "UNVERIFIED ex. 34-35"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'Tristan' is extinct."
    discourseSegments := []
    glossedTokens := []
    translation := "'Tristan' is extinct."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject_type", "quoted_name"), ("licensor", "kind_level_pred")]
    comment := "Migrated from Phenomena/Generics/BareNames.lean quoted_tristan_extinct. Quotation rescues kind-level predication for names: the quoted name denotes the name-kind."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def dodo_extinct : LinguisticExample :=
  { id := "gasparri2025_dodo_extinct"
    source := ⟨"gasparri-2025", "UNVERIFIED ex. 34-35"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The dodo is extinct."
    discourseSegments := []
    glossedTokens := []
    translation := "The dodo is extinct."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("token", .questionable), ("generic", .acceptable)]
    paperFeatures := [("subject_type", "definite_common"), ("licensor", "kind_level_pred")]
    comment := "Migrated from Phenomena/Generics/BareNames.lean dodo_extinct. Definite common NPs accept kind-level predicates — the parallel bare names break and quotation restores."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ruth_dancer, the_tiger_striped, ruth_good_grades, tristan_extinct, quoted_tristan_extinct, dodo_extinct]

end Gasparri2025.Examples
