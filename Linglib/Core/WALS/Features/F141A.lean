import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 141A: Writing Systems
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 141A`.

Chapter 141, 6 languages.
-/

namespace Core.WALS.F141A

/-- WALS 141A values. -/
inductive WritingSystems where
  | alphabetic  -- Alphabetic (0 languages)
  | consonantal  -- Consonantal (0 languages)
  | alphasyllabic  -- Alphasyllabic (4 languages)
  | syllabic  -- Syllabic (2 languages)
  | logographic  -- Logographic (0 languages)
  | mixedLogographicSyllabic  -- Mixed logographic–syllabic (0 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 141A dataset (6 languages). -/
def allData : List (Datapoint WritingSystems) :=
  [ { walsCode := "che", language := "Cherokee", iso := "chr", value := .syllabic }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .alphasyllabic }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .alphasyllabic }
  , { walsCode := "iql", language := "Inuktitut (Quebec-Labrador)", iso := "ike", value := .alphasyllabic }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .alphasyllabic }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .syllabic }
  ]

-- Count verification
theorem total_count : allData.length = 6 := by native_decide

theorem count_alphabetic :
    (allData.filter (·.value == .alphabetic)).length = 0 := by native_decide
theorem count_consonantal :
    (allData.filter (·.value == .consonantal)).length = 0 := by native_decide
theorem count_alphasyllabic :
    (allData.filter (·.value == .alphasyllabic)).length = 4 := by native_decide
theorem count_syllabic :
    (allData.filter (·.value == .syllabic)).length = 2 := by native_decide
theorem count_logographic :
    (allData.filter (·.value == .logographic)).length = 0 := by native_decide
theorem count_mixedLogographicSyllabic :
    (allData.filter (·.value == .mixedLogographicSyllabic)).length = 0 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F141A
