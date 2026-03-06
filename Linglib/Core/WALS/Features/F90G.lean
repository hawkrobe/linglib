/-!
# WALS Feature 90G: Double-headed relative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90G`.

Chapter 90, 5 languages.
-/

namespace Core.WALS.F90G

/-- WALS 90G values. -/
inductive DoubleHeadedRelativeClauses where
  | doubleHeadedDominant  -- Double-headed dominant (1 languages)
  | doubleHeadedOrReln  -- Double-headed or RelN (1 languages)
  | doubleHeadedOrInternallyHeaded  -- Double-headed or internally-headed (1 languages)
  | doubleHeadedAsNondominantType  -- Double-headed as nondominant type (2 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 90G datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : DoubleHeadedRelativeClauses
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 90G dataset (5 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "jms", language := "Jamsay", iso := "djm", value := .doubleHeadedOrInternallyHeaded }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .doubleHeadedOrReln }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .doubleHeadedDominant }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .doubleHeadedAsNondominantType }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .doubleHeadedAsNondominantType }
  ]

-- Count verification
theorem total_count : allData.length = 5 := by native_decide

theorem count_doubleHeadedDominant :
    (allData.filter (·.value == .doubleHeadedDominant)).length = 1 := by native_decide
theorem count_doubleHeadedOrReln :
    (allData.filter (·.value == .doubleHeadedOrReln)).length = 1 := by native_decide
theorem count_doubleHeadedOrInternallyHeaded :
    (allData.filter (·.value == .doubleHeadedOrInternallyHeaded)).length = 1 := by native_decide
theorem count_doubleHeadedAsNondominantType :
    (allData.filter (·.value == .doubleHeadedAsNondominantType)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F90G
