import Linglib.Core.WALS.Datapoint

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
  /-- Double-headed dominant (1 languages). -/
  | dominant
  /-- Double-headed or RelN (1 languages). -/
  | orReln
  /-- Double-headed or internally-headed (1 languages). -/
  | orInternallyHeaded
  /-- Double-headed as nondominant type (2 languages). -/
  | asNondominantType
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 90G dataset (5 languages). -/
def allData : List (Datapoint DoubleHeadedRelativeClauses) :=
  [ { walsCode := "jms", iso := "djm", value := .orInternallyHeaded }
  , { walsCode := "kob", iso := "kpw", value := .orReln }
  , { walsCode := "kmb", iso := "", value := .dominant }
  , { walsCode := "hna", iso := "hna", value := .asNondominantType }
  , { walsCode := "ygr", iso := "ygr", value := .asNondominantType }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F90G
