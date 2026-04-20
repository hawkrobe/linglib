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
  /-- Alphabetic (0 languages). -/
  | alphabetic
  /-- Consonantal (0 languages). -/
  | consonantal
  /-- Alphasyllabic (4 languages). -/
  | alphasyllabic
  /-- Syllabic (2 languages). -/
  | syllabic
  /-- Logographic (0 languages). -/
  | logographic
  /-- Mixed logographic–syllabic (0 languages). -/
  | mixedLogographicSyllabic
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 141A dataset (6 languages). -/
def allData : List (Datapoint WritingSystems) :=
  [ { walsCode := "che", iso := "chr", value := .syllabic }
  , { walsCode := "chp", iso := "chp", value := .alphasyllabic }
  , { walsCode := "cre", iso := "crk", value := .alphasyllabic }
  , { walsCode := "iql", iso := "ike", value := .alphasyllabic }
  , { walsCode := "oji", iso := "", value := .alphasyllabic }
  , { walsCode := "vai", iso := "vai", value := .syllabic }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F141A
