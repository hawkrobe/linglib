import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 90F: Adjoined relative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90F`.

Chapter 90, 10 languages.
-/

namespace Core.WALS.F90F

/-- WALS 90F values. -/
inductive AdjoinedRelativeClauses where
  /-- Adjoined relative clause dominant (8 languages). -/
  | relativeClauseDominant
  /-- Adjoined or correlative (2 languages). -/
  | orCorrelative
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 90F dataset (10 languages). -/
def allData : List (Datapoint AdjoinedRelativeClauses) :=
  [ { walsCode := "diy", iso := "dif", value := .relativeClauseDominant }
  , { walsCode := "kkq", iso := "kui", value := .relativeClauseDominant }
  , { walsCode := "kya", iso := "gvn", value := .relativeClauseDominant }
  , { walsCode := "mrt", iso := "vma", value := .relativeClauseDominant }
  , { walsCode := "mek", iso := "skf", value := .relativeClauseDominant }
  , { walsCode := "ngk", iso := "nam", value := .relativeClauseDominant }
  , { walsCode := "ngi", iso := "wyb", value := .orCorrelative }
  , { walsCode := "wrl", iso := "wbp", value := .relativeClauseDominant }
  , { walsCode := "xas", iso := "kao", value := .orCorrelative }
  , { walsCode := "yid", iso := "yii", value := .relativeClauseDominant }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F90F
