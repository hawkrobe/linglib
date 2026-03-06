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
  | adjoinedRelativeClauseDominant  -- Adjoined relative clause dominant (8 languages)
  | adjoinedOrCorrelative  -- Adjoined or correlative (2 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 90F datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : AdjoinedRelativeClauses
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 90F dataset (10 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "diy", language := "Diyari", iso := "dif", value := .adjoinedRelativeClauseDominant }
  , { walsCode := "kkq", language := "Kuikúro", iso := "kui", value := .adjoinedRelativeClauseDominant }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .adjoinedRelativeClauseDominant }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .adjoinedRelativeClauseDominant }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .adjoinedRelativeClauseDominant }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .adjoinedRelativeClauseDominant }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .adjoinedOrCorrelative }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .adjoinedRelativeClauseDominant }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .adjoinedOrCorrelative }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .adjoinedRelativeClauseDominant }
  ]

-- Count verification
theorem total_count : allData.length = 10 := by native_decide

theorem count_adjoinedRelativeClauseDominant :
    (allData.filter (·.value == .adjoinedRelativeClauseDominant)).length = 8 := by native_decide
theorem count_adjoinedOrCorrelative :
    (allData.filter (·.value == .adjoinedOrCorrelative)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F90F
