import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 90E: Correlative relative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90E`.

Chapter 90, 23 languages.
-/

namespace Core.WALS.F90E

/-- WALS 90E values. -/
inductive CorrelativeRelativeClauses where
  | correlativeRelativeClauseDominant  -- Correlative relative clause dominant (7 languages)
  | correlativeOrReln  -- Correlative or RelN (7 languages)
  | correlativeOrNrel  -- Correlative or NRel (2 languages)
  | correlativeOrInternallyHeaded  -- Correlative or internally-headed (1 languages)
  | correlativeOrAdjoined  -- Correlative or adjoined (2 languages)
  | correlativeAsNondominantType  -- Correlative as nondominant type (3 languages)
  | correlativeExists  -- Correlative exists (1 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 90E dataset (23 languages). -/
def allData : List (Datapoint CorrelativeRelativeClauses) :=
  [ { walsCode := "bam", language := "Bambara", iso := "bam", value := .correlativeRelativeClauseDominant }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .correlativeOrReln }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .correlativeOrReln }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .correlativeRelativeClauseDominant }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .correlativeExists }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .correlativeOrReln }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .correlativeOrNrel }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .correlativeOrReln }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .correlativeOrReln }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .correlativeOrNrel }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .correlativeRelativeClauseDominant }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .correlativeAsNondominantType }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .correlativeOrAdjoined }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .correlativeRelativeClauseDominant }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .correlativeAsNondominantType }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .correlativeOrReln }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .correlativeOrInternallyHeaded }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .correlativeOrReln }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .correlativeRelativeClauseDominant }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .correlativeRelativeClauseDominant }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .correlativeRelativeClauseDominant }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .correlativeOrAdjoined }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .correlativeAsNondominantType }
  ]

-- Count verification
theorem total_count : allData.length = 23 := by native_decide

theorem count_correlativeRelativeClauseDominant :
    (allData.filter (·.value == .correlativeRelativeClauseDominant)).length = 7 := by native_decide
theorem count_correlativeOrReln :
    (allData.filter (·.value == .correlativeOrReln)).length = 7 := by native_decide
theorem count_correlativeOrNrel :
    (allData.filter (·.value == .correlativeOrNrel)).length = 2 := by native_decide
theorem count_correlativeOrInternallyHeaded :
    (allData.filter (·.value == .correlativeOrInternallyHeaded)).length = 1 := by native_decide
theorem count_correlativeOrAdjoined :
    (allData.filter (·.value == .correlativeOrAdjoined)).length = 2 := by native_decide
theorem count_correlativeAsNondominantType :
    (allData.filter (·.value == .correlativeAsNondominantType)).length = 3 := by native_decide
theorem count_correlativeExists :
    (allData.filter (·.value == .correlativeExists)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F90E
