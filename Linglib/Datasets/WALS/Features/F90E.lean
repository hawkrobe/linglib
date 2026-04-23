import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 90E: Correlative relative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90E`.

Chapter 90, 23 languages.
-/

namespace Datasets.WALS.F90E

/-- WALS 90E values. -/
inductive CorrelativeRelativeClauses where
  /-- Correlative relative clause dominant (7 languages). -/
  | correlativeRelativeClauseDominant
  /-- Correlative or RelN (7 languages). -/
  | correlativeOrReln
  /-- Correlative or NRel (2 languages). -/
  | correlativeOrNrel
  /-- Correlative or internally-headed (1 languages). -/
  | correlativeOrInternallyHeaded
  /-- Correlative or adjoined (2 languages). -/
  | correlativeOrAdjoined
  /-- Correlative as nondominant type (3 languages). -/
  | correlativeAsNondominantType
  /-- Correlative exists (1 languages). -/
  | correlativeExists
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 90E dataset (23 languages). -/
def allData : List (Datapoint CorrelativeRelativeClauses) :=
  [ { walsCode := "bam", iso := "bam", value := .correlativeRelativeClauseDominant }
  , { walsCode := "bod", iso := "brx", value := .correlativeOrReln }
  , { walsCode := "drm", iso := "drd", value := .correlativeOrReln }
  , { walsCode := "hin", iso := "hin", value := .correlativeRelativeClauseDominant }
  , { walsCode := "xns", iso := "xns", value := .correlativeExists }
  , { walsCode := "knd", iso := "kan", value := .correlativeOrReln }
  , { walsCode := "kas", iso := "kas", value := .correlativeOrNrel }
  , { walsCode := "khr", iso := "khr", value := .correlativeOrReln }
  , { walsCode := "kgy", iso := "kgy", value := .correlativeOrReln }
  , { walsCode := "mai", iso := "mai", value := .correlativeOrNrel }
  , { walsCode := "mka", iso := "mxx", value := .correlativeRelativeClauseDominant }
  , { walsCode := "nwd", iso := "new", value := .correlativeAsNondominantType }
  , { walsCode := "ngi", iso := "wyb", value := .correlativeOrAdjoined }
  , { walsCode := "oya", iso := "ory", value := .correlativeRelativeClauseDominant }
  , { walsCode := "qim", iso := "qvi", value := .correlativeAsNondominantType }
  , { walsCode := "stl", iso := "sat", value := .correlativeOrReln }
  , { walsCode := "snm", iso := "xsu", value := .correlativeOrInternallyHeaded }
  , { walsCode := "skw", iso := "swv", value := .correlativeOrReln }
  , { walsCode := "sup", iso := "spp", value := .correlativeRelativeClauseDominant }
  , { walsCode := "urd", iso := "urd", value := .correlativeRelativeClauseDominant }
  , { walsCode := "vai", iso := "vai", value := .correlativeRelativeClauseDominant }
  , { walsCode := "xas", iso := "kao", value := .correlativeOrAdjoined }
  , { walsCode := "yko", iso := "yux", value := .correlativeAsNondominantType }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F90E
