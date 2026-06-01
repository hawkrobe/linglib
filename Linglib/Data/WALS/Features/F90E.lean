import Linglib.Data.WALS.Datapoint

/-!
# WALS Feature 90E: Correlative relative clauses
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90E`.

Chapter 90, 23 languages.
-/

namespace Data.WALS.F90E

/-- WALS 90E values. -/
inductive CorrelativeRelativeClauses where
  /-- Correlative relative clause dominant (7 languages). -/
  | relativeClauseDominant
  /-- Correlative or RelN (7 languages). -/
  | orReln
  /-- Correlative or NRel (2 languages). -/
  | orNrel
  /-- Correlative or internally-headed (1 languages). -/
  | orInternallyHeaded
  /-- Correlative or adjoined (2 languages). -/
  | orAdjoined
  /-- Correlative as nondominant type (3 languages). -/
  | asNondominantType
  /-- Correlative exists (1 languages). -/
  | exists_
  deriving DecidableEq, Repr

/-- Complete WALS 90E dataset (23 languages). -/
def allData : List (Datapoint CorrelativeRelativeClauses) :=
  [ { walsCode := "bam", iso := "bam", value := .relativeClauseDominant }
  , { walsCode := "bod", iso := "brx", value := .orReln }
  , { walsCode := "drm", iso := "drd", value := .orReln }
  , { walsCode := "hin", iso := "hin", value := .relativeClauseDominant }
  , { walsCode := "xns", iso := "xns", value := .exists_ }
  , { walsCode := "knd", iso := "kan", value := .orReln }
  , { walsCode := "kas", iso := "kas", value := .orNrel }
  , { walsCode := "khr", iso := "khr", value := .orReln }
  , { walsCode := "kgy", iso := "kgy", value := .orReln }
  , { walsCode := "mai", iso := "mai", value := .orNrel }
  , { walsCode := "mka", iso := "mxx", value := .relativeClauseDominant }
  , { walsCode := "nwd", iso := "new", value := .asNondominantType }
  , { walsCode := "ngi", iso := "wyb", value := .orAdjoined }
  , { walsCode := "oya", iso := "ory", value := .relativeClauseDominant }
  , { walsCode := "qim", iso := "qvi", value := .asNondominantType }
  , { walsCode := "stl", iso := "sat", value := .orReln }
  , { walsCode := "snm", iso := "xsu", value := .orInternallyHeaded }
  , { walsCode := "skw", iso := "swv", value := .orReln }
  , { walsCode := "sup", iso := "spp", value := .relativeClauseDominant }
  , { walsCode := "urd", iso := "urd", value := .relativeClauseDominant }
  , { walsCode := "vai", iso := "vai", value := .relativeClauseDominant }
  , { walsCode := "xas", iso := "kao", value := .orAdjoined }
  , { walsCode := "yko", iso := "yux", value := .asNondominantType }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option (Datapoint CorrelativeRelativeClauses) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option (Datapoint CorrelativeRelativeClauses) := Datapoint.lookupISO allData iso

end Data.WALS.F90E
