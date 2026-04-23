import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 90D: Internally-headed relative clauses
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90D`.

Chapter 90, 63 languages.
-/

namespace Datasets.WALS.F90D

/-- WALS 90D values. -/
inductive InternallyHeadedRelativeClauses where
  /-- Internally-headed relative clause dominant (24 languages). -/
  | relativeClauseDominant
  /-- Internally-headed or RelN (15 languages). -/
  | orReln
  /-- Internally-headed or NRel (8 languages). -/
  | orNrel
  /-- Internally-headed or correlative (1 languages). -/
  | orCorrelative
  /-- Internally-headed or double-headed (1 languages). -/
  | orDoubleHeaded
  /-- Internally-headed occurs as nondominant type (10 languages). -/
  | occursAsNondominantType
  /-- Internally-headed exists (4 languages). -/
  | exists_
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 90D dataset (63 languages). -/
def allData : List (Datapoint InternallyHeadedRelativeClauses) :=
  [ { walsCode := "amt", iso := "adx", value := .orReln }
  , { walsCode := "ao", iso := "njo", value := .orReln }
  , { walsCode := "ath", iso := "aph", value := .occursAsNondominantType }
  , { walsCode := "baw", iso := "bgr", value := .orReln }
  , { walsCode := "bel", iso := "byw", value := .occursAsNondominantType }
  , { walsCode := "bya", iso := "bee", value := .orReln }
  , { walsCode := "cnl", iso := "ram", value := .orNrel }
  , { walsCode := "chg", iso := "nbc", value := .orReln }
  , { walsCode := "chi", iso := "cid", value := .relativeClauseDominant }
  , { walsCode := "cmr", iso := "mrh", value := .relativeClauseDominant }
  , { walsCode := "cti", iso := "ctd", value := .exists_ }
  , { walsCode := "cct", iso := "cho", value := .relativeClauseDominant }
  , { walsCode := "die", iso := "dih", value := .relativeClauseDominant }
  , { walsCode := "dlm", iso := "kbv", value := .orReln }
  , { walsCode := "dds", iso := "dds", value := .relativeClauseDominant }
  , { walsCode := "epe", iso := "sja", value := .relativeClauseDominant }
  , { walsCode := "evn", iso := "eve", value := .occursAsNondominantType }
  , { walsCode := "eve", iso := "evn", value := .occursAsNondominantType }
  , { walsCode := "gmw", iso := "gvs", value := .orNrel }
  , { walsCode := "hai", iso := "hai", value := .relativeClauseDominant }
  , { walsCode := "har", iso := "tmd", value := .orReln }
  , { walsCode := "ika", iso := "arh", value := .relativeClauseDominant }
  , { walsCode := "imo", iso := "imn", value := .orReln }
  , { walsCode := "jms", iso := "djm", value := .orDoubleHeaded }
  , { walsCode := "jpn", iso := "jpn", value := .occursAsNondominantType }
  , { walsCode := "kew", iso := "kew", value := .orReln }
  , { walsCode := "khd", iso := "khg", value := .occursAsNondominantType }
  , { walsCode := "kio", iso := "kio", value := .relativeClauseDominant }
  , { walsCode := "koa", iso := "cku", value := .orReln }
  , { walsCode := "kor", iso := "kor", value := .occursAsNondominantType }
  , { walsCode := "kut", iso := "kut", value := .relativeClauseDominant }
  , { walsCode := "lai", iso := "cnh", value := .orReln }
  , { walsCode := "lkt", iso := "lkt", value := .relativeClauseDominant }
  , { walsCode := "lav", iso := "lvk", value := .relativeClauseDominant }
  , { walsCode := "msn", iso := "mbq", value := .relativeClauseDominant }
  , { walsCode := "mar", iso := "mrc", value := .orNrel }
  , { walsCode := "mpt", iso := "mpt", value := .relativeClauseDominant }
  , { walsCode := "mpa", iso := "mwf", value := .orNrel }
  , { walsCode := "nze", iso := "nzm", value := .exists_ }
  , { walsCode := "nav", iso := "nav", value := .relativeClauseDominant }
  , { walsCode := "ngj", iso := "nju", value := .exists_ }
  , { walsCode := "ond", iso := "one", value := .relativeClauseDominant }
  , { walsCode := "osa", iso := "osa", value := .relativeClauseDominant }
  , { walsCode := "pan", iso := "pan", value := .orReln }
  , { walsCode := "pit", iso := "pjt", value := .orNrel }
  , { walsCode := "res", iso := "rgr", value := .orNrel }
  , { walsCode := "ret", iso := "tnc", value := .relativeClauseDominant }
  , { walsCode := "snm", iso := "xsu", value := .orCorrelative }
  , { walsCode := "see", iso := "trv", value := .occursAsNondominantType }
  , { walsCode := "ser", iso := "sei", value := .relativeClauseDominant }
  , { walsCode := "sla", iso := "den", value := .orNrel }
  , { walsCode := "tou", iso := "wib", value := .relativeClauseDominant }
  , { walsCode := "sup", iso := "spp", value := .occursAsNondominantType }
  , { walsCode := "tag", iso := "tgl", value := .occursAsNondominantType }
  , { walsCode := "tis", iso := "bod", value := .orReln }
  , { walsCode := "tja", iso := "dih", value := .relativeClauseDominant }
  , { walsCode := "tuk", iso := "", value := .orNrel }
  , { walsCode := "udh", iso := "ude", value := .orReln }
  , { walsCode := "wbn", iso := "wms", value := .orReln }
  , { walsCode := "wap", iso := "wao", value := .relativeClauseDominant }
  , { walsCode := "way", iso := "oym", value := .exists_ }
  , { walsCode := "yuw", iso := "kld", value := .relativeClauseDominant }
  , { walsCode := "rgc", iso := "jya", value := .relativeClauseDominant }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F90D
