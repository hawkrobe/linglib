import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 90D: Internally-headed relative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90D`.

Chapter 90, 63 languages.
-/

namespace Core.WALS.F90D

/-- WALS 90D values. -/
inductive InternallyHeadedRelativeClauses where
  /-- Internally-headed relative clause dominant (24 languages). -/
  | internallyHeadedRelativeClauseDominant
  /-- Internally-headed or RelN (15 languages). -/
  | internallyHeadedOrReln
  /-- Internally-headed or NRel (8 languages). -/
  | internallyHeadedOrNrel
  /-- Internally-headed or correlative (1 languages). -/
  | internallyHeadedOrCorrelative
  /-- Internally-headed or double-headed (1 languages). -/
  | internallyHeadedOrDoubleHeaded
  /-- Internally-headed occurs as nondominant type (10 languages). -/
  | internallyHeadedOccursAsNondominantType
  /-- Internally-headed exists (4 languages). -/
  | internallyHeadedExists
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 90D dataset (63 languages). -/
def allData : List (Datapoint InternallyHeadedRelativeClauses) :=
  [ { walsCode := "amt", iso := "adx", value := .internallyHeadedOrReln }
  , { walsCode := "ao", iso := "njo", value := .internallyHeadedOrReln }
  , { walsCode := "ath", iso := "aph", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "baw", iso := "bgr", value := .internallyHeadedOrReln }
  , { walsCode := "bel", iso := "byw", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "bya", iso := "bee", value := .internallyHeadedOrReln }
  , { walsCode := "cnl", iso := "ram", value := .internallyHeadedOrNrel }
  , { walsCode := "chg", iso := "nbc", value := .internallyHeadedOrReln }
  , { walsCode := "chi", iso := "cid", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "cmr", iso := "mrh", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "cti", iso := "ctd", value := .internallyHeadedExists }
  , { walsCode := "cct", iso := "cho", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "die", iso := "dih", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "dlm", iso := "kbv", value := .internallyHeadedOrReln }
  , { walsCode := "dds", iso := "dds", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "epe", iso := "sja", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "evn", iso := "eve", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "eve", iso := "evn", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "gmw", iso := "gvs", value := .internallyHeadedOrNrel }
  , { walsCode := "hai", iso := "hai", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "har", iso := "tmd", value := .internallyHeadedOrReln }
  , { walsCode := "ika", iso := "arh", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "imo", iso := "imn", value := .internallyHeadedOrReln }
  , { walsCode := "jms", iso := "djm", value := .internallyHeadedOrDoubleHeaded }
  , { walsCode := "jpn", iso := "jpn", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "kew", iso := "kew", value := .internallyHeadedOrReln }
  , { walsCode := "khd", iso := "khg", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "kio", iso := "kio", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "koa", iso := "cku", value := .internallyHeadedOrReln }
  , { walsCode := "kor", iso := "kor", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "kut", iso := "kut", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "lai", iso := "cnh", value := .internallyHeadedOrReln }
  , { walsCode := "lkt", iso := "lkt", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "lav", iso := "lvk", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "msn", iso := "mbq", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "mar", iso := "mrc", value := .internallyHeadedOrNrel }
  , { walsCode := "mpt", iso := "mpt", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "mpa", iso := "mwf", value := .internallyHeadedOrNrel }
  , { walsCode := "nze", iso := "nzm", value := .internallyHeadedExists }
  , { walsCode := "nav", iso := "nav", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "ngj", iso := "nju", value := .internallyHeadedExists }
  , { walsCode := "ond", iso := "one", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "osa", iso := "osa", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "pan", iso := "pan", value := .internallyHeadedOrReln }
  , { walsCode := "pit", iso := "pjt", value := .internallyHeadedOrNrel }
  , { walsCode := "res", iso := "rgr", value := .internallyHeadedOrNrel }
  , { walsCode := "ret", iso := "tnc", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "snm", iso := "xsu", value := .internallyHeadedOrCorrelative }
  , { walsCode := "see", iso := "trv", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "ser", iso := "sei", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "sla", iso := "den", value := .internallyHeadedOrNrel }
  , { walsCode := "tou", iso := "wib", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "sup", iso := "spp", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "tag", iso := "tgl", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "tis", iso := "bod", value := .internallyHeadedOrReln }
  , { walsCode := "tja", iso := "dih", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "tuk", iso := "", value := .internallyHeadedOrNrel }
  , { walsCode := "udh", iso := "ude", value := .internallyHeadedOrReln }
  , { walsCode := "wbn", iso := "wms", value := .internallyHeadedOrReln }
  , { walsCode := "wap", iso := "wao", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "way", iso := "oym", value := .internallyHeadedExists }
  , { walsCode := "yuw", iso := "kld", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "rgc", iso := "jya", value := .internallyHeadedRelativeClauseDominant }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F90D
