/-!
# WALS Feature 90D: Internally-headed relative clauses
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90D`.

Chapter 90, 63 languages.
-/

namespace Core.WALS.F90D

/-- WALS 90D values. -/
inductive InternallyHeadedRelativeClauses where
  | internallyHeadedRelativeClauseDominant  -- Internally-headed relative clause dominant (24 languages)
  | internallyHeadedOrReln  -- Internally-headed or RelN (15 languages)
  | internallyHeadedOrNrel  -- Internally-headed or NRel (8 languages)
  | internallyHeadedOrCorrelative  -- Internally-headed or correlative (1 languages)
  | internallyHeadedOrDoubleHeaded  -- Internally-headed or double-headed (1 languages)
  | internallyHeadedOccursAsNondominantType  -- Internally-headed occurs as nondominant type (10 languages)
  | internallyHeadedExists  -- Internally-headed exists (4 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 90D datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : InternallyHeadedRelativeClauses
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 90D dataset (63 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .internallyHeadedOrReln }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .internallyHeadedOrReln }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .internallyHeadedOrReln }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .internallyHeadedOrReln }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .internallyHeadedOrNrel }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .internallyHeadedOrReln }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .internallyHeadedExists }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .internallyHeadedOrReln }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .internallyHeadedOrNrel }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .internallyHeadedOrReln }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .internallyHeadedOrReln }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .internallyHeadedOrDoubleHeaded }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .internallyHeadedOrReln }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .internallyHeadedOrReln }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .internallyHeadedOrReln }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .internallyHeadedOrNrel }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .internallyHeadedOrNrel }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .internallyHeadedExists }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .internallyHeadedExists }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .internallyHeadedOrReln }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .internallyHeadedOrNrel }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .internallyHeadedOrNrel }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .internallyHeadedOrCorrelative }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .internallyHeadedOrNrel }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .internallyHeadedOccursAsNondominantType }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .internallyHeadedOrReln }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .internallyHeadedOrNrel }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .internallyHeadedOrReln }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .internallyHeadedOrReln }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .internallyHeadedExists }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .internallyHeadedRelativeClauseDominant }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .internallyHeadedRelativeClauseDominant }
  ]

-- Count verification
theorem total_count : allData.length = 63 := by native_decide

theorem count_internallyHeadedRelativeClauseDominant :
    (allData.filter (·.value == .internallyHeadedRelativeClauseDominant)).length = 24 := by native_decide
theorem count_internallyHeadedOrReln :
    (allData.filter (·.value == .internallyHeadedOrReln)).length = 15 := by native_decide
theorem count_internallyHeadedOrNrel :
    (allData.filter (·.value == .internallyHeadedOrNrel)).length = 8 := by native_decide
theorem count_internallyHeadedOrCorrelative :
    (allData.filter (·.value == .internallyHeadedOrCorrelative)).length = 1 := by native_decide
theorem count_internallyHeadedOrDoubleHeaded :
    (allData.filter (·.value == .internallyHeadedOrDoubleHeaded)).length = 1 := by native_decide
theorem count_internallyHeadedOccursAsNondominantType :
    (allData.filter (·.value == .internallyHeadedOccursAsNondominantType)).length = 10 := by native_decide
theorem count_internallyHeadedExists :
    (allData.filter (·.value == .internallyHeadedExists)).length = 4 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F90D
