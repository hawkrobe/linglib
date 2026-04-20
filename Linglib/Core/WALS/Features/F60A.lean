import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 60A: Genitives, Adjectives and Relative Clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 60A`.

Chapter 60, 138 languages.
-/

namespace Core.WALS.F60A

/-- WALS 60A values. -/
inductive GenitivesAdjectivesAndRelativeClauses where
  /-- Weakly differentiated (15 languages). -/
  | weaklyDifferentiated
  /-- Genitives and adjectives collapsed (8 languages). -/
  | genitivesAndAdjectivesCollapsed
  /-- Genitives and relative clauses collapsed (2 languages). -/
  | genitivesAndRelativeClausesCollapsed
  /-- Adjectives and relative clauses collapsed (33 languages). -/
  | adjectivesAndRelativeClausesCollapsed
  /-- Moderately differentiated in other ways (3 languages). -/
  | moderatelyDifferentiatedInOtherWays
  /-- Highly differentiated (77 languages). -/
  | highlyDifferentiated
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 60A dataset (138 languages). -/
def allData : List (Datapoint GenitivesAdjectivesAndRelativeClauses) :=
  [ { walsCode := "xam", iso := "xam", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "abk", iso := "abk", value := .highlyDifferentiated }
  , { walsCode := "abu", iso := "kgr", value := .highlyDifferentiated }
  , { walsCode := "ain", iso := "ain", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "agw", iso := "wbj", value := .highlyDifferentiated }
  , { walsCode := "alb", iso := "sqi", value := .highlyDifferentiated }
  , { walsCode := "ame", iso := "aey", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "ath", iso := "aph", value := .highlyDifferentiated }
  , { walsCode := "ava", iso := "ava", value := .highlyDifferentiated }
  , { walsCode := "bgv", iso := "kva", value := .highlyDifferentiated }
  , { walsCode := "bal", iso := "ban", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "bae", iso := "bae", value := .highlyDifferentiated }
  , { walsCode := "bsq", iso := "eus", value := .highlyDifferentiated }
  , { walsCode := "bkr", iso := "btx", value := .moderatelyDifferentiatedInOtherWays }
  , { walsCode := "beg", iso := "dbj", value := .weaklyDifferentiated }
  , { walsCode := "bel", iso := "byw", value := .highlyDifferentiated }
  , { walsCode := "bok", iso := "bqc", value := .highlyDifferentiated }
  , { walsCode := "brm", iso := "mya", value := .genitivesAndRelativeClausesCollapsed }
  , { walsCode := "brn", iso := "bds", value := .highlyDifferentiated }
  , { walsCode := "cml", iso := "rab", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "cnt", iso := "yue", value := .weaklyDifferentiated }
  , { walsCode := "cme", iso := "cjm", value := .weaklyDifferentiated }
  , { walsCode := "cha", iso := "cha", value := .highlyDifferentiated }
  , { walsCode := "chk", iso := "ckt", value := .highlyDifferentiated }
  , { walsCode := "drg", iso := "dar", value := .highlyDifferentiated }
  , { walsCode := "dat", iso := "tcc", value := .highlyDifferentiated }
  , { walsCode := "eng", iso := "eng", value := .highlyDifferentiated }
  , { walsCode := "epe", iso := "sja", value := .highlyDifferentiated }
  , { walsCode := "eve", iso := "evn", value := .highlyDifferentiated }
  , { walsCode := "fij", iso := "fij", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "fin", iso := "fin", value := .highlyDifferentiated }
  , { walsCode := "fre", iso := "fra", value := .highlyDifferentiated }
  , { walsCode := "gav", iso := "gvo", value := .highlyDifferentiated }
  , { walsCode := "geo", iso := "kat", value := .highlyDifferentiated }
  , { walsCode := "gil", iso := "glk", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "goo", iso := "gni", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "hat", iso := "had", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "heb", iso := "heb", value := .highlyDifferentiated }
  , { walsCode := "hin", iso := "hin", value := .highlyDifferentiated }
  , { walsCode := "hmd", iso := "mww", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "hun", iso := "hun", value := .highlyDifferentiated }
  , { walsCode := "hzb", iso := "huz", value := .highlyDifferentiated }
  , { walsCode := "hpd", iso := "jup", value := .highlyDifferentiated }
  , { walsCode := "ika", iso := "arh", value := .highlyDifferentiated }
  , { walsCode := "imo", iso := "imn", value := .highlyDifferentiated }
  , { walsCode := "ind", iso := "ind", value := .weaklyDifferentiated }
  , { walsCode := "ing", iso := "inh", value := .highlyDifferentiated }
  , { walsCode := "irq", iso := "irk", value := .highlyDifferentiated }
  , { walsCode := "jam", iso := "djd", value := .highlyDifferentiated }
  , { walsCode := "jpn", iso := "jpn", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "jaq", iso := "jqr", value := .highlyDifferentiated }
  , { walsCode := "jav", iso := "jav", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "kan", iso := "ogo", value := .highlyDifferentiated }
  , { walsCode := "knr", iso := "knc", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "kyl", iso := "eky", value := .highlyDifferentiated }
  , { walsCode := "kay", iso := "gyd", value := .highlyDifferentiated }
  , { walsCode := "kha", iso := "khk", value := .highlyDifferentiated }
  , { walsCode := "khr", iso := "khr", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "khm", iso := "khm", value := .weaklyDifferentiated }
  , { walsCode := "kmb", iso := "", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "kor", iso := "kor", value := .highlyDifferentiated }
  , { walsCode := "kfe", iso := "kfz", value := .highlyDifferentiated }
  , { walsCode := "kch", iso := "khq", value := .highlyDifferentiated }
  , { walsCode := "kut", iso := "kut", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "kwz", iso := "xwa", value := .highlyDifferentiated }
  , { walsCode := "lai", iso := "cnh", value := .highlyDifferentiated }
  , { walsCode := "lan", iso := "laj", value := .weaklyDifferentiated }
  , { walsCode := "lez", iso := "lez", value := .highlyDifferentiated }
  , { walsCode := "lov", iso := "lbo", value := .weaklyDifferentiated }
  , { walsCode := "luc", iso := "lch", value := .highlyDifferentiated }
  , { walsCode := "mks", iso := "mak", value := .highlyDifferentiated }
  , { walsCode := "mal", iso := "plt", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "mnd", iso := "cmn", value := .weaklyDifferentiated }
  , { walsCode := "mao", iso := "mri", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "mhi", iso := "mar", value := .highlyDifferentiated }
  , { walsCode := "mrg", iso := "mrt", value := .highlyDifferentiated }
  , { walsCode := "mar", iso := "mrc", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "mrt", iso := "vma", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "mau", iso := "mph", value := .highlyDifferentiated }
  , { walsCode := "may", iso := "ayz", value := .weaklyDifferentiated }
  , { walsCode := "mzn", iso := "mzn", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "mee", iso := "mym", value := .highlyDifferentiated }
  , { walsCode := "mei", iso := "mni", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "hok", iso := "nan", value := .weaklyDifferentiated }
  , { walsCode := "min", iso := "min", value := .weaklyDifferentiated }
  , { walsCode := "miy", iso := "mkf", value := .highlyDifferentiated }
  , { walsCode := "mos", iso := "cas", value := .weaklyDifferentiated }
  , { walsCode := "msc", iso := "chb", value := .highlyDifferentiated }
  , { walsCode := "mup", iso := "sur", value := .moderatelyDifferentiatedInOtherWays }
  , { walsCode := "nht", iso := "nhg", value := .highlyDifferentiated }
  , { walsCode := "kho", iso := "naq", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "nan", iso := "niq", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "ndy", iso := "djk", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "naj", iso := "aij", value := .genitivesAndRelativeClausesCollapsed }
  , { walsCode := "ngz", iso := "ngi", value := .weaklyDifferentiated }
  , { walsCode := "nvs", iso := "niv", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "nbd", iso := "dgl", value := .highlyDifferentiated }
  , { walsCode := "pad", iso := "pdo", value := .weaklyDifferentiated }
  , { walsCode := "pnr", iso := "pbh", value := .highlyDifferentiated }
  , { walsCode := "prs", iso := "pes", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "pil", iso := "piv", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "pba", iso := "pia", value := .highlyDifferentiated }
  , { walsCode := "qim", iso := "qvi", value := .highlyDifferentiated }
  , { walsCode := "rap", iso := "rap", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "rus", iso := "rus", value := .highlyDifferentiated }
  , { walsCode := "rcp", iso := "", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "snm", iso := "xsu", value := .highlyDifferentiated }
  , { walsCode := "see", iso := "trv", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "sml", iso := "sza", value := .weaklyDifferentiated }
  , { walsCode := "ses", iso := "sot", value := .highlyDifferentiated }
  , { walsCode := "shk", iso := "shp", value := .highlyDifferentiated }
  , { walsCode := "so", iso := "teu", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "sup", iso := "spp", value := .highlyDifferentiated }
  , { walsCode := "swv", iso := "swe", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "tab", iso := "mky", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tag", iso := "tgl", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tam", iso := "taj", value := .highlyDifferentiated }
  , { walsCode := "tvo", iso := "tat", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tts", iso := "tks", value := .highlyDifferentiated }
  , { walsCode := "taw", iso := "tbo", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "trb", iso := "tfr", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tha", iso := "tha", value := .moderatelyDifferentiatedInOtherWays }
  , { walsCode := "tid", iso := "tvo", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tiw", iso := "tiw", value := .highlyDifferentiated }
  , { walsCode := "tgh", iso := "thv", value := .highlyDifferentiated }
  , { walsCode := "tuk", iso := "", value := .highlyDifferentiated }
  , { walsCode := "tur", iso := "tur", value := .highlyDifferentiated }
  , { walsCode := "ura", iso := "uur", value := .highlyDifferentiated }
  , { walsCode := "vaf", iso := "vaf", value := .highlyDifferentiated }
  , { walsCode := "vie", iso := "vie", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "wra", iso := "wba", value := .highlyDifferentiated }
  , { walsCode := "war", iso := "pav", value := .highlyDifferentiated }
  , { walsCode := "yag", iso := "yad", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "yid", iso := "yii", value := .highlyDifferentiated }
  , { walsCode := "yim", iso := "yee", value := .highlyDifferentiated }
  , { walsCode := "yng", iso := "yia", value := .highlyDifferentiated }
  , { walsCode := "yko", iso := "yux", value := .highlyDifferentiated }
  , { walsCode := "zul", iso := "zul", value := .highlyDifferentiated }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F60A
