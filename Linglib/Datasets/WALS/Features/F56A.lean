import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 56A: Conjunctions and Universal Quantifiers
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 56A`.

Chapter 56, 116 languages.
-/

namespace Datasets.WALS.F56A

/-- WALS 56A values. -/
inductive ConjunctionsAndUniversalQuantifiers where
  /-- Formally different (40 languages). -/
  | different
  /-- Formally similar, without interrogative (33 languages). -/
  | similarWithoutInterrogative
  /-- Formally similar, with interrogative (43 languages). -/
  | similarWithInterrogative
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 56A dataset (116 languages). -/
def allData : List (Datapoint ConjunctionsAndUniversalQuantifiers) :=
  [ { walsCode := "abu", iso := "kgr", value := .similarWithoutInterrogative }
  , { walsCode := "ain", iso := "ain", value := .similarWithInterrogative }
  , { walsCode := "ame", iso := "aey", value := .similarWithoutInterrogative }
  , { walsCode := "arn", iso := "shu", value := .similarWithInterrogative }
  , { walsCode := "amr", iso := "ary", value := .different }
  , { walsCode := "arm", iso := "hye", value := .different }
  , { walsCode := "ath", iso := "aph", value := .similarWithInterrogative }
  , { walsCode := "bgv", iso := "kva", value := .similarWithInterrogative }
  , { walsCode := "bae", iso := "bae", value := .different }
  , { walsCode := "bsk", iso := "bak", value := .similarWithoutInterrogative }
  , { walsCode := "bsq", iso := "eus", value := .different }
  , { walsCode := "bkr", iso := "btx", value := .similarWithoutInterrogative }
  , { walsCode := "beg", iso := "dbj", value := .similarWithInterrogative }
  , { walsCode := "bel", iso := "byw", value := .similarWithInterrogative }
  , { walsCode := "brh", iso := "brh", value := .different }
  , { walsCode := "but", iso := "bxm", value := .similarWithInterrogative }
  , { walsCode := "brm", iso := "mya", value := .similarWithInterrogative }
  , { walsCode := "cnt", iso := "yue", value := .similarWithInterrogative }
  , { walsCode := "chk", iso := "ckt", value := .similarWithoutInterrogative }
  , { walsCode := "drg", iso := "dar", value := .similarWithInterrogative }
  , { walsCode := "dut", iso := "nld", value := .similarWithoutInterrogative }
  , { walsCode := "eng", iso := "eng", value := .similarWithoutInterrogative }
  , { walsCode := "epe", iso := "sja", value := .different }
  , { walsCode := "eve", iso := "evn", value := .similarWithInterrogative }
  , { walsCode := "fin", iso := "fin", value := .similarWithInterrogative }
  , { walsCode := "fre", iso := "fra", value := .different }
  , { walsCode := "gaa", iso := "gbu", value := .different }
  , { walsCode := "geo", iso := "kat", value := .different }
  , { walsCode := "goo", iso := "gni", value := .similarWithoutInterrogative }
  , { walsCode := "hai", iso := "hai", value := .different }
  , { walsCode := "hsl", iso := "has", value := .similarWithoutInterrogative }
  , { walsCode := "heb", iso := "heb", value := .similarWithoutInterrogative }
  , { walsCode := "hin", iso := "hin", value := .similarWithInterrogative }
  , { walsCode := "hix", iso := "hix", value := .different }
  , { walsCode := "hun", iso := "hun", value := .similarWithoutInterrogative }
  , { walsCode := "hzb", iso := "huz", value := .different }
  , { walsCode := "hpd", iso := "jup", value := .similarWithoutInterrogative }
  , { walsCode := "ika", iso := "arh", value := .different }
  , { walsCode := "imo", iso := "imn", value := .similarWithoutInterrogative }
  , { walsCode := "ind", iso := "ind", value := .similarWithInterrogative }
  , { walsCode := "ing", iso := "inh", value := .similarWithInterrogative }
  , { walsCode := "irq", iso := "irk", value := .similarWithoutInterrogative }
  , { walsCode := "jam", iso := "djd", value := .different }
  , { walsCode := "jpn", iso := "jpn", value := .similarWithInterrogative }
  , { walsCode := "jaq", iso := "jqr", value := .similarWithInterrogative }
  , { walsCode := "jav", iso := "jav", value := .similarWithInterrogative }
  , { walsCode := "knd", iso := "kan", value := .similarWithInterrogative }
  , { walsCode := "knr", iso := "knc", value := .similarWithInterrogative }
  , { walsCode := "kay", iso := "gyd", value := .similarWithoutInterrogative }
  , { walsCode := "kha", iso := "khk", value := .similarWithInterrogative }
  , { walsCode := "khm", iso := "khm", value := .similarWithInterrogative }
  , { walsCode := "koi", iso := "kbk", value := .similarWithoutInterrogative }
  , { walsCode := "kda", iso := "kfc", value := .similarWithoutInterrogative }
  , { walsCode := "kku", iso := "kfq", value := .similarWithInterrogative }
  , { walsCode := "kfe", iso := "kfz", value := .similarWithoutInterrogative }
  , { walsCode := "kch", iso := "khq", value := .different }
  , { walsCode := "kut", iso := "kut", value := .different }
  , { walsCode := "lan", iso := "laj", value := .different }
  , { walsCode := "lat", iso := "lav", value := .different }
  , { walsCode := "lez", iso := "lez", value := .similarWithoutInterrogative }
  , { walsCode := "lu", iso := "khb", value := .similarWithoutInterrogative }
  , { walsCode := "mal", iso := "plt", value := .similarWithInterrogative }
  , { walsCode := "mym", iso := "mal", value := .similarWithInterrogative }
  , { walsCode := "mnd", iso := "cmn", value := .similarWithInterrogative }
  , { walsCode := "mao", iso := "mri", value := .different }
  , { walsCode := "mhi", iso := "mar", value := .similarWithInterrogative }
  , { walsCode := "mrg", iso := "mrt", value := .similarWithInterrogative }
  , { walsCode := "mar", iso := "mrc", value := .different }
  , { walsCode := "mau", iso := "mph", value := .different }
  , { walsCode := "may", iso := "ayz", value := .different }
  , { walsCode := "mei", iso := "mni", value := .similarWithoutInterrogative }
  , { walsCode := "min", iso := "min", value := .similarWithInterrogative }
  , { walsCode := "mos", iso := "cas", value := .similarWithInterrogative }
  , { walsCode := "nht", iso := "nhg", value := .different }
  , { walsCode := "kho", iso := "naq", value := .different }
  , { walsCode := "ndy", iso := "djk", value := .different }
  , { walsCode := "ngz", iso := "ngi", value := .similarWithInterrogative }
  , { walsCode := "niv", iso := "niv", value := .similarWithInterrogative }
  , { walsCode := "nvs", iso := "niv", value := .similarWithInterrogative }
  , { walsCode := "nbd", iso := "dgl", value := .different }
  , { walsCode := "nyu", iso := "nyv", value := .similarWithoutInterrogative }
  , { walsCode := "pnr", iso := "pbh", value := .different }
  , { walsCode := "pan", iso := "pan", value := .similarWithInterrogative }
  , { walsCode := "pen", iso := "peg", value := .similarWithoutInterrogative }
  , { walsCode := "prs", iso := "pes", value := .similarWithoutInterrogative }
  , { walsCode := "pba", iso := "pia", value := .different }
  , { walsCode := "qhu", iso := "qub", value := .similarWithInterrogative }
  , { walsCode := "qim", iso := "qvi", value := .different }
  , { walsCode := "saw", iso := "hvn", value := .different }
  , { walsCode := "sml", iso := "sza", value := .different }
  , { walsCode := "ses", iso := "sot", value := .similarWithInterrogative }
  , { walsCode := "shk", iso := "shp", value := .similarWithoutInterrogative }
  , { walsCode := "sup", iso := "spp", value := .similarWithoutInterrogative }
  , { walsCode := "tab", iso := "mky", value := .similarWithoutInterrogative }
  , { walsCode := "tag", iso := "tgl", value := .similarWithInterrogative }
  , { walsCode := "tam", iso := "taj", value := .similarWithInterrogative }
  , { walsCode := "tml", iso := "tam", value := .similarWithInterrogative }
  , { walsCode := "tvo", iso := "tat", value := .similarWithoutInterrogative }
  , { walsCode := "taw", iso := "tbo", value := .similarWithInterrogative }
  , { walsCode := "tel", iso := "tel", value := .similarWithInterrogative }
  , { walsCode := "tps", iso := "stp", value := .different }
  , { walsCode := "trb", iso := "tfr", value := .different }
  , { walsCode := "tha", iso := "tha", value := .similarWithInterrogative }
  , { walsCode := "tiw", iso := "tiw", value := .different }
  , { walsCode := "tsi", iso := "tsi", value := .similarWithoutInterrogative }
  , { walsCode := "tuk", iso := "", value := .different }
  , { walsCode := "tur", iso := "tur", value := .different }
  , { walsCode := "uzb", iso := "", value := .similarWithoutInterrogative }
  , { walsCode := "vaf", iso := "vaf", value := .different }
  , { walsCode := "vie", iso := "vie", value := .similarWithInterrogative }
  , { walsCode := "war", iso := "pav", value := .different }
  , { walsCode := "was", iso := "was", value := .different }
  , { walsCode := "ykt", iso := "sah", value := .similarWithoutInterrogative }
  , { walsCode := "yid", iso := "yii", value := .similarWithoutInterrogative }
  , { walsCode := "yim", iso := "yee", value := .different }
  , { walsCode := "zul", iso := "zul", value := .similarWithoutInterrogative }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F56A
