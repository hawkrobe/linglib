import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 61A: Adjectives without Nouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 61A`.

Chapter 61, 124 languages.
-/

namespace Core.WALS.F61A

/-- WALS 61A values. -/
inductive AdjectivesWithoutNouns where
  /-- Not without noun (1 languages). -/
  | notWithoutNoun
  /-- Without marking (73 languages). -/
  | withoutMarking
  /-- Marked by prefix (7 languages). -/
  | markedByPrefix
  /-- Marked by suffix (13 languages). -/
  | markedBySuffix
  /-- Marked by preceding word (18 languages). -/
  | markedByPrecedingWord
  /-- Marked by following word (7 languages). -/
  | markedByFollowingWord
  /-- Marked by mixed or other strategies (5 languages). -/
  | markedByMixedOrOtherStrategies
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 61A dataset (124 languages). -/
def allData : List (Datapoint AdjectivesWithoutNouns) :=
  [ { walsCode := "abk", iso := "abk", value := .withoutMarking }
  , { walsCode := "agw", iso := "wbj", value := .markedByPrecedingWord }
  , { walsCode := "alb", iso := "sqi", value := .markedByPrecedingWord }
  , { walsCode := "aly", iso := "aly", value := .withoutMarking }
  , { walsCode := "aml", iso := "omb", value := .markedBySuffix }
  , { walsCode := "ame", iso := "aey", value := .withoutMarking }
  , { walsCode := "amr", iso := "ary", value := .withoutMarking }
  , { walsCode := "ava", iso := "ava", value := .withoutMarking }
  , { walsCode := "awp", iso := "kwi", value := .withoutMarking }
  , { walsCode := "bal", iso := "ban", value := .markedByPrecedingWord }
  , { walsCode := "bae", iso := "bae", value := .withoutMarking }
  , { walsCode := "bsq", iso := "eus", value := .withoutMarking }
  , { walsCode := "bkr", iso := "btx", value := .markedByPrecedingWord }
  , { walsCode := "bel", iso := "byw", value := .markedBySuffix }
  , { walsCode := "brm", iso := "mya", value := .withoutMarking }
  , { walsCode := "brn", iso := "bds", value := .markedByPrecedingWord }
  , { walsCode := "cnt", iso := "yue", value := .markedByFollowingWord }
  , { walsCode := "cha", iso := "cha", value := .withoutMarking }
  , { walsCode := "chk", iso := "ckt", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "cba", iso := "boi", value := .markedByPrefix }
  , { walsCode := "cem", iso := "cam", value := .markedBySuffix }
  , { walsCode := "drg", iso := "dar", value := .withoutMarking }
  , { walsCode := "dyi", iso := "dbl", value := .withoutMarking }
  , { walsCode := "eng", iso := "eng", value := .markedByFollowingWord }
  , { walsCode := "epe", iso := "sja", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "eve", iso := "evn", value := .withoutMarking }
  , { walsCode := "fin", iso := "fin", value := .withoutMarking }
  , { walsCode := "fre", iso := "fra", value := .withoutMarking }
  , { walsCode := "gaa", iso := "gbu", value := .withoutMarking }
  , { walsCode := "gav", iso := "gvo", value := .markedByPrefix }
  , { walsCode := "geo", iso := "kat", value := .withoutMarking }
  , { walsCode := "goo", iso := "gni", value := .withoutMarking }
  , { walsCode := "gum", iso := "kgs", value := .withoutMarking }
  , { walsCode := "hat", iso := "had", value := .markedByPrefix }
  , { walsCode := "heb", iso := "heb", value := .withoutMarking }
  , { walsCode := "hin", iso := "hin", value := .markedByFollowingWord }
  , { walsCode := "hmd", iso := "mww", value := .withoutMarking }
  , { walsCode := "hun", iso := "hun", value := .withoutMarking }
  , { walsCode := "hzb", iso := "huz", value := .markedBySuffix }
  , { walsCode := "hpd", iso := "jup", value := .markedByPrefix }
  , { walsCode := "imo", iso := "imn", value := .markedBySuffix }
  , { walsCode := "ind", iso := "ind", value := .markedByPrecedingWord }
  , { walsCode := "ing", iso := "inh", value := .markedBySuffix }
  , { walsCode := "irq", iso := "irk", value := .markedByPrecedingWord }
  , { walsCode := "iri", iso := "gle", value := .markedByPrecedingWord }
  , { walsCode := "jam", iso := "djd", value := .withoutMarking }
  , { walsCode := "jpn", iso := "jpn", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "jav", iso := "jav", value := .markedByPrecedingWord }
  , { walsCode := "knr", iso := "knc", value := .withoutMarking }
  , { walsCode := "kyl", iso := "eky", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "kay", iso := "gyd", value := .notWithoutNoun }
  , { walsCode := "kha", iso := "khk", value := .withoutMarking }
  , { walsCode := "krf", iso := "kpr", value := .withoutMarking }
  , { walsCode := "kor", iso := "kor", value := .markedByFollowingWord }
  , { walsCode := "kfe", iso := "kfz", value := .withoutMarking }
  , { walsCode := "kch", iso := "khq", value := .markedByPrefix }
  , { walsCode := "kut", iso := "kut", value := .withoutMarking }
  , { walsCode := "kwz", iso := "xwa", value := .markedBySuffix }
  , { walsCode := "lai", iso := "cnh", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "lan", iso := "laj", value := .markedByPrecedingWord }
  , { walsCode := "lez", iso := "lez", value := .markedBySuffix }
  , { walsCode := "lil", iso := "lil", value := .withoutMarking }
  , { walsCode := "ara", iso := "arw", value := .markedBySuffix }
  , { walsCode := "lov", iso := "lbo", value := .markedByPrecedingWord }
  , { walsCode := "luc", iso := "lch", value := .withoutMarking }
  , { walsCode := "myn", iso := "mhy", value := .markedByPrecedingWord }
  , { walsCode := "mks", iso := "mak", value := .withoutMarking }
  , { walsCode := "mal", iso := "plt", value := .markedByPrecedingWord }
  , { walsCode := "mnd", iso := "cmn", value := .markedByFollowingWord }
  , { walsCode := "mmb", iso := "mna", value := .withoutMarking }
  , { walsCode := "mrg", iso := "mrt", value := .withoutMarking }
  , { walsCode := "mar", iso := "mrc", value := .withoutMarking }
  , { walsCode := "mrt", iso := "vma", value := .withoutMarking }
  , { walsCode := "mau", iso := "mph", value := .withoutMarking }
  , { walsCode := "may", iso := "ayz", value := .markedByPrecedingWord }
  , { walsCode := "mbg", iso := "mhd", value := .withoutMarking }
  , { walsCode := "hok", iso := "nan", value := .markedByFollowingWord }
  , { walsCode := "min", iso := "min", value := .withoutMarking }
  , { walsCode := "mxc", iso := "mig", value := .markedByPrefix }
  , { walsCode := "mos", iso := "cas", value := .withoutMarking }
  , { walsCode := "nkk", iso := "nck", value := .withoutMarking }
  , { walsCode := "kho", iso := "naq", value := .withoutMarking }
  , { walsCode := "nan", iso := "niq", value := .markedByPrecedingWord }
  , { walsCode := "ndy", iso := "djk", value := .markedByFollowingWord }
  , { walsCode := "naj", iso := "aij", value := .markedByPrecedingWord }
  , { walsCode := "ngz", iso := "ngi", value := .withoutMarking }
  , { walsCode := "nvs", iso := "niv", value := .markedBySuffix }
  , { walsCode := "nbd", iso := "dgl", value := .withoutMarking }
  , { walsCode := "ood", iso := "ood", value := .withoutMarking }
  , { walsCode := "pnr", iso := "pbh", value := .withoutMarking }
  , { walsCode := "prs", iso := "pes", value := .withoutMarking }
  , { walsCode := "qim", iso := "qvi", value := .withoutMarking }
  , { walsCode := "rus", iso := "rus", value := .withoutMarking }
  , { walsCode := "rcp", iso := "", value := .withoutMarking }
  , { walsCode := "stl", iso := "sat", value := .markedBySuffix }
  , { walsCode := "sml", iso := "sza", value := .markedByPrefix }
  , { walsCode := "ses", iso := "sot", value := .withoutMarking }
  , { walsCode := "shk", iso := "shp", value := .withoutMarking }
  , { walsCode := "spa", iso := "spa", value := .withoutMarking }
  , { walsCode := "sup", iso := "spp", value := .withoutMarking }
  , { walsCode := "swa", iso := "swh", value := .withoutMarking }
  , { walsCode := "tag", iso := "tgl", value := .withoutMarking }
  , { walsCode := "tam", iso := "taj", value := .withoutMarking }
  , { walsCode := "tvo", iso := "tat", value := .withoutMarking }
  , { walsCode := "taw", iso := "tbo", value := .withoutMarking }
  , { walsCode := "tha", iso := "tha", value := .withoutMarking }
  , { walsCode := "tid", iso := "tvo", value := .markedByPrecedingWord }
  , { walsCode := "tiw", iso := "tiw", value := .withoutMarking }
  , { walsCode := "tuk", iso := "", value := .withoutMarking }
  , { walsCode := "tnn", iso := "tvu", value := .withoutMarking }
  , { walsCode := "tur", iso := "tur", value := .withoutMarking }
  , { walsCode := "ura", iso := "uur", value := .withoutMarking }
  , { walsCode := "vaf", iso := "vaf", value := .withoutMarking }
  , { walsCode := "vie", iso := "vie", value := .markedByPrecedingWord }
  , { walsCode := "war", iso := "pav", value := .withoutMarking }
  , { walsCode := "wat", iso := "wbv", value := .withoutMarking }
  , { walsCode := "wir", iso := "wgu", value := .withoutMarking }
  , { walsCode := "yag", iso := "yad", value := .markedBySuffix }
  , { walsCode := "yes", iso := "yss", value := .withoutMarking }
  , { walsCode := "yid", iso := "yii", value := .withoutMarking }
  , { walsCode := "yim", iso := "yee", value := .withoutMarking }
  , { walsCode := "yng", iso := "yia", value := .withoutMarking }
  , { walsCode := "yko", iso := "yux", value := .markedBySuffix }
  , { walsCode := "zul", iso := "zul", value := .withoutMarking }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F61A
