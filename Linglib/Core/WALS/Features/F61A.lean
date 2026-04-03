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
  | notWithoutNoun  -- Not without noun (1 languages)
  | withoutMarking  -- Without marking (73 languages)
  | markedByPrefix  -- Marked by prefix (7 languages)
  | markedBySuffix  -- Marked by suffix (13 languages)
  | markedByPrecedingWord  -- Marked by preceding word (18 languages)
  | markedByFollowingWord  -- Marked by following word (7 languages)
  | markedByMixedOrOtherStrategies  -- Marked by mixed or other strategies (5 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 61A dataset (124 languages). -/
def allData : List (Datapoint AdjectivesWithoutNouns) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .withoutMarking }
  , { walsCode := "agw", language := "Alagwa", iso := "wbj", value := .markedByPrecedingWord }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .markedByPrecedingWord }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .withoutMarking }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .markedBySuffix }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .withoutMarking }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .withoutMarking }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .withoutMarking }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .withoutMarking }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .markedByPrecedingWord }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .withoutMarking }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .withoutMarking }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .markedByPrecedingWord }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .markedBySuffix }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .withoutMarking }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .markedByPrecedingWord }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .markedByFollowingWord }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .withoutMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .markedByPrefix }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .markedBySuffix }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .withoutMarking }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .withoutMarking }
  , { walsCode := "eng", language := "English", iso := "eng", value := .markedByFollowingWord }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .withoutMarking }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .withoutMarking }
  , { walsCode := "fre", language := "French", iso := "fra", value := .withoutMarking }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .withoutMarking }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .markedByPrefix }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .withoutMarking }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .withoutMarking }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .withoutMarking }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .markedByPrefix }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .withoutMarking }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .markedByFollowingWord }
  , { walsCode := "hmd", language := "Hmong Daw", iso := "mww", value := .withoutMarking }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .withoutMarking }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .markedBySuffix }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .markedByPrefix }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .markedBySuffix }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .markedByPrecedingWord }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .markedBySuffix }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .markedByPrecedingWord }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .markedByPrecedingWord }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .withoutMarking }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .markedByPrecedingWord }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .withoutMarking }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .notWithoutNoun }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .withoutMarking }
  , { walsCode := "krf", language := "Korafe", iso := "kpr", value := .withoutMarking }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .markedByFollowingWord }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .withoutMarking }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .markedByPrefix }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .withoutMarking }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .markedBySuffix }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .markedByMixedOrOtherStrategies }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .markedByPrecedingWord }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .markedBySuffix }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .withoutMarking }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .markedBySuffix }
  , { walsCode := "lov", language := "Loven", iso := "lbo", value := .markedByPrecedingWord }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .withoutMarking }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .markedByPrecedingWord }
  , { walsCode := "mks", language := "Makassar", iso := "mak", value := .withoutMarking }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .markedByPrecedingWord }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .markedByFollowingWord }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .withoutMarking }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .withoutMarking }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .withoutMarking }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .withoutMarking }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .withoutMarking }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .markedByPrecedingWord }
  , { walsCode := "mbg", language := "Mbugu", iso := "mhd", value := .withoutMarking }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .markedByFollowingWord }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .withoutMarking }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .markedByPrefix }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .withoutMarking }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .withoutMarking }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .withoutMarking }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .markedByPrecedingWord }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .markedByFollowingWord }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .markedByPrecedingWord }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .withoutMarking }
  , { walsCode := "nvs", language := "Nivkh (South Sakhalin)", iso := "niv", value := .markedBySuffix }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .withoutMarking }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .withoutMarking }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .withoutMarking }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .withoutMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .withoutMarking }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .withoutMarking }
  , { walsCode := "rcp", language := "Russian-Chinese Pidgin (Birobidjan)", iso := "", value := .withoutMarking }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .markedBySuffix }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .markedByPrefix }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .withoutMarking }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .withoutMarking }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .withoutMarking }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .withoutMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .withoutMarking }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .withoutMarking }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .withoutMarking }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .withoutMarking }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .withoutMarking }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .withoutMarking }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .markedByPrecedingWord }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .withoutMarking }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .withoutMarking }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .withoutMarking }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .withoutMarking }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .withoutMarking }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .withoutMarking }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .markedByPrecedingWord }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .withoutMarking }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .withoutMarking }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .withoutMarking }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .markedBySuffix }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .withoutMarking }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .withoutMarking }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .withoutMarking }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .withoutMarking }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .markedBySuffix }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .withoutMarking }
  ]

-- Count verification
theorem total_count : allData.length = 124 := by native_decide

theorem count_notWithoutNoun :
    (allData.filter (·.value == .notWithoutNoun)).length = 1 := by native_decide
theorem count_withoutMarking :
    (allData.filter (·.value == .withoutMarking)).length = 73 := by native_decide
theorem count_markedByPrefix :
    (allData.filter (·.value == .markedByPrefix)).length = 7 := by native_decide
theorem count_markedBySuffix :
    (allData.filter (·.value == .markedBySuffix)).length = 13 := by native_decide
theorem count_markedByPrecedingWord :
    (allData.filter (·.value == .markedByPrecedingWord)).length = 18 := by native_decide
theorem count_markedByFollowingWord :
    (allData.filter (·.value == .markedByFollowingWord)).length = 7 := by native_decide
theorem count_markedByMixedOrOtherStrategies :
    (allData.filter (·.value == .markedByMixedOrOtherStrategies)).length = 5 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F61A
