/-!
# WALS Feature 56A: Conjunctions and Universal Quantifiers
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 56A`.

Chapter 56, 116 languages.
-/

namespace Core.WALS.F56A

/-- WALS 56A values. -/
inductive ConjunctionsAndUniversalQuantifiers where
  | formallyDifferent  -- Formally different (40 languages)
  | formallySimilarWithoutInterrogative  -- Formally similar, without interrogative (33 languages)
  | formallySimilarWithInterrogative  -- Formally similar, with interrogative (43 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 56A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ConjunctionsAndUniversalQuantifiers
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 56A dataset (116 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abu", language := "Abun", iso := "kgr", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .formallySimilarWithInterrogative }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "arn", language := "Arabic (Borno Nigerian)", iso := "shu", value := .formallySimilarWithInterrogative }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .formallyDifferent }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .formallyDifferent }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .formallySimilarWithInterrogative }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .formallySimilarWithInterrogative }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .formallyDifferent }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .formallyDifferent }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "beg", language := "Begak-Ida'an", iso := "dbj", value := .formallySimilarWithInterrogative }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .formallySimilarWithInterrogative }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .formallyDifferent }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .formallySimilarWithInterrogative }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .formallySimilarWithInterrogative }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .formallySimilarWithInterrogative }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .formallySimilarWithInterrogative }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "eng", language := "English", iso := "eng", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .formallyDifferent }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .formallySimilarWithInterrogative }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .formallySimilarWithInterrogative }
  , { walsCode := "fre", language := "French", iso := "fra", value := .formallyDifferent }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .formallyDifferent }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .formallyDifferent }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .formallyDifferent }
  , { walsCode := "hsl", language := "Haisla", iso := "has", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .formallySimilarWithInterrogative }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .formallyDifferent }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .formallyDifferent }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .formallyDifferent }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .formallySimilarWithInterrogative }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .formallySimilarWithInterrogative }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .formallyDifferent }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .formallySimilarWithInterrogative }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .formallySimilarWithInterrogative }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .formallySimilarWithInterrogative }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .formallySimilarWithInterrogative }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .formallySimilarWithInterrogative }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .formallySimilarWithInterrogative }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .formallySimilarWithInterrogative }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "kda", language := "Konda", iso := "kfc", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .formallySimilarWithInterrogative }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .formallyDifferent }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .formallyDifferent }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .formallyDifferent }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .formallyDifferent }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .formallySimilarWithInterrogative }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .formallySimilarWithInterrogative }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .formallySimilarWithInterrogative }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .formallyDifferent }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .formallySimilarWithInterrogative }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .formallySimilarWithInterrogative }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .formallyDifferent }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .formallyDifferent }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .formallyDifferent }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .formallySimilarWithInterrogative }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .formallySimilarWithInterrogative }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .formallyDifferent }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .formallyDifferent }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .formallyDifferent }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .formallySimilarWithInterrogative }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .formallySimilarWithInterrogative }
  , { walsCode := "nvs", language := "Nivkh (South Sakhalin)", iso := "niv", value := .formallySimilarWithInterrogative }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .formallyDifferent }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .formallyDifferent }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .formallySimilarWithInterrogative }
  , { walsCode := "pen", language := "Pengo", iso := "peg", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .formallyDifferent }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .formallySimilarWithInterrogative }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .formallyDifferent }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .formallyDifferent }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .formallyDifferent }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .formallySimilarWithInterrogative }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .formallySimilarWithInterrogative }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .formallySimilarWithInterrogative }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .formallySimilarWithInterrogative }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .formallySimilarWithInterrogative }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .formallySimilarWithInterrogative }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .formallyDifferent }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .formallyDifferent }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .formallySimilarWithInterrogative }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .formallyDifferent }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .formallyDifferent }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .formallyDifferent }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .formallyDifferent }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .formallySimilarWithInterrogative }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .formallyDifferent }
  , { walsCode := "was", language := "Washo", iso := "was", value := .formallyDifferent }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .formallySimilarWithoutInterrogative }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .formallyDifferent }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .formallySimilarWithoutInterrogative }
  ]

-- Count verification
theorem total_count : allData.length = 116 := by native_decide

theorem count_formallyDifferent :
    (allData.filter (·.value == .formallyDifferent)).length = 40 := by native_decide
theorem count_formallySimilarWithoutInterrogative :
    (allData.filter (·.value == .formallySimilarWithoutInterrogative)).length = 33 := by native_decide
theorem count_formallySimilarWithInterrogative :
    (allData.filter (·.value == .formallySimilarWithInterrogative)).length = 43 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F56A
