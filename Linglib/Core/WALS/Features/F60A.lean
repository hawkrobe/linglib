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
  | weaklyDifferentiated  -- Weakly differentiated (15 languages)
  | genitivesAndAdjectivesCollapsed  -- Genitives and adjectives collapsed (8 languages)
  | genitivesAndRelativeClausesCollapsed  -- Genitives and relative clauses collapsed (2 languages)
  | adjectivesAndRelativeClausesCollapsed  -- Adjectives and relative clauses collapsed (33 languages)
  | moderatelyDifferentiatedInOtherWays  -- Moderately differentiated in other ways (3 languages)
  | highlyDifferentiated  -- Highly differentiated (77 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 60A dataset (138 languages). -/
def allData : List (Datapoint GenitivesAdjectivesAndRelativeClauses) :=
  [ { walsCode := "xam", language := "/Xam", iso := "xam", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .highlyDifferentiated }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .highlyDifferentiated }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "agw", language := "Alagwa", iso := "wbj", value := .highlyDifferentiated }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .highlyDifferentiated }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .highlyDifferentiated }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .highlyDifferentiated }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .highlyDifferentiated }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .highlyDifferentiated }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .highlyDifferentiated }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .moderatelyDifferentiatedInOtherWays }
  , { walsCode := "beg", language := "Begak-Ida'an", iso := "dbj", value := .weaklyDifferentiated }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .highlyDifferentiated }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .highlyDifferentiated }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .genitivesAndRelativeClausesCollapsed }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .highlyDifferentiated }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .weaklyDifferentiated }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .weaklyDifferentiated }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .highlyDifferentiated }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .highlyDifferentiated }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .highlyDifferentiated }
  , { walsCode := "dat", language := "Datooga", iso := "tcc", value := .highlyDifferentiated }
  , { walsCode := "eng", language := "English", iso := "eng", value := .highlyDifferentiated }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .highlyDifferentiated }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .highlyDifferentiated }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .highlyDifferentiated }
  , { walsCode := "fre", language := "French", iso := "fra", value := .highlyDifferentiated }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .highlyDifferentiated }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .highlyDifferentiated }
  , { walsCode := "gil", language := "Gilaki", iso := "glk", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .highlyDifferentiated }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .highlyDifferentiated }
  , { walsCode := "hmd", language := "Hmong Daw", iso := "mww", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .highlyDifferentiated }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .highlyDifferentiated }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .highlyDifferentiated }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .highlyDifferentiated }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .highlyDifferentiated }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .weaklyDifferentiated }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .highlyDifferentiated }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .highlyDifferentiated }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .highlyDifferentiated }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .highlyDifferentiated }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .highlyDifferentiated }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .highlyDifferentiated }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .highlyDifferentiated }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .highlyDifferentiated }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .weaklyDifferentiated }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .highlyDifferentiated }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .highlyDifferentiated }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .highlyDifferentiated }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .highlyDifferentiated }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .highlyDifferentiated }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .weaklyDifferentiated }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .highlyDifferentiated }
  , { walsCode := "lov", language := "Loven", iso := "lbo", value := .weaklyDifferentiated }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .highlyDifferentiated }
  , { walsCode := "mks", language := "Makassar", iso := "mak", value := .highlyDifferentiated }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .weaklyDifferentiated }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .highlyDifferentiated }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .highlyDifferentiated }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .highlyDifferentiated }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .weaklyDifferentiated }
  , { walsCode := "mzn", language := "Mazanderani", iso := "mzn", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .highlyDifferentiated }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .weaklyDifferentiated }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .weaklyDifferentiated }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .highlyDifferentiated }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .weaklyDifferentiated }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .highlyDifferentiated }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .moderatelyDifferentiatedInOtherWays }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .highlyDifferentiated }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .genitivesAndRelativeClausesCollapsed }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .weaklyDifferentiated }
  , { walsCode := "nvs", language := "Nivkh (South Sakhalin)", iso := "niv", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .highlyDifferentiated }
  , { walsCode := "pad", language := "Padoe", iso := "pdo", value := .weaklyDifferentiated }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .highlyDifferentiated }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "pil", language := "Pileni", iso := "piv", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .highlyDifferentiated }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .highlyDifferentiated }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .highlyDifferentiated }
  , { walsCode := "rcp", language := "Russian-Chinese Pidgin (Birobidjan)", iso := "", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .highlyDifferentiated }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .weaklyDifferentiated }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .highlyDifferentiated }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .highlyDifferentiated }
  , { walsCode := "so", language := "So", iso := "teu", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .highlyDifferentiated }
  , { walsCode := "swv", language := "Swedish (Västerbotten)", iso := "swe", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .highlyDifferentiated }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .highlyDifferentiated }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .moderatelyDifferentiatedInOtherWays }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .highlyDifferentiated }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .highlyDifferentiated }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .highlyDifferentiated }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .highlyDifferentiated }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .highlyDifferentiated }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .highlyDifferentiated }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .adjectivesAndRelativeClausesCollapsed }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .highlyDifferentiated }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .highlyDifferentiated }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .genitivesAndAdjectivesCollapsed }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .highlyDifferentiated }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .highlyDifferentiated }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .highlyDifferentiated }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .highlyDifferentiated }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .highlyDifferentiated }
  ]

-- Count verification
theorem total_count : allData.length = 138 := by native_decide

theorem count_weaklyDifferentiated :
    (allData.filter (·.value == .weaklyDifferentiated)).length = 15 := by native_decide
theorem count_genitivesAndAdjectivesCollapsed :
    (allData.filter (·.value == .genitivesAndAdjectivesCollapsed)).length = 8 := by native_decide
theorem count_genitivesAndRelativeClausesCollapsed :
    (allData.filter (·.value == .genitivesAndRelativeClausesCollapsed)).length = 2 := by native_decide
theorem count_adjectivesAndRelativeClausesCollapsed :
    (allData.filter (·.value == .adjectivesAndRelativeClausesCollapsed)).length = 33 := by native_decide
theorem count_moderatelyDifferentiatedInOtherWays :
    (allData.filter (·.value == .moderatelyDifferentiatedInOtherWays)).length = 3 := by native_decide
theorem count_highlyDifferentiated :
    (allData.filter (·.value == .highlyDifferentiated)).length = 77 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F60A
