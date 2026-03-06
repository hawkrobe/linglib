/-!
# WALS Feature 108B: Productivity of the Antipassive Construction
@cite{polinsky-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 108B`.

Chapter 108, 186 languages.
-/

namespace Core.WALS.F108B

/-- WALS 108B values. -/
inductive AntipassiveProductivity where
  | productive  -- Productive (24 languages)
  | partiallyProductive  -- Partially productive (14 languages)
  | notProductive  -- Not productive (2 languages)
  | noAntipassive  -- No antipassive (146 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 108B datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : AntipassiveProductivity
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 108B dataset (186 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noAntipassive }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noAntipassive }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noAntipassive }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noAntipassive }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noAntipassive }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noAntipassive }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noAntipassive }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .productive }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noAntipassive }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noAntipassive }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noAntipassive }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noAntipassive }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noAntipassive }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .partiallyProductive }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noAntipassive }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noAntipassive }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noAntipassive }
  , { walsCode := "bez", language := "Bezhta", iso := "kap", value := .partiallyProductive }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noAntipassive }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noAntipassive }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noAntipassive }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .productive }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .noAntipassive }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .partiallyProductive }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .productive }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .noAntipassive }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .notProductive }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .productive }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .productive }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .productive }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noAntipassive }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noAntipassive }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .partiallyProductive }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .partiallyProductive }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noAntipassive }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noAntipassive }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .productive }
  , { walsCode := "eml", language := "Embaloh", iso := "emb", value := .productive }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noAntipassive }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noAntipassive }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noAntipassive }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noAntipassive }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noAntipassive }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noAntipassive }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noAntipassive }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .noAntipassive }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noAntipassive }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noAntipassive }
  , { walsCode := "gdi", language := "Godié", iso := "god", value := .noAntipassive }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .partiallyProductive }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .partiallyProductive }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noAntipassive }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noAntipassive }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .productive }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noAntipassive }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .productive }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noAntipassive }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noAntipassive }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noAntipassive }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noAntipassive }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noAntipassive }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noAntipassive }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .partiallyProductive }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noAntipassive }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noAntipassive }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noAntipassive }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noAntipassive }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noAntipassive }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noAntipassive }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noAntipassive }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .productive }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noAntipassive }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noAntipassive }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .productive }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .noAntipassive }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noAntipassive }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noAntipassive }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .productive }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noAntipassive }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noAntipassive }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noAntipassive }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noAntipassive }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noAntipassive }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .noAntipassive }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noAntipassive }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noAntipassive }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noAntipassive }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .partiallyProductive }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .noAntipassive }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noAntipassive }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noAntipassive }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noAntipassive }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noAntipassive }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .productive }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .productive }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noAntipassive }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .productive }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noAntipassive }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .partiallyProductive }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noAntipassive }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .notProductive }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noAntipassive }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .noAntipassive }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noAntipassive }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noAntipassive }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noAntipassive }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noAntipassive }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .productive }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noAntipassive }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noAntipassive }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noAntipassive }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noAntipassive }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noAntipassive }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noAntipassive }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noAntipassive }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noAntipassive }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noAntipassive }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noAntipassive }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noAntipassive }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noAntipassive }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .productive }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noAntipassive }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noAntipassive }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noAntipassive }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noAntipassive }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .productive }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noAntipassive }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noAntipassive }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noAntipassive }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noAntipassive }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .productive }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .noAntipassive }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noAntipassive }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noAntipassive }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noAntipassive }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noAntipassive }
  , { walsCode := "pmc", language := "Pomo (Central)", iso := "poo", value := .noAntipassive }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .noAntipassive }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noAntipassive }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noAntipassive }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noAntipassive }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noAntipassive }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noAntipassive }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noAntipassive }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noAntipassive }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noAntipassive }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noAntipassive }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noAntipassive }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noAntipassive }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noAntipassive }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noAntipassive }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noAntipassive }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noAntipassive }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .noAntipassive }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .noAntipassive }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noAntipassive }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noAntipassive }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .partiallyProductive }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noAntipassive }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .partiallyProductive }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noAntipassive }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noAntipassive }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noAntipassive }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .productive }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .noAntipassive }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noAntipassive }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noAntipassive }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noAntipassive }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noAntipassive }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noAntipassive }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noAntipassive }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .productive }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noAntipassive }
  , { walsCode := "wgu", language := "Warrongo", iso := "wrg", value := .partiallyProductive }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noAntipassive }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noAntipassive }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noAntipassive }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noAntipassive }
  , { walsCode := "yaz", language := "Yazgulyam", iso := "yah", value := .noAntipassive }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .productive }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noAntipassive }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noAntipassive }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .productive }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noAntipassive }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .partiallyProductive }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noAntipassive }
  ]

-- Count verification
theorem total_count : allData.length = 186 := by native_decide

theorem count_productive :
    (allData.filter (·.value == .productive)).length = 24 := by native_decide
theorem count_partiallyProductive :
    (allData.filter (·.value == .partiallyProductive)).length = 14 := by native_decide
theorem count_notProductive :
    (allData.filter (·.value == .notProductive)).length = 2 := by native_decide
theorem count_noAntipassive :
    (allData.filter (·.value == .noAntipassive)).length = 146 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F108B
