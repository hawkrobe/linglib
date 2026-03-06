/-!
# WALS Feature 79A: Suppletion According to Tense and Aspect
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 79A`.

Chapter 79, 193 languages.
-/

namespace Core.WALS.F79A

/-- WALS 79A values. -/
inductive SuppletionAccordingToTenseAndAspect where
  | tense  -- Tense (36 languages)
  | aspect  -- Aspect (10 languages)
  | tenseAndAspect  -- Tense and aspect (24 languages)
  | none  -- None (123 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 79A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : SuppletionAccordingToTenseAndAspect
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 79A dataset (193 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "xun", language := "!Xun (Ekoka)", iso := "knw", value := .none }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .tense }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .none }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .none }
  , { walsCode := "agw", language := "Alagwa", iso := "wbj", value := .none }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .tense }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .none }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .none }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .none }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .none }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .none }
  , { walsCode := "atu", language := "Arabic (Tunisian)", iso := "aeb", value := .none }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .none }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .none }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .tenseAndAspect }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .none }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .tense }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .none }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .none }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .none }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .tense }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .tenseAndAspect }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .tenseAndAspect }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .none }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .tense }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .tense }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .none }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .tenseAndAspect }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .none }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .none }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .none }
  , { walsCode := "car", language := "Carib", iso := "car", value := .tense }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .none }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .tense }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .aspect }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .none }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .none }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .none }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .tenseAndAspect }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .none }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .none }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .none }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .tense }
  , { walsCode := "eng", language := "English", iso := "eng", value := .tense }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .none }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .tense }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .none }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .none }
  , { walsCode := "fre", language := "French", iso := "fra", value := .tenseAndAspect }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .tense }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .none }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .none }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .tenseAndAspect }
  , { walsCode := "ger", language := "German", iso := "deu", value := .tense }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .none }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .none }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .tenseAndAspect }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .none }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .none }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .none }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .tense }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .tenseAndAspect }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .tense }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .none }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .tense }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .tense }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .none }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .none }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .aspect }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .none }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .none }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .tenseAndAspect }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .none }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .tenseAndAspect }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .none }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .none }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .tense }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .tense }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .none }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .none }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .tense }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .none }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .none }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .none }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .none }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .none }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .none }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .none }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .none }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .none }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .none }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .tense }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .none }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .none }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .none }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .none }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .tense }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .none }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .tenseAndAspect }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .none }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .tense }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .tense }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .none }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .none }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .none }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .none }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .none }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .none }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .none }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .none }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .aspect }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .none }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .none }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .none }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .tense }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .none }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .none }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .none }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .aspect }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .none }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .tense }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .none }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .none }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .tenseAndAspect }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .tense }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .none }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .none }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .none }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .none }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .none }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .aspect }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .aspect }
  , { walsCode := "orb", language := "Oromo (Boraana)", iso := "gax", value := .none }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .tense }
  , { walsCode := "oix", language := "Otomí (Ixtenco)", iso := "otz", value := .aspect }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .tenseAndAspect }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .none }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .tenseAndAspect }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .tense }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .none }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .tenseAndAspect }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .none }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .none }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .none }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .none }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .none }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .tenseAndAspect }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .none }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .none }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .none }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .none }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .none }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .none }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .none }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .tenseAndAspect }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .none }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .none }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .aspect }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .tenseAndAspect }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .tenseAndAspect }
  , { walsCode := "sou", language := "Sorbian (Upper)", iso := "hsb", value := .tenseAndAspect }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .tenseAndAspect }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .none }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .tense }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .tenseAndAspect }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .none }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .tense }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .none }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .none }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .aspect }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .none }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .none }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .none }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .tense }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .tense }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .tense }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .tenseAndAspect }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .tense }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .none }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .none }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .none }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .none }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .aspect }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .none }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .none }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .none }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .none }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .tense }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .none }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .none }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .none }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .none }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .none }
  ]

-- Count verification
theorem total_count : allData.length = 193 := by native_decide

theorem count_tense :
    (allData.filter (·.value == .tense)).length = 36 := by native_decide
theorem count_aspect :
    (allData.filter (·.value == .aspect)).length = 10 := by native_decide
theorem count_tenseAndAspect :
    (allData.filter (·.value == .tenseAndAspect)).length = 24 := by native_decide
theorem count_none :
    (allData.filter (·.value == .none)).length = 123 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F79A
