/-!
# WALS Feature 22A: Inflectional Synthesis of the Verb
@cite{bickel-nichols-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 22A`.

Chapter 22, 145 languages.
-/

namespace Core.WALS.F22A

/-- WALS 22A values. -/
inductive InflectionalSynthesis where
  | categoryPerWord0_1  -- 0-1 category per word (5 languages)
  | categoriesPerWord2_3  -- 2-3 categories per word (24 languages)
  | categoriesPerWord4_5  -- 4-5 categories per word (52 languages)
  | categoriesPerWord6_7  -- 6-7 categories per word (31 languages)
  | categoriesPerWord8_9  -- 8-9 categories per word (24 languages)
  | categoriesPerWord10_11  -- 10-11 categories per word (7 languages)
  | categoriesPerWord12_13  -- 12-13 categories per word (2 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 22A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : InflectionalSynthesis
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 22A dataset (145 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .categoriesPerWord10_11 }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .categoriesPerWord4_5 }
  , { walsCode := "ash", language := "Adyghe (Shapsugh)", iso := "ady", value := .categoriesPerWord8_9 }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .categoriesPerWord4_5 }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .categoriesPerWord10_11 }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .categoriesPerWord6_7 }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .categoriesPerWord6_7 }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .categoriesPerWord6_7 }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .categoriesPerWord4_5 }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .categoriesPerWord2_3 }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .categoriesPerWord4_5 }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .categoriesPerWord4_5 }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .categoriesPerWord8_9 }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .categoriesPerWord8_9 }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .categoriesPerWord8_9 }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .categoriesPerWord6_7 }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .categoriesPerWord4_5 }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .categoriesPerWord4_5 }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .categoriesPerWord4_5 }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .categoriesPerWord6_7 }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .categoriesPerWord6_7 }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .categoriesPerWord4_5 }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .categoriesPerWord2_3 }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .categoriesPerWord2_3 }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .categoriesPerWord8_9 }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .categoriesPerWord4_5 }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .categoriesPerWord6_7 }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .categoriesPerWord6_7 }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .categoriesPerWord10_11 }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .categoriesPerWord4_5 }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .categoriesPerWord6_7 }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .categoriesPerWord8_9 }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .categoriesPerWord6_7 }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .categoriesPerWord4_5 }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .categoriesPerWord4_5 }
  , { walsCode := "eng", language := "English", iso := "eng", value := .categoriesPerWord2_3 }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .categoriesPerWord4_5 }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .categoriesPerWord6_7 }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .categoriesPerWord6_7 }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .categoriesPerWord2_3 }
  , { walsCode := "fre", language := "French", iso := "fra", value := .categoriesPerWord4_5 }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .categoriesPerWord2_3 }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .categoriesPerWord8_9 }
  , { walsCode := "ger", language := "German", iso := "deu", value := .categoriesPerWord2_3 }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .categoriesPerWord6_7 }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .categoriesPerWord6_7 }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .categoriesPerWord4_5 }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .categoriesPerWord4_5 }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .categoriesPerWord4_5 }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .categoriesPerWord8_9 }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .categoriesPerWord2_3 }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .categoriesPerWord6_7 }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .categoriesPerWord4_5 }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .categoriesPerWord2_3 }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .categoriesPerWord4_5 }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .categoriesPerWord2_3 }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .categoriesPerWord4_5 }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .categoriesPerWord4_5 }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .categoriesPerWord6_7 }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .categoriesPerWord10_11 }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .categoriesPerWord4_5 }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .categoriesPerWord10_11 }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .categoriesPerWord4_5 }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .categoriesPerWord4_5 }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .categoriesPerWord2_3 }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .categoriesPerWord2_3 }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .categoriesPerWord8_9 }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .categoriesPerWord4_5 }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .categoriesPerWord2_3 }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .categoriesPerWord6_7 }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .categoriesPerWord2_3 }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .categoriesPerWord4_5 }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .categoriesPerWord8_9 }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .categoriesPerWord2_3 }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .categoriesPerWord12_13 }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .categoriesPerWord6_7 }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .categoriesPerWord2_3 }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .categoriesPerWord4_5 }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .categoriesPerWord4_5 }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .categoriesPerWord8_9 }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .categoriesPerWord10_11 }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .categoriesPerWord6_7 }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .categoriesPerWord4_5 }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .categoriesPerWord2_3 }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .categoriesPerWord8_9 }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .categoriesPerWord6_7 }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .categoriesPerWord4_5 }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .categoryPerWord0_1 }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .categoriesPerWord6_7 }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .categoriesPerWord8_9 }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .categoriesPerWord8_9 }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .categoriesPerWord2_3 }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .categoriesPerWord4_5 }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .categoryPerWord0_1 }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .categoriesPerWord4_5 }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .categoriesPerWord4_5 }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .categoriesPerWord4_5 }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .categoriesPerWord6_7 }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .categoryPerWord0_1 }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .categoriesPerWord6_7 }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .categoriesPerWord8_9 }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .categoriesPerWord4_5 }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .categoriesPerWord2_3 }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .categoriesPerWord4_5 }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .categoriesPerWord6_7 }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .categoriesPerWord4_5 }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .categoriesPerWord8_9 }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .categoriesPerWord8_9 }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .categoriesPerWord6_7 }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .categoriesPerWord8_9 }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .categoriesPerWord4_5 }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .categoriesPerWord4_5 }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .categoriesPerWord4_5 }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .categoriesPerWord8_9 }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .categoriesPerWord4_5 }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .categoriesPerWord8_9 }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .categoriesPerWord2_3 }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .categoriesPerWord8_9 }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .categoriesPerWord4_5 }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .categoryPerWord0_1 }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .categoriesPerWord4_5 }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .categoriesPerWord6_7 }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .categoriesPerWord8_9 }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .categoriesPerWord4_5 }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .categoriesPerWord8_9 }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .categoriesPerWord2_3 }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .categoriesPerWord4_5 }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .categoriesPerWord2_3 }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .categoriesPerWord2_3 }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .categoriesPerWord4_5 }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .categoriesPerWord4_5 }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .categoriesPerWord8_9 }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .categoriesPerWord6_7 }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .categoriesPerWord6_7 }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .categoryPerWord0_1 }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .categoriesPerWord4_5 }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .categoriesPerWord4_5 }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .categoriesPerWord12_13 }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .categoriesPerWord2_3 }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .categoriesPerWord10_11 }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .categoriesPerWord4_5 }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .categoriesPerWord6_7 }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .categoriesPerWord6_7 }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .categoriesPerWord6_7 }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .categoriesPerWord4_5 }
  ]

-- Count verification
theorem total_count : allData.length = 145 := by native_decide

theorem count_categoryPerWord0_1 :
    (allData.filter (·.value == .categoryPerWord0_1)).length = 5 := by native_decide
theorem count_categoriesPerWord2_3 :
    (allData.filter (·.value == .categoriesPerWord2_3)).length = 24 := by native_decide
theorem count_categoriesPerWord4_5 :
    (allData.filter (·.value == .categoriesPerWord4_5)).length = 52 := by native_decide
theorem count_categoriesPerWord6_7 :
    (allData.filter (·.value == .categoriesPerWord6_7)).length = 31 := by native_decide
theorem count_categoriesPerWord8_9 :
    (allData.filter (·.value == .categoriesPerWord8_9)).length = 24 := by native_decide
theorem count_categoriesPerWord10_11 :
    (allData.filter (·.value == .categoriesPerWord10_11)).length = 7 := by native_decide
theorem count_categoriesPerWord12_13 :
    (allData.filter (·.value == .categoriesPerWord12_13)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F22A
