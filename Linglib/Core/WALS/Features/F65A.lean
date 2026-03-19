import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 65A: Perfective/Imperfective Aspect
@cite{dahl-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 65A`.

Chapter 65, 222 languages.
-/

namespace Core.WALS.F65A

/-- WALS 65A values. -/
inductive PerfectiveImperfective where
  | grammaticalMarking  -- Grammatical marking (101 languages)
  | noGrammaticalMarking  -- No grammatical marking (121 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 65A dataset (222 languages). -/
def allData : List (Datapoint PerfectiveImperfective) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noGrammaticalMarking }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .grammaticalMarking }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noGrammaticalMarking }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .noGrammaticalMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noGrammaticalMarking }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .grammaticalMarking }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .grammaticalMarking }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .grammaticalMarking }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .grammaticalMarking }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noGrammaticalMarking }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noGrammaticalMarking }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noGrammaticalMarking }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .grammaticalMarking }
  , { walsCode := "atu", language := "Arabic (Tunisian)", iso := "aeb", value := .grammaticalMarking }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noGrammaticalMarking }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noGrammaticalMarking }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .grammaticalMarking }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noGrammaticalMarking }
  , { walsCode := "atc", language := "Atchin", iso := "upv", value := .noGrammaticalMarking }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .grammaticalMarking }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .grammaticalMarking }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .noGrammaticalMarking }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .grammaticalMarking }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .grammaticalMarking }
  , { walsCode := "blc", language := "Baluchi", iso := "bgn", value := .noGrammaticalMarking }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .grammaticalMarking }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noGrammaticalMarking }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noGrammaticalMarking }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .grammaticalMarking }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .grammaticalMarking }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .noGrammaticalMarking }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .grammaticalMarking }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .noGrammaticalMarking }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .grammaticalMarking }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .grammaticalMarking }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .noGrammaticalMarking }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .grammaticalMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noGrammaticalMarking }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .grammaticalMarking }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noGrammaticalMarking }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .grammaticalMarking }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .grammaticalMarking }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .grammaticalMarking }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .grammaticalMarking }
  , { walsCode := "cyn", language := "Cheyenne", iso := "chy", value := .noGrammaticalMarking }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .noGrammaticalMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .grammaticalMarking }
  , { walsCode := "cuu", language := "Chuukese", iso := "chk", value := .grammaticalMarking }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .grammaticalMarking }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .noGrammaticalMarking }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noGrammaticalMarking }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noGrammaticalMarking }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .grammaticalMarking }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .noGrammaticalMarking }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noGrammaticalMarking }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .grammaticalMarking }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noGrammaticalMarking }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .grammaticalMarking }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noGrammaticalMarking }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noGrammaticalMarking }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noGrammaticalMarking }
  , { walsCode := "fre", language := "French", iso := "fra", value := .grammaticalMarking }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .grammaticalMarking }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .grammaticalMarking }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noGrammaticalMarking }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noGrammaticalMarking }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .grammaticalMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .grammaticalMarking }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noGrammaticalMarking }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noGrammaticalMarking }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .noGrammaticalMarking }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .noGrammaticalMarking }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noGrammaticalMarking }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .grammaticalMarking }
  , { walsCode := "hwc", language := "Hawaiian Creole", iso := "hwc", value := .grammaticalMarking }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noGrammaticalMarking }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .grammaticalMarking }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .grammaticalMarking }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noGrammaticalMarking }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noGrammaticalMarking }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noGrammaticalMarking }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .grammaticalMarking }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noGrammaticalMarking }
  , { walsCode := "ins", language := "Inuktitut (Salluit)", iso := "ike", value := .noGrammaticalMarking }
  , { walsCode := "ise", language := "Isekiri", iso := "its", value := .noGrammaticalMarking }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .grammaticalMarking }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noGrammaticalMarking }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .noGrammaticalMarking }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noGrammaticalMarking }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .grammaticalMarking }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .grammaticalMarking }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noGrammaticalMarking }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .grammaticalMarking }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noGrammaticalMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noGrammaticalMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .grammaticalMarking }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noGrammaticalMarking }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noGrammaticalMarking }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noGrammaticalMarking }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noGrammaticalMarking }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .grammaticalMarking }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .grammaticalMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noGrammaticalMarking }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .grammaticalMarking }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .grammaticalMarking }
  , { walsCode := "kfc", language := "Kriol (Fitzroy Crossing)", iso := "rop", value := .noGrammaticalMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .grammaticalMarking }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .noGrammaticalMarking }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noGrammaticalMarking }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .grammaticalMarking }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noGrammaticalMarking }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noGrammaticalMarking }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noGrammaticalMarking }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noGrammaticalMarking }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .grammaticalMarking }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noGrammaticalMarking }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noGrammaticalMarking }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noGrammaticalMarking }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .grammaticalMarking }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .noGrammaticalMarking }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noGrammaticalMarking }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noGrammaticalMarking }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .noGrammaticalMarking }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .grammaticalMarking }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .grammaticalMarking }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .grammaticalMarking }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .grammaticalMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noGrammaticalMarking }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .noGrammaticalMarking }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noGrammaticalMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noGrammaticalMarking }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .grammaticalMarking }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noGrammaticalMarking }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noGrammaticalMarking }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .grammaticalMarking }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noGrammaticalMarking }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noGrammaticalMarking }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .grammaticalMarking }
  , { walsCode := "mtg", language := "Montagnais", iso := "moe", value := .noGrammaticalMarking }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .noGrammaticalMarking }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .grammaticalMarking }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .grammaticalMarking }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .grammaticalMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noGrammaticalMarking }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .grammaticalMarking }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noGrammaticalMarking }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .grammaticalMarking }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noGrammaticalMarking }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .noGrammaticalMarking }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noGrammaticalMarking }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .grammaticalMarking }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .grammaticalMarking }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .noGrammaticalMarking }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .grammaticalMarking }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noGrammaticalMarking }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .noGrammaticalMarking }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .grammaticalMarking }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .grammaticalMarking }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .grammaticalMarking }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .grammaticalMarking }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .grammaticalMarking }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .grammaticalMarking }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .noGrammaticalMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noGrammaticalMarking }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noGrammaticalMarking }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noGrammaticalMarking }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .noGrammaticalMarking }
  , { walsCode := "ren", language := "Rendille", iso := "rel", value := .grammaticalMarking }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .grammaticalMarking }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .grammaticalMarking }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .grammaticalMarking }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noGrammaticalMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noGrammaticalMarking }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noGrammaticalMarking }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .grammaticalMarking }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .grammaticalMarking }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .grammaticalMarking }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .grammaticalMarking }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noGrammaticalMarking }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .grammaticalMarking }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noGrammaticalMarking }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noGrammaticalMarking }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .grammaticalMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noGrammaticalMarking }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .noGrammaticalMarking }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .grammaticalMarking }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .grammaticalMarking }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .noGrammaticalMarking }
  , { walsCode := "tga", language := "Tangga", iso := "hrc", value := .noGrammaticalMarking }
  , { walsCode := "tem", language := "Tem", iso := "kdh", value := .grammaticalMarking }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .noGrammaticalMarking }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .grammaticalMarking }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noGrammaticalMarking }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .noGrammaticalMarking }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .noGrammaticalMarking }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noGrammaticalMarking }
  , { walsCode := "toj", language := "Tojolabal", iso := "toj", value := .grammaticalMarking }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .noGrammaticalMarking }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .grammaticalMarking }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .noGrammaticalMarking }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noGrammaticalMarking }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .grammaticalMarking }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .noGrammaticalMarking }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .grammaticalMarking }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noGrammaticalMarking }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noGrammaticalMarking }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noGrammaticalMarking }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .grammaticalMarking }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noGrammaticalMarking }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .grammaticalMarking }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .noGrammaticalMarking }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .grammaticalMarking }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .grammaticalMarking }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .grammaticalMarking }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .grammaticalMarking }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .noGrammaticalMarking }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noGrammaticalMarking }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .grammaticalMarking }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noGrammaticalMarking }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .grammaticalMarking }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .grammaticalMarking }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noGrammaticalMarking }
  ]

-- Count verification
theorem total_count : allData.length = 222 := by native_decide

theorem count_grammaticalMarking :
    (allData.filter (·.value == .grammaticalMarking)).length = 101 := by native_decide
theorem count_noGrammaticalMarking :
    (allData.filter (·.value == .noGrammaticalMarking)).length = 121 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F65A
