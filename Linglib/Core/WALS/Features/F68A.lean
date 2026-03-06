/-!
# WALS Feature 68A: The Perfect
@cite{dahl-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 68A`.

Chapter 68, 222 languages.
-/

namespace Core.WALS.F68A

/-- WALS 68A values. -/
inductive PerfectType where
  | fromPossessive  -- From possessive (7 languages)
  | fromFinishAlready  -- From 'finish', 'already' (21 languages)
  | otherPerfect  -- Other perfect (80 languages)
  | noPerfect  -- No perfect (114 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 68A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PerfectType
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 68A dataset (222 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noPerfect }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .otherPerfect }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noPerfect }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .fromFinishAlready }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noPerfect }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .otherPerfect }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noPerfect }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noPerfect }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .otherPerfect }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .fromFinishAlready }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .otherPerfect }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noPerfect }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noPerfect }
  , { walsCode := "atu", language := "Arabic (Tunisian)", iso := "aeb", value := .noPerfect }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noPerfect }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noPerfect }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .otherPerfect }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .otherPerfect }
  , { walsCode := "atc", language := "Atchin", iso := "upv", value := .noPerfect }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .noPerfect }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noPerfect }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .otherPerfect }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .otherPerfect }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noPerfect }
  , { walsCode := "blc", language := "Baluchi", iso := "bgn", value := .otherPerfect }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .noPerfect }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noPerfect }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .otherPerfect }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .otherPerfect }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .otherPerfect }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .otherPerfect }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noPerfect }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .fromFinishAlready }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .otherPerfect }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .otherPerfect }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .fromFinishAlready }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .otherPerfect }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .fromFinishAlready }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .otherPerfect }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noPerfect }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .otherPerfect }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .noPerfect }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noPerfect }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .otherPerfect }
  , { walsCode := "cyn", language := "Cheyenne", iso := "chy", value := .noPerfect }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .otherPerfect }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noPerfect }
  , { walsCode := "cuu", language := "Chuukese", iso := "chk", value := .noPerfect }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .noPerfect }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .otherPerfect }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noPerfect }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noPerfect }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noPerfect }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .noPerfect }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noPerfect }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .fromFinishAlready }
  , { walsCode := "eng", language := "English", iso := "eng", value := .fromPossessive }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .otherPerfect }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noPerfect }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .fromFinishAlready }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .otherPerfect }
  , { walsCode := "fre", language := "French", iso := "fra", value := .fromPossessive }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .otherPerfect }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noPerfect }
  , { walsCode := "ger", language := "German", iso := "deu", value := .fromPossessive }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noPerfect }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .otherPerfect }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .fromPossessive }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noPerfect }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noPerfect }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .noPerfect }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .noPerfect }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noPerfect }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noPerfect }
  , { walsCode := "hwc", language := "Hawaiian Creole", iso := "hwc", value := .noPerfect }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noPerfect }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .otherPerfect }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noPerfect }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noPerfect }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noPerfect }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .fromPossessive }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .otherPerfect }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .fromFinishAlready }
  , { walsCode := "ins", language := "Inuktitut (Salluit)", iso := "ike", value := .fromFinishAlready }
  , { walsCode := "ise", language := "Isekiri", iso := "its", value := .fromFinishAlready }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noPerfect }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noPerfect }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .fromFinishAlready }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .otherPerfect }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noPerfect }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .noPerfect }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .otherPerfect }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .otherPerfect }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .otherPerfect }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noPerfect }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noPerfect }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .otherPerfect }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .otherPerfect }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .fromFinishAlready }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .fromFinishAlready }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .otherPerfect }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noPerfect }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noPerfect }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noPerfect }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noPerfect }
  , { walsCode := "kfc", language := "Kriol (Fitzroy Crossing)", iso := "rop", value := .noPerfect }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .otherPerfect }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .otherPerfect }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noPerfect }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .noPerfect }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noPerfect }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .otherPerfect }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .otherPerfect }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noPerfect }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noPerfect }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .fromFinishAlready }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .otherPerfect }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noPerfect }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .otherPerfect }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .otherPerfect }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .otherPerfect }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .otherPerfect }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .otherPerfect }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noPerfect }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noPerfect }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .noPerfect }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noPerfect }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noPerfect }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .otherPerfect }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .otherPerfect }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noPerfect }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .otherPerfect }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noPerfect }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noPerfect }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noPerfect }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noPerfect }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .fromFinishAlready }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noPerfect }
  , { walsCode := "mtg", language := "Montagnais", iso := "moe", value := .otherPerfect }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .otherPerfect }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .otherPerfect }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .otherPerfect }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .otherPerfect }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noPerfect }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .noPerfect }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noPerfect }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .otherPerfect }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noPerfect }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .noPerfect }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noPerfect }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .otherPerfect }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noPerfect }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .noPerfect }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .otherPerfect }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .otherPerfect }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .otherPerfect }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .noPerfect }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .otherPerfect }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noPerfect }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noPerfect }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .noPerfect }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .otherPerfect }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .noPerfect }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noPerfect }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .otherPerfect }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .otherPerfect }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .otherPerfect }
  , { walsCode := "ren", language := "Rendille", iso := "rel", value := .noPerfect }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noPerfect }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .otherPerfect }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noPerfect }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noPerfect }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noPerfect }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .fromFinishAlready }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noPerfect }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .otherPerfect }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .noPerfect }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .otherPerfect }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noPerfect }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .fromPossessive }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noPerfect }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .fromFinishAlready }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .otherPerfect }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .otherPerfect }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .fromPossessive }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noPerfect }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .otherPerfect }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .otherPerfect }
  , { walsCode := "tga", language := "Tangga", iso := "hrc", value := .noPerfect }
  , { walsCode := "tem", language := "Tem", iso := "kdh", value := .otherPerfect }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .fromFinishAlready }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .fromFinishAlready }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .fromFinishAlready }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .noPerfect }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .otherPerfect }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noPerfect }
  , { walsCode := "toj", language := "Tojolabal", iso := "toj", value := .otherPerfect }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .noPerfect }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .noPerfect }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .otherPerfect }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noPerfect }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noPerfect }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .otherPerfect }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .otherPerfect }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .otherPerfect }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noPerfect }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noPerfect }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noPerfect }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noPerfect }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .noPerfect }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .otherPerfect }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .noPerfect }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .otherPerfect }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noPerfect }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noPerfect }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .noPerfect }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .fromFinishAlready }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .noPerfect }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noPerfect }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .otherPerfect }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .otherPerfect }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noPerfect }
  ]

-- Count verification
theorem total_count : allData.length = 222 := by native_decide

theorem count_fromPossessive :
    (allData.filter (·.value == .fromPossessive)).length = 7 := by native_decide
theorem count_fromFinishAlready :
    (allData.filter (·.value == .fromFinishAlready)).length = 21 := by native_decide
theorem count_otherPerfect :
    (allData.filter (·.value == .otherPerfect)).length = 80 := by native_decide
theorem count_noPerfect :
    (allData.filter (·.value == .noPerfect)).length = 114 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F68A
