import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 66A: The Past Tense
@cite{dahl-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 66A`.

Chapter 66, 222 languages.
-/

namespace Core.WALS.F66A

/-- WALS 66A values. -/
inductive PastTenseType where
  | presentNoRemotenessDistinctions  -- Present, no remoteness distinctions (94 languages)
  | present23RemotenessDistinctions  -- Present, 2-3 remoteness distinctions (38 languages)
  | present4OrMoreRemotenessDistinctions  -- Present, 4 or more remoteness distinctions (2 languages)
  | noPastTense  -- No past tense (88 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 66A dataset (222 languages). -/
def allData : List (Datapoint PastTenseType) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noPastTense }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .presentNoRemotenessDistinctions }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noPastTense }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noPastTense }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noPastTense }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .present23RemotenessDistinctions }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .present23RemotenessDistinctions }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noPastTense }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .presentNoRemotenessDistinctions }
  , { walsCode := "atu", language := "Arabic (Tunisian)", iso := "aeb", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noPastTense }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noPastTense }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .presentNoRemotenessDistinctions }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .present23RemotenessDistinctions }
  , { walsCode := "atc", language := "Atchin", iso := "upv", value := .presentNoRemotenessDistinctions }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .presentNoRemotenessDistinctions }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .presentNoRemotenessDistinctions }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noPastTense }
  , { walsCode := "blc", language := "Baluchi", iso := "bgn", value := .present23RemotenessDistinctions }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .presentNoRemotenessDistinctions }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .present23RemotenessDistinctions }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noPastTense }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .present23RemotenessDistinctions }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .noPastTense }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .present23RemotenessDistinctions }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noPastTense }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .presentNoRemotenessDistinctions }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .present23RemotenessDistinctions }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noPastTense }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .noPastTense }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noPastTense }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .noPastTense }
  , { walsCode := "cyn", language := "Cheyenne", iso := "chy", value := .present23RemotenessDistinctions }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .present23RemotenessDistinctions }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noPastTense }
  , { walsCode := "cuu", language := "Chuukese", iso := "chk", value := .noPastTense }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .present4OrMoreRemotenessDistinctions }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .present23RemotenessDistinctions }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noPastTense }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .presentNoRemotenessDistinctions }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .present23RemotenessDistinctions }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .presentNoRemotenessDistinctions }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noPastTense }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noPastTense }
  , { walsCode := "eng", language := "English", iso := "eng", value := .presentNoRemotenessDistinctions }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noPastTense }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .presentNoRemotenessDistinctions }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .presentNoRemotenessDistinctions }
  , { walsCode := "fre", language := "French", iso := "fra", value := .presentNoRemotenessDistinctions }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .noPastTense }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ger", language := "German", iso := "deu", value := .presentNoRemotenessDistinctions }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .presentNoRemotenessDistinctions }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .present23RemotenessDistinctions }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .presentNoRemotenessDistinctions }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noPastTense }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .presentNoRemotenessDistinctions }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .presentNoRemotenessDistinctions }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .noPastTense }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noPastTense }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noPastTense }
  , { walsCode := "hwc", language := "Hawaiian Creole", iso := "hwc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .presentNoRemotenessDistinctions }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .presentNoRemotenessDistinctions }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .present23RemotenessDistinctions }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noPastTense }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .presentNoRemotenessDistinctions }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noPastTense }
  , { walsCode := "ins", language := "Inuktitut (Salluit)", iso := "ike", value := .present23RemotenessDistinctions }
  , { walsCode := "ise", language := "Isekiri", iso := "its", value := .noPastTense }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noPastTense }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .noPastTense }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .presentNoRemotenessDistinctions }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noPastTense }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .presentNoRemotenessDistinctions }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .presentNoRemotenessDistinctions }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noPastTense }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noPastTense }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noPastTense }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .present23RemotenessDistinctions }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .presentNoRemotenessDistinctions }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noPastTense }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noPastTense }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .present23RemotenessDistinctions }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noPastTense }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .present23RemotenessDistinctions }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noPastTense }
  , { walsCode := "kfc", language := "Kriol (Fitzroy Crossing)", iso := "rop", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noPastTense }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noPastTense }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noPastTense }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noPastTense }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noPastTense }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noPastTense }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noPastTense }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .presentNoRemotenessDistinctions }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noPastTense }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .presentNoRemotenessDistinctions }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .present23RemotenessDistinctions }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .present23RemotenessDistinctions }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .present23RemotenessDistinctions }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .presentNoRemotenessDistinctions }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noPastTense }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noPastTense }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .presentNoRemotenessDistinctions }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noPastTense }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .noPastTense }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .presentNoRemotenessDistinctions }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noPastTense }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .noPastTense }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noPastTense }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .presentNoRemotenessDistinctions }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .presentNoRemotenessDistinctions }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noPastTense }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noPastTense }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noPastTense }
  , { walsCode := "mtg", language := "Montagnais", iso := "moe", value := .presentNoRemotenessDistinctions }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .noPastTense }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .present23RemotenessDistinctions }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noPastTense }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .present23RemotenessDistinctions }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .noPastTense }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .presentNoRemotenessDistinctions }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .present23RemotenessDistinctions }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noPastTense }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .present23RemotenessDistinctions }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noPastTense }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .present23RemotenessDistinctions }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noPastTense }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .present23RemotenessDistinctions }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .presentNoRemotenessDistinctions }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noPastTense }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .noPastTense }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .noPastTense }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .presentNoRemotenessDistinctions }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .presentNoRemotenessDistinctions }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noPastTense }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .noPastTense }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .presentNoRemotenessDistinctions }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .presentNoRemotenessDistinctions }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ren", language := "Rendille", iso := "rel", value := .noPastTense }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .presentNoRemotenessDistinctions }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .presentNoRemotenessDistinctions }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noPastTense }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .present23RemotenessDistinctions }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noPastTense }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noPastTense }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .present23RemotenessDistinctions }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .noPastTense }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .present23RemotenessDistinctions }
  , { walsCode := "som", language := "Somali", iso := "som", value := .presentNoRemotenessDistinctions }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .presentNoRemotenessDistinctions }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .present23RemotenessDistinctions }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noPastTense }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .present23RemotenessDistinctions }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noPastTense }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tga", language := "Tangga", iso := "hrc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tem", language := "Tem", iso := "kdh", value := .noPastTense }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noPastTense }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .presentNoRemotenessDistinctions }
  , { walsCode := "toj", language := "Tojolabal", iso := "toj", value := .noPastTense }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .noPastTense }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .present23RemotenessDistinctions }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noPastTense }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .presentNoRemotenessDistinctions }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .present23RemotenessDistinctions }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .present23RemotenessDistinctions }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noPastTense }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .presentNoRemotenessDistinctions }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noPastTense }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noPastTense }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .present23RemotenessDistinctions }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .noPastTense }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .presentNoRemotenessDistinctions }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .noPastTense }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .present4OrMoreRemotenessDistinctions }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .presentNoRemotenessDistinctions }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .present23RemotenessDistinctions }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noPastTense }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .noPastTense }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noPastTense }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .present23RemotenessDistinctions }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .presentNoRemotenessDistinctions }
  ]

-- Count verification
theorem total_count : allData.length = 222 := by native_decide

theorem count_presentNoRemotenessDistinctions :
    (allData.filter (·.value == .presentNoRemotenessDistinctions)).length = 94 := by native_decide
theorem count_present23RemotenessDistinctions :
    (allData.filter (·.value == .present23RemotenessDistinctions)).length = 38 := by native_decide
theorem count_present4OrMoreRemotenessDistinctions :
    (allData.filter (·.value == .present4OrMoreRemotenessDistinctions)).length = 2 := by native_decide
theorem count_noPastTense :
    (allData.filter (·.value == .noPastTense)).length = 88 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F66A
