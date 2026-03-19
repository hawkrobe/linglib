import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 67A: The Future Tense
@cite{dahl-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 67A`.

Chapter 67, 222 languages.
-/

namespace Core.WALS.F67A

/-- WALS 67A values. -/
inductive FutureTenseType where
  | inflectionalFutureExists  -- Inflectional future exists (110 languages)
  | noInflectionalFuture  -- No inflectional future (112 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 67A dataset (222 languages). -/
def allData : List (Datapoint FutureTenseType) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noInflectionalFuture }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .inflectionalFutureExists }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noInflectionalFuture }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .noInflectionalFuture }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noInflectionalFuture }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .inflectionalFutureExists }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .inflectionalFutureExists }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .inflectionalFutureExists }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .inflectionalFutureExists }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .inflectionalFutureExists }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noInflectionalFuture }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .inflectionalFutureExists }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .inflectionalFutureExists }
  , { walsCode := "atu", language := "Arabic (Tunisian)", iso := "aeb", value := .noInflectionalFuture }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noInflectionalFuture }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .inflectionalFutureExists }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noInflectionalFuture }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .inflectionalFutureExists }
  , { walsCode := "atc", language := "Atchin", iso := "upv", value := .noInflectionalFuture }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .noInflectionalFuture }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .inflectionalFutureExists }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .inflectionalFutureExists }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .inflectionalFutureExists }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noInflectionalFuture }
  , { walsCode := "blc", language := "Baluchi", iso := "bgn", value := .inflectionalFutureExists }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .inflectionalFutureExists }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noInflectionalFuture }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noInflectionalFuture }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .inflectionalFutureExists }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noInflectionalFuture }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .inflectionalFutureExists }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noInflectionalFuture }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .inflectionalFutureExists }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noInflectionalFuture }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noInflectionalFuture }
  , { walsCode := "bui", language := "Buli (in Indonesia)", iso := "bzq", value := .inflectionalFutureExists }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .noInflectionalFuture }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noInflectionalFuture }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .inflectionalFutureExists }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noInflectionalFuture }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noInflectionalFuture }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .noInflectionalFuture }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noInflectionalFuture }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .inflectionalFutureExists }
  , { walsCode := "cyn", language := "Cheyenne", iso := "chy", value := .inflectionalFutureExists }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .inflectionalFutureExists }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .inflectionalFutureExists }
  , { walsCode := "cuu", language := "Chuukese", iso := "chk", value := .noInflectionalFuture }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .inflectionalFutureExists }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .inflectionalFutureExists }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noInflectionalFuture }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .inflectionalFutureExists }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .inflectionalFutureExists }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .noInflectionalFuture }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .inflectionalFutureExists }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .inflectionalFutureExists }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noInflectionalFuture }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .inflectionalFutureExists }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .inflectionalFutureExists }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noInflectionalFuture }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noInflectionalFuture }
  , { walsCode := "fre", language := "French", iso := "fra", value := .inflectionalFutureExists }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .inflectionalFutureExists }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .inflectionalFutureExists }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noInflectionalFuture }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .inflectionalFutureExists }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .inflectionalFutureExists }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noInflectionalFuture }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .inflectionalFutureExists }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .inflectionalFutureExists }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .inflectionalFutureExists }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .inflectionalFutureExists }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noInflectionalFuture }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noInflectionalFuture }
  , { walsCode := "hwc", language := "Hawaiian Creole", iso := "hwc", value := .noInflectionalFuture }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .inflectionalFutureExists }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .inflectionalFutureExists }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noInflectionalFuture }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noInflectionalFuture }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noInflectionalFuture }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noInflectionalFuture }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .inflectionalFutureExists }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noInflectionalFuture }
  , { walsCode := "ins", language := "Inuktitut (Salluit)", iso := "ike", value := .inflectionalFutureExists }
  , { walsCode := "ise", language := "Isekiri", iso := "its", value := .noInflectionalFuture }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noInflectionalFuture }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noInflectionalFuture }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .noInflectionalFuture }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .inflectionalFutureExists }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noInflectionalFuture }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .inflectionalFutureExists }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .inflectionalFutureExists }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .inflectionalFutureExists }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .inflectionalFutureExists }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .inflectionalFutureExists }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noInflectionalFuture }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .inflectionalFutureExists }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noInflectionalFuture }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noInflectionalFuture }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noInflectionalFuture }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .noInflectionalFuture }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .inflectionalFutureExists }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .inflectionalFutureExists }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noInflectionalFuture }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noInflectionalFuture }
  , { walsCode := "kfc", language := "Kriol (Fitzroy Crossing)", iso := "rop", value := .noInflectionalFuture }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noInflectionalFuture }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .inflectionalFutureExists }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noInflectionalFuture }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .inflectionalFutureExists }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .inflectionalFutureExists }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noInflectionalFuture }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noInflectionalFuture }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noInflectionalFuture }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noInflectionalFuture }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noInflectionalFuture }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .inflectionalFutureExists }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .inflectionalFutureExists }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .inflectionalFutureExists }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .inflectionalFutureExists }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .inflectionalFutureExists }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .inflectionalFutureExists }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .inflectionalFutureExists }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noInflectionalFuture }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noInflectionalFuture }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .noInflectionalFuture }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noInflectionalFuture }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noInflectionalFuture }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .noInflectionalFuture }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noInflectionalFuture }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .inflectionalFutureExists }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .inflectionalFutureExists }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .inflectionalFutureExists }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .inflectionalFutureExists }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .inflectionalFutureExists }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noInflectionalFuture }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noInflectionalFuture }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .inflectionalFutureExists }
  , { walsCode := "mtg", language := "Montagnais", iso := "moe", value := .inflectionalFutureExists }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .noInflectionalFuture }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .inflectionalFutureExists }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noInflectionalFuture }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noInflectionalFuture }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .inflectionalFutureExists }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .inflectionalFutureExists }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .inflectionalFutureExists }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .noInflectionalFuture }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noInflectionalFuture }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .inflectionalFutureExists }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .inflectionalFutureExists }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noInflectionalFuture }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .inflectionalFutureExists }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .inflectionalFutureExists }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noInflectionalFuture }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noInflectionalFuture }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .noInflectionalFuture }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .inflectionalFutureExists }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .inflectionalFutureExists }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noInflectionalFuture }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noInflectionalFuture }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .noInflectionalFuture }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .inflectionalFutureExists }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .noInflectionalFuture }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .inflectionalFutureExists }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .inflectionalFutureExists }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noInflectionalFuture }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .noInflectionalFuture }
  , { walsCode := "ren", language := "Rendille", iso := "rel", value := .noInflectionalFuture }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noInflectionalFuture }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .inflectionalFutureExists }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noInflectionalFuture }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noInflectionalFuture }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noInflectionalFuture }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noInflectionalFuture }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .inflectionalFutureExists }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .noInflectionalFuture }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .noInflectionalFuture }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .inflectionalFutureExists }
  , { walsCode := "som", language := "Somali", iso := "som", value := .inflectionalFutureExists }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .inflectionalFutureExists }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .inflectionalFutureExists }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noInflectionalFuture }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noInflectionalFuture }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .inflectionalFutureExists }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .noInflectionalFuture }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .inflectionalFutureExists }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .noInflectionalFuture }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .inflectionalFutureExists }
  , { walsCode := "tga", language := "Tangga", iso := "hrc", value := .noInflectionalFuture }
  , { walsCode := "tem", language := "Tem", iso := "kdh", value := .inflectionalFutureExists }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .inflectionalFutureExists }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .noInflectionalFuture }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noInflectionalFuture }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .inflectionalFutureExists }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .noInflectionalFuture }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .inflectionalFutureExists }
  , { walsCode := "toj", language := "Tojolabal", iso := "toj", value := .noInflectionalFuture }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .noInflectionalFuture }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .inflectionalFutureExists }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .inflectionalFutureExists }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .inflectionalFutureExists }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .inflectionalFutureExists }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .inflectionalFutureExists }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .noInflectionalFuture }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noInflectionalFuture }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noInflectionalFuture }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noInflectionalFuture }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .inflectionalFutureExists }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .inflectionalFutureExists }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .inflectionalFutureExists }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .noInflectionalFuture }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .noInflectionalFuture }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .inflectionalFutureExists }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noInflectionalFuture }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .inflectionalFutureExists }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .inflectionalFutureExists }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noInflectionalFuture }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .noInflectionalFuture }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .inflectionalFutureExists }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noInflectionalFuture }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .inflectionalFutureExists }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noInflectionalFuture }
  ]

-- Count verification
theorem total_count : allData.length = 222 := by native_decide

theorem count_inflectionalFutureExists :
    (allData.filter (·.value == .inflectionalFutureExists)).length = 110 := by native_decide
theorem count_noInflectionalFuture :
    (allData.filter (·.value == .noInflectionalFuture)).length = 112 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F67A
