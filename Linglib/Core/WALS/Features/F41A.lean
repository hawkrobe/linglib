/-!
# WALS Feature 41A: Distance Contrasts in Demonstratives
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 41A`.

Chapter 41, 234 languages.
-/

namespace Core.WALS.F41A

/-- WALS 41A values. -/
inductive DistanceContrastsInDemonstratives where
  | noDistanceContrast  -- No distance contrast (7 languages)
  | twoWayContrast  -- Two-way contrast (126 languages)
  | threeWayContrast  -- Three-way contrast (88 languages)
  | fourWayContrast  -- Four-way contrast (9 languages)
  | fiveWayContrast  -- Five (or more)-way contrast (4 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 41A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : DistanceContrastsInDemonstratives
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 41A dataset (234 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .threeWayContrast }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .twoWayContrast }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .threeWayContrast }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .threeWayContrast }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .twoWayContrast }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .twoWayContrast }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .twoWayContrast }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .threeWayContrast }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .threeWayContrast }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .threeWayContrast }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .threeWayContrast }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .twoWayContrast }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .threeWayContrast }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .twoWayContrast }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .threeWayContrast }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .twoWayContrast }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .twoWayContrast }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .twoWayContrast }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .threeWayContrast }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .fourWayContrast }
  , { walsCode := "bad", language := "Bade", iso := "bde", value := .twoWayContrast }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .twoWayContrast }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .threeWayContrast }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .threeWayContrast }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .twoWayContrast }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .twoWayContrast }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .twoWayContrast }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .twoWayContrast }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .twoWayContrast }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .twoWayContrast }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .twoWayContrast }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .threeWayContrast }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .threeWayContrast }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .threeWayContrast }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .threeWayContrast }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .twoWayContrast }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .threeWayContrast }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .twoWayContrast }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .twoWayContrast }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .threeWayContrast }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .twoWayContrast }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .threeWayContrast }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .twoWayContrast }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .twoWayContrast }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .twoWayContrast }
  , { walsCode := "eng", language := "English", iso := "eng", value := .twoWayContrast }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .twoWayContrast }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .twoWayContrast }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .twoWayContrast }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .twoWayContrast }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .threeWayContrast }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .threeWayContrast }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .twoWayContrast }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noDistanceContrast }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .threeWayContrast }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .threeWayContrast }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noDistanceContrast }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .twoWayContrast }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .threeWayContrast }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .threeWayContrast }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .threeWayContrast }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .twoWayContrast }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .threeWayContrast }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .fourWayContrast }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .threeWayContrast }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .threeWayContrast }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .twoWayContrast }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .threeWayContrast }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .threeWayContrast }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .threeWayContrast }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .twoWayContrast }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .threeWayContrast }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .threeWayContrast }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .twoWayContrast }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .twoWayContrast }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .twoWayContrast }
  , { walsCode := "inr", language := "Inuktitut (Aivilingmiutut)", iso := "ike", value := .twoWayContrast }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .fourWayContrast }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .threeWayContrast }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .twoWayContrast }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .twoWayContrast }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .threeWayContrast }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .threeWayContrast }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .twoWayContrast }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .threeWayContrast }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .threeWayContrast }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .fourWayContrast }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .twoWayContrast }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .twoWayContrast }
  , { walsCode := "krg", language := "Karanga", iso := "sna", value := .twoWayContrast }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .twoWayContrast }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .twoWayContrast }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .twoWayContrast }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noDistanceContrast }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .threeWayContrast }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .twoWayContrast }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .threeWayContrast }
  , { walsCode := "klb", language := "Kilba", iso := "hbb", value := .threeWayContrast }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .threeWayContrast }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .twoWayContrast }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .twoWayContrast }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .twoWayContrast }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .fiveWayContrast }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .twoWayContrast }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .twoWayContrast }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .threeWayContrast }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noDistanceContrast }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .threeWayContrast }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noDistanceContrast }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .threeWayContrast }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .twoWayContrast }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .threeWayContrast }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .twoWayContrast }
  , { walsCode := "kwm", language := "Kwami", iso := "ksq", value := .twoWayContrast }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .threeWayContrast }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .threeWayContrast }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .twoWayContrast }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .threeWayContrast }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .threeWayContrast }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .twoWayContrast }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .twoWayContrast }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .twoWayContrast }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .threeWayContrast }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .twoWayContrast }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .twoWayContrast }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .fiveWayContrast }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .twoWayContrast }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .twoWayContrast }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .noDistanceContrast }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .twoWayContrast }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .twoWayContrast }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .threeWayContrast }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .threeWayContrast }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .twoWayContrast }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .twoWayContrast }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .fiveWayContrast }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .fourWayContrast }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .twoWayContrast }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .threeWayContrast }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .threeWayContrast }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .twoWayContrast }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .twoWayContrast }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .twoWayContrast }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .twoWayContrast }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .twoWayContrast }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .threeWayContrast }
  , { walsCode := "mul", language := "Mulao", iso := "mlm", value := .twoWayContrast }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .twoWayContrast }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .threeWayContrast }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .fiveWayContrast }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .twoWayContrast }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .twoWayContrast }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .twoWayContrast }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .threeWayContrast }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .twoWayContrast }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .twoWayContrast }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .twoWayContrast }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .threeWayContrast }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .twoWayContrast }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .twoWayContrast }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .twoWayContrast }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .threeWayContrast }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .twoWayContrast }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .twoWayContrast }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .fourWayContrast }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .twoWayContrast }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .twoWayContrast }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .twoWayContrast }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .threeWayContrast }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .threeWayContrast }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .twoWayContrast }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .twoWayContrast }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .twoWayContrast }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .threeWayContrast }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .threeWayContrast }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .fourWayContrast }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .twoWayContrast }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .threeWayContrast }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .twoWayContrast }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .twoWayContrast }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .threeWayContrast }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .threeWayContrast }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .twoWayContrast }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .twoWayContrast }
  , { walsCode := "so", language := "So", iso := "teu", value := .twoWayContrast }
  , { walsCode := "som", language := "Somali", iso := "som", value := .fourWayContrast }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .threeWayContrast }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noDistanceContrast }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .twoWayContrast }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .threeWayContrast }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .twoWayContrast }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .threeWayContrast }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .twoWayContrast }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .threeWayContrast }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .twoWayContrast }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .threeWayContrast }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .threeWayContrast }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .twoWayContrast }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .fourWayContrast }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .twoWayContrast }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .threeWayContrast }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .twoWayContrast }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .twoWayContrast }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .threeWayContrast }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .twoWayContrast }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .twoWayContrast }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .twoWayContrast }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .threeWayContrast }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .threeWayContrast }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .threeWayContrast }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .twoWayContrast }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .twoWayContrast }
  , { walsCode := "uri", language := "Urim", iso := "uri", value := .threeWayContrast }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .threeWayContrast }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .twoWayContrast }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .twoWayContrast }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .twoWayContrast }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .threeWayContrast }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .threeWayContrast }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .twoWayContrast }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .threeWayContrast }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .twoWayContrast }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .threeWayContrast }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .twoWayContrast }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .twoWayContrast }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .twoWayContrast }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .threeWayContrast }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .twoWayContrast }
  , { walsCode := "ynk", language := "Yankuntjatjara", iso := "kdd", value := .twoWayContrast }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .threeWayContrast }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .threeWayContrast }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .twoWayContrast }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .twoWayContrast }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .twoWayContrast }
  ]

-- Count verification
theorem total_count : allData.length = 234 := by native_decide

theorem count_noDistanceContrast :
    (allData.filter (·.value == .noDistanceContrast)).length = 7 := by native_decide
theorem count_twoWayContrast :
    (allData.filter (·.value == .twoWayContrast)).length = 126 := by native_decide
theorem count_threeWayContrast :
    (allData.filter (·.value == .threeWayContrast)).length = 88 := by native_decide
theorem count_fourWayContrast :
    (allData.filter (·.value == .fourWayContrast)).length = 9 := by native_decide
theorem count_fiveWayContrast :
    (allData.filter (·.value == .fiveWayContrast)).length = 4 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F41A
