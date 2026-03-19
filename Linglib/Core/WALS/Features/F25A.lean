/-!
# WALS Feature 25A: Locus of Marking: Whole-language Typology
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 25A`.

Chapter 25, 236 languages.
-/

namespace Core.WALS.F25A

/-- WALS 25A values. -/
inductive LocusOfMarkingWholeLanguageTypology where
  | headMarking  -- Head-marking (47 languages)
  | dependentMarking  -- Dependent-marking (46 languages)
  | doubleMarking  -- Double-marking (16 languages)
  | zeroMarking  -- Zero-marking (6 languages)
  | inconsistentOrOther  -- Inconsistent or other (121 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 25A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : LocusOfMarkingWholeLanguageTypology
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 25A dataset (236 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .headMarking }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .headMarking }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .headMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .inconsistentOrOther }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .inconsistentOrOther }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .dependentMarking }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .inconsistentOrOther }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .headMarking }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .headMarking }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .inconsistentOrOther }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .inconsistentOrOther }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .dependentMarking }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .inconsistentOrOther }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .inconsistentOrOther }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .inconsistentOrOther }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .dependentMarking }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .doubleMarking }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .inconsistentOrOther }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .inconsistentOrOther }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .inconsistentOrOther }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .inconsistentOrOther }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .dependentMarking }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .doubleMarking }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .dependentMarking }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .inconsistentOrOther }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .inconsistentOrOther }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .dependentMarking }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .inconsistentOrOther }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .dependentMarking }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .inconsistentOrOther }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .doubleMarking }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .inconsistentOrOther }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .inconsistentOrOther }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .inconsistentOrOther }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .inconsistentOrOther }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .headMarking }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .headMarking }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .inconsistentOrOther }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .headMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .inconsistentOrOther }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .headMarking }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .inconsistentOrOther }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .headMarking }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .headMarking }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .headMarking }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .inconsistentOrOther }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .dependentMarking }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .inconsistentOrOther }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .dependentMarking }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .doubleMarking }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .inconsistentOrOther }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .dependentMarking }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .inconsistentOrOther }
  , { walsCode := "eng", language := "English", iso := "eng", value := .dependentMarking }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .inconsistentOrOther }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .inconsistentOrOther }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .inconsistentOrOther }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .headMarking }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .inconsistentOrOther }
  , { walsCode := "fre", language := "French", iso := "fra", value := .inconsistentOrOther }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .dependentMarking }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .dependentMarking }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .inconsistentOrOther }
  , { walsCode := "ger", language := "German", iso := "deu", value := .dependentMarking }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .inconsistentOrOther }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .dependentMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .doubleMarking }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .doubleMarking }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .headMarking }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .inconsistentOrOther }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .inconsistentOrOther }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .inconsistentOrOther }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .inconsistentOrOther }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .inconsistentOrOther }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .inconsistentOrOther }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .inconsistentOrOther }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .headMarking }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .inconsistentOrOther }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .doubleMarking }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .headMarking }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .inconsistentOrOther }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .inconsistentOrOther }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .dependentMarking }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .zeroMarking }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .dependentMarking }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .inconsistentOrOther }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .doubleMarking }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .zeroMarking }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .inconsistentOrOther }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .headMarking }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .dependentMarking }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .inconsistentOrOther }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .doubleMarking }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .zeroMarking }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .dependentMarking }
  , { walsCode := "knp", language := "Kanum (Ngkâlmpw)", iso := "kcd", value := .inconsistentOrOther }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .inconsistentOrOther }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .headMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .dependentMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .headMarking }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .dependentMarking }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .dependentMarking }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .inconsistentOrOther }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .inconsistentOrOther }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .inconsistentOrOther }
  , { walsCode := "kkr", language := "Kirikiri", iso := "kiy", value := .inconsistentOrOther }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .inconsistentOrOther }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .inconsistentOrOther }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .inconsistentOrOther }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .inconsistentOrOther }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .dependentMarking }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .dependentMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .inconsistentOrOther }
  , { walsCode := "kiu", language := "Kui (in Indonesia)", iso := "kvd", value := .headMarking }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .dependentMarking }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .inconsistentOrOther }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .inconsistentOrOther }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .headMarking }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .zeroMarking }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .headMarking }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .headMarking }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .dependentMarking }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .inconsistentOrOther }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .inconsistentOrOther }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .dependentMarking }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .inconsistentOrOther }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .inconsistentOrOther }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .dependentMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .doubleMarking }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .dependentMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .inconsistentOrOther }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .inconsistentOrOther }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .headMarking }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .dependentMarking }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .inconsistentOrOther }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .inconsistentOrOther }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .dependentMarking }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .inconsistentOrOther }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .doubleMarking }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .inconsistentOrOther }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .inconsistentOrOther }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .inconsistentOrOther }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .inconsistentOrOther }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .dependentMarking }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .inconsistentOrOther }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .dependentMarking }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .headMarking }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .inconsistentOrOther }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .headMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .inconsistentOrOther }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .dependentMarking }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .dependentMarking }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .dependentMarking }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .inconsistentOrOther }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .headMarking }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .headMarking }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .dependentMarking }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .inconsistentOrOther }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .inconsistentOrOther }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .inconsistentOrOther }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .headMarking }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .inconsistentOrOther }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .inconsistentOrOther }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .headMarking }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .doubleMarking }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .inconsistentOrOther }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .inconsistentOrOther }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .headMarking }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .zeroMarking }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .dependentMarking }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .dependentMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .dependentMarking }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .inconsistentOrOther }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .inconsistentOrOther }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .inconsistentOrOther }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .dependentMarking }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .headMarking }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .inconsistentOrOther }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .inconsistentOrOther }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .inconsistentOrOther }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .inconsistentOrOther }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .inconsistentOrOther }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .dependentMarking }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .inconsistentOrOther }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .headMarking }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .inconsistentOrOther }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .inconsistentOrOther }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .inconsistentOrOther }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .inconsistentOrOther }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .inconsistentOrOther }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .inconsistentOrOther }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .headMarking }
  , { walsCode := "tgp", language := "Tanglapui", iso := "tpg", value := .headMarking }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .inconsistentOrOther }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .headMarking }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .inconsistentOrOther }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .dependentMarking }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .inconsistentOrOther }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .inconsistentOrOther }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .headMarking }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .inconsistentOrOther }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .dependentMarking }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .inconsistentOrOther }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .headMarking }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .inconsistentOrOther }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .dependentMarking }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .inconsistentOrOther }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .dependentMarking }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .headMarking }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .zeroMarking }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .inconsistentOrOther }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .inconsistentOrOther }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .inconsistentOrOther }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .headMarking }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .inconsistentOrOther }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .headMarking }
  , { walsCode := "was", language := "Washo", iso := "was", value := .headMarking }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .inconsistentOrOther }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .doubleMarking }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .headMarking }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .inconsistentOrOther }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .inconsistentOrOther }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .inconsistentOrOther }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .inconsistentOrOther }
  , { walsCode := "yli", language := "Yali", iso := "yli", value := .headMarking }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .doubleMarking }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .headMarking }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .inconsistentOrOther }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .inconsistentOrOther }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .headMarking }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .inconsistentOrOther }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .doubleMarking }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .headMarking }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .doubleMarking }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .inconsistentOrOther }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .inconsistentOrOther }
  ]

-- Count verification
theorem total_count : allData.length = 236 := by native_decide

theorem count_headMarking :
    (allData.filter (·.value == .headMarking)).length = 47 := by native_decide
theorem count_dependentMarking :
    (allData.filter (·.value == .dependentMarking)).length = 46 := by native_decide
theorem count_doubleMarking :
    (allData.filter (·.value == .doubleMarking)).length = 16 := by native_decide
theorem count_zeroMarking :
    (allData.filter (·.value == .zeroMarking)).length = 6 := by native_decide
theorem count_inconsistentOrOther :
    (allData.filter (·.value == .inconsistentOrOther)).length = 121 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F25A
