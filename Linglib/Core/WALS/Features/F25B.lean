import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 25B: Zero Marking of A and P Arguments
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 25B`.

Chapter 25, 235 languages.
-/

namespace Core.WALS.F25B

/-- WALS 25B values. -/
inductive ZeroMarkingOfAAndPArguments where
  | zeroMarking  -- Zero-marking (16 languages)
  | nonZeroMarking  -- Non-zero marking (219 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 25B dataset (235 languages). -/
def allData : List (Datapoint ZeroMarkingOfAAndPArguments) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .nonZeroMarking }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .nonZeroMarking }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .nonZeroMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .nonZeroMarking }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .nonZeroMarking }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .nonZeroMarking }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .nonZeroMarking }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .nonZeroMarking }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .nonZeroMarking }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .nonZeroMarking }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .nonZeroMarking }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .nonZeroMarking }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .nonZeroMarking }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .nonZeroMarking }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .nonZeroMarking }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .nonZeroMarking }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .nonZeroMarking }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .nonZeroMarking }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .nonZeroMarking }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .nonZeroMarking }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .zeroMarking }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .nonZeroMarking }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .nonZeroMarking }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .nonZeroMarking }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .nonZeroMarking }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .nonZeroMarking }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .nonZeroMarking }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .nonZeroMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .nonZeroMarking }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .zeroMarking }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .nonZeroMarking }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .nonZeroMarking }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .nonZeroMarking }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .nonZeroMarking }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .nonZeroMarking }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .nonZeroMarking }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .nonZeroMarking }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .nonZeroMarking }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .nonZeroMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .nonZeroMarking }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .nonZeroMarking }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .nonZeroMarking }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .nonZeroMarking }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .nonZeroMarking }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .nonZeroMarking }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .nonZeroMarking }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .nonZeroMarking }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .nonZeroMarking }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .nonZeroMarking }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .nonZeroMarking }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .nonZeroMarking }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .nonZeroMarking }
  , { walsCode := "eng", language := "English", iso := "eng", value := .nonZeroMarking }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .nonZeroMarking }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .nonZeroMarking }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .zeroMarking }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .nonZeroMarking }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .nonZeroMarking }
  , { walsCode := "fre", language := "French", iso := "fra", value := .nonZeroMarking }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .nonZeroMarking }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .nonZeroMarking }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .nonZeroMarking }
  , { walsCode := "ger", language := "German", iso := "deu", value := .nonZeroMarking }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .nonZeroMarking }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nonZeroMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .nonZeroMarking }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .nonZeroMarking }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .nonZeroMarking }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .nonZeroMarking }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .nonZeroMarking }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .zeroMarking }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .nonZeroMarking }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .nonZeroMarking }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .nonZeroMarking }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .nonZeroMarking }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .nonZeroMarking }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .zeroMarking }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .nonZeroMarking }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .nonZeroMarking }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .nonZeroMarking }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .zeroMarking }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .nonZeroMarking }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .zeroMarking }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .nonZeroMarking }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .nonZeroMarking }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .nonZeroMarking }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .zeroMarking }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .nonZeroMarking }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .nonZeroMarking }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .nonZeroMarking }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .zeroMarking }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .nonZeroMarking }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .zeroMarking }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .nonZeroMarking }
  , { walsCode := "knp", language := "Kanum (Ngkâlmpw)", iso := "kcd", value := .nonZeroMarking }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .nonZeroMarking }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .nonZeroMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .nonZeroMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .nonZeroMarking }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .nonZeroMarking }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .nonZeroMarking }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .nonZeroMarking }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .nonZeroMarking }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .nonZeroMarking }
  , { walsCode := "kkr", language := "Kirikiri", iso := "kiy", value := .nonZeroMarking }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .zeroMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .nonZeroMarking }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .nonZeroMarking }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .nonZeroMarking }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .nonZeroMarking }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .nonZeroMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .nonZeroMarking }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .nonZeroMarking }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .nonZeroMarking }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .nonZeroMarking }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .nonZeroMarking }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .nonZeroMarking }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .zeroMarking }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .nonZeroMarking }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .nonZeroMarking }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .nonZeroMarking }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .nonZeroMarking }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .nonZeroMarking }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .nonZeroMarking }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .nonZeroMarking }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .nonZeroMarking }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .nonZeroMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .nonZeroMarking }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .nonZeroMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .nonZeroMarking }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .nonZeroMarking }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .nonZeroMarking }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .nonZeroMarking }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .nonZeroMarking }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .nonZeroMarking }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .nonZeroMarking }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .nonZeroMarking }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .nonZeroMarking }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .nonZeroMarking }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .nonZeroMarking }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .nonZeroMarking }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .nonZeroMarking }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .nonZeroMarking }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .nonZeroMarking }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .nonZeroMarking }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .nonZeroMarking }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .nonZeroMarking }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .nonZeroMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .nonZeroMarking }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .nonZeroMarking }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .nonZeroMarking }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .nonZeroMarking }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .nonZeroMarking }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .nonZeroMarking }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .nonZeroMarking }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .nonZeroMarking }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .nonZeroMarking }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .nonZeroMarking }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .nonZeroMarking }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .nonZeroMarking }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .nonZeroMarking }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .nonZeroMarking }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .nonZeroMarking }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .nonZeroMarking }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .nonZeroMarking }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .nonZeroMarking }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .zeroMarking }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .nonZeroMarking }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .nonZeroMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .nonZeroMarking }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .nonZeroMarking }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .nonZeroMarking }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .nonZeroMarking }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .nonZeroMarking }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .nonZeroMarking }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .nonZeroMarking }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .nonZeroMarking }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .nonZeroMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .nonZeroMarking }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .nonZeroMarking }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .nonZeroMarking }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .nonZeroMarking }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .nonZeroMarking }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .nonZeroMarking }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .nonZeroMarking }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .nonZeroMarking }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .zeroMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .nonZeroMarking }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .nonZeroMarking }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .nonZeroMarking }
  , { walsCode := "tgp", language := "Tanglapui", iso := "tpg", value := .nonZeroMarking }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .nonZeroMarking }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .nonZeroMarking }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .zeroMarking }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .nonZeroMarking }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .nonZeroMarking }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .nonZeroMarking }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .nonZeroMarking }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .nonZeroMarking }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .nonZeroMarking }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .nonZeroMarking }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .nonZeroMarking }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .nonZeroMarking }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .nonZeroMarking }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .nonZeroMarking }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .nonZeroMarking }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .nonZeroMarking }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .zeroMarking }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .nonZeroMarking }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .nonZeroMarking }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .nonZeroMarking }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .nonZeroMarking }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .nonZeroMarking }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .nonZeroMarking }
  , { walsCode := "was", language := "Washo", iso := "was", value := .nonZeroMarking }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .nonZeroMarking }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .nonZeroMarking }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .nonZeroMarking }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .nonZeroMarking }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .nonZeroMarking }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .nonZeroMarking }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .nonZeroMarking }
  , { walsCode := "yli", language := "Yali", iso := "yli", value := .nonZeroMarking }
  , { walsCode := "ynk", language := "Yankuntjatjara", iso := "kdd", value := .nonZeroMarking }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .nonZeroMarking }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .nonZeroMarking }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .nonZeroMarking }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .nonZeroMarking }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .nonZeroMarking }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .nonZeroMarking }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .nonZeroMarking }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .nonZeroMarking }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .nonZeroMarking }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .nonZeroMarking }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .nonZeroMarking }
  ]

-- Count verification
theorem total_count : allData.length = 235 := by native_decide

theorem count_zeroMarking :
    (allData.filter (·.value == .zeroMarking)).length = 16 := by native_decide
theorem count_nonZeroMarking :
    (allData.filter (·.value == .nonZeroMarking)).length = 219 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F25B
