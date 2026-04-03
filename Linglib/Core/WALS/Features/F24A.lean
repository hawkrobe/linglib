import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 24A: Locus of Marking in Possessive Noun Phrases
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 24A`.

Chapter 24, 236 languages.
-/

namespace Core.WALS.F24A

/-- WALS 24A values. -/
inductive LocusOfMarkingInPossessiveNounPhrases where
  | headMarking  -- Head marking (78 languages)
  | dependentMarking  -- Dependent marking (98 languages)
  | doubleMarking  -- Double marking (22 languages)
  | noMarking  -- No marking (32 languages)
  | other  -- Other (6 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 24A dataset (236 languages). -/
def allData : List (Datapoint LocusOfMarkingInPossessiveNounPhrases) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .headMarking }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .headMarking }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .headMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .headMarking }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .dependentMarking }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .dependentMarking }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .dependentMarking }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .headMarking }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .headMarking }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noMarking }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .dependentMarking }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .dependentMarking }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noMarking }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .noMarking }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .dependentMarking }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .dependentMarking }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .doubleMarking }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noMarking }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .headMarking }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .dependentMarking }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .dependentMarking }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .dependentMarking }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .doubleMarking }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .dependentMarking }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .dependentMarking }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .headMarking }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .dependentMarking }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .dependentMarking }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .headMarking }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .doubleMarking }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .dependentMarking }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .headMarking }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .headMarking }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .noMarking }
  , { walsCode := "cjo", language := "Chichimeca-Jonaz", iso := "pei", value := .headMarking }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .headMarking }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noMarking }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .headMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noMarking }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .headMarking }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .headMarking }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .headMarking }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .headMarking }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .headMarking }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .doubleMarking }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .dependentMarking }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .doubleMarking }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .dependentMarking }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .doubleMarking }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .headMarking }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .dependentMarking }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noMarking }
  , { walsCode := "eng", language := "English", iso := "eng", value := .dependentMarking }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noMarking }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .doubleMarking }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .dependentMarking }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .headMarking }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .doubleMarking }
  , { walsCode := "fre", language := "French", iso := "fra", value := .dependentMarking }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .dependentMarking }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .dependentMarking }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .dependentMarking }
  , { walsCode := "ger", language := "German", iso := "deu", value := .dependentMarking }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .dependentMarking }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .dependentMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .doubleMarking }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .doubleMarking }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .headMarking }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .noMarking }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .headMarking }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .headMarking }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .headMarking }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .dependentMarking }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .dependentMarking }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .dependentMarking }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .headMarking }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .dependentMarking }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .doubleMarking }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .headMarking }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .headMarking }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .headMarking }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .dependentMarking }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .noMarking }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .dependentMarking }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .dependentMarking }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .doubleMarking }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noMarking }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .dependentMarking }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .headMarking }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .dependentMarking }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .dependentMarking }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .doubleMarking }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noMarking }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .dependentMarking }
  , { walsCode := "knp", language := "Kanum (Ngkâlmpw)", iso := "kcd", value := .dependentMarking }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .dependentMarking }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .headMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .dependentMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .headMarking }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .dependentMarking }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .dependentMarking }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .dependentMarking }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .headMarking }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .doubleMarking }
  , { walsCode := "kkr", language := "Kirikiri", iso := "kiy", value := .noMarking }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .dependentMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .headMarking }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noMarking }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .dependentMarking }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .dependentMarking }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .dependentMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .dependentMarking }
  , { walsCode := "kiu", language := "Kui (in Indonesia)", iso := "kvd", value := .headMarking }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .dependentMarking }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .headMarking }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noMarking }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .headMarking }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noMarking }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .headMarking }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .headMarking }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .dependentMarking }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .dependentMarking }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .dependentMarking }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .dependentMarking }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .other }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .dependentMarking }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .dependentMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .doubleMarking }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .dependentMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .headMarking }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .headMarking }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .headMarking }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .dependentMarking }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noMarking }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .dependentMarking }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .dependentMarking }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .headMarking }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .doubleMarking }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noMarking }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .dependentMarking }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .dependentMarking }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noMarking }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .dependentMarking }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .other }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .dependentMarking }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .headMarking }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noMarking }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .headMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .dependentMarking }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .dependentMarking }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .dependentMarking }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .dependentMarking }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noMarking }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .headMarking }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .headMarking }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .dependentMarking }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .dependentMarking }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .headMarking }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .dependentMarking }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .headMarking }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .dependentMarking }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .other }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .headMarking }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .doubleMarking }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .headMarking }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .headMarking }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .headMarking }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noMarking }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .dependentMarking }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .dependentMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .dependentMarking }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .headMarking }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .other }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .dependentMarking }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .dependentMarking }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .headMarking }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noMarking }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .noMarking }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .dependentMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .dependentMarking }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noMarking }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .dependentMarking }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .dependentMarking }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .headMarking }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .dependentMarking }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .headMarking }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .dependentMarking }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .headMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .dependentMarking }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .other }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .headMarking }
  , { walsCode := "tgp", language := "Tanglapui", iso := "tpg", value := .headMarking }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .dependentMarking }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .headMarking }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .dependentMarking }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .dependentMarking }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .noMarking }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noMarking }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .headMarking }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .dependentMarking }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .dependentMarking }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .dependentMarking }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .headMarking }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .doubleMarking }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .dependentMarking }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .dependentMarking }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .dependentMarking }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .headMarking }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noMarking }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noMarking }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .other }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .dependentMarking }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .headMarking }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .dependentMarking }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .headMarking }
  , { walsCode := "was", language := "Washo", iso := "was", value := .headMarking }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .headMarking }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .doubleMarking }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .headMarking }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .headMarking }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .dependentMarking }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .headMarking }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .headMarking }
  , { walsCode := "yli", language := "Yali", iso := "yli", value := .headMarking }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .doubleMarking }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .headMarking }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .dependentMarking }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .headMarking }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .headMarking }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noMarking }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .doubleMarking }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .headMarking }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .doubleMarking }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .dependentMarking }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .headMarking }
  ]

-- Count verification
theorem total_count : allData.length = 236 := by native_decide

theorem count_headMarking :
    (allData.filter (·.value == .headMarking)).length = 78 := by native_decide
theorem count_dependentMarking :
    (allData.filter (·.value == .dependentMarking)).length = 98 := by native_decide
theorem count_doubleMarking :
    (allData.filter (·.value == .doubleMarking)).length = 22 := by native_decide
theorem count_noMarking :
    (allData.filter (·.value == .noMarking)).length = 32 := by native_decide
theorem count_other :
    (allData.filter (·.value == .other)).length = 6 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F24A
