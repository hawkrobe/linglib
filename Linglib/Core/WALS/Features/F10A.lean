/-!
# WALS Feature 10A: Vowel Nasalization
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 10A`.

Chapter 10, 244 languages.
-/

namespace Core.WALS.F10A

/-- WALS 10A values. -/
inductive VowelNasalization where
  | contrastPresent  -- Contrast present (64 languages)
  | contrastAbsent  -- Contrast absent (180 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 10A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : VowelNasalization
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 10A dataset (244 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .contrastAbsent }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .contrastAbsent }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .contrastAbsent }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .contrastAbsent }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .contrastAbsent }
  , { walsCode := "aka", language := "Aka", iso := "axk", value := .contrastAbsent }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .contrastAbsent }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .contrastPresent }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .contrastAbsent }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .contrastAbsent }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .contrastPresent }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .contrastAbsent }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .contrastAbsent }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .contrastAbsent }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .contrastAbsent }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .contrastAbsent }
  , { walsCode := "avt", language := "Avatime", iso := "avn", value := .contrastPresent }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .contrastAbsent }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .contrastAbsent }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .contrastPresent }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .contrastAbsent }
  , { walsCode := "ban", language := "Bana", iso := "bcw", value := .contrastAbsent }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .contrastPresent }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .contrastPresent }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .contrastAbsent }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .contrastAbsent }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .contrastAbsent }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .contrastAbsent }
  , { walsCode := "bfd", language := "Biafada", iso := "bif", value := .contrastAbsent }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .contrastAbsent }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .contrastPresent }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .contrastAbsent }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .contrastPresent }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .contrastAbsent }
  , { walsCode := "car", language := "Carib", iso := "car", value := .contrastAbsent }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .contrastPresent }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .contrastAbsent }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .contrastPresent }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .contrastAbsent }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .contrastAbsent }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .contrastAbsent }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .contrastAbsent }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .contrastAbsent }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .contrastAbsent }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .contrastAbsent }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .contrastPresent }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .contrastAbsent }
  , { walsCode := "day", language := "Day", iso := "dai", value := .contrastPresent }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .contrastPresent }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .contrastAbsent }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .contrastAbsent }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .contrastAbsent }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .contrastAbsent }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .contrastAbsent }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .contrastPresent }
  , { walsCode := "eng", language := "English", iso := "eng", value := .contrastAbsent }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .contrastPresent }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .contrastAbsent }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .contrastAbsent }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .contrastAbsent }
  , { walsCode := "fre", language := "French", iso := "fra", value := .contrastPresent }
  , { walsCode := "fus", language := "Fula (Senegal)", iso := "fuc", value := .contrastAbsent }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .contrastAbsent }
  , { walsCode := "gad", language := "Gade", iso := "ged", value := .contrastAbsent }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .contrastAbsent }
  , { walsCode := "gbk", language := "Gbaya (Northwest)", iso := "gya", value := .contrastPresent }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .contrastAbsent }
  , { walsCode := "ger", language := "German", iso := "deu", value := .contrastAbsent }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .contrastAbsent }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .contrastPresent }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .contrastAbsent }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .contrastAbsent }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .contrastPresent }
  , { walsCode := "gir", language := "Gula Iro", iso := "glj", value := .contrastPresent }
  , { walsCode := "grm", language := "Gurma", iso := "gux", value := .contrastPresent }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .contrastAbsent }
  , { walsCode := "hrs", language := "Harsusi", iso := "hss", value := .contrastAbsent }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .contrastAbsent }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .contrastPresent }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .contrastAbsent }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .contrastPresent }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .contrastAbsent }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .contrastAbsent }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .contrastPresent }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .contrastAbsent }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .contrastAbsent }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .contrastAbsent }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .contrastAbsent }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .contrastAbsent }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .contrastAbsent }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .contrastAbsent }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .contrastAbsent }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .contrastAbsent }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .contrastAbsent }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .contrastPresent }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .contrastPresent }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .contrastAbsent }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .contrastAbsent }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .contrastPresent }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .contrastAbsent }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .contrastAbsent }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .contrastAbsent }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .contrastAbsent }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .contrastAbsent }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .contrastAbsent }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .contrastAbsent }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .contrastAbsent }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .contrastAbsent }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .contrastAbsent }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .contrastAbsent }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .contrastPresent }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .contrastAbsent }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .contrastAbsent }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .contrastAbsent }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .contrastPresent }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .contrastAbsent }
  , { walsCode := "ksp", language := "Kosop", iso := "kia", value := .contrastPresent }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .contrastAbsent }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .contrastPresent }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .contrastAbsent }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .contrastAbsent }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .contrastAbsent }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .contrastAbsent }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .contrastAbsent }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .contrastAbsent }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .contrastAbsent }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .contrastAbsent }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .contrastPresent }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .contrastAbsent }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .contrastPresent }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .contrastAbsent }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .contrastAbsent }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .contrastAbsent }
  , { walsCode := "lok", language := "Loko", iso := "lok", value := .contrastPresent }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .contrastPresent }
  , { walsCode := "mdz", language := "Mada (in Nigeria)", iso := "mda", value := .contrastPresent }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .contrastAbsent }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .contrastAbsent }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .contrastAbsent }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .contrastAbsent }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .contrastAbsent }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .contrastAbsent }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .contrastAbsent }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .contrastAbsent }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .contrastAbsent }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .contrastAbsent }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .contrastAbsent }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .contrastPresent }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .contrastPresent }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .contrastAbsent }
  , { walsCode := "mid", language := "Midob", iso := "mei", value := .contrastAbsent }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .contrastAbsent }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .contrastPresent }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .contrastPresent }
  , { walsCode := "mul", language := "Mulao", iso := "mlm", value := .contrastAbsent }
  , { walsCode := "mnu", language := "Mun", iso := "mji", value := .contrastAbsent }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .contrastPresent }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .contrastAbsent }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .contrastAbsent }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .contrastAbsent }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .contrastPresent }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .contrastAbsent }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .contrastAbsent }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .contrastAbsent }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .contrastAbsent }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .contrastAbsent }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .contrastAbsent }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .contrastAbsent }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .contrastAbsent }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .contrastAbsent }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .contrastPresent }
  , { walsCode := "oku", language := "Oku", iso := "oku", value := .contrastAbsent }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .contrastAbsent }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .contrastAbsent }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .contrastPresent }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .contrastAbsent }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .contrastAbsent }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .contrastAbsent }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .contrastAbsent }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .contrastPresent }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .contrastAbsent }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .contrastAbsent }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .contrastAbsent }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .contrastAbsent }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .contrastAbsent }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .contrastAbsent }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .contrastAbsent }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .contrastAbsent }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .contrastAbsent }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .contrastAbsent }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .contrastPresent }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .contrastPresent }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .contrastAbsent }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .contrastPresent }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .contrastPresent }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .contrastPresent }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .contrastPresent }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .contrastAbsent }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .contrastAbsent }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .contrastAbsent }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .contrastPresent }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .contrastAbsent }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .contrastAbsent }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .contrastAbsent }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .contrastAbsent }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .contrastPresent }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .contrastPresent }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .contrastAbsent }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .contrastAbsent }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .contrastAbsent }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .contrastAbsent }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .contrastPresent }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .contrastAbsent }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .contrastAbsent }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .contrastAbsent }
  , { walsCode := "tmk", language := "Tumak", iso := "tmc", value := .contrastPresent }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .contrastAbsent }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .contrastAbsent }
  , { walsCode := "kgl", language := "Umbu Ungu", iso := "ubu", value := .contrastAbsent }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .contrastAbsent }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .contrastPresent }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .contrastAbsent }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .contrastAbsent }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .contrastAbsent }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .contrastPresent }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .contrastAbsent }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .contrastPresent }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .contrastAbsent }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .contrastAbsent }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .contrastAbsent }
  , { walsCode := "wmn", language := "Wéménugbé", iso := "wem", value := .contrastPresent }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .contrastAbsent }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .contrastPresent }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .contrastAbsent }
  , { walsCode := "yem", language := "Yemba", iso := "ybb", value := .contrastAbsent }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .contrastAbsent }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .contrastAbsent }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .contrastPresent }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .contrastPresent }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .contrastAbsent }
  , { walsCode := "ykp", language := "Yukpa", iso := "yup", value := .contrastPresent }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .contrastAbsent }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .contrastAbsent }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .contrastAbsent }
  ]

-- Count verification
theorem total_count : allData.length = 244 := by native_decide

theorem count_contrastPresent :
    (allData.filter (·.value == .contrastPresent)).length = 64 := by native_decide
theorem count_contrastAbsent :
    (allData.filter (·.value == .contrastAbsent)).length = 180 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F10A
