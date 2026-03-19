import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 113A: Symmetric and Asymmetric Standard Negation
@cite{miestamo-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 113A`.

Chapter 113, 297 languages.
-/

namespace Core.WALS.F113A

/-- WALS 113A values. -/
inductive NegationSymmetry where
  | symmetric  -- Symmetric (114 languages)
  | asymmetric  -- Asymmetric (53 languages)
  | both  -- Both (130 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 113A dataset (297 languages). -/
def allData : List (Datapoint NegationSymmetry) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .both }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .both }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .asymmetric }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .both }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .symmetric }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .both }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .symmetric }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .both }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .symmetric }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .asymmetric }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .symmetric }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .symmetric }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .asymmetric }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .both }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .both }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .both }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .both }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .asymmetric }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .both }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .both }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .both }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .symmetric }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .asymmetric }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .asymmetric }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .symmetric }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .both }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .both }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .both }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .asymmetric }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .symmetric }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .both }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .both }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .both }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .both }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .asymmetric }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .symmetric }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .symmetric }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .both }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .symmetric }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .both }
  , { walsCode := "car", language := "Carib", iso := "car", value := .asymmetric }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .symmetric }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .symmetric }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .both }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .symmetric }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .symmetric }
  , { walsCode := "crt", language := "Chorote", iso := "", value := .symmetric }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .both }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .symmetric }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .both }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .symmetric }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .symmetric }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .both }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .symmetric }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .both }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .asymmetric }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .both }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .symmetric }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .asymmetric }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .symmetric }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .asymmetric }
  , { walsCode := "eng", language := "English", iso := "eng", value := .both }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .asymmetric }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .asymmetric }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .both }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .asymmetric }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .asymmetric }
  , { walsCode := "fre", language := "French", iso := "fra", value := .symmetric }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .symmetric }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .both }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .symmetric }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .both }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .symmetric }
  , { walsCode := "ger", language := "German", iso := "deu", value := .symmetric }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .both }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .both }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .symmetric }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .asymmetric }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .symmetric }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .asymmetric }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .both }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .symmetric }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .symmetric }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .symmetric }
  , { walsCode := "hcr", language := "Haitian Creole", iso := "hat", value := .both }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .asymmetric }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .asymmetric }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .both }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .both }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .both }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .both }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .asymmetric }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .symmetric }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .both }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .symmetric }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .symmetric }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .both }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .symmetric }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .asymmetric }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .both }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .both }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .asymmetric }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .both }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .both }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .symmetric }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .symmetric }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .asymmetric }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .both }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .symmetric }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .both }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .asymmetric }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .asymmetric }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .symmetric }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .symmetric }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .both }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .both }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .asymmetric }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .both }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .asymmetric }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .both }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .both }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .asymmetric }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .both }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .symmetric }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .symmetric }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .both }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .asymmetric }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .both }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .symmetric }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .symmetric }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .symmetric }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .both }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .symmetric }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .both }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .symmetric }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .both }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .symmetric }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .both }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .symmetric }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .both }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .both }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .both }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .symmetric }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .both }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .symmetric }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .symmetric }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .both }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .both }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .symmetric }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .symmetric }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .both }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .both }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .both }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .asymmetric }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .both }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .both }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .both }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .both }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .both }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .symmetric }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .asymmetric }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .symmetric }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .both }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .both }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .both }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .both }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .symmetric }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .asymmetric }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .symmetric }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .symmetric }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .symmetric }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .symmetric }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .symmetric }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .both }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .symmetric }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .both }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .symmetric }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .symmetric }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .both }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .symmetric }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .symmetric }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .symmetric }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .asymmetric }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .asymmetric }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .symmetric }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .both }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .both }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .asymmetric }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .symmetric }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .asymmetric }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .symmetric }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .symmetric }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .symmetric }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .symmetric }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .both }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .both }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .asymmetric }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .both }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .both }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .asymmetric }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .both }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .symmetric }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .both }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .both }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .both }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .both }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .both }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .symmetric }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .both }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .symmetric }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .symmetric }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .symmetric }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .both }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .both }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .symmetric }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .symmetric }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .both }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .symmetric }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .both }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .asymmetric }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .both }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .both }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .symmetric }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .symmetric }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .both }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .symmetric }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .symmetric }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .both }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .asymmetric }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .both }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .asymmetric }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .symmetric }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .asymmetric }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .symmetric }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .symmetric }
  , { walsCode := "so", language := "So", iso := "teu", value := .both }
  , { walsCode := "som", language := "Somali", iso := "som", value := .asymmetric }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .symmetric }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .asymmetric }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .both }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .both }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .both }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .symmetric }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .symmetric }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .both }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .symmetric }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .both }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .symmetric }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .both }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .both }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .both }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .symmetric }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .asymmetric }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .symmetric }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .symmetric }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .both }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .both }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .symmetric }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .both }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .both }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .symmetric }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .symmetric }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .symmetric }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .both }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .symmetric }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .both }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .both }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .symmetric }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .both }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .both }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .asymmetric }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .symmetric }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .symmetric }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .asymmetric }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .asymmetric }
  , { walsCode := "was", language := "Washo", iso := "was", value := .symmetric }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .both }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .both }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .both }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .asymmetric }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .both }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .symmetric }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .symmetric }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .both }
  , { walsCode := "yrr", language := "Yaruro", iso := "yae", value := .symmetric }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .symmetric }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .symmetric }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .asymmetric }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .both }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .symmetric }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .both }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .both }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .both }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .asymmetric }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .symmetric }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .asymmetric }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .both }
  ]

-- Count verification
theorem total_count : allData.length = 297 := by native_decide

theorem count_symmetric :
    (allData.filter (·.value == .symmetric)).length = 114 := by native_decide
theorem count_asymmetric :
    (allData.filter (·.value == .asymmetric)).length = 53 := by native_decide
theorem count_both :
    (allData.filter (·.value == .both)).length = 130 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F113A
