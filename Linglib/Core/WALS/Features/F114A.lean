import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 114A: Subtypes of Asymmetric Standard Negation
@cite{miestamo-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 114A`.

Chapter 114, 297 languages.
-/

namespace Core.WALS.F114A

/-- WALS 114A values. -/
inductive AsymmetricNegationSubtype where
  | aFin  -- A/Fin (40 languages)
  | aNonreal  -- A/NonReal (20 languages)
  | aCat  -- A/Cat (82 languages)
  | aFinAndANonreal  -- A/Fin and A/NonReal (9 languages)
  | aFinAndACat  -- A/Fin and A/Cat (21 languages)
  | aNonrealAndACat  -- A/NonReal and A/Cat (11 languages)
  | nonAssignable  -- Non-assignable (114 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 114A dataset (297 languages). -/
def allData : List (Datapoint AsymmetricNegationSubtype) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .aCat }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .aCat }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .aFin }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .aCat }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .nonAssignable }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .aNonreal }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .nonAssignable }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .aCat }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .nonAssignable }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .aFin }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .nonAssignable }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .nonAssignable }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .aFin }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .aNonreal }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .aFin }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .aNonreal }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .aFinAndACat }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .aNonreal }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .aCat }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .aCat }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .aCat }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .nonAssignable }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .aFin }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .aCat }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .nonAssignable }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .aCat }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .aFinAndACat }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .aCat }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .aFinAndACat }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .nonAssignable }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .aCat }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .aCat }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .aCat }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .aNonreal }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .aCat }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .nonAssignable }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .nonAssignable }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .aCat }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .nonAssignable }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .aCat }
  , { walsCode := "car", language := "Carib", iso := "car", value := .aFin }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .nonAssignable }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .nonAssignable }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .aFinAndACat }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .nonAssignable }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .nonAssignable }
  , { walsCode := "crt", language := "Chorote", iso := "", value := .nonAssignable }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .aFinAndANonreal }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .nonAssignable }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .aCat }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .nonAssignable }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .nonAssignable }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .aNonrealAndACat }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .nonAssignable }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .aFin }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .aCat }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .aCat }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .nonAssignable }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .aNonrealAndACat }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .nonAssignable }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .aCat }
  , { walsCode := "eng", language := "English", iso := "eng", value := .aCat }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .aFinAndACat }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .aFin }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .aCat }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .aFin }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .aFin }
  , { walsCode := "fre", language := "French", iso := "fra", value := .nonAssignable }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .nonAssignable }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .aCat }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .nonAssignable }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .aFin }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .nonAssignable }
  , { walsCode := "ger", language := "German", iso := "deu", value := .nonAssignable }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .aCat }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .aCat }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .nonAssignable }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .aNonrealAndACat }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .nonAssignable }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .aCat }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .aCat }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .nonAssignable }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .nonAssignable }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .nonAssignable }
  , { walsCode := "hcr", language := "Haitian Creole", iso := "hat", value := .aCat }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .aFinAndANonreal }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .aFin }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .aNonreal }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .aCat }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .aFin }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .aCat }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .aFin }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .nonAssignable }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .aFin }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .nonAssignable }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .nonAssignable }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .aCat }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .nonAssignable }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .aCat }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .aNonreal }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .aFinAndACat }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .aFin }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .aFinAndANonreal }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .aFin }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .nonAssignable }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .nonAssignable }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .aFin }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .aCat }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .nonAssignable }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .aNonreal }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .aFinAndACat }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .aNonreal }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .nonAssignable }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .nonAssignable }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .aNonrealAndACat }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .aNonrealAndACat }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .aFinAndACat }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .aCat }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .aCat }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .aCat }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .aFinAndACat }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .aCat }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .aCat }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .nonAssignable }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .nonAssignable }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .aFin }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .aFin }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .aCat }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .nonAssignable }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .nonAssignable }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .nonAssignable }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .aCat }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .nonAssignable }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .aCat }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .nonAssignable }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .aCat }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .nonAssignable }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .aFinAndANonreal }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .nonAssignable }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .aCat }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .aCat }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .aFin }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .nonAssignable }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .aCat }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .nonAssignable }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .nonAssignable }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .aCat }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .aCat }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .nonAssignable }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .nonAssignable }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .aNonreal }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .aCat }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .aFinAndACat }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .aFin }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .aCat }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .aCat }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .aFinAndACat }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .aFin }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .aCat }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .nonAssignable }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .aFin }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .nonAssignable }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .aFinAndACat }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .aFinAndACat }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .aFin }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .aNonrealAndACat }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .nonAssignable }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .aFin }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .nonAssignable }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .nonAssignable }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .nonAssignable }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .nonAssignable }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .nonAssignable }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .aNonreal }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .nonAssignable }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .aFinAndACat }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .nonAssignable }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .nonAssignable }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .aCat }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .nonAssignable }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .nonAssignable }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .nonAssignable }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .aFin }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .aFin }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .nonAssignable }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .aFinAndACat }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .aCat }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .aCat }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .nonAssignable }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .aFin }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .nonAssignable }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .nonAssignable }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .nonAssignable }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .nonAssignable }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .aFinAndANonreal }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .aCat }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .aFin }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .aNonrealAndACat }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .aNonreal }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .aCat }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .aCat }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .nonAssignable }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .aFinAndACat }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .aCat }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .aCat }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .aCat }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .aCat }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .nonAssignable }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .aCat }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .nonAssignable }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .nonAssignable }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .nonAssignable }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .aFin }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .aCat }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .nonAssignable }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .nonAssignable }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .aCat }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .nonAssignable }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .aNonreal }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .aFin }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .aFinAndACat }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .aCat }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .nonAssignable }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .nonAssignable }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .aCat }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .nonAssignable }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .nonAssignable }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .aNonreal }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .aFin }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .aCat }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .aFin }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .nonAssignable }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .aFinAndANonreal }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .nonAssignable }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .nonAssignable }
  , { walsCode := "so", language := "So", iso := "teu", value := .aCat }
  , { walsCode := "som", language := "Somali", iso := "som", value := .aFinAndACat }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .nonAssignable }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .aFinAndANonreal }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .aFin }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .aFinAndACat }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .aCat }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .nonAssignable }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .nonAssignable }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .aNonreal }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .nonAssignable }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .aCat }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .nonAssignable }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .aCat }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .aNonreal }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .aNonrealAndACat }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .nonAssignable }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .aCat }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .nonAssignable }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .nonAssignable }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .aCat }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .aNonreal }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .nonAssignable }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .aCat }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .aCat }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .nonAssignable }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .nonAssignable }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .nonAssignable }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .aNonreal }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .nonAssignable }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .aFinAndANonreal }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .aCat }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .nonAssignable }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .aNonreal }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .aFin }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .aFin }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .nonAssignable }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .nonAssignable }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .aFin }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .aNonrealAndACat }
  , { walsCode := "was", language := "Washo", iso := "was", value := .nonAssignable }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .aCat }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .aCat }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .aNonreal }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .aFin }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .aFinAndACat }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .nonAssignable }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .nonAssignable }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .aFin }
  , { walsCode := "yrr", language := "Yaruro", iso := "yae", value := .nonAssignable }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .nonAssignable }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .nonAssignable }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .aFinAndACat }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .aCat }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .nonAssignable }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .aCat }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .aCat }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .aNonrealAndACat }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .aNonrealAndACat }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .nonAssignable }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .aFinAndANonreal }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .aCat }
  ]

-- Count verification
theorem total_count : allData.length = 297 := by native_decide

theorem count_aFin :
    (allData.filter (·.value == .aFin)).length = 40 := by native_decide
theorem count_aNonreal :
    (allData.filter (·.value == .aNonreal)).length = 20 := by native_decide
theorem count_aCat :
    (allData.filter (·.value == .aCat)).length = 82 := by native_decide
theorem count_aFinAndANonreal :
    (allData.filter (·.value == .aFinAndANonreal)).length = 9 := by native_decide
theorem count_aFinAndACat :
    (allData.filter (·.value == .aFinAndACat)).length = 21 := by native_decide
theorem count_aNonrealAndACat :
    (allData.filter (·.value == .aNonrealAndACat)).length = 11 := by native_decide
theorem count_nonAssignable :
    (allData.filter (·.value == .nonAssignable)).length = 114 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F114A
