/-!
# WALS Feature 49A: Number of Cases
@cite{iggesen-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 49A`.

Chapter 49, 261 languages.
-/

namespace Core.WALS.F49A

/-- WALS 49A values. -/
inductive CaseCount where
  | noMorphologicalCaseMarking  -- No morphological case-marking (100 languages)
  | cases2  -- 2 cases (23 languages)
  | cases3  -- 3 cases (9 languages)
  | cases4  -- 4 cases (9 languages)
  | cases5  -- 5 cases (12 languages)
  | cases6_7  -- 6-7 cases (37 languages)
  | cases8_9  -- 8-9 cases (23 languages)
  | cases10OrMore  -- 10 or more cases (24 languages)
  | exclusivelyBorderlineCaseMarking  -- Exclusively borderline case-marking (24 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 49A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : CaseCount
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 49A dataset (261 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noMorphologicalCaseMarking }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .cases2 }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noMorphologicalCaseMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .cases8_9 }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .cases4 }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .cases2 }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noMorphologicalCaseMarking }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .cases2 }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .cases8_9 }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noMorphologicalCaseMarking }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .cases5 }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noMorphologicalCaseMarking }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .cases5 }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noMorphologicalCaseMarking }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .cases10OrMore }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .cases6_7 }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noMorphologicalCaseMarking }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noMorphologicalCaseMarking }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .cases2 }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .cases10OrMore }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noMorphologicalCaseMarking }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .cases4 }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .cases2 }
  , { walsCode := "bec", language := "Bengali (Chittagong)", iso := "ctg", value := .cases6_7 }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .cases2 }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .cases10OrMore }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noMorphologicalCaseMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .cases8_9 }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .cases8_9 }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .cases5 }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noMorphologicalCaseMarking }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noMorphologicalCaseMarking }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noMorphologicalCaseMarking }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noMorphologicalCaseMarking }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noMorphologicalCaseMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .cases10OrMore }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .noMorphologicalCaseMarking }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .cases6_7 }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .cases3 }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .cases8_9 }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .cases6_7 }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noMorphologicalCaseMarking }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noMorphologicalCaseMarking }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noMorphologicalCaseMarking }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noMorphologicalCaseMarking }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .cases6_7 }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "eng", language := "English", iso := "eng", value := .cases2 }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .cases10OrMore }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .cases10OrMore }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .cases10OrMore }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noMorphologicalCaseMarking }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noMorphologicalCaseMarking }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .cases10OrMore }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noMorphologicalCaseMarking }
  , { walsCode := "frw", language := "Frisian (Western)", iso := "fry", value := .noMorphologicalCaseMarking }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .noMorphologicalCaseMarking }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .cases4 }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .cases8_9 }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .cases6_7 }
  , { walsCode := "ger", language := "German", iso := "deu", value := .cases4 }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .cases6_7 }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .cases10OrMore }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noMorphologicalCaseMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .cases3 }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .cases8_9 }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noMorphologicalCaseMarking }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noMorphologicalCaseMarking }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .cases10OrMore }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noMorphologicalCaseMarking }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noMorphologicalCaseMarking }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noMorphologicalCaseMarking }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noMorphologicalCaseMarking }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .cases8_9 }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noMorphologicalCaseMarking }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .cases6_7 }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .cases10OrMore }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .cases10OrMore }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noMorphologicalCaseMarking }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .cases4 }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noMorphologicalCaseMarking }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .cases6_7 }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .noMorphologicalCaseMarking }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .cases5 }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noMorphologicalCaseMarking }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .cases10OrMore }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .cases2 }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noMorphologicalCaseMarking }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noMorphologicalCaseMarking }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .cases8_9 }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noMorphologicalCaseMarking }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .cases8_9 }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .cases6_7 }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .cases6_7 }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .cases6_7 }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .cases3 }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .cases4 }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noMorphologicalCaseMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .cases10OrMore }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .cases10OrMore }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .cases6_7 }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .cases8_9 }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .cases3 }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noMorphologicalCaseMarking }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noMorphologicalCaseMarking }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noMorphologicalCaseMarking }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noMorphologicalCaseMarking }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .noMorphologicalCaseMarking }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noMorphologicalCaseMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .cases6_7 }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noMorphologicalCaseMarking }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noMorphologicalCaseMarking }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noMorphologicalCaseMarking }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .cases6_7 }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noMorphologicalCaseMarking }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noMorphologicalCaseMarking }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noMorphologicalCaseMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .cases6_7 }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .cases6_7 }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noMorphologicalCaseMarking }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .cases5 }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .cases10OrMore }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noMorphologicalCaseMarking }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noMorphologicalCaseMarking }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .cases5 }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noMorphologicalCaseMarking }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .cases2 }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .cases10OrMore }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .cases6_7 }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noMorphologicalCaseMarking }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .cases3 }
  , { walsCode := "mdr", language := "Madurese", iso := "mad", value := .noMorphologicalCaseMarking }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noMorphologicalCaseMarking }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noMorphologicalCaseMarking }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .cases6_7 }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .cases6_7 }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noMorphologicalCaseMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .cases8_9 }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noMorphologicalCaseMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .cases2 }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .cases5 }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .cases6_7 }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noMorphologicalCaseMarking }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .cases10OrMore }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noMorphologicalCaseMarking }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .cases2 }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .cases6_7 }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .cases6_7 }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noMorphologicalCaseMarking }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noMorphologicalCaseMarking }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .cases10OrMore }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .cases8_9 }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .cases4 }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noMorphologicalCaseMarking }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .cases2 }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noMorphologicalCaseMarking }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noMorphologicalCaseMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .cases6_7 }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .cases10OrMore }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noMorphologicalCaseMarking }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .cases5 }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .cases8_9 }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noMorphologicalCaseMarking }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .cases6_7 }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .cases10OrMore }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noMorphologicalCaseMarking }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .cases6_7 }
  , { walsCode := "ots", language := "Otomí (Sierra)", iso := "otm", value := .noMorphologicalCaseMarking }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noMorphologicalCaseMarking }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noMorphologicalCaseMarking }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noMorphologicalCaseMarking }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .cases2 }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .cases3 }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .cases3 }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .cases2 }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .cases10OrMore }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .cases6_7 }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .cases6_7 }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .cases6_7 }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .cases2 }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .cases8_9 }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .cases8_9 }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noMorphologicalCaseMarking }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .cases6_7 }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .cases2 }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .cases6_7 }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .cases6_7 }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noMorphologicalCaseMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .cases2 }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .cases3 }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noMorphologicalCaseMarking }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .cases5 }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .cases6_7 }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .cases5 }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noMorphologicalCaseMarking }
  , { walsCode := "som", language := "Somali", iso := "som", value := .cases3 }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noMorphologicalCaseMarking }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .cases2 }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .cases4 }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noMorphologicalCaseMarking }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .cases2 }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noMorphologicalCaseMarking }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noMorphologicalCaseMarking }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .cases2 }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noMorphologicalCaseMarking }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noMorphologicalCaseMarking }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noMorphologicalCaseMarking }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .cases8_9 }
  , { walsCode := "tda", language := "Toda", iso := "tcx", value := .cases10OrMore }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .cases5 }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noMorphologicalCaseMarking }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noMorphologicalCaseMarking }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .cases6_7 }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .cases6_7 }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noMorphologicalCaseMarking }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .cases8_9 }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .cases10OrMore }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noMorphologicalCaseMarking }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .cases8_9 }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .cases2 }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noMorphologicalCaseMarking }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noMorphologicalCaseMarking }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .cases8_9 }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .cases5 }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .cases8_9 }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noMorphologicalCaseMarking }
  , { walsCode := "was", language := "Washo", iso := "was", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .noMorphologicalCaseMarking }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noMorphologicalCaseMarking }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .cases4 }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .cases2 }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .cases6_7 }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .cases8_9 }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noMorphologicalCaseMarking }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .cases8_9 }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .cases6_7 }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .exclusivelyBorderlineCaseMarking }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .cases2 }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noMorphologicalCaseMarking }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noMorphologicalCaseMarking }
  ]

-- Count verification
theorem total_count : allData.length = 261 := by native_decide

theorem count_noMorphologicalCaseMarking :
    (allData.filter (·.value == .noMorphologicalCaseMarking)).length = 100 := by native_decide
theorem count_cases2 :
    (allData.filter (·.value == .cases2)).length = 23 := by native_decide
theorem count_cases3 :
    (allData.filter (·.value == .cases3)).length = 9 := by native_decide
theorem count_cases4 :
    (allData.filter (·.value == .cases4)).length = 9 := by native_decide
theorem count_cases5 :
    (allData.filter (·.value == .cases5)).length = 12 := by native_decide
theorem count_cases6_7 :
    (allData.filter (·.value == .cases6_7)).length = 37 := by native_decide
theorem count_cases8_9 :
    (allData.filter (·.value == .cases8_9)).length = 23 := by native_decide
theorem count_cases10OrMore :
    (allData.filter (·.value == .cases10OrMore)).length = 24 := by native_decide
theorem count_exclusivelyBorderlineCaseMarking :
    (allData.filter (·.value == .exclusivelyBorderlineCaseMarking)).length = 24 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F49A
