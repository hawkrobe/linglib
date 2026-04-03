import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 50A: Asymmetrical Case-Marking
@cite{iggesen-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 50A`.

Chapter 50, 261 languages.
-/

namespace Core.WALS.F50A

/-- WALS 50A values. -/
inductive AsymmetricalCaseMarking where
  | noCaseMarking  -- No case-marking (81 languages)
  | symmetrical  -- Symmetrical (79 languages)
  | additiveQuantitativelyAsymmetrical  -- Additive-quantitatively asymmetrical (53 languages)
  | subtractiveQuantitativelyAsymmetrical  -- Subtractive-quantitatively asymmetrical (20 languages)
  | qualitativelyAsymmetrical  -- Qualitatively asymmetrical (7 languages)
  | syncretismInRelevantNpTypes  -- Syncretism in relevant NP-types (21 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 50A dataset (261 languages). -/
def allData : List (Datapoint AsymmetricalCaseMarking) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noCaseMarking }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .symmetrical }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noCaseMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .symmetrical }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .symmetrical }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .syncretismInRelevantNpTypes }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noCaseMarking }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .symmetrical }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .symmetrical }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .symmetrical }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .symmetrical }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noCaseMarking }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noCaseMarking }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noCaseMarking }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .symmetrical }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noCaseMarking }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noCaseMarking }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .symmetrical }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .syncretismInRelevantNpTypes }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noCaseMarking }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .symmetrical }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .syncretismInRelevantNpTypes }
  , { walsCode := "bec", language := "Bengali (Chittagong)", iso := "ctg", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .symmetrical }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .symmetrical }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .symmetrical }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noCaseMarking }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noCaseMarking }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .symmetrical }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noCaseMarking }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noCaseMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .noCaseMarking }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .symmetrical }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .symmetrical }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .symmetrical }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .symmetrical }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noCaseMarking }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noCaseMarking }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noCaseMarking }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .qualitativelyAsymmetrical }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "eng", language := "English", iso := "eng", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .symmetrical }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .symmetrical }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .symmetrical }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noCaseMarking }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noCaseMarking }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noCaseMarking }
  , { walsCode := "frw", language := "Frisian (Western)", iso := "fry", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .noCaseMarking }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .symmetrical }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "ger", language := "German", iso := "deu", value := .syncretismInRelevantNpTypes }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noCaseMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .syncretismInRelevantNpTypes }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .syncretismInRelevantNpTypes }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noCaseMarking }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .syncretismInRelevantNpTypes }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noCaseMarking }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noCaseMarking }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noCaseMarking }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noCaseMarking }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .symmetrical }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .symmetrical }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .syncretismInRelevantNpTypes }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noCaseMarking }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .syncretismInRelevantNpTypes }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noCaseMarking }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .symmetrical }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .symmetrical }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noCaseMarking }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .syncretismInRelevantNpTypes }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .symmetrical }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .symmetrical }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noCaseMarking }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .symmetrical }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noCaseMarking }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .qualitativelyAsymmetrical }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .symmetrical }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .symmetrical }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noCaseMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .symmetrical }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .symmetrical }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .symmetrical }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .symmetrical }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .symmetrical }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noCaseMarking }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noCaseMarking }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noCaseMarking }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noCaseMarking }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .noCaseMarking }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .symmetrical }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noCaseMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .symmetrical }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noCaseMarking }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noCaseMarking }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .symmetrical }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noCaseMarking }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noCaseMarking }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .syncretismInRelevantNpTypes }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .symmetrical }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noCaseMarking }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .symmetrical }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .symmetrical }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noCaseMarking }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noCaseMarking }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .syncretismInRelevantNpTypes }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noCaseMarking }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .syncretismInRelevantNpTypes }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noCaseMarking }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .symmetrical }
  , { walsCode := "mdr", language := "Madurese", iso := "mad", value := .noCaseMarking }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noCaseMarking }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .symmetrical }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noCaseMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .qualitativelyAsymmetrical }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noCaseMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .symmetrical }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .symmetrical }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .symmetrical }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noCaseMarking }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .syncretismInRelevantNpTypes }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .symmetrical }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .symmetrical }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .symmetrical }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noCaseMarking }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noCaseMarking }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .symmetrical }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .symmetrical }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noCaseMarking }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .symmetrical }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noCaseMarking }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noCaseMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .symmetrical }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .qualitativelyAsymmetrical }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .symmetrical }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noCaseMarking }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .symmetrical }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noCaseMarking }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "ots", language := "Otomí (Sierra)", iso := "otm", value := .noCaseMarking }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noCaseMarking }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noCaseMarking }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .syncretismInRelevantNpTypes }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .symmetrical }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .symmetrical }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .qualitativelyAsymmetrical }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .syncretismInRelevantNpTypes }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .symmetrical }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .symmetrical }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .symmetrical }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .symmetrical }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .syncretismInRelevantNpTypes }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noCaseMarking }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .symmetrical }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .syncretismInRelevantNpTypes }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noCaseMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .symmetrical }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noCaseMarking }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .syncretismInRelevantNpTypes }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .symmetrical }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noCaseMarking }
  , { walsCode := "som", language := "Somali", iso := "som", value := .symmetrical }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .syncretismInRelevantNpTypes }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .symmetrical }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noCaseMarking }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noCaseMarking }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noCaseMarking }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noCaseMarking }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noCaseMarking }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tda", language := "Toda", iso := "tcx", value := .symmetrical }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .symmetrical }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noCaseMarking }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .symmetrical }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .symmetrical }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noCaseMarking }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .symmetrical }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .symmetrical }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noCaseMarking }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noCaseMarking }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .qualitativelyAsymmetrical }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noCaseMarking }
  , { walsCode := "was", language := "Washo", iso := "was", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .noCaseMarking }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .symmetrical }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noCaseMarking }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .symmetrical }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .symmetrical }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .symmetrical }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .qualitativelyAsymmetrical }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .subtractiveQuantitativelyAsymmetrical }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noCaseMarking }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .symmetrical }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .syncretismInRelevantNpTypes }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .additiveQuantitativelyAsymmetrical }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .symmetrical }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noCaseMarking }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .additiveQuantitativelyAsymmetrical }
  ]

-- Count verification
theorem total_count : allData.length = 261 := by native_decide

theorem count_noCaseMarking :
    (allData.filter (·.value == .noCaseMarking)).length = 81 := by native_decide
theorem count_symmetrical :
    (allData.filter (·.value == .symmetrical)).length = 79 := by native_decide
theorem count_additiveQuantitativelyAsymmetrical :
    (allData.filter (·.value == .additiveQuantitativelyAsymmetrical)).length = 53 := by native_decide
theorem count_subtractiveQuantitativelyAsymmetrical :
    (allData.filter (·.value == .subtractiveQuantitativelyAsymmetrical)).length = 20 := by native_decide
theorem count_qualitativelyAsymmetrical :
    (allData.filter (·.value == .qualitativelyAsymmetrical)).length = 7 := by native_decide
theorem count_syncretismInRelevantNpTypes :
    (allData.filter (·.value == .syncretismInRelevantNpTypes)).length = 21 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F50A
