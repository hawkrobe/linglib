/-!
# WALS Feature 45A: Politeness Distinctions in Pronouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 45A`.

Chapter 45, 207 languages.
-/

namespace Core.WALS.F45A

/-- WALS 45A values. -/
inductive PolitenessDistinctionsInPronouns where
  | noPolitenessDistinction  -- No politeness distinction (136 languages)
  | binaryPolitenessDistinction  -- Binary politeness distinction (49 languages)
  | multiplePolitenessDistinctions  -- Multiple politeness distinctions (15 languages)
  | pronounsAvoidedForPoliteness  -- Pronouns avoided for politeness (7 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 45A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PolitenessDistinctionsInPronouns
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 45A dataset (207 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abu", language := "Abun", iso := "kgr", value := .noPolitenessDistinction }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noPolitenessDistinction }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .binaryPolitenessDistinction }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noPolitenessDistinction }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noPolitenessDistinction }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noPolitenessDistinction }
  , { walsCode := "ago", language := "Angolar", iso := "aoa", value := .binaryPolitenessDistinction }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noPolitenessDistinction }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noPolitenessDistinction }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noPolitenessDistinction }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .binaryPolitenessDistinction }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noPolitenessDistinction }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noPolitenessDistinction }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noPolitenessDistinction }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .noPolitenessDistinction }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noPolitenessDistinction }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noPolitenessDistinction }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .noPolitenessDistinction }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noPolitenessDistinction }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .binaryPolitenessDistinction }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .binaryPolitenessDistinction }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noPolitenessDistinction }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noPolitenessDistinction }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .binaryPolitenessDistinction }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noPolitenessDistinction }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noPolitenessDistinction }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noPolitenessDistinction }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noPolitenessDistinction }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noPolitenessDistinction }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noPolitenessDistinction }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noPolitenessDistinction }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .noPolitenessDistinction }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .binaryPolitenessDistinction }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noPolitenessDistinction }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noPolitenessDistinction }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noPolitenessDistinction }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .binaryPolitenessDistinction }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .noPolitenessDistinction }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .binaryPolitenessDistinction }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noPolitenessDistinction }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noPolitenessDistinction }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noPolitenessDistinction }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noPolitenessDistinction }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .binaryPolitenessDistinction }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .binaryPolitenessDistinction }
  , { walsCode := "fre", language := "French", iso := "fra", value := .binaryPolitenessDistinction }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noPolitenessDistinction }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .binaryPolitenessDistinction }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noPolitenessDistinction }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .binaryPolitenessDistinction }
  , { walsCode := "ger", language := "German", iso := "deu", value := .binaryPolitenessDistinction }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noPolitenessDistinction }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noPolitenessDistinction }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .binaryPolitenessDistinction }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noPolitenessDistinction }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noPolitenessDistinction }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noPolitenessDistinction }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noPolitenessDistinction }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noPolitenessDistinction }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noPolitenessDistinction }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .multiplePolitenessDistinctions }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noPolitenessDistinction }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noPolitenessDistinction }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .multiplePolitenessDistinctions }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noPolitenessDistinction }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noPolitenessDistinction }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noPolitenessDistinction }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noPolitenessDistinction }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .binaryPolitenessDistinction }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noPolitenessDistinction }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noPolitenessDistinction }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noPolitenessDistinction }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .noPolitenessDistinction }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .multiplePolitenessDistinctions }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noPolitenessDistinction }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noPolitenessDistinction }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .binaryPolitenessDistinction }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noPolitenessDistinction }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noPolitenessDistinction }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noPolitenessDistinction }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noPolitenessDistinction }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .binaryPolitenessDistinction }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .binaryPolitenessDistinction }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noPolitenessDistinction }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noPolitenessDistinction }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noPolitenessDistinction }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noPolitenessDistinction }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noPolitenessDistinction }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noPolitenessDistinction }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noPolitenessDistinction }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noPolitenessDistinction }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .binaryPolitenessDistinction }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .binaryPolitenessDistinction }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noPolitenessDistinction }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noPolitenessDistinction }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noPolitenessDistinction }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .noPolitenessDistinction }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noPolitenessDistinction }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noPolitenessDistinction }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noPolitenessDistinction }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .binaryPolitenessDistinction }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noPolitenessDistinction }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noPolitenessDistinction }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .noPolitenessDistinction }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .multiplePolitenessDistinctions }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .binaryPolitenessDistinction }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noPolitenessDistinction }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noPolitenessDistinction }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .multiplePolitenessDistinctions }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .binaryPolitenessDistinction }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .noPolitenessDistinction }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noPolitenessDistinction }
  , { walsCode := "mnx", language := "Manx", iso := "glv", value := .binaryPolitenessDistinction }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noPolitenessDistinction }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noPolitenessDistinction }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .multiplePolitenessDistinctions }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noPolitenessDistinction }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noPolitenessDistinction }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .noPolitenessDistinction }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noPolitenessDistinction }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noPolitenessDistinction }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noPolitenessDistinction }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noPolitenessDistinction }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .binaryPolitenessDistinction }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noPolitenessDistinction }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .binaryPolitenessDistinction }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .binaryPolitenessDistinction }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .multiplePolitenessDistinctions }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .binaryPolitenessDistinction }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .multiplePolitenessDistinctions }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noPolitenessDistinction }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noPolitenessDistinction }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noPolitenessDistinction }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .noPolitenessDistinction }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .binaryPolitenessDistinction }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noPolitenessDistinction }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noPolitenessDistinction }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noPolitenessDistinction }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noPolitenessDistinction }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noPolitenessDistinction }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noPolitenessDistinction }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noPolitenessDistinction }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .binaryPolitenessDistinction }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .binaryPolitenessDistinction }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .noPolitenessDistinction }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .binaryPolitenessDistinction }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noPolitenessDistinction }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noPolitenessDistinction }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noPolitenessDistinction }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .multiplePolitenessDistinctions }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .binaryPolitenessDistinction }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noPolitenessDistinction }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .binaryPolitenessDistinction }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .binaryPolitenessDistinction }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noPolitenessDistinction }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noPolitenessDistinction }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .multiplePolitenessDistinctions }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .binaryPolitenessDistinction }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .binaryPolitenessDistinction }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noPolitenessDistinction }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .noPolitenessDistinction }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noPolitenessDistinction }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .noPolitenessDistinction }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .multiplePolitenessDistinctions }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noPolitenessDistinction }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noPolitenessDistinction }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .binaryPolitenessDistinction }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .binaryPolitenessDistinction }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noPolitenessDistinction }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noPolitenessDistinction }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .binaryPolitenessDistinction }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .binaryPolitenessDistinction }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .multiplePolitenessDistinctions }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .multiplePolitenessDistinctions }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .noPolitenessDistinction }
  , { walsCode := "tay", language := "Tayo", iso := "cks", value := .binaryPolitenessDistinction }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .binaryPolitenessDistinction }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .binaryPolitenessDistinction }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noPolitenessDistinction }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noPolitenessDistinction }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .multiplePolitenessDistinctions }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .binaryPolitenessDistinction }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .noPolitenessDistinction }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .multiplePolitenessDistinctions }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .pronounsAvoidedForPoliteness }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noPolitenessDistinction }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noPolitenessDistinction }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noPolitenessDistinction }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .binaryPolitenessDistinction }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noPolitenessDistinction }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noPolitenessDistinction }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noPolitenessDistinction }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noPolitenessDistinction }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noPolitenessDistinction }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .noPolitenessDistinction }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .binaryPolitenessDistinction }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .noPolitenessDistinction }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noPolitenessDistinction }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noPolitenessDistinction }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noPolitenessDistinction }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noPolitenessDistinction }
  ]

-- Count verification
theorem total_count : allData.length = 207 := by native_decide

theorem count_noPolitenessDistinction :
    (allData.filter (·.value == .noPolitenessDistinction)).length = 136 := by native_decide
theorem count_binaryPolitenessDistinction :
    (allData.filter (·.value == .binaryPolitenessDistinction)).length = 49 := by native_decide
theorem count_multiplePolitenessDistinctions :
    (allData.filter (·.value == .multiplePolitenessDistinctions)).length = 15 := by native_decide
theorem count_pronounsAvoidedForPoliteness :
    (allData.filter (·.value == .pronounsAvoidedForPoliteness)).length = 7 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F45A
