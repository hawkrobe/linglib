/-!
# WALS Feature 28A: Case Syncretism
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 28A`.

Chapter 28, 198 languages.
-/

namespace Core.WALS.F28A

/-- WALS 28A values. -/
inductive CaseSyncretism where
  | noCaseMarking  -- No case marking (123 languages)
  | coreCasesOnly  -- Core cases only (18 languages)
  | coreAndNonCore  -- Core and non-core (22 languages)
  | noSyncretism  -- No syncretism (35 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 28A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : CaseSyncretism
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 28A dataset (198 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noCaseMarking }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noCaseMarking }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noCaseMarking }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noCaseMarking }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noCaseMarking }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noCaseMarking }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noCaseMarking }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noCaseMarking }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .coreAndNonCore }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noCaseMarking }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .coreAndNonCore }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noCaseMarking }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noCaseMarking }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noCaseMarking }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noCaseMarking }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noCaseMarking }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noCaseMarking }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .coreCasesOnly }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noCaseMarking }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noSyncretism }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noCaseMarking }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noCaseMarking }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noSyncretism }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noCaseMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noCaseMarking }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .coreAndNonCore }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noSyncretism }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noCaseMarking }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noCaseMarking }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noCaseMarking }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noCaseMarking }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noCaseMarking }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .coreAndNonCore }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .noSyncretism }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .coreAndNonCore }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noCaseMarking }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noCaseMarking }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noCaseMarking }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noCaseMarking }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noCaseMarking }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noCaseMarking }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noCaseMarking }
  , { walsCode := "eng", language := "English", iso := "eng", value := .coreCasesOnly }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noSyncretism }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noSyncretism }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noCaseMarking }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .coreCasesOnly }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .coreAndNonCore }
  , { walsCode := "fre", language := "French", iso := "fra", value := .coreAndNonCore }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noCaseMarking }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noSyncretism }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .coreAndNonCore }
  , { walsCode := "ger", language := "German", iso := "deu", value := .coreAndNonCore }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noCaseMarking }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noCaseMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .coreAndNonCore }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .coreCasesOnly }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noCaseMarking }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noCaseMarking }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noCaseMarking }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noSyncretism }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noCaseMarking }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .coreAndNonCore }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noCaseMarking }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noCaseMarking }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noSyncretism }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noSyncretism }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noSyncretism }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noCaseMarking }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noSyncretism }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noSyncretism }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noCaseMarking }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .coreAndNonCore }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noCaseMarking }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .coreAndNonCore }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noCaseMarking }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noCaseMarking }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noCaseMarking }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noSyncretism }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noCaseMarking }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noCaseMarking }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noCaseMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .coreAndNonCore }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noCaseMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noSyncretism }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noCaseMarking }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noSyncretism }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noCaseMarking }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noCaseMarking }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noCaseMarking }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noCaseMarking }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noCaseMarking }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noCaseMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noSyncretism }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noCaseMarking }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noCaseMarking }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noCaseMarking }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noCaseMarking }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noCaseMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .coreAndNonCore }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noCaseMarking }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noCaseMarking }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noSyncretism }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .coreCasesOnly }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noCaseMarking }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noCaseMarking }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .coreAndNonCore }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noCaseMarking }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noSyncretism }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .coreAndNonCore }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noCaseMarking }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noCaseMarking }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noCaseMarking }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noCaseMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .coreCasesOnly }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noCaseMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noCaseMarking }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noCaseMarking }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noSyncretism }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noCaseMarking }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .coreAndNonCore }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noCaseMarking }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noCaseMarking }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noSyncretism }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noSyncretism }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noCaseMarking }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noCaseMarking }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .coreCasesOnly }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noCaseMarking }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noCaseMarking }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noCaseMarking }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noCaseMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .coreAndNonCore }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noSyncretism }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noCaseMarking }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .coreAndNonCore }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noSyncretism }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noCaseMarking }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noSyncretism }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noSyncretism }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .coreCasesOnly }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noCaseMarking }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noCaseMarking }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noSyncretism }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noCaseMarking }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .coreCasesOnly }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noCaseMarking }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noCaseMarking }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .coreCasesOnly }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noSyncretism }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noCaseMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noSyncretism }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noCaseMarking }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noCaseMarking }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .coreAndNonCore }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noCaseMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noCaseMarking }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noCaseMarking }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noCaseMarking }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noCaseMarking }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noCaseMarking }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .coreAndNonCore }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noCaseMarking }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .coreCasesOnly }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noCaseMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noCaseMarking }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noCaseMarking }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noCaseMarking }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noCaseMarking }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noCaseMarking }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noCaseMarking }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noSyncretism }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noCaseMarking }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noCaseMarking }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noCaseMarking }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noSyncretism }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noSyncretism }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noCaseMarking }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noCaseMarking }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noCaseMarking }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noCaseMarking }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .coreCasesOnly }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .coreCasesOnly }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noSyncretism }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noCaseMarking }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noCaseMarking }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noCaseMarking }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noCaseMarking }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .coreCasesOnly }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .coreCasesOnly }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noCaseMarking }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noSyncretism }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noCaseMarking }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .coreCasesOnly }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .coreCasesOnly }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .coreCasesOnly }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noSyncretism }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noCaseMarking }
  ]

-- Count verification
theorem total_count : allData.length = 198 := by native_decide

theorem count_noCaseMarking :
    (allData.filter (·.value == .noCaseMarking)).length = 123 := by native_decide
theorem count_coreCasesOnly :
    (allData.filter (·.value == .coreCasesOnly)).length = 18 := by native_decide
theorem count_coreAndNonCore :
    (allData.filter (·.value == .coreAndNonCore)).length = 22 := by native_decide
theorem count_noSyncretism :
    (allData.filter (·.value == .noSyncretism)).length = 35 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F28A
