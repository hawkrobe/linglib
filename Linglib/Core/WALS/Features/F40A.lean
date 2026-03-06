/-!
# WALS Feature 40A: Inclusive/Exclusive Distinction in Verbal Inflection
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 40A`.

Chapter 40, 200 languages.
-/

namespace Core.WALS.F40A

/-- WALS 40A values. -/
inductive InclusiveExclusiveDistinctionInVerbalInflection where
  | noPersonMarking  -- No person marking (70 languages)
  | weTheSameAsI  -- 'We' the same as 'I' (12 languages)
  | noInclusiveExclusive  -- No inclusive/exclusive (79 languages)
  | onlyInclusive  -- Only inclusive (9 languages)
  | inclusiveExclusive  -- Inclusive/exclusive (30 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 40A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : InclusiveExclusiveDistinctionInVerbalInflection
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 40A dataset (200 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .weTheSameAsI }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noInclusiveExclusive }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .weTheSameAsI }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .inclusiveExclusive }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noInclusiveExclusive }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noInclusiveExclusive }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noInclusiveExclusive }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noInclusiveExclusive }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noPersonMarking }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noInclusiveExclusive }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noInclusiveExclusive }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noInclusiveExclusive }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .weTheSameAsI }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .onlyInclusive }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noPersonMarking }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noPersonMarking }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noPersonMarking }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noInclusiveExclusive }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noPersonMarking }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noPersonMarking }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noInclusiveExclusive }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noInclusiveExclusive }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noInclusiveExclusive }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noPersonMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noPersonMarking }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noInclusiveExclusive }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noInclusiveExclusive }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .onlyInclusive }
  , { walsCode := "car", language := "Carib", iso := "car", value := .onlyInclusive }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .inclusiveExclusive }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noPersonMarking }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noInclusiveExclusive }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noInclusiveExclusive }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noPersonMarking }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .inclusiveExclusive }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .onlyInclusive }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .weTheSameAsI }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noInclusiveExclusive }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .inclusiveExclusive }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noPersonMarking }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noInclusiveExclusive }
  , { walsCode := "eng", language := "English", iso := "eng", value := .weTheSameAsI }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noPersonMarking }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .inclusiveExclusive }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noPersonMarking }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noPersonMarking }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noInclusiveExclusive }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noInclusiveExclusive }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noInclusiveExclusive }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noPersonMarking }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .weTheSameAsI }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noInclusiveExclusive }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .inclusiveExclusive }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noPersonMarking }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noInclusiveExclusive }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noInclusiveExclusive }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .inclusiveExclusive }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noPersonMarking }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noInclusiveExclusive }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noPersonMarking }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noInclusiveExclusive }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noPersonMarking }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .inclusiveExclusive }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noPersonMarking }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .noInclusiveExclusive }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noInclusiveExclusive }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noPersonMarking }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noPersonMarking }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noInclusiveExclusive }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noPersonMarking }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noPersonMarking }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noPersonMarking }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noInclusiveExclusive }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noInclusiveExclusive }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noInclusiveExclusive }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noPersonMarking }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noPersonMarking }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noInclusiveExclusive }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noInclusiveExclusive }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noInclusiveExclusive }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noPersonMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noPersonMarking }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noPersonMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noInclusiveExclusive }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noInclusiveExclusive }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noPersonMarking }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noPersonMarking }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noPersonMarking }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noPersonMarking }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .inclusiveExclusive }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .inclusiveExclusive }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noPersonMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noInclusiveExclusive }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noInclusiveExclusive }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noInclusiveExclusive }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noPersonMarking }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noPersonMarking }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noPersonMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .inclusiveExclusive }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .inclusiveExclusive }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .weTheSameAsI }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noPersonMarking }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noInclusiveExclusive }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noInclusiveExclusive }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noInclusiveExclusive }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noInclusiveExclusive }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .inclusiveExclusive }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noPersonMarking }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noPersonMarking }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noInclusiveExclusive }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noInclusiveExclusive }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noInclusiveExclusive }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noPersonMarking }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noPersonMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .inclusiveExclusive }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noPersonMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noInclusiveExclusive }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .inclusiveExclusive }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .weTheSameAsI }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noInclusiveExclusive }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noPersonMarking }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .inclusiveExclusive }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noInclusiveExclusive }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noPersonMarking }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .inclusiveExclusive }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .onlyInclusive }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .inclusiveExclusive }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .weTheSameAsI }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noInclusiveExclusive }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noPersonMarking }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noInclusiveExclusive }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noPersonMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noInclusiveExclusive }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .weTheSameAsI }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .onlyInclusive }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noPersonMarking }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noPersonMarking }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noInclusiveExclusive }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noInclusiveExclusive }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .inclusiveExclusive }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .inclusiveExclusive }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noInclusiveExclusive }
  , { walsCode := "oix", language := "Otomí (Ixtenco)", iso := "otz", value := .weTheSameAsI }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .inclusiveExclusive }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noPersonMarking }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .onlyInclusive }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noInclusiveExclusive }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noInclusiveExclusive }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noPersonMarking }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noPersonMarking }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noPersonMarking }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noPersonMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noInclusiveExclusive }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noInclusiveExclusive }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noPersonMarking }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noInclusiveExclusive }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noPersonMarking }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noPersonMarking }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noPersonMarking }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .onlyInclusive }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noInclusiveExclusive }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noPersonMarking }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noInclusiveExclusive }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noInclusiveExclusive }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noInclusiveExclusive }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .inclusiveExclusive }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noPersonMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noInclusiveExclusive }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .inclusiveExclusive }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noPersonMarking }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noPersonMarking }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .inclusiveExclusive }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noInclusiveExclusive }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noPersonMarking }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noInclusiveExclusive }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noInclusiveExclusive }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noInclusiveExclusive }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noInclusiveExclusive }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noInclusiveExclusive }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .inclusiveExclusive }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noInclusiveExclusive }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noInclusiveExclusive }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noPersonMarking }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noPersonMarking }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noPersonMarking }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .inclusiveExclusive }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .inclusiveExclusive }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .onlyInclusive }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .weTheSameAsI }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .inclusiveExclusive }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noPersonMarking }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noPersonMarking }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noInclusiveExclusive }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noPersonMarking }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .inclusiveExclusive }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noInclusiveExclusive }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noInclusiveExclusive }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noInclusiveExclusive }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .inclusiveExclusive }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noInclusiveExclusive }
  ]

-- Count verification
theorem total_count : allData.length = 200 := by native_decide

theorem count_noPersonMarking :
    (allData.filter (·.value == .noPersonMarking)).length = 70 := by native_decide
theorem count_weTheSameAsI :
    (allData.filter (·.value == .weTheSameAsI)).length = 12 := by native_decide
theorem count_noInclusiveExclusive :
    (allData.filter (·.value == .noInclusiveExclusive)).length = 79 := by native_decide
theorem count_onlyInclusive :
    (allData.filter (·.value == .onlyInclusive)).length = 9 := by native_decide
theorem count_inclusiveExclusive :
    (allData.filter (·.value == .inclusiveExclusive)).length = 30 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F40A
