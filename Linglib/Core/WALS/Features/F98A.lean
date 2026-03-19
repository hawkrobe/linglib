import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 98A: Alignment of Case Marking of Full Noun Phrases
@cite{comrie-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 98A`.

Chapter 98, 190 languages.
-/

namespace Core.WALS.F98A

/-- WALS 98A values. -/
inductive NPCaseAlignment where
  | neutral  -- Neutral (98 languages)
  | nominativeAccusative  -- Nominative - accusative (standard) (46 languages)
  | nominativeAccusative_3  -- Nominative - accusative (marked nominative) (6 languages)
  | ergativeAbsolutive  -- Ergative - absolutive (32 languages)
  | tripartite  -- Tripartite (4 languages)
  | activeInactive  -- Active-inactive (4 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 98A dataset (190 languages). -/
def allData : List (Datapoint NPCaseAlignment) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .neutral }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .neutral }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .neutral }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .neutral }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .neutral }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .neutral }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .neutral }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .neutral }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .ergativeAbsolutive }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .neutral }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .nominativeAccusative }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .neutral }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .nominativeAccusative }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .nominativeAccusative_3 }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .neutral }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .neutral }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .nominativeAccusative }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .activeInactive }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .neutral }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .ergativeAbsolutive }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .nominativeAccusative_3 }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .nominativeAccusative }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .ergativeAbsolutive }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .nominativeAccusative }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .ergativeAbsolutive }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .nominativeAccusative }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .neutral }
  , { walsCode := "car", language := "Carib", iso := "car", value := .neutral }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .neutral }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .neutral }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .neutral }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .ergativeAbsolutive }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .nominativeAccusative }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .ergativeAbsolutive }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .neutral }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .neutral }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .ergativeAbsolutive }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .neutral }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .activeInactive }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .neutral }
  , { walsCode := "eng", language := "English", iso := "eng", value := .neutral }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .ergativeAbsolutive }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .nominativeAccusative }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .neutral }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .neutral }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .nominativeAccusative }
  , { walsCode := "fre", language := "French", iso := "fra", value := .neutral }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .nominativeAccusative }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .nominativeAccusative }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .activeInactive }
  , { walsCode := "ger", language := "German", iso := "deu", value := .nominativeAccusative }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .ergativeAbsolutive }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .neutral }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .nominativeAccusative }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .ergativeAbsolutive }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .nominativeAccusative }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .neutral }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .neutral }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .neutral }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .nominativeAccusative }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .tripartite }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .neutral }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .neutral }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .nominativeAccusative }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .ergativeAbsolutive }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .nominativeAccusative_3 }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .ergativeAbsolutive }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .activeInactive }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .neutral }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .ergativeAbsolutive }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .nominativeAccusative }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .neutral }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .neutral }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .nominativeAccusative }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .neutral }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .nominativeAccusative }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .nominativeAccusative }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .neutral }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .neutral }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .nominativeAccusative }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .neutral }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .neutral }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .ergativeAbsolutive }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .nominativeAccusative }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .nominativeAccusative }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .neutral }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .neutral }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .neutral }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .neutral }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .neutral }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .nominativeAccusative }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .neutral }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .neutral }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .nominativeAccusative }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .neutral }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .neutral }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .neutral }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .nominativeAccusative }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .neutral }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .ergativeAbsolutive }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .ergativeAbsolutive }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .neutral }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .neutral }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .nominativeAccusative }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .neutral }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .nominativeAccusative }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .ergativeAbsolutive }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .neutral }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .nominativeAccusative }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .neutral }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .nominativeAccusative }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .nominativeAccusative }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .neutral }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .neutral }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .tripartite }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .nominativeAccusative_3 }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .neutral }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .nominativeAccusative }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .neutral }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .neutral }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .nominativeAccusative }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .nominativeAccusative }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .neutral }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .neutral }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .nominativeAccusative_3 }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .neutral }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .nominativeAccusative }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .neutral }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .neutral }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .nominativeAccusative }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .tripartite }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .neutral }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .ergativeAbsolutive }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .neutral }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .neutral }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .nominativeAccusative }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .neutral }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .nominativeAccusative_3 }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .neutral }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .neutral }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .neutral }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .ergativeAbsolutive }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .nominativeAccusative }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .neutral }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .ergativeAbsolutive }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .nominativeAccusative }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .nominativeAccusative }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .neutral }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .neutral }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .nominativeAccusative }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .neutral }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .ergativeAbsolutive }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .tripartite }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .ergativeAbsolutive }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .neutral }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .nominativeAccusative }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .neutral }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .ergativeAbsolutive }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .neutral }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .neutral }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .neutral }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .neutral }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .neutral }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .neutral }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .ergativeAbsolutive }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .ergativeAbsolutive }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .ergativeAbsolutive }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .neutral }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .nominativeAccusative }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .ergativeAbsolutive }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .neutral }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .nominativeAccusative }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .neutral }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .neutral }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .ergativeAbsolutive }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .neutral }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .ergativeAbsolutive }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .neutral }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .neutral }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .neutral }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .neutral }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .nominativeAccusative }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .ergativeAbsolutive }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .neutral }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .neutral }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .nominativeAccusative }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .ergativeAbsolutive }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .neutral }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .ergativeAbsolutive }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .neutral }
  ]

-- Count verification
theorem total_count : allData.length = 190 := by native_decide

theorem count_neutral :
    (allData.filter (·.value == .neutral)).length = 98 := by native_decide
theorem count_nominativeAccusative :
    (allData.filter (·.value == .nominativeAccusative)).length = 46 := by native_decide
theorem count_nominativeAccusative_3 :
    (allData.filter (·.value == .nominativeAccusative_3)).length = 6 := by native_decide
theorem count_ergativeAbsolutive :
    (allData.filter (·.value == .ergativeAbsolutive)).length = 32 := by native_decide
theorem count_tripartite :
    (allData.filter (·.value == .tripartite)).length = 4 := by native_decide
theorem count_activeInactive :
    (allData.filter (·.value == .activeInactive)).length = 4 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F98A
