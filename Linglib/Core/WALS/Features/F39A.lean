import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 39A: Inclusive/Exclusive Distinction in Independent Pronouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 39A`.

Chapter 39, 200 languages.
-/

namespace Core.WALS.F39A

/-- WALS 39A values. -/
inductive InclusiveExclusiveDistinctionInIndependentPronouns where
  | noWe  -- No 'we' (2 languages)
  | weTheSameAsI  -- 'We' the same as 'I' (10 languages)
  | noInclusiveExclusive  -- No inclusive/exclusive (120 languages)
  | onlyInclusive  -- Only inclusive (5 languages)
  | inclusiveExclusive  -- Inclusive/exclusive (63 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 39A dataset (200 languages). -/
def allData : List (Datapoint InclusiveExclusiveDistinctionInIndependentPronouns) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noInclusiveExclusive }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .inclusiveExclusive }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noWe }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .inclusiveExclusive }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noInclusiveExclusive }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noInclusiveExclusive }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noInclusiveExclusive }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noInclusiveExclusive }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .inclusiveExclusive }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noInclusiveExclusive }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noInclusiveExclusive }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noInclusiveExclusive }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noInclusiveExclusive }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .onlyInclusive }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noInclusiveExclusive }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noInclusiveExclusive }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .inclusiveExclusive }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noInclusiveExclusive }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .inclusiveExclusive }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noInclusiveExclusive }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noInclusiveExclusive }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noInclusiveExclusive }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noInclusiveExclusive }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .inclusiveExclusive }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .weTheSameAsI }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noInclusiveExclusive }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noInclusiveExclusive }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .onlyInclusive }
  , { walsCode := "car", language := "Carib", iso := "car", value := .inclusiveExclusive }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .inclusiveExclusive }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .inclusiveExclusive }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .inclusiveExclusive }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noInclusiveExclusive }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .inclusiveExclusive }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .inclusiveExclusive }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .inclusiveExclusive }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noInclusiveExclusive }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noInclusiveExclusive }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .inclusiveExclusive }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .inclusiveExclusive }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noInclusiveExclusive }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noInclusiveExclusive }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noInclusiveExclusive }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .inclusiveExclusive }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noInclusiveExclusive }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .inclusiveExclusive }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noInclusiveExclusive }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noInclusiveExclusive }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noInclusiveExclusive }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .inclusiveExclusive }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noInclusiveExclusive }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noInclusiveExclusive }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .inclusiveExclusive }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noInclusiveExclusive }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noInclusiveExclusive }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noInclusiveExclusive }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .inclusiveExclusive }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noInclusiveExclusive }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noInclusiveExclusive }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noInclusiveExclusive }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noInclusiveExclusive }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noInclusiveExclusive }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .inclusiveExclusive }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noInclusiveExclusive }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .noInclusiveExclusive }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noInclusiveExclusive }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noInclusiveExclusive }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noInclusiveExclusive }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noInclusiveExclusive }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .onlyInclusive }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .inclusiveExclusive }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .inclusiveExclusive }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noInclusiveExclusive }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noInclusiveExclusive }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noInclusiveExclusive }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noInclusiveExclusive }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .inclusiveExclusive }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noInclusiveExclusive }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noInclusiveExclusive }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noInclusiveExclusive }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noInclusiveExclusive }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .inclusiveExclusive }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .inclusiveExclusive }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noInclusiveExclusive }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noInclusiveExclusive }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noInclusiveExclusive }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noInclusiveExclusive }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noInclusiveExclusive }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noInclusiveExclusive }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .inclusiveExclusive }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .weTheSameAsI }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noInclusiveExclusive }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noInclusiveExclusive }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noInclusiveExclusive }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noInclusiveExclusive }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noInclusiveExclusive }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noInclusiveExclusive }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noInclusiveExclusive }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .inclusiveExclusive }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .inclusiveExclusive }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noInclusiveExclusive }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .inclusiveExclusive }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noInclusiveExclusive }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noInclusiveExclusive }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noInclusiveExclusive }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noInclusiveExclusive }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .inclusiveExclusive }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noInclusiveExclusive }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noInclusiveExclusive }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noInclusiveExclusive }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noInclusiveExclusive }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noInclusiveExclusive }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .inclusiveExclusive }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .inclusiveExclusive }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .inclusiveExclusive }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .inclusiveExclusive }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .weTheSameAsI }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .inclusiveExclusive }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .weTheSameAsI }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .weTheSameAsI }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .inclusiveExclusive }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .inclusiveExclusive }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noInclusiveExclusive }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noInclusiveExclusive }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .inclusiveExclusive }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .onlyInclusive }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .inclusiveExclusive }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noInclusiveExclusive }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noInclusiveExclusive }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .inclusiveExclusive }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noInclusiveExclusive }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noInclusiveExclusive }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noInclusiveExclusive }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noInclusiveExclusive }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .inclusiveExclusive }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .inclusiveExclusive }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .inclusiveExclusive }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noInclusiveExclusive }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noInclusiveExclusive }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .inclusiveExclusive }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .weTheSameAsI }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noInclusiveExclusive }
  , { walsCode := "oix", language := "Otomí (Ixtenco)", iso := "otz", value := .inclusiveExclusive }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .inclusiveExclusive }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .inclusiveExclusive }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .inclusiveExclusive }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noInclusiveExclusive }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noInclusiveExclusive }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noWe }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noInclusiveExclusive }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noInclusiveExclusive }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .weTheSameAsI }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noInclusiveExclusive }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noInclusiveExclusive }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .inclusiveExclusive }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noInclusiveExclusive }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noInclusiveExclusive }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .inclusiveExclusive }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noInclusiveExclusive }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .onlyInclusive }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noInclusiveExclusive }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noInclusiveExclusive }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noInclusiveExclusive }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noInclusiveExclusive }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noInclusiveExclusive }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .inclusiveExclusive }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noInclusiveExclusive }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noInclusiveExclusive }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .inclusiveExclusive }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .inclusiveExclusive }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .weTheSameAsI }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .inclusiveExclusive }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noInclusiveExclusive }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .weTheSameAsI }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noInclusiveExclusive }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noInclusiveExclusive }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noInclusiveExclusive }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noInclusiveExclusive }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noInclusiveExclusive }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .inclusiveExclusive }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noInclusiveExclusive }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noInclusiveExclusive }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .weTheSameAsI }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .inclusiveExclusive }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noInclusiveExclusive }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .inclusiveExclusive }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .inclusiveExclusive }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .inclusiveExclusive }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noInclusiveExclusive }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .inclusiveExclusive }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noInclusiveExclusive }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noInclusiveExclusive }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noInclusiveExclusive }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noInclusiveExclusive }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .inclusiveExclusive }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noInclusiveExclusive }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noInclusiveExclusive }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noInclusiveExclusive }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .inclusiveExclusive }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noInclusiveExclusive }
  ]

-- Count verification
theorem total_count : allData.length = 200 := by native_decide

theorem count_noWe :
    (allData.filter (·.value == .noWe)).length = 2 := by native_decide
theorem count_weTheSameAsI :
    (allData.filter (·.value == .weTheSameAsI)).length = 10 := by native_decide
theorem count_noInclusiveExclusive :
    (allData.filter (·.value == .noInclusiveExclusive)).length = 120 := by native_decide
theorem count_onlyInclusive :
    (allData.filter (·.value == .onlyInclusive)).length = 5 := by native_decide
theorem count_inclusiveExclusive :
    (allData.filter (·.value == .inclusiveExclusive)).length = 63 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F39A
