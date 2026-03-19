import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 29A: Syncretism in Verbal Person/Number Marking
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 29A`.

Chapter 29, 198 languages.
-/

namespace Core.WALS.F29A

/-- WALS 29A values. -/
inductive SyncretismInVerbalPersonNumberMarking where
  | noSubjectPersonNumberMarking  -- No subject person/number marking (57 languages)
  | syncretic  -- Syncretic (60 languages)
  | notSyncretic  -- Not syncretic (81 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 29A dataset (198 languages). -/
def allData : List (Datapoint SyncretismInVerbalPersonNumberMarking) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .syncretic }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .notSyncretic }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .notSyncretic }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .notSyncretic }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .notSyncretic }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .syncretic }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .notSyncretic }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .syncretic }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noSubjectPersonNumberMarking }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .notSyncretic }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .notSyncretic }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .notSyncretic }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .syncretic }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .syncretic }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .syncretic }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noSubjectPersonNumberMarking }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .notSyncretic }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .notSyncretic }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .notSyncretic }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .notSyncretic }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .syncretic }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .notSyncretic }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .notSyncretic }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noSubjectPersonNumberMarking }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noSubjectPersonNumberMarking }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .syncretic }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .notSyncretic }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .syncretic }
  , { walsCode := "car", language := "Carib", iso := "car", value := .syncretic }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .syncretic }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .notSyncretic }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .syncretic }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .syncretic }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .notSyncretic }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noSubjectPersonNumberMarking }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .notSyncretic }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .notSyncretic }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .syncretic }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .syncretic }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .syncretic }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noSubjectPersonNumberMarking }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .syncretic }
  , { walsCode := "eng", language := "English", iso := "eng", value := .syncretic }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noSubjectPersonNumberMarking }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .notSyncretic }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .syncretic }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noSubjectPersonNumberMarking }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .notSyncretic }
  , { walsCode := "fre", language := "French", iso := "fra", value := .syncretic }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .notSyncretic }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noSubjectPersonNumberMarking }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .notSyncretic }
  , { walsCode := "ger", language := "German", iso := "deu", value := .syncretic }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .notSyncretic }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .notSyncretic }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .notSyncretic }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .notSyncretic }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .notSyncretic }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .syncretic }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noSubjectPersonNumberMarking }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .syncretic }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .syncretic }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .syncretic }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noSubjectPersonNumberMarking }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .notSyncretic }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .notSyncretic }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .notSyncretic }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .syncretic }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .notSyncretic }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .syncretic }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .syncretic }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .notSyncretic }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noSubjectPersonNumberMarking }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noSubjectPersonNumberMarking }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .syncretic }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .notSyncretic }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .syncretic }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .syncretic }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .syncretic }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noSubjectPersonNumberMarking }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noSubjectPersonNumberMarking }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noSubjectPersonNumberMarking }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .notSyncretic }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .syncretic }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noSubjectPersonNumberMarking }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .notSyncretic }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .syncretic }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .syncretic }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .notSyncretic }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .syncretic }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .notSyncretic }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noSubjectPersonNumberMarking }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .syncretic }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .notSyncretic }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .syncretic }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .syncretic }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .syncretic }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noSubjectPersonNumberMarking }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noSubjectPersonNumberMarking }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .syncretic }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .notSyncretic }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .notSyncretic }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noSubjectPersonNumberMarking }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .notSyncretic }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noSubjectPersonNumberMarking }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .notSyncretic }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .notSyncretic }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .notSyncretic }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .syncretic }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noSubjectPersonNumberMarking }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .notSyncretic }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .notSyncretic }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noSubjectPersonNumberMarking }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .notSyncretic }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .notSyncretic }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .notSyncretic }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .syncretic }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .notSyncretic }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .syncretic }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .notSyncretic }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .syncretic }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .notSyncretic }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .syncretic }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noSubjectPersonNumberMarking }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .syncretic }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .syncretic }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .syncretic }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .syncretic }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .notSyncretic }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .syncretic }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .notSyncretic }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .notSyncretic }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .notSyncretic }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .notSyncretic }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .notSyncretic }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noSubjectPersonNumberMarking }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noSubjectPersonNumberMarking }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noSubjectPersonNumberMarking }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noSubjectPersonNumberMarking }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .notSyncretic }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noSubjectPersonNumberMarking }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noSubjectPersonNumberMarking }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .notSyncretic }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .notSyncretic }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noSubjectPersonNumberMarking }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noSubjectPersonNumberMarking }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .syncretic }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noSubjectPersonNumberMarking }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .notSyncretic }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .syncretic }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .notSyncretic }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .syncretic }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noSubjectPersonNumberMarking }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .syncretic }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .notSyncretic }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noSubjectPersonNumberMarking }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noSubjectPersonNumberMarking }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .syncretic }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .notSyncretic }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noSubjectPersonNumberMarking }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .notSyncretic }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .notSyncretic }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .notSyncretic }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .notSyncretic }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .notSyncretic }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .notSyncretic }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .notSyncretic }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .syncretic }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noSubjectPersonNumberMarking }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .notSyncretic }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noSubjectPersonNumberMarking }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .notSyncretic }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noSubjectPersonNumberMarking }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .notSyncretic }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .notSyncretic }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noSubjectPersonNumberMarking }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noSubjectPersonNumberMarking }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noSubjectPersonNumberMarking }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .syncretic }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noSubjectPersonNumberMarking }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .notSyncretic }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .syncretic }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .notSyncretic }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .notSyncretic }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .notSyncretic }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .syncretic }
  ]

-- Count verification
theorem total_count : allData.length = 198 := by native_decide

theorem count_noSubjectPersonNumberMarking :
    (allData.filter (·.value == .noSubjectPersonNumberMarking)).length = 57 := by native_decide
theorem count_syncretic :
    (allData.filter (·.value == .syncretic)).length = 60 := by native_decide
theorem count_notSyncretic :
    (allData.filter (·.value == .notSyncretic)).length = 81 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F29A
