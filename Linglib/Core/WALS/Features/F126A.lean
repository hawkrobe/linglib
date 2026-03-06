/-!
# WALS Feature 126A: 'When' Clauses
@cite{cristofaro-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 126A`.

Chapter 126, 174 languages.
-/

namespace Core.WALS.F126A

/-- WALS 126A values. -/
inductive WhenClauseType where
  | balanced  -- Balanced (84 languages)
  | balancedDeranked  -- Balanced/deranked (39 languages)
  | deranked  -- Deranked (51 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 126A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : WhenClauseType
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 126A dataset (174 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .deranked }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .balanced }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .balanced }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .balanced }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .balanced }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .balancedDeranked }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .deranked }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .deranked }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .balanced }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .balanced }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .balancedDeranked }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .deranked }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .deranked }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .balancedDeranked }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .balanced }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .deranked }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .balancedDeranked }
  , { walsCode := "bdc", language := "Berbice Dutch Creole", iso := "brc", value := .balanced }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .balanced }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .deranked }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .balanced }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .balanced }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .balanced }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .balanced }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .deranked }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .deranked }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .deranked }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .balanced }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .balanced }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .balanced }
  , { walsCode := "eng", language := "English", iso := "eng", value := .balancedDeranked }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .balanced }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .balanced }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .deranked }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .balanced }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .balanced }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .balancedDeranked }
  , { walsCode := "fre", language := "French", iso := "fra", value := .balancedDeranked }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .balancedDeranked }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .balancedDeranked }
  , { walsCode := "ger", language := "German", iso := "deu", value := .balancedDeranked }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .deranked }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .balancedDeranked }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .balanced }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .balanced }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .deranked }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .balanced }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .balanced }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .deranked }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .balancedDeranked }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .balanced }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .balancedDeranked }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .deranked }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .deranked }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .balanced }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .deranked }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .deranked }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .deranked }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .balanced }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .balanced }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .deranked }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .deranked }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .balancedDeranked }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .balancedDeranked }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .balancedDeranked }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .balancedDeranked }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .balanced }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .balanced }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .deranked }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .balanced }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .balancedDeranked }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .balancedDeranked }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .balanced }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .balanced }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .deranked }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .balanced }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .balanced }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .deranked }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .balanced }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .balanced }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .balanced }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .balanced }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .balanced }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .balanced }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .balanced }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .balancedDeranked }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .deranked }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .balancedDeranked }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .balanced }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .balancedDeranked }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .balanced }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .balanced }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .balancedDeranked }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .balancedDeranked }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .deranked }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .balancedDeranked }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .deranked }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .deranked }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .balanced }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .balanced }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .deranked }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .balanced }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .balanced }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .balanced }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .balanced }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .deranked }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .balanced }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .balanced }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .balanced }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .balanced }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .balancedDeranked }
  , { walsCode := "npi", language := "Nigerian Pidgin", iso := "pcm", value := .balanced }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .deranked }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .balancedDeranked }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .deranked }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .deranked }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .balanced }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .balanced }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .balanced }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .balanced }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .balanced }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .balancedDeranked }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .balanced }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .balanced }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .balanced }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .balanced }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .deranked }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .balanced }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .deranked }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .balanced }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .balancedDeranked }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .balancedDeranked }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .balanced }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .deranked }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .balanced }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .deranked }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .balanced }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .balanced }
  , { walsCode := "som", language := "Somali", iso := "som", value := .balanced }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .balancedDeranked }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .deranked }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .balancedDeranked }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .balanced }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .balancedDeranked }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .deranked }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .deranked }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .balanced }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .balanced }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .balanced }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .balancedDeranked }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .balancedDeranked }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .deranked }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .balancedDeranked }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .balanced }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .deranked }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .deranked }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .balanced }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .balanced }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .deranked }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .balanced }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .balanced }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .deranked }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .deranked }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .balancedDeranked }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .balancedDeranked }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .balanced }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .deranked }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .balanced }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .deranked }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .balancedDeranked }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .balanced }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .deranked }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .deranked }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .deranked }
  ]

-- Count verification
theorem total_count : allData.length = 174 := by native_decide

theorem count_balanced :
    (allData.filter (·.value == .balanced)).length = 84 := by native_decide
theorem count_balancedDeranked :
    (allData.filter (·.value == .balancedDeranked)).length = 39 := by native_decide
theorem count_deranked :
    (allData.filter (·.value == .deranked)).length = 51 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F126A
