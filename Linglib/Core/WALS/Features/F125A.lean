import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 125A: Purpose Clauses
@cite{cristofaro-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 125A`.

Chapter 125, 170 languages.
-/

namespace Core.WALS.F125A

/-- WALS 125A values. -/
inductive PurposeClauseType where
  | balanced  -- Balanced (38 languages)
  | balancedDeranked  -- Balanced/deranked (30 languages)
  | deranked  -- Deranked (102 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 125A dataset (170 languages). -/
def allData : List (Datapoint PurposeClauseType) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .balancedDeranked }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .deranked }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .balanced }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .balanced }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .balancedDeranked }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .deranked }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .balancedDeranked }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .balancedDeranked }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .balancedDeranked }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .balanced }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .deranked }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .deranked }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .deranked }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .balanced }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .deranked }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .balancedDeranked }
  , { walsCode := "bdc", language := "Berbice Dutch Creole", iso := "brc", value := .deranked }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .balancedDeranked }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .deranked }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .deranked }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .balanced }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .deranked }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .deranked }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .balanced }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .deranked }
  , { walsCode := "eng", language := "English", iso := "eng", value := .balancedDeranked }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .deranked }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .deranked }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .deranked }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .balanced }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .balancedDeranked }
  , { walsCode := "fre", language := "French", iso := "fra", value := .deranked }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .deranked }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .balancedDeranked }
  , { walsCode := "ger", language := "German", iso := "deu", value := .balancedDeranked }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .deranked }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .balancedDeranked }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .deranked }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .deranked }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .deranked }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .balanced }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .deranked }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .deranked }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .deranked }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .deranked }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .balancedDeranked }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .deranked }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .balanced }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .deranked }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .deranked }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .deranked }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .deranked }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .deranked }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .deranked }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .balanced }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .deranked }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .deranked }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .balancedDeranked }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .deranked }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .deranked }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .balancedDeranked }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .balanced }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .balancedDeranked }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .deranked }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .deranked }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .balancedDeranked }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .deranked }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .balanced }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .deranked }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .deranked }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .deranked }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .balanced }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .balanced }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .deranked }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .deranked }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .balanced }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .balancedDeranked }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .deranked }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .deranked }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .balanced }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .deranked }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .deranked }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .deranked }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .deranked }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .balanced }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .deranked }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .balanced }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .deranked }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .balanced }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .deranked }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .deranked }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .deranked }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .balanced }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .deranked }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .deranked }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .balanced }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .deranked }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .balanced }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .deranked }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .deranked }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .balanced }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .deranked }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .balancedDeranked }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .balanced }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .balancedDeranked }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .balancedDeranked }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .deranked }
  , { walsCode := "npi", language := "Nigerian Pidgin", iso := "pcm", value := .deranked }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .deranked }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .deranked }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .deranked }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .deranked }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .balanced }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .deranked }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .deranked }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .balanced }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .deranked }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .balancedDeranked }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .balancedDeranked }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .deranked }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .deranked }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .balancedDeranked }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .deranked }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .deranked }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .deranked }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .deranked }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .deranked }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .deranked }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .deranked }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .balancedDeranked }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .deranked }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .balanced }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .balanced }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .deranked }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .balancedDeranked }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .balanced }
  , { walsCode := "som", language := "Somali", iso := "som", value := .balanced }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .deranked }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .balancedDeranked }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .balanced }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .deranked }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .deranked }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .deranked }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .deranked }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .balanced }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .balanced }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .balancedDeranked }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .balancedDeranked }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .deranked }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .deranked }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .deranked }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .deranked }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .deranked }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .deranked }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .deranked }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .balanced }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .deranked }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .deranked }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .deranked }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .balanced }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .deranked }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .balancedDeranked }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .balanced }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .deranked }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .balanced }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .deranked }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .deranked }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .balanced }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .deranked }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .deranked }
  ]

-- Count verification
theorem total_count : allData.length = 170 := by native_decide

theorem count_balanced :
    (allData.filter (·.value == .balanced)).length = 38 := by native_decide
theorem count_balancedDeranked :
    (allData.filter (·.value == .balancedDeranked)).length = 30 := by native_decide
theorem count_deranked :
    (allData.filter (·.value == .deranked)).length = 102 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F125A
