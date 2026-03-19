import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 127A: Reason Clauses
@cite{cristofaro-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 127A`.

Chapter 127, 169 languages.
-/

namespace Core.WALS.F127A

/-- WALS 127A values. -/
inductive ReasonClauseType where
  | balanced  -- Balanced (90 languages)
  | balancedDeranked  -- Balanced/deranked (37 languages)
  | deranked  -- Deranked (42 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 127A dataset (169 languages). -/
def allData : List (Datapoint ReasonClauseType) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .deranked }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .balanced }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .balanced }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .balanced }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .balancedDeranked }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .deranked }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .balanced }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .balanced }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .balanced }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .balancedDeranked }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .deranked }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .deranked }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .balancedDeranked }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .balanced }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .balancedDeranked }
  , { walsCode := "bdc", language := "Berbice Dutch Creole", iso := "brc", value := .deranked }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .balanced }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .balanced }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .balancedDeranked }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .balanced }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .balanced }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .balanced }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .balancedDeranked }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .deranked }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .balancedDeranked }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .balanced }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .balanced }
  , { walsCode := "eng", language := "English", iso := "eng", value := .balancedDeranked }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .balanced }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .deranked }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .balanced }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .balanced }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .balancedDeranked }
  , { walsCode := "fre", language := "French", iso := "fra", value := .balancedDeranked }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .balanced }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .balanced }
  , { walsCode := "ger", language := "German", iso := "deu", value := .balanced }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .deranked }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .deranked }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .balanced }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .deranked }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .balanced }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .deranked }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .balanced }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .balanced }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .balancedDeranked }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .deranked }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .balanced }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .balancedDeranked }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .deranked }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .balanced }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .deranked }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .deranked }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .deranked }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .balanced }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .balanced }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .balanced }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .deranked }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .balancedDeranked }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .balancedDeranked }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .balanced }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .balanced }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .balanced }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .deranked }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .balanced }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .balancedDeranked }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .balancedDeranked }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .balanced }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .balanced }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .balanced }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .balanced }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .balancedDeranked }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .balanced }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .balancedDeranked }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .balanced }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .balanced }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .balanced }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .balanced }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .balanced }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .deranked }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .balancedDeranked }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .balancedDeranked }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .balanced }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .balancedDeranked }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .balanced }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .balancedDeranked }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .balanced }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .balanced }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .balanced }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .balancedDeranked }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .balanced }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .balancedDeranked }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .deranked }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .deranked }
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
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .balancedDeranked }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .balanced }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .deranked }
  , { walsCode := "npi", language := "Nigerian Pidgin", iso := "pcm", value := .balanced }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .deranked }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .balancedDeranked }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .balanced }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .deranked }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .balanced }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .balanced }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .balanced }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .balanced }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .balancedDeranked }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .balancedDeranked }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .deranked }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .balanced }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .balanced }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .balanced }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .deranked }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .deranked }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .balancedDeranked }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .deranked }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .deranked }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .deranked }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .balancedDeranked }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .balanced }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .deranked }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .balanced }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .balanced }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .balanced }
  , { walsCode := "som", language := "Somali", iso := "som", value := .balanced }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .balancedDeranked }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .balanced }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .balanced }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .balancedDeranked }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .deranked }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .balancedDeranked }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .balanced }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .balanced }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .balanced }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .balanced }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .balanced }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .balancedDeranked }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .balancedDeranked }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .balanced }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .deranked }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .deranked }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .balanced }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .balanced }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .deranked }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .deranked }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .balanced }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .balanced }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .balanced }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .balanced }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .balancedDeranked }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .balancedDeranked }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .balanced }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .deranked }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .balanced }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .balanced }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .balanced }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .deranked }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .deranked }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .deranked }
  ]

-- Count verification
theorem total_count : allData.length = 169 := by native_decide

theorem count_balanced :
    (allData.filter (·.value == .balanced)).length = 90 := by native_decide
theorem count_balancedDeranked :
    (allData.filter (·.value == .balancedDeranked)).length = 37 := by native_decide
theorem count_deranked :
    (allData.filter (·.value == .deranked)).length = 42 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F127A
