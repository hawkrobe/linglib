import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 128A: Utterance Complement Clauses
@cite{cristofaro-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 128A`.

Chapter 128, 143 languages.
-/

namespace Core.WALS.F128A

/-- WALS 128A values. -/
inductive UtteranceComplementType where
  | balanced  -- Balanced (114 languages)
  | balancedDeranked  -- Balanced/deranked (18 languages)
  | deranked  -- Deranked (11 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 128A dataset (143 languages). -/
def allData : List (Datapoint UtteranceComplementType) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .balancedDeranked }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .balanced }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .balanced }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .balanced }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .balanced }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .balanced }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .balanced }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .balanced }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .balanced }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .balancedDeranked }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .balanced }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .deranked }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .balanced }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .balanced }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .balanced }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .balancedDeranked }
  , { walsCode := "bdc", language := "Berbice Dutch Creole", iso := "brc", value := .balanced }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .balanced }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .balanced }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .deranked }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .balanced }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .balanced }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .balanced }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .deranked }
  , { walsCode := "eng", language := "English", iso := "eng", value := .balanced }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .balanced }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .balanced }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .deranked }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .balanced }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .balancedDeranked }
  , { walsCode := "fre", language := "French", iso := "fra", value := .balancedDeranked }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .balanced }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .balanced }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .balanced }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .balanced }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .balancedDeranked }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .balanced }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .balanced }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .balanced }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .balanced }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .balanced }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .balanced }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .balanced }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .balanced }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .balanced }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .balanced }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .balancedDeranked }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .balanced }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .balancedDeranked }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .balanced }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .balanced }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .balanced }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .balanced }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .balanced }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .balancedDeranked }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .balanced }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .balanced }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .balanced }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .balanced }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .balanced }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .balanced }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .balanced }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .balanced }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .balanced }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .balancedDeranked }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .balanced }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .balancedDeranked }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .balanced }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .balanced }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .balancedDeranked }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .balanced }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .balanced }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .balanced }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .balanced }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .balanced }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .balanced }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .balancedDeranked }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .deranked }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .balanced }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .balanced }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .balanced }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .balanced }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .balanced }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .balancedDeranked }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .balanced }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .balanced }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .balanced }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .balanced }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .balanced }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .balanced }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .balanced }
  , { walsCode := "npi", language := "Nigerian Pidgin", iso := "pcm", value := .balanced }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .deranked }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .balanced }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .balanced }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .balanced }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .balanced }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .balanced }
  , { walsCode := "orb", language := "Oromo (Boraana)", iso := "gax", value := .balanced }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .balanced }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .balanced }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .balanced }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .balanced }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .balanced }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .balanced }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .balanced }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .balanced }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .balanced }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .deranked }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .balanced }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .balanced }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .balanced }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .balanced }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .balanced }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .balancedDeranked }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .deranked }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .balanced }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .balanced }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .balanced }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .balanced }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .deranked }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .deranked }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .balanced }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .deranked }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .balanced }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .balancedDeranked }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .balanced }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .balanced }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .balanced }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .balancedDeranked }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .balanced }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .balanced }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .balanced }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .balanced }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .balanced }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .balanced }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .balanced }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .balanced }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .balanced }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .balanced }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .balanced }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .balanced }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .balancedDeranked }
  ]

-- Count verification
theorem total_count : allData.length = 143 := by native_decide

theorem count_balanced :
    (allData.filter (·.value == .balanced)).length = 114 := by native_decide
theorem count_balancedDeranked :
    (allData.filter (·.value == .balancedDeranked)).length = 18 := by native_decide
theorem count_deranked :
    (allData.filter (·.value == .deranked)).length = 11 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F128A
