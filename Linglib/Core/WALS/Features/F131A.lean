import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 131A: Numeral Bases
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 131A`.

Chapter 131, 196 languages.
-/

namespace Core.WALS.F131A

/-- WALS 131A values. -/
inductive NumeralBases where
  | decimal  -- Decimal (125 languages)
  | hybridVigesimalDecimal  -- Hybrid vigesimal-decimal (22 languages)
  | pureVigesimal  -- Pure vigesimal (20 languages)
  | otherBase  -- Other base (5 languages)
  | extendedBodyPartSystem  -- Extended body-part system (4 languages)
  | restricted  -- Restricted (20 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 131A dataset (196 languages). -/
def allData : List (Datapoint NumeralBases) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .restricted }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .hybridVigesimalDecimal }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .decimal }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .restricted }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .decimal }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .pureVigesimal }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .decimal }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .pureVigesimal }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .decimal }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .decimal }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .pureVigesimal }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .decimal }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .restricted }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .decimal }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .decimal }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .restricted }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .decimal }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .decimal }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .decimal }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .restricted }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .restricted }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .decimal }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .hybridVigesimalDecimal }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .decimal }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .decimal }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .decimal }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .decimal }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .decimal }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .decimal }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .hybridVigesimalDecimal }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .decimal }
  , { walsCode := "car", language := "Carib", iso := "car", value := .pureVigesimal }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .decimal }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .decimal }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .hybridVigesimalDecimal }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .pureVigesimal }
  , { walsCode := "cuu", language := "Chuukese", iso := "chk", value := .decimal }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .decimal }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .decimal }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .decimal }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .pureVigesimal }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .decimal }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .hybridVigesimalDecimal }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .hybridVigesimalDecimal }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .pureVigesimal }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .extendedBodyPartSystem }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .otherBase }
  , { walsCode := "emc", language := "Embera Chami", iso := "cmi", value := .otherBase }
  , { walsCode := "eng", language := "English", iso := "eng", value := .decimal }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .decimal }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .decimal }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .decimal }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .decimal }
  , { walsCode := "fre", language := "French", iso := "fra", value := .decimal }
  , { walsCode := "fum", language := "Fulfulde (Maasina)", iso := "ffm", value := .hybridVigesimalDecimal }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .decimal }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .decimal }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .hybridVigesimalDecimal }
  , { walsCode := "ger", language := "German", iso := "deu", value := .decimal }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .decimal }
  , { walsCode := "gol", language := "Gola", iso := "gol", value := .hybridVigesimalDecimal }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .restricted }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .decimal }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .hybridVigesimalDecimal }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .decimal }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .decimal }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .decimal }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .extendedBodyPartSystem }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .decimal }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .decimal }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .decimal }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .restricted }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .decimal }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .decimal }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .hybridVigesimalDecimal }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .decimal }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .decimal }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .restricted }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .decimal }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .pureVigesimal }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .decimal }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .restricted }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .decimal }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .hybridVigesimalDecimal }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .decimal }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .hybridVigesimalDecimal }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .hybridVigesimalDecimal }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .decimal }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .decimal }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .decimal }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .pureVigesimal }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .decimal }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .decimal }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .decimal }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .decimal }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .restricted }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .decimal }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .decimal }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .decimal }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .decimal }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .decimal }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .decimal }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .decimal }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .decimal }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .extendedBodyPartSystem }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .decimal }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .decimal }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .decimal }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .pureVigesimal }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .decimal }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .decimal }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .decimal }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .decimal }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .decimal }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .decimal }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .decimal }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .decimal }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .hybridVigesimalDecimal }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .pureVigesimal }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .decimal }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .decimal }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .decimal }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .pureVigesimal }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .restricted }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .decimal }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .decimal }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .restricted }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .decimal }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .hybridVigesimalDecimal }
  , { walsCode := "mxa", language := "Mixtec (Atatlahuca)", iso := "mib", value := .hybridVigesimalDecimal }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .hybridVigesimalDecimal }
  , { walsCode := "nsz", language := "Nahuatl (Sierra de Zacapoaxtla)", iso := "azz", value := .hybridVigesimalDecimal }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .decimal }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .decimal }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .decimal }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .decimal }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .decimal }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .decimal }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .otherBase }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .decimal }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .decimal }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .decimal }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .decimal }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .decimal }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .decimal }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .hybridVigesimalDecimal }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .decimal }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .decimal }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .restricted }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .restricted }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .decimal }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .decimal }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .decimal }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .decimal }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .restricted }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .decimal }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .decimal }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .decimal }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .decimal }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .decimal }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .decimal }
  , { walsCode := "so", language := "So", iso := "teu", value := .decimal }
  , { walsCode := "sou", language := "Sorbian (Upper)", iso := "hsb", value := .decimal }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .decimal }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .otherBase }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .decimal }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .decimal }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .decimal }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .pureVigesimal }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .decimal }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .pureVigesimal }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .decimal }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .decimal }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .decimal }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .otherBase }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .hybridVigesimalDecimal }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .decimal }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .decimal }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .decimal }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .extendedBodyPartSystem }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .decimal }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .pureVigesimal }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .restricted }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .restricted }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .restricted }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .decimal }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .decimal }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .hybridVigesimalDecimal }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .restricted }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .pureVigesimal }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .pureVigesimal }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .pureVigesimal }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .decimal }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .pureVigesimal }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .pureVigesimal }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .decimal }
  ]

-- Count verification
theorem total_count : allData.length = 196 := by native_decide

theorem count_decimal :
    (allData.filter (·.value == .decimal)).length = 125 := by native_decide
theorem count_hybridVigesimalDecimal :
    (allData.filter (·.value == .hybridVigesimalDecimal)).length = 22 := by native_decide
theorem count_pureVigesimal :
    (allData.filter (·.value == .pureVigesimal)).length = 20 := by native_decide
theorem count_otherBase :
    (allData.filter (·.value == .otherBase)).length = 5 := by native_decide
theorem count_extendedBodyPartSystem :
    (allData.filter (·.value == .extendedBodyPartSystem)).length = 4 := by native_decide
theorem count_restricted :
    (allData.filter (·.value == .restricted)).length = 20 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F131A
