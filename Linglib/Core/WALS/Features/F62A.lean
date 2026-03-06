/-!
# WALS Feature 62A: Action Nominal Constructions
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 62A`.

Chapter 62, 168 languages.
-/

namespace Core.WALS.F62A

/-- WALS 62A values. -/
inductive ActionNominalConstructions where
  | sentential  -- Sentential (25 languages)
  | possessiveAccusative  -- Possessive-Accusative (29 languages)
  | ergativePossessive  -- Ergative-Possessive (21 languages)
  | doublePossessive  -- Double-Possessive (7 languages)
  | other  -- Other (6 languages)
  | mixed  -- Mixed (14 languages)
  | restricted  -- Restricted (24 languages)
  | noActionNominals  -- No action nominals (42 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 62A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ActionNominalConstructions
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 62A dataset (168 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "xun", language := "!Xun (Ekoka)", iso := "knw", value := .restricted }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .ergativePossessive }
  , { walsCode := "agl", language := "Aghul", iso := "agx", value := .mixed }
  , { walsCode := "axv", language := "Akhvakh", iso := "akv", value := .sentential }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noActionNominals }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .ergativePossessive }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .possessiveAccusative }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .possessiveAccusative }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .ergativePossessive }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .sentential }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .mixed }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noActionNominals }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .sentential }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .possessiveAccusative }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .sentential }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noActionNominals }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .doublePossessive }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .sentential }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .sentential }
  , { walsCode := "bez", language := "Bezhta", iso := "kap", value := .sentential }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .ergativePossessive }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .possessiveAccusative }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .other }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .sentential }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .restricted }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .sentential }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noActionNominals }
  , { walsCode := "car", language := "Carib", iso := "car", value := .ergativePossessive }
  , { walsCode := "crj", language := "Carijona", iso := "cbd", value := .ergativePossessive }
  , { walsCode := "chm", language := "Chamalal", iso := "cji", value := .sentential }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .other }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .restricted }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .restricted }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .doublePossessive }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noActionNominals }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .ergativePossessive }
  , { walsCode := "eng", language := "English", iso := "eng", value := .mixed }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .mixed }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .possessiveAccusative }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .restricted }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .doublePossessive }
  , { walsCode := "for", language := "Fore", iso := "for", value := .noActionNominals }
  , { walsCode := "fre", language := "French", iso := "fra", value := .ergativePossessive }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .restricted }
  , { walsCode := "gag", language := "Gagauz", iso := "gag", value := .noActionNominals }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .ergativePossessive }
  , { walsCode := "ger", language := "German", iso := "deu", value := .ergativePossessive }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .sentential }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noActionNominals }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .ergativePossessive }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .restricted }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .restricted }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .restricted }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .mixed }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .possessiveAccusative }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .ergativePossessive }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noActionNominals }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noActionNominals }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .noActionNominals }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .restricted }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .other }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noActionNominals }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noActionNominals }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .ergativePossessive }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .sentential }
  , { walsCode := "iql", language := "Inuktitut (Quebec-Labrador)", iso := "ike", value := .restricted }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .restricted }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .mixed }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .doublePossessive }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .ergativePossessive }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .mixed }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .mixed }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noActionNominals }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noActionNominals }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .restricted }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .possessiveAccusative }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .restricted }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noActionNominals }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .restricted }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .sentential }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .sentential }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .restricted }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .restricted }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .possessiveAccusative }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .restricted }
  , { walsCode := "kji", language := "Kurmanji", iso := "kmr", value := .ergativePossessive }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noActionNominals }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .sentential }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noActionNominals }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .possessiveAccusative }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .doublePossessive }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .sentential }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .mixed }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .sentential }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .possessiveAccusative }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .possessiveAccusative }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noActionNominals }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .doublePossessive }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noActionNominals }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noActionNominals }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .mixed }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .possessiveAccusative }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .possessiveAccusative }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .possessiveAccusative }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noActionNominals }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noActionNominals }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noActionNominals }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noActionNominals }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noActionNominals }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noActionNominals }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .sentential }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noActionNominals }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .possessiveAccusative }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .sentential }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .possessiveAccusative }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noActionNominals }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .sentential }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noActionNominals }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .possessiveAccusative }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .restricted }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .possessiveAccusative }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .ergativePossessive }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .sentential }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .sentential }
  , { walsCode := "qch", language := "Quiché", iso := "quc", value := .restricted }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noActionNominals }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .ergativePossessive }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .other }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .possessiveAccusative }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noActionNominals }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .possessiveAccusative }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noActionNominals }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .ergativePossessive }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noActionNominals }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .mixed }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .possessiveAccusative }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .other }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noActionNominals }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .possessiveAccusative }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .sentential }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .restricted }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .mixed }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noActionNominals }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .restricted }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noActionNominals }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .mixed }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .doublePossessive }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .possessiveAccusative }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .mixed }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .possessiveAccusative }
  , { walsCode := "vat", language := "Vata", iso := "dic", value := .possessiveAccusative }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .possessiveAccusative }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .ergativePossessive }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noActionNominals }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .other }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noActionNominals }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .noActionNominals }
  , { walsCode := "wyn", language := "Wayana", iso := "way", value := .ergativePossessive }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .ergativePossessive }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noActionNominals }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .restricted }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .possessiveAccusative }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .sentential }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noActionNominals }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .possessiveAccusative }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .restricted }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .possessiveAccusative }
  , { walsCode := "ysi", language := "Yupik (Sirenik)", iso := "ysr", value := .sentential }
  ]

-- Count verification
theorem total_count : allData.length = 168 := by native_decide

theorem count_sentential :
    (allData.filter (·.value == .sentential)).length = 25 := by native_decide
theorem count_possessiveAccusative :
    (allData.filter (·.value == .possessiveAccusative)).length = 29 := by native_decide
theorem count_ergativePossessive :
    (allData.filter (·.value == .ergativePossessive)).length = 21 := by native_decide
theorem count_doublePossessive :
    (allData.filter (·.value == .doublePossessive)).length = 7 := by native_decide
theorem count_other :
    (allData.filter (·.value == .other)).length = 6 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 14 := by native_decide
theorem count_restricted :
    (allData.filter (·.value == .restricted)).length = 24 := by native_decide
theorem count_noActionNominals :
    (allData.filter (·.value == .noActionNominals)).length = 42 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F62A
