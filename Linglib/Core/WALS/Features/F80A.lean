import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 80A: Verbal Number and Suppletion
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 80A`.

Chapter 80, 193 languages.
-/

namespace Core.WALS.F80A

/-- WALS 80A values. -/
inductive VerbalNumberAndSuppletion where
  | none  -- None (159 languages)
  | singularPluralPairsNoSuppletion  -- Singular-plural pairs, no suppletion (12 languages)
  | singularPluralPairsSuppletion  -- Singular-plural pairs, suppletion (15 languages)
  | singularDualPluralTriplesNoSuppletion  -- Singular-dual-plural triples, no suppletion (5 languages)
  | singularDualPluralTriplesSuppletion  -- Singular-dual-plural triples, suppletion (2 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 80A dataset (193 languages). -/
def allData : List (Datapoint VerbalNumberAndSuppletion) :=
  [ { walsCode := "xun", language := "!Xun (Ekoka)", iso := "knw", value := .singularPluralPairsSuppletion }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .none }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .none }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .singularPluralPairsSuppletion }
  , { walsCode := "agw", language := "Alagwa", iso := "wbj", value := .none }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .none }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .none }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .none }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .none }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .none }
  , { walsCode := "atu", language := "Arabic (Tunisian)", iso := "aeb", value := .none }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .none }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .none }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .none }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .none }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .none }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .none }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .none }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .none }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .none }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .none }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .none }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .none }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .none }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .none }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .singularPluralPairsSuppletion }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .singularPluralPairsSuppletion }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .none }
  , { walsCode := "car", language := "Carib", iso := "car", value := .none }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .none }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .none }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .none }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .none }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .none }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .none }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .none }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .none }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .none }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .none }
  , { walsCode := "eng", language := "English", iso := "eng", value := .none }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .none }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .none }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .none }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .none }
  , { walsCode := "fre", language := "French", iso := "fra", value := .none }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .none }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .none }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .none }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "ger", language := "German", iso := "deu", value := .none }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .none }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .none }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .none }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .none }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .none }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .none }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .none }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .none }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .none }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .none }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .none }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .none }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .none }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .none }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .singularPluralPairsSuppletion }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .none }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .none }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .none }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .none }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .none }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .none }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .none }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .singularPluralPairsSuppletion }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .none }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .none }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .none }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .none }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .none }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .none }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .none }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .singularPluralPairsSuppletion }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .singularDualPluralTriplesSuppletion }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .none }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .none }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .none }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .none }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .none }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .none }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .none }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .none }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .none }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .none }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .none }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .none }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .none }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .none }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .none }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .none }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .none }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .none }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .none }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .none }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .none }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .none }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .none }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .none }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .none }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .none }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .none }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .none }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .none }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .singularPluralPairsSuppletion }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .none }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .none }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .none }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .none }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .none }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .none }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .none }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .none }
  , { walsCode := "orb", language := "Oromo (Boraana)", iso := "gax", value := .none }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .none }
  , { walsCode := "oix", language := "Otomí (Ixtenco)", iso := "otz", value := .none }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .none }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .singularPluralPairsSuppletion }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .none }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .none }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .none }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .none }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .none }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .none }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .none }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .none }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .none }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .singularPluralPairsSuppletion }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .none }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .none }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .none }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .none }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .none }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .none }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .none }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .none }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .singularPluralPairsSuppletion }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .singularDualPluralTriplesSuppletion }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .none }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .none }
  , { walsCode := "sou", language := "Sorbian (Upper)", iso := "hsb", value := .none }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .none }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .none }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .none }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .none }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .none }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .none }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .none }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .none }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .singularPluralPairsSuppletion }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .none }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .none }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .none }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .none }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .none }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .none }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .none }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .singularPluralPairsSuppletion }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .singularPluralPairsSuppletion }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .none }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .none }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .singularPluralPairsSuppletion }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .none }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .none }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .none }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .none }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .none }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .none }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .none }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .none }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .singularPluralPairsNoSuppletion }
  ]

-- Count verification
theorem total_count : allData.length = 193 := by native_decide

theorem count_none :
    (allData.filter (·.value == .none)).length = 159 := by native_decide
theorem count_singularPluralPairsNoSuppletion :
    (allData.filter (·.value == .singularPluralPairsNoSuppletion)).length = 12 := by native_decide
theorem count_singularPluralPairsSuppletion :
    (allData.filter (·.value == .singularPluralPairsSuppletion)).length = 15 := by native_decide
theorem count_singularDualPluralTriplesNoSuppletion :
    (allData.filter (·.value == .singularDualPluralTriplesNoSuppletion)).length = 5 := by native_decide
theorem count_singularDualPluralTriplesSuppletion :
    (allData.filter (·.value == .singularDualPluralTriplesSuppletion)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F80A
