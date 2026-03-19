import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 20A: Fusion of Selected Inflectional Formatives
@cite{bickel-nichols-2013a}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 20A`.

Chapter 20, 165 languages.
-/

namespace Core.WALS.F20A

/-- WALS 20A values. -/
inductive FusionType where
  | exclusivelyConcatenative  -- Exclusively concatenative (125 languages)
  | exclusivelyIsolating  -- Exclusively isolating (16 languages)
  | exclusivelyTonal  -- Exclusively tonal (3 languages)
  | tonalIsolating  -- Tonal/isolating (1 languages)
  | tonalConcatenative  -- Tonal/concatenative (2 languages)
  | ablautConcatenative  -- Ablaut/concatenative (5 languages)
  | isolatingConcatenative  -- Isolating/concatenative (13 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 20A dataset (165 languages). -/
def allData : List (Datapoint FusionType) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .exclusivelyConcatenative }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .exclusivelyConcatenative }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .exclusivelyConcatenative }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .exclusivelyConcatenative }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .exclusivelyConcatenative }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .exclusivelyConcatenative }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .ablautConcatenative }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .exclusivelyConcatenative }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .exclusivelyConcatenative }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .exclusivelyConcatenative }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .exclusivelyConcatenative }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .exclusivelyConcatenative }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .exclusivelyConcatenative }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .exclusivelyConcatenative }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .exclusivelyConcatenative }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .exclusivelyConcatenative }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .exclusivelyConcatenative }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .exclusivelyConcatenative }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .ablautConcatenative }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .exclusivelyConcatenative }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .ablautConcatenative }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .exclusivelyConcatenative }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .exclusivelyConcatenative }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .exclusivelyConcatenative }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .exclusivelyConcatenative }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .exclusivelyConcatenative }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .exclusivelyConcatenative }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .exclusivelyConcatenative }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .isolatingConcatenative }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .exclusivelyConcatenative }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .exclusivelyConcatenative }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .exclusivelyConcatenative }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .exclusivelyConcatenative }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .exclusivelyConcatenative }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .isolatingConcatenative }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .exclusivelyConcatenative }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .exclusivelyConcatenative }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .exclusivelyConcatenative }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .exclusivelyConcatenative }
  , { walsCode := "eng", language := "English", iso := "eng", value := .exclusivelyConcatenative }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .exclusivelyConcatenative }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .exclusivelyConcatenative }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .exclusivelyIsolating }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .exclusivelyConcatenative }
  , { walsCode := "fre", language := "French", iso := "fra", value := .exclusivelyConcatenative }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .exclusivelyConcatenative }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .exclusivelyConcatenative }
  , { walsCode := "ger", language := "German", iso := "deu", value := .exclusivelyConcatenative }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .isolatingConcatenative }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .exclusivelyConcatenative }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .exclusivelyConcatenative }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .exclusivelyConcatenative }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .exclusivelyConcatenative }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .exclusivelyConcatenative }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .exclusivelyConcatenative }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .exclusivelyIsolating }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .ablautConcatenative }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .exclusivelyConcatenative }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .exclusivelyConcatenative }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .exclusivelyIsolating }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .exclusivelyConcatenative }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .exclusivelyConcatenative }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .exclusivelyConcatenative }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .exclusivelyTonal }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .exclusivelyConcatenative }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .exclusivelyIsolating }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .exclusivelyConcatenative }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .exclusivelyConcatenative }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .exclusivelyConcatenative }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .exclusivelyIsolating }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .exclusivelyConcatenative }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .exclusivelyConcatenative }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .exclusivelyConcatenative }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .exclusivelyConcatenative }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .exclusivelyConcatenative }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .exclusivelyConcatenative }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .exclusivelyIsolating }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .exclusivelyConcatenative }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .exclusivelyIsolating }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .exclusivelyTonal }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .exclusivelyConcatenative }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .exclusivelyConcatenative }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .exclusivelyConcatenative }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .exclusivelyConcatenative }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .exclusivelyIsolating }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .exclusivelyConcatenative }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .isolatingConcatenative }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .exclusivelyConcatenative }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .exclusivelyIsolating }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .exclusivelyIsolating }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .isolatingConcatenative }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .exclusivelyTonal }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .exclusivelyConcatenative }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .exclusivelyConcatenative }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .ablautConcatenative }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .exclusivelyConcatenative }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .tonalConcatenative }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .exclusivelyConcatenative }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .isolatingConcatenative }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .exclusivelyConcatenative }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .isolatingConcatenative }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .exclusivelyConcatenative }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .exclusivelyConcatenative }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .exclusivelyConcatenative }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .exclusivelyConcatenative }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .exclusivelyConcatenative }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .exclusivelyConcatenative }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .exclusivelyConcatenative }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .exclusivelyConcatenative }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .exclusivelyConcatenative }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .exclusivelyConcatenative }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .exclusivelyConcatenative }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .isolatingConcatenative }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .exclusivelyConcatenative }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .tonalConcatenative }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .exclusivelyConcatenative }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .exclusivelyConcatenative }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .exclusivelyConcatenative }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .exclusivelyConcatenative }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .exclusivelyConcatenative }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .exclusivelyConcatenative }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .exclusivelyConcatenative }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .exclusivelyConcatenative }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .isolatingConcatenative }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .exclusivelyConcatenative }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .exclusivelyConcatenative }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .exclusivelyConcatenative }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .exclusivelyConcatenative }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .exclusivelyConcatenative }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .exclusivelyConcatenative }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .exclusivelyIsolating }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .exclusivelyConcatenative }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .exclusivelyConcatenative }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .exclusivelyConcatenative }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .exclusivelyConcatenative }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .exclusivelyConcatenative }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .exclusivelyConcatenative }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .exclusivelyConcatenative }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .exclusivelyIsolating }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .exclusivelyConcatenative }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .exclusivelyConcatenative }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .exclusivelyIsolating }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .isolatingConcatenative }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .exclusivelyConcatenative }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .exclusivelyConcatenative }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .exclusivelyConcatenative }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .exclusivelyConcatenative }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .isolatingConcatenative }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .isolatingConcatenative }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .exclusivelyConcatenative }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .exclusivelyIsolating }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .isolatingConcatenative }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .exclusivelyConcatenative }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .exclusivelyConcatenative }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .exclusivelyIsolating }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .exclusivelyConcatenative }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .exclusivelyConcatenative }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .exclusivelyIsolating }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .exclusivelyConcatenative }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .exclusivelyConcatenative }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .exclusivelyConcatenative }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .tonalIsolating }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .exclusivelyConcatenative }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .exclusivelyConcatenative }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .exclusivelyConcatenative }
  ]

-- Count verification
theorem total_count : allData.length = 165 := by native_decide

theorem count_exclusivelyConcatenative :
    (allData.filter (·.value == .exclusivelyConcatenative)).length = 125 := by native_decide
theorem count_exclusivelyIsolating :
    (allData.filter (·.value == .exclusivelyIsolating)).length = 16 := by native_decide
theorem count_exclusivelyTonal :
    (allData.filter (·.value == .exclusivelyTonal)).length = 3 := by native_decide
theorem count_tonalIsolating :
    (allData.filter (·.value == .tonalIsolating)).length = 1 := by native_decide
theorem count_tonalConcatenative :
    (allData.filter (·.value == .tonalConcatenative)).length = 2 := by native_decide
theorem count_ablautConcatenative :
    (allData.filter (·.value == .ablautConcatenative)).length = 5 := by native_decide
theorem count_isolatingConcatenative :
    (allData.filter (·.value == .isolatingConcatenative)).length = 13 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F20A
