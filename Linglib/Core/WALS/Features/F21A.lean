import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 21A: Exponence of Selected Inflectional Formatives
@cite{bickel-nichols-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 21A`.

Chapter 21, 162 languages.
-/

namespace Core.WALS.F21A

/-- WALS 21A values. -/
inductive ExponenceType where
  | monoexponentialCase  -- Monoexponential case (71 languages)
  | caseNumber  -- Case + number (8 languages)
  | caseReferentiality  -- Case + referentiality (6 languages)
  | caseTam  -- Case + TAM (2 languages)
  | noCase  -- No case (75 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 21A dataset (162 languages). -/
def allData : List (Datapoint ExponenceType) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .noCase }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noCase }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noCase }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noCase }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noCase }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noCase }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noCase }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .monoexponentialCase }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noCase }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .monoexponentialCase }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noCase }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .noCase }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .monoexponentialCase }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .monoexponentialCase }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noCase }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .monoexponentialCase }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .monoexponentialCase }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .monoexponentialCase }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .monoexponentialCase }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .monoexponentialCase }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .monoexponentialCase }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .noCase }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noCase }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .monoexponentialCase }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .monoexponentialCase }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .monoexponentialCase }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .monoexponentialCase }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noCase }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noCase }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noCase }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .noCase }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .noCase }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .caseNumber }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .monoexponentialCase }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .caseReferentiality }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noCase }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noCase }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .monoexponentialCase }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noCase }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noCase }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .monoexponentialCase }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .caseReferentiality }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noCase }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .caseNumber }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noCase }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .monoexponentialCase }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .monoexponentialCase }
  , { walsCode := "ger", language := "German", iso := "deu", value := .caseNumber }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .monoexponentialCase }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noCase }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .caseNumber }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .caseNumber }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noCase }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noCase }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noCase }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noCase }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noCase }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .monoexponentialCase }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noCase }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noCase }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noCase }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .monoexponentialCase }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .monoexponentialCase }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .noCase }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .monoexponentialCase }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noCase }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .monoexponentialCase }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noCase }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .monoexponentialCase }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .noCase }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .monoexponentialCase }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noCase }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .caseTam }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noCase }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .monoexponentialCase }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .monoexponentialCase }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .monoexponentialCase }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noCase }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noCase }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .noCase }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .monoexponentialCase }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .noCase }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .monoexponentialCase }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noCase }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noCase }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .monoexponentialCase }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .caseReferentiality }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .monoexponentialCase }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .monoexponentialCase }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noCase }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noCase }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noCase }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .monoexponentialCase }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .caseTam }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noCase }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .monoexponentialCase }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .monoexponentialCase }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .monoexponentialCase }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .monoexponentialCase }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .monoexponentialCase }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noCase }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .noCase }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .monoexponentialCase }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .monoexponentialCase }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noCase }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noCase }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .monoexponentialCase }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .monoexponentialCase }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noCase }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .monoexponentialCase }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .monoexponentialCase }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .monoexponentialCase }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noCase }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .monoexponentialCase }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .caseNumber }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .monoexponentialCase }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noCase }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .monoexponentialCase }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noCase }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .monoexponentialCase }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noCase }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .caseReferentiality }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .monoexponentialCase }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noCase }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .monoexponentialCase }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .monoexponentialCase }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .monoexponentialCase }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .monoexponentialCase }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .caseNumber }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noCase }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .monoexponentialCase }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noCase }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .monoexponentialCase }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .monoexponentialCase }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noCase }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noCase }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .caseReferentiality }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .noCase }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noCase }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .monoexponentialCase }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noCase }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .monoexponentialCase }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noCase }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .monoexponentialCase }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .caseReferentiality }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .monoexponentialCase }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noCase }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .monoexponentialCase }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .monoexponentialCase }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .noCase }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noCase }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .monoexponentialCase }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .monoexponentialCase }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noCase }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noCase }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .caseNumber }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .monoexponentialCase }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .monoexponentialCase }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noCase }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noCase }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .monoexponentialCase }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noCase }
  ]

-- Count verification
theorem total_count : allData.length = 162 := by native_decide

theorem count_monoexponentialCase :
    (allData.filter (·.value == .monoexponentialCase)).length = 71 := by native_decide
theorem count_caseNumber :
    (allData.filter (·.value == .caseNumber)).length = 8 := by native_decide
theorem count_caseReferentiality :
    (allData.filter (·.value == .caseReferentiality)).length = 6 := by native_decide
theorem count_caseTam :
    (allData.filter (·.value == .caseTam)).length = 2 := by native_decide
theorem count_noCase :
    (allData.filter (·.value == .noCase)).length = 75 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F21A
