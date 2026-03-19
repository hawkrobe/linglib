import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 21B: Exponence of Tense-Aspect-Mood Inflection
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 21B`.

Chapter 21, 160 languages.
-/

namespace Core.WALS.F21B

/-- WALS 21B values. -/
inductive ExponenceOfTenseAspectMoodInflection where
  | monoexponentialTam  -- monoexponential TAM (127 languages)
  | tamAgreement  -- TAM+agreement (19 languages)
  | tamAgreementDiathesis  -- TAM+agreement+diathesis (4 languages)
  | tamAgreementConstruct  -- TAM+agreement+construct (1 languages)
  | tamPolarity  -- TAM+polarity (5 languages)
  | noTam  -- no TAM (4 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 21B dataset (160 languages). -/
def allData : List (Datapoint ExponenceOfTenseAspectMoodInflection) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .monoexponentialTam }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .monoexponentialTam }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .tamAgreement }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .monoexponentialTam }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .monoexponentialTam }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .monoexponentialTam }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .tamAgreementDiathesis }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .monoexponentialTam }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .monoexponentialTam }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .monoexponentialTam }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .monoexponentialTam }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .monoexponentialTam }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .monoexponentialTam }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .tamAgreement }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .tamAgreement }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .monoexponentialTam }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .monoexponentialTam }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .monoexponentialTam }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .monoexponentialTam }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .monoexponentialTam }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .monoexponentialTam }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .monoexponentialTam }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noTam }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .tamAgreement }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .monoexponentialTam }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .monoexponentialTam }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .monoexponentialTam }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .monoexponentialTam }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .tamAgreement }
  , { walsCode := "cku", language := "Chinook (Upper)", iso := "wac", value := .monoexponentialTam }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .monoexponentialTam }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .monoexponentialTam }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .monoexponentialTam }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .tamAgreement }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .monoexponentialTam }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .monoexponentialTam }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .monoexponentialTam }
  , { walsCode := "eng", language := "English", iso := "eng", value := .monoexponentialTam }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .monoexponentialTam }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .monoexponentialTam }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .monoexponentialTam }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .monoexponentialTam }
  , { walsCode := "fre", language := "French", iso := "fra", value := .tamAgreement }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .monoexponentialTam }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .tamAgreement }
  , { walsCode := "ger", language := "German", iso := "deu", value := .monoexponentialTam }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .monoexponentialTam }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .monoexponentialTam }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .tamAgreementDiathesis }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .monoexponentialTam }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .monoexponentialTam }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .monoexponentialTam }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .monoexponentialTam }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .monoexponentialTam }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .tamAgreementDiathesis }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .tamAgreement }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .monoexponentialTam }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .monoexponentialTam }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .tamAgreement }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .monoexponentialTam }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .tamPolarity }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .monoexponentialTam }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .monoexponentialTam }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .monoexponentialTam }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .monoexponentialTam }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .monoexponentialTam }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .monoexponentialTam }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .monoexponentialTam }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .monoexponentialTam }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .monoexponentialTam }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .tamPolarity }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .tamAgreement }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .tamAgreementDiathesis }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .monoexponentialTam }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .monoexponentialTam }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .monoexponentialTam }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .monoexponentialTam }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .tamAgreement }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .monoexponentialTam }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .tamAgreement }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .monoexponentialTam }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .tamPolarity }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .monoexponentialTam }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .monoexponentialTam }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .monoexponentialTam }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .monoexponentialTam }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .monoexponentialTam }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .monoexponentialTam }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .tamAgreementConstruct }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .monoexponentialTam }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .monoexponentialTam }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .monoexponentialTam }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .monoexponentialTam }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .tamPolarity }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .monoexponentialTam }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .monoexponentialTam }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .tamPolarity }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .monoexponentialTam }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .tamAgreement }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .monoexponentialTam }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .monoexponentialTam }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .monoexponentialTam }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .monoexponentialTam }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noTam }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .monoexponentialTam }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .monoexponentialTam }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .monoexponentialTam }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .monoexponentialTam }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .monoexponentialTam }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .monoexponentialTam }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .monoexponentialTam }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .monoexponentialTam }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .monoexponentialTam }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .monoexponentialTam }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .monoexponentialTam }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .monoexponentialTam }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .monoexponentialTam }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .monoexponentialTam }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .tamAgreement }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .monoexponentialTam }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .monoexponentialTam }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .monoexponentialTam }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .monoexponentialTam }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .monoexponentialTam }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .monoexponentialTam }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .monoexponentialTam }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .monoexponentialTam }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noTam }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .monoexponentialTam }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .monoexponentialTam }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .tamAgreement }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .monoexponentialTam }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .monoexponentialTam }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .monoexponentialTam }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .monoexponentialTam }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .monoexponentialTam }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .monoexponentialTam }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .tamAgreement }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noTam }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .monoexponentialTam }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .monoexponentialTam }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .monoexponentialTam }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .tamAgreement }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .monoexponentialTam }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .monoexponentialTam }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .monoexponentialTam }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .monoexponentialTam }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .monoexponentialTam }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .tamAgreement }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .monoexponentialTam }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .monoexponentialTam }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .monoexponentialTam }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .monoexponentialTam }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .monoexponentialTam }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .monoexponentialTam }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .monoexponentialTam }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .monoexponentialTam }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .monoexponentialTam }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .monoexponentialTam }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .monoexponentialTam }
  ]

-- Count verification
theorem total_count : allData.length = 160 := by native_decide

theorem count_monoexponentialTam :
    (allData.filter (·.value == .monoexponentialTam)).length = 127 := by native_decide
theorem count_tamAgreement :
    (allData.filter (·.value == .tamAgreement)).length = 19 := by native_decide
theorem count_tamAgreementDiathesis :
    (allData.filter (·.value == .tamAgreementDiathesis)).length = 4 := by native_decide
theorem count_tamAgreementConstruct :
    (allData.filter (·.value == .tamAgreementConstruct)).length = 1 := by native_decide
theorem count_tamPolarity :
    (allData.filter (·.value == .tamPolarity)).length = 5 := by native_decide
theorem count_noTam :
    (allData.filter (·.value == .noTam)).length = 4 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F21B
