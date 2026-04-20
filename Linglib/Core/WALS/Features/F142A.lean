import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 142A: Para-Linguistic Usages of Clicks
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 142A`.

Chapter 142, 143 languages.
-/

namespace Core.WALS.F142A

/-- WALS 142A values. -/
inductive ParaLinguisticUsagesOfClicks where
  /-- Logical meanings (47 languages). -/
  | logicalMeanings
  /-- Affective meanings (71 languages). -/
  | affectiveMeanings
  /-- Other or none (25 languages). -/
  | otherOrNone
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 142A dataset (143 languages). -/
def allData : List (Datapoint ParaLinguisticUsagesOfClicks) :=
  [ { walsCode := "alb", language := "Albanian", iso := "sqi", value := .logicalMeanings }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .affectiveMeanings }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .otherOrNone }
  , { walsCode := "abh", language := "Arabic (Bahrain)", iso := "abv", value := .logicalMeanings }
  , { walsCode := "ako", language := "Arabic (Kormakiti)", iso := "acy", value := .logicalMeanings }
  , { walsCode := "arl", language := "Arabic (Lebanese)", iso := "apc", value := .logicalMeanings }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .logicalMeanings }
  , { walsCode := "ars", language := "Arabic (San'ani)", iso := "ayn", value := .logicalMeanings }
  , { walsCode := "atu", language := "Arabic (Tunisian)", iso := "aeb", value := .logicalMeanings }
  , { walsCode := "akm", language := "Arakanese (Marma)", iso := "rmz", value := .affectiveMeanings }
  , { walsCode := "aul", language := "Aulua", iso := "aul", value := .affectiveMeanings }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .logicalMeanings }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .logicalMeanings }
  , { walsCode := "bal", language := "Balinese", iso := "ban", value := .affectiveMeanings }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .logicalMeanings }
  , { walsCode := "bmn", language := "Bamun", iso := "bax", value := .affectiveMeanings }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .logicalMeanings }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .otherOrNone }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .logicalMeanings }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .otherOrNone }
  , { walsCode := "bos", language := "Bosnian", iso := "bos", value := .logicalMeanings }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .affectiveMeanings }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .logicalMeanings }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .affectiveMeanings }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .logicalMeanings }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .otherOrNone }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .affectiveMeanings }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .affectiveMeanings }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .otherOrNone }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .affectiveMeanings }
  , { walsCode := "dge", language := "Deutsche Gebärdensprache", iso := "gsg", value := .affectiveMeanings }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .affectiveMeanings }
  , { walsCode := "dyu", language := "Dyula", iso := "dyu", value := .logicalMeanings }
  , { walsCode := "eng", language := "English", iso := "eng", value := .affectiveMeanings }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .affectiveMeanings }
  , { walsCode := "fiw", language := "Fijian (Wayan)", iso := "wyy", value := .affectiveMeanings }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .affectiveMeanings }
  , { walsCode := "fbf", language := "Fula (Burkina Faso)", iso := "fuh", value := .logicalMeanings }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .affectiveMeanings }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .logicalMeanings }
  , { walsCode := "ger", language := "German", iso := "deu", value := .affectiveMeanings }
  , { walsCode := "gvi", language := "German (Viennese)", iso := "bar", value := .affectiveMeanings }
  , { walsCode := "gho", language := "Ghotuo", iso := "aaa", value := .logicalMeanings }
  , { walsCode := "gcy", language := "Greek (Cypriot)", iso := "ell", value := .logicalMeanings }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .logicalMeanings }
  , { walsCode := "gue", language := "Guere", iso := "", value := .logicalMeanings }
  , { walsCode := "gfr", language := "Guianese French Creole", iso := "gcr", value := .affectiveMeanings }
  , { walsCode := "gji", language := "Gurindji", iso := "gue", value := .otherOrNone }
  , { walsCode := "gro", language := "Guro", iso := "goa", value := .logicalMeanings }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .otherOrNone }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .affectiveMeanings }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .logicalMeanings }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .logicalMeanings }
  , { walsCode := "hmd", language := "Hmong Daw", iso := "mww", value := .affectiveMeanings }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .affectiveMeanings }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .affectiveMeanings }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .logicalMeanings }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .otherOrNone }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .affectiveMeanings }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .affectiveMeanings }
  , { walsCode := "inj", language := "Indonesian (Jakarta)", iso := "ind", value := .affectiveMeanings }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .logicalMeanings }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .affectiveMeanings }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .logicalMeanings }
  , { walsCode := "itb", language := "Italian (Bologna)", iso := "egl", value := .logicalMeanings }
  , { walsCode := "ifi", language := "Italian (Fiorentino)", iso := "ita", value := .logicalMeanings }
  , { walsCode := "itg", language := "Italian (Genoa)", iso := "lij", value := .logicalMeanings }
  , { walsCode := "itn", language := "Italian (Napolitanian)", iso := "nap", value := .logicalMeanings }
  , { walsCode := "jah", language := "Jahai", iso := "jhi", value := .affectiveMeanings }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .affectiveMeanings }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .affectiveMeanings }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .affectiveMeanings }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .otherOrNone }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .otherOrNone }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .affectiveMeanings }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .affectiveMeanings }
  , { walsCode := "khu", language := "Khumi", iso := "cnk", value := .affectiveMeanings }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .affectiveMeanings }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .affectiveMeanings }
  , { walsCode := "kij", language := "Kitja", iso := "gia", value := .otherOrNone }
  , { walsCode := "kou", language := "Kom", iso := "bkm", value := .affectiveMeanings }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .affectiveMeanings }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .logicalMeanings }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .otherOrNone }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .otherOrNone }
  , { walsCode := "lns", language := "Lamnso'", iso := "lns", value := .affectiveMeanings }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .affectiveMeanings }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .affectiveMeanings }
  , { walsCode := "lov", language := "Loven", iso := "lbo", value := .affectiveMeanings }
  , { walsCode := "lye", language := "Lyele", iso := "lee", value := .logicalMeanings }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .affectiveMeanings }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .affectiveMeanings }
  , { walsCode := "myk", language := "Malay (Kuala Lumpur)", iso := "zlm", value := .affectiveMeanings }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .logicalMeanings }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .logicalMeanings }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .affectiveMeanings }
  , { walsCode := "mnk", language := "Maninka", iso := "emk", value := .logicalMeanings }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .affectiveMeanings }
  , { walsCode := "mbz", language := "Mbe'", iso := "mtk", value := .affectiveMeanings }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .otherOrNone }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .affectiveMeanings }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .affectiveMeanings }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .otherOrNone }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .otherOrNone }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .logicalMeanings }
  , { walsCode := "mdb", language := "Mudburra", iso := "dmw", value := .otherOrNone }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .otherOrNone }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .affectiveMeanings }
  , { walsCode := "nvs", language := "Nivkh (South Sakhalin)", iso := "niv", value := .otherOrNone }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .affectiveMeanings }
  , { walsCode := "oi", language := "Oi", iso := "oyb", value := .affectiveMeanings }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .logicalMeanings }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .affectiveMeanings }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .logicalMeanings }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .otherOrNone }
  , { walsCode := "fma", language := "Pulaar", iso := "fuc", value := .logicalMeanings }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .affectiveMeanings }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .affectiveMeanings }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .affectiveMeanings }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .otherOrNone }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .logicalMeanings }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .affectiveMeanings }
  , { walsCode := "som", language := "Somali", iso := "som", value := .logicalMeanings }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .affectiveMeanings }
  , { walsCode := "spc", language := "Spanish (Canary Islands)", iso := "spa", value := .affectiveMeanings }
  , { walsCode := "sra", language := "Sranan", iso := "srn", value := .logicalMeanings }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .affectiveMeanings }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .affectiveMeanings }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .affectiveMeanings }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .otherOrNone }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .logicalMeanings }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .affectiveMeanings }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .affectiveMeanings }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .logicalMeanings }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .affectiveMeanings }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .logicalMeanings }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .otherOrNone }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .otherOrNone }
  , { walsCode := "yba", language := "Yamba", iso := "yam", value := .affectiveMeanings }
  , { walsCode := "ydd", language := "Yiddish", iso := "ydd", value := .affectiveMeanings }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .affectiveMeanings }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .otherOrNone }
  , { walsCode := "zsq", language := "Zapotec (San Lucas Quiaviní)", iso := "zab", value := .affectiveMeanings }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F142A
