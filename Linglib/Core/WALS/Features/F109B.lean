import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 109B: Other Roles of Applied Objects
@cite{polinsky-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 109B`.

Chapter 109, 183 languages.
-/

namespace Core.WALS.F109B

/-- WALS 109B values. -/
inductive AppliedObjectRole where
  | instrument  -- Instrument (17 languages)
  | locative  -- Locative (18 languages)
  | instrumentAndLocative  -- Instrument and locative (12 languages)
  | onlyBenefactive  -- No other roles (= Only benefactive) (36 languages)
  | noApplicative  -- No applicative construction (100 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 109B dataset (183 languages). -/
def allData : List (Datapoint AppliedObjectRole) :=
  [ { walsCode := "abz", language := "Abaza", iso := "abq", value := .instrumentAndLocative }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .instrument }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .onlyBenefactive }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .instrumentAndLocative }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .onlyBenefactive }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .onlyBenefactive }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noApplicative }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noApplicative }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .locative }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noApplicative }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noApplicative }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .onlyBenefactive }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noApplicative }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noApplicative }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noApplicative }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noApplicative }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noApplicative }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noApplicative }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noApplicative }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .onlyBenefactive }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .locative }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noApplicative }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .onlyBenefactive }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .onlyBenefactive }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .instrumentAndLocative }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noApplicative }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .instrument }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .onlyBenefactive }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noApplicative }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .locative }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .locative }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noApplicative }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .instrument }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noApplicative }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .onlyBenefactive }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noApplicative }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noApplicative }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .locative }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noApplicative }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noApplicative }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .noApplicative }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .locative }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noApplicative }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .noApplicative }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noApplicative }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .instrument }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noApplicative }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .instrument }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noApplicative }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .onlyBenefactive }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .locative }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noApplicative }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noApplicative }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noApplicative }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noApplicative }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noApplicative }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noApplicative }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noApplicative }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .onlyBenefactive }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .onlyBenefactive }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .onlyBenefactive }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .onlyBenefactive }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noApplicative }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noApplicative }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .instrument }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noApplicative }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .locative }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .locative }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .onlyBenefactive }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .locative }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .instrument }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noApplicative }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noApplicative }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noApplicative }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .onlyBenefactive }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .noApplicative }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noApplicative }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noApplicative }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noApplicative }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noApplicative }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .noApplicative }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noApplicative }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noApplicative }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .noApplicative }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noApplicative }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noApplicative }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .instrument }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .locative }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .instrument }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .instrument }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noApplicative }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .onlyBenefactive }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .locative }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noApplicative }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noApplicative }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noApplicative }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .locative }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .instrumentAndLocative }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noApplicative }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noApplicative }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .instrumentAndLocative }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noApplicative }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noApplicative }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noApplicative }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noApplicative }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .locative }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noApplicative }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noApplicative }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .instrument }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .onlyBenefactive }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noApplicative }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noApplicative }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .onlyBenefactive }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noApplicative }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .locative }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .onlyBenefactive }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noApplicative }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noApplicative }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .instrument }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .onlyBenefactive }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .onlyBenefactive }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .onlyBenefactive }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .instrumentAndLocative }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noApplicative }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noApplicative }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noApplicative }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .instrumentAndLocative }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .noApplicative }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .onlyBenefactive }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .onlyBenefactive }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noApplicative }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noApplicative }
  , { walsCode := "pmc", language := "Pomo (Central)", iso := "poo", value := .noApplicative }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .onlyBenefactive }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .onlyBenefactive }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noApplicative }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noApplicative }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noApplicative }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noApplicative }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noApplicative }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noApplicative }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .instrumentAndLocative }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .onlyBenefactive }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noApplicative }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noApplicative }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noApplicative }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noApplicative }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .locative }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .onlyBenefactive }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .instrumentAndLocative }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .onlyBenefactive }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .noApplicative }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .instrument }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noApplicative }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .locative }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .instrument }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .noApplicative }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .instrumentAndLocative }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noApplicative }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noApplicative }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .noApplicative }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .onlyBenefactive }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .instrument }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .onlyBenefactive }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noApplicative }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noApplicative }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .locative }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noApplicative }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noApplicative }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noApplicative }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .instrument }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noApplicative }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .instrumentAndLocative }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .instrumentAndLocative }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .onlyBenefactive }
  , { walsCode := "yaz", language := "Yazgulyam", iso := "yah", value := .noApplicative }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .onlyBenefactive }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .onlyBenefactive }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noApplicative }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noApplicative }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noApplicative }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .onlyBenefactive }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .instrument }
  ]

-- Count verification
theorem total_count : allData.length = 183 := by native_decide

theorem count_instrument :
    (allData.filter (·.value == .instrument)).length = 17 := by native_decide
theorem count_locative :
    (allData.filter (·.value == .locative)).length = 18 := by native_decide
theorem count_instrumentAndLocative :
    (allData.filter (·.value == .instrumentAndLocative)).length = 12 := by native_decide
theorem count_onlyBenefactive :
    (allData.filter (·.value == .onlyBenefactive)).length = 36 := by native_decide
theorem count_noApplicative :
    (allData.filter (·.value == .noApplicative)).length = 100 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F109B
