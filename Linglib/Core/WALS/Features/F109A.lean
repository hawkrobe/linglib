import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 109A: Applicative Constructions
@cite{polinsky-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 109A`.

Chapter 109, 183 languages.
-/

namespace Core.WALS.F109A

/-- WALS 109A values. -/
inductive ApplicativeType where
  | benefactiveBothBases  -- Benefactive object; both bases (16 languages)
  | benefactiveTransOnly  -- Benefactive object; only transitive (4 languages)
  | benefactiveAndOtherBothBases  -- Benefactive and other; both bases (49 languages)
  | benefactiveAndOtherTransOnly  -- Benefactive and other; only transitive (2 languages)
  | nonBenefactiveBothBases  -- Non-benefactive object; both bases (9 languages)
  | nonBenefactiveTransOnly  -- Non-benefactive object; only transitive (1 languages)
  | nonBenefactiveIntransOnly  -- Non-benefactive object; only intransitive (2 languages)
  | noApplicative  -- No applicative construction (100 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 109A dataset (183 languages). -/
def allData : List (Datapoint ApplicativeType) :=
  [ { walsCode := "abz", language := "Abaza", iso := "abq", value := .benefactiveAndOtherBothBases }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .benefactiveAndOtherTransOnly }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .benefactiveBothBases }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .benefactiveBothBases }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noApplicative }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noApplicative }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .benefactiveAndOtherBothBases }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noApplicative }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noApplicative }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .benefactiveTransOnly }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noApplicative }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noApplicative }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noApplicative }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noApplicative }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noApplicative }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noApplicative }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noApplicative }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .benefactiveAndOtherBothBases }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .benefactiveAndOtherBothBases }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noApplicative }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .benefactiveTransOnly }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .benefactiveBothBases }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .benefactiveAndOtherBothBases }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noApplicative }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .benefactiveAndOtherBothBases }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .benefactiveBothBases }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noApplicative }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .benefactiveAndOtherBothBases }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .benefactiveAndOtherBothBases }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noApplicative }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .nonBenefactiveBothBases }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noApplicative }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .nonBenefactiveBothBases }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noApplicative }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noApplicative }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .nonBenefactiveIntransOnly }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noApplicative }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noApplicative }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .noApplicative }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noApplicative }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .noApplicative }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noApplicative }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .benefactiveAndOtherBothBases }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noApplicative }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .benefactiveAndOtherBothBases }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noApplicative }
  , { walsCode := "hli", language := "Halkomelem (Island)", iso := "hur", value := .benefactiveAndOtherBothBases }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .benefactiveAndOtherBothBases }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noApplicative }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noApplicative }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noApplicative }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noApplicative }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noApplicative }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noApplicative }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noApplicative }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .benefactiveAndOtherBothBases }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .benefactiveTransOnly }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noApplicative }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noApplicative }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .nonBenefactiveTransOnly }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noApplicative }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .nonBenefactiveBothBases }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .benefactiveAndOtherBothBases }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .benefactiveBothBases }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .benefactiveAndOtherBothBases }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .benefactiveAndOtherBothBases }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noApplicative }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noApplicative }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noApplicative }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .benefactiveBothBases }
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
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .nonBenefactiveBothBases }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .benefactiveAndOtherBothBases }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .benefactiveAndOtherBothBases }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .benefactiveAndOtherBothBases }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noApplicative }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .benefactiveAndOtherBothBases }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .benefactiveAndOtherBothBases }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noApplicative }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noApplicative }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noApplicative }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .benefactiveAndOtherBothBases }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noApplicative }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noApplicative }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noApplicative }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noApplicative }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noApplicative }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noApplicative }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noApplicative }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noApplicative }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noApplicative }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noApplicative }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noApplicative }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .benefactiveBothBases }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noApplicative }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noApplicative }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .nonBenefactiveBothBases }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .benefactiveAndOtherBothBases }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .benefactiveBothBases }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .benefactiveBothBases }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .benefactiveAndOtherBothBases }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noApplicative }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noApplicative }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noApplicative }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .benefactiveAndOtherBothBases }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .noApplicative }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .benefactiveBothBases }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .benefactiveBothBases }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noApplicative }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noApplicative }
  , { walsCode := "pmc", language := "Pomo (Central)", iso := "poo", value := .noApplicative }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .benefactiveBothBases }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .benefactiveBothBases }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noApplicative }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noApplicative }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noApplicative }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noApplicative }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noApplicative }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noApplicative }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .benefactiveAndOtherBothBases }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .benefactiveAndOtherBothBases }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noApplicative }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noApplicative }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noApplicative }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noApplicative }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .nonBenefactiveBothBases }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tap", language := "Taiap", iso := "gpn", value := .benefactiveAndOtherTransOnly }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .noApplicative }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noApplicative }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .nonBenefactiveBothBases }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .noApplicative }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noApplicative }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noApplicative }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .noApplicative }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .benefactiveTransOnly }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .benefactiveAndOtherBothBases }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .benefactiveBothBases }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noApplicative }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noApplicative }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .nonBenefactiveIntransOnly }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noApplicative }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noApplicative }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noApplicative }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .benefactiveAndOtherBothBases }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noApplicative }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .benefactiveAndOtherBothBases }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .nonBenefactiveBothBases }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .benefactiveBothBases }
  , { walsCode := "yaz", language := "Yazgulyam", iso := "yah", value := .noApplicative }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .nonBenefactiveBothBases }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .benefactiveAndOtherBothBases }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noApplicative }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noApplicative }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noApplicative }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .benefactiveBothBases }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .benefactiveAndOtherBothBases }
  ]

-- Count verification
theorem total_count : allData.length = 183 := by native_decide

theorem count_benefactiveBothBases :
    (allData.filter (·.value == .benefactiveBothBases)).length = 16 := by native_decide
theorem count_benefactiveTransOnly :
    (allData.filter (·.value == .benefactiveTransOnly)).length = 4 := by native_decide
theorem count_benefactiveAndOtherBothBases :
    (allData.filter (·.value == .benefactiveAndOtherBothBases)).length = 49 := by native_decide
theorem count_benefactiveAndOtherTransOnly :
    (allData.filter (·.value == .benefactiveAndOtherTransOnly)).length = 2 := by native_decide
theorem count_nonBenefactiveBothBases :
    (allData.filter (·.value == .nonBenefactiveBothBases)).length = 9 := by native_decide
theorem count_nonBenefactiveTransOnly :
    (allData.filter (·.value == .nonBenefactiveTransOnly)).length = 1 := by native_decide
theorem count_nonBenefactiveIntransOnly :
    (allData.filter (·.value == .nonBenefactiveIntransOnly)).length = 2 := by native_decide
theorem count_noApplicative :
    (allData.filter (·.value == .noApplicative)).length = 100 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F109A
