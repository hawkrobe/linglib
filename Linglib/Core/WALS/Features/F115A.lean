import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 115A: Negative Indefinite Pronouns and Predicate Negation
@cite{haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 115A`.

Chapter 115, 206 languages.
-/

namespace Core.WALS.F115A

/-- WALS 115A values. -/
inductive NegativeIndefiniteType where
  | predicateNegationAlsoPresent  -- Predicate negation also present (170 languages)
  | noPredicateNegation  -- No predicate negation (11 languages)
  | mixedBehaviour  -- Mixed behaviour (13 languages)
  | negativeExistentialConstruction  -- Negative existential construction (12 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 115A dataset (206 languages). -/
def allData : List (Datapoint NegativeIndefiniteType) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .predicateNegationAlsoPresent }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .predicateNegationAlsoPresent }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .predicateNegationAlsoPresent }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .predicateNegationAlsoPresent }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .predicateNegationAlsoPresent }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .predicateNegationAlsoPresent }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .predicateNegationAlsoPresent }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .predicateNegationAlsoPresent }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .predicateNegationAlsoPresent }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .predicateNegationAlsoPresent }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .predicateNegationAlsoPresent }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .predicateNegationAlsoPresent }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .negativeExistentialConstruction }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .predicateNegationAlsoPresent }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .predicateNegationAlsoPresent }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .predicateNegationAlsoPresent }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .predicateNegationAlsoPresent }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .predicateNegationAlsoPresent }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .predicateNegationAlsoPresent }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .predicateNegationAlsoPresent }
  , { walsCode := "boz", language := "Bozo (Tigemaxo)", iso := "boz", value := .predicateNegationAlsoPresent }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .predicateNegationAlsoPresent }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .predicateNegationAlsoPresent }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .predicateNegationAlsoPresent }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .predicateNegationAlsoPresent }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .predicateNegationAlsoPresent }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .predicateNegationAlsoPresent }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .predicateNegationAlsoPresent }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noPredicateNegation }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .predicateNegationAlsoPresent }
  , { walsCode := "cch", language := "Chocho", iso := "coz", value := .noPredicateNegation }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .predicateNegationAlsoPresent }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .predicateNegationAlsoPresent }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .predicateNegationAlsoPresent }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .predicateNegationAlsoPresent }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .predicateNegationAlsoPresent }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noPredicateNegation }
  , { walsCode := "eng", language := "English", iso := "eng", value := .mixedBehaviour }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .predicateNegationAlsoPresent }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .predicateNegationAlsoPresent }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .predicateNegationAlsoPresent }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .predicateNegationAlsoPresent }
  , { walsCode := "fre", language := "French", iso := "fra", value := .mixedBehaviour }
  , { walsCode := "fue", language := "Futuna (East)", iso := "fud", value := .negativeExistentialConstruction }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .mixedBehaviour }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noPredicateNegation }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .predicateNegationAlsoPresent }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .predicateNegationAlsoPresent }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .predicateNegationAlsoPresent }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .predicateNegationAlsoPresent }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .predicateNegationAlsoPresent }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .predicateNegationAlsoPresent }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .predicateNegationAlsoPresent }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .predicateNegationAlsoPresent }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .predicateNegationAlsoPresent }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .predicateNegationAlsoPresent }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .predicateNegationAlsoPresent }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .predicateNegationAlsoPresent }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .predicateNegationAlsoPresent }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .mixedBehaviour }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .predicateNegationAlsoPresent }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .negativeExistentialConstruction }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .predicateNegationAlsoPresent }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .mixedBehaviour }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .mixedBehaviour }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .predicateNegationAlsoPresent }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .predicateNegationAlsoPresent }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .predicateNegationAlsoPresent }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .predicateNegationAlsoPresent }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .predicateNegationAlsoPresent }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .predicateNegationAlsoPresent }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .predicateNegationAlsoPresent }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .predicateNegationAlsoPresent }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .predicateNegationAlsoPresent }
  , { walsCode := "kaz", language := "Kazakh", iso := "kaz", value := .predicateNegationAlsoPresent }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .predicateNegationAlsoPresent }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .predicateNegationAlsoPresent }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .predicateNegationAlsoPresent }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .predicateNegationAlsoPresent }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .predicateNegationAlsoPresent }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .predicateNegationAlsoPresent }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .predicateNegationAlsoPresent }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .predicateNegationAlsoPresent }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .predicateNegationAlsoPresent }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .predicateNegationAlsoPresent }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .predicateNegationAlsoPresent }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .predicateNegationAlsoPresent }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .predicateNegationAlsoPresent }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .predicateNegationAlsoPresent }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .predicateNegationAlsoPresent }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .predicateNegationAlsoPresent }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .predicateNegationAlsoPresent }
  , { walsCode := "kug", language := "Kunming", iso := "cmn", value := .predicateNegationAlsoPresent }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .predicateNegationAlsoPresent }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .predicateNegationAlsoPresent }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .negativeExistentialConstruction }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .predicateNegationAlsoPresent }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .predicateNegationAlsoPresent }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .predicateNegationAlsoPresent }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .predicateNegationAlsoPresent }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .predicateNegationAlsoPresent }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .predicateNegationAlsoPresent }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .predicateNegationAlsoPresent }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .predicateNegationAlsoPresent }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .predicateNegationAlsoPresent }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .predicateNegationAlsoPresent }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .predicateNegationAlsoPresent }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .mixedBehaviour }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .mixedBehaviour }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .predicateNegationAlsoPresent }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .predicateNegationAlsoPresent }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noPredicateNegation }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .predicateNegationAlsoPresent }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .predicateNegationAlsoPresent }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .predicateNegationAlsoPresent }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .predicateNegationAlsoPresent }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .predicateNegationAlsoPresent }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .predicateNegationAlsoPresent }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .predicateNegationAlsoPresent }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noPredicateNegation }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .predicateNegationAlsoPresent }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .negativeExistentialConstruction }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .predicateNegationAlsoPresent }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .predicateNegationAlsoPresent }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .predicateNegationAlsoPresent }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .predicateNegationAlsoPresent }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .predicateNegationAlsoPresent }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noPredicateNegation }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .predicateNegationAlsoPresent }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .predicateNegationAlsoPresent }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .predicateNegationAlsoPresent }
  , { walsCode := "nel", language := "Nelemwa", iso := "nee", value := .negativeExistentialConstruction }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .predicateNegationAlsoPresent }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .predicateNegationAlsoPresent }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .predicateNegationAlsoPresent }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .predicateNegationAlsoPresent }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .predicateNegationAlsoPresent }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .predicateNegationAlsoPresent }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .negativeExistentialConstruction }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .predicateNegationAlsoPresent }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .predicateNegationAlsoPresent }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .predicateNegationAlsoPresent }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .predicateNegationAlsoPresent }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noPredicateNegation }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .predicateNegationAlsoPresent }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .predicateNegationAlsoPresent }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .predicateNegationAlsoPresent }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .predicateNegationAlsoPresent }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .predicateNegationAlsoPresent }
  , { walsCode := "pop", language := "Popoloca (Metzontla)", iso := "pbe", value := .predicateNegationAlsoPresent }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .mixedBehaviour }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noPredicateNegation }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .predicateNegationAlsoPresent }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .predicateNegationAlsoPresent }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .predicateNegationAlsoPresent }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .predicateNegationAlsoPresent }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .predicateNegationAlsoPresent }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .predicateNegationAlsoPresent }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .predicateNegationAlsoPresent }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .predicateNegationAlsoPresent }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .predicateNegationAlsoPresent }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .predicateNegationAlsoPresent }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .predicateNegationAlsoPresent }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .predicateNegationAlsoPresent }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .predicateNegationAlsoPresent }
  , { walsCode := "som", language := "Somali", iso := "som", value := .predicateNegationAlsoPresent }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .mixedBehaviour }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .predicateNegationAlsoPresent }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .predicateNegationAlsoPresent }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .predicateNegationAlsoPresent }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .mixedBehaviour }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .mixedBehaviour }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .predicateNegationAlsoPresent }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .negativeExistentialConstruction }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .predicateNegationAlsoPresent }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .predicateNegationAlsoPresent }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .negativeExistentialConstruction }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .predicateNegationAlsoPresent }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .predicateNegationAlsoPresent }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .predicateNegationAlsoPresent }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .predicateNegationAlsoPresent }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .predicateNegationAlsoPresent }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .predicateNegationAlsoPresent }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noPredicateNegation }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .negativeExistentialConstruction }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .predicateNegationAlsoPresent }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .predicateNegationAlsoPresent }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .predicateNegationAlsoPresent }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .negativeExistentialConstruction }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .predicateNegationAlsoPresent }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noPredicateNegation }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .predicateNegationAlsoPresent }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .predicateNegationAlsoPresent }
  , { walsCode := "uku", language := "Upper Kuskokwim", iso := "kuu", value := .negativeExistentialConstruction }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .predicateNegationAlsoPresent }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .predicateNegationAlsoPresent }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .predicateNegationAlsoPresent }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .predicateNegationAlsoPresent }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .predicateNegationAlsoPresent }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .mixedBehaviour }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .predicateNegationAlsoPresent }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .predicateNegationAlsoPresent }
  , { walsCode := "zaq", language := "Zapotec (Quiegolani)", iso := "zpi", value := .predicateNegationAlsoPresent }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .predicateNegationAlsoPresent }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .predicateNegationAlsoPresent }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .predicateNegationAlsoPresent }
  ]

-- Count verification
theorem total_count : allData.length = 206 := by native_decide

theorem count_predicateNegationAlsoPresent :
    (allData.filter (·.value == .predicateNegationAlsoPresent)).length = 170 := by native_decide
theorem count_noPredicateNegation :
    (allData.filter (·.value == .noPredicateNegation)).length = 11 := by native_decide
theorem count_mixedBehaviour :
    (allData.filter (·.value == .mixedBehaviour)).length = 13 := by native_decide
theorem count_negativeExistentialConstruction :
    (allData.filter (·.value == .negativeExistentialConstruction)).length = 12 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F115A
