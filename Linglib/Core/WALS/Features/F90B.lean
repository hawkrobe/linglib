import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 90B: Prenominal relative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90B`.

Chapter 90, 191 languages.
-/

namespace Core.WALS.F90B

/-- WALS 90B values. -/
inductive PrenominalRelativeClauses where
  | relativeClauseNounDominant  -- Relative clause-Noun (RelN) dominant (141 languages)
  | relnOrNrel  -- RelN or NRel (29 languages)
  | relnOrInternallyHeaded  -- RelN or internally-headed (15 languages)
  | relnOrCorrelative  -- RelN or correlative (5 languages)
  | relnOrDoubleHeaded  -- RelN or double-headed (1 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 90B dataset (191 languages). -/
def allData : List (Datapoint PrenominalRelativeClauses) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .relativeClauseNounDominant }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .relativeClauseNounDominant }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .relativeClauseNounDominant }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .relativeClauseNounDominant }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .relativeClauseNounDominant }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .relativeClauseNounDominant }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .relnOrInternallyHeaded }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .relativeClauseNounDominant }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .relativeClauseNounDominant }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .relnOrInternallyHeaded }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .relativeClauseNounDominant }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .relnOrNrel }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .relativeClauseNounDominant }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .relativeClauseNounDominant }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .relativeClauseNounDominant }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .relativeClauseNounDominant }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .relnOrNrel }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .relativeClauseNounDominant }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .relativeClauseNounDominant }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .relativeClauseNounDominant }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .relativeClauseNounDominant }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .relativeClauseNounDominant }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .relnOrInternallyHeaded }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .relativeClauseNounDominant }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .relnOrNrel }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .relnOrNrel }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .relativeClauseNounDominant }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .relativeClauseNounDominant }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .relativeClauseNounDominant }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .relnOrInternallyHeaded }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .relativeClauseNounDominant }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .relativeClauseNounDominant }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .relativeClauseNounDominant }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .relnOrInternallyHeaded }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .relativeClauseNounDominant }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .relativeClauseNounDominant }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .relativeClauseNounDominant }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .relativeClauseNounDominant }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .relativeClauseNounDominant }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .relativeClauseNounDominant }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .relnOrNrel }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .relativeClauseNounDominant }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .relativeClauseNounDominant }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .relativeClauseNounDominant }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .relnOrCorrelative }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .relativeClauseNounDominant }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .relativeClauseNounDominant }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .relativeClauseNounDominant }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .relativeClauseNounDominant }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .relnOrInternallyHeaded }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .relativeClauseNounDominant }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .relativeClauseNounDominant }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .relativeClauseNounDominant }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .relnOrNrel }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .relativeClauseNounDominant }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .relativeClauseNounDominant }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .relativeClauseNounDominant }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .relnOrNrel }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .relnOrNrel }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .relativeClauseNounDominant }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .relativeClauseNounDominant }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .relativeClauseNounDominant }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .relativeClauseNounDominant }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .relativeClauseNounDominant }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .relnOrInternallyHeaded }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .relativeClauseNounDominant }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .relativeClauseNounDominant }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .relativeClauseNounDominant }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .relativeClauseNounDominant }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .relnOrNrel }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .relativeClauseNounDominant }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .relativeClauseNounDominant }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .relativeClauseNounDominant }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .relnOrInternallyHeaded }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .relativeClauseNounDominant }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .relativeClauseNounDominant }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .relativeClauseNounDominant }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .relativeClauseNounDominant }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .relativeClauseNounDominant }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .relnOrNrel }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .relnOrCorrelative }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .relativeClauseNounDominant }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .relativeClauseNounDominant }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .relativeClauseNounDominant }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .relnOrInternallyHeaded }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .relativeClauseNounDominant }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .relativeClauseNounDominant }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .relativeClauseNounDominant }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .relativeClauseNounDominant }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .relativeClauseNounDominant }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .relnOrCorrelative }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .relativeClauseNounDominant }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .relnOrInternallyHeaded }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .relnOrDoubleHeaded }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .relativeClauseNounDominant }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .relnOrNrel }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .relativeClauseNounDominant }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .relativeClauseNounDominant }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .relnOrNrel }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .relativeClauseNounDominant }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .relnOrNrel }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .relativeClauseNounDominant }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .relativeClauseNounDominant }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .relativeClauseNounDominant }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .relativeClauseNounDominant }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .relativeClauseNounDominant }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .relnOrInternallyHeaded }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .relnOrNrel }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .relativeClauseNounDominant }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .relnOrNrel }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .relativeClauseNounDominant }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .relativeClauseNounDominant }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .relativeClauseNounDominant }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .relnOrNrel }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .relnOrNrel }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .relativeClauseNounDominant }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .relnOrNrel }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .relativeClauseNounDominant }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .relativeClauseNounDominant }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .relativeClauseNounDominant }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .relativeClauseNounDominant }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .relativeClauseNounDominant }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .relativeClauseNounDominant }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .relativeClauseNounDominant }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .relativeClauseNounDominant }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .relativeClauseNounDominant }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .relativeClauseNounDominant }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .relativeClauseNounDominant }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .relativeClauseNounDominant }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .relnOrNrel }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .relativeClauseNounDominant }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .relnOrNrel }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .relativeClauseNounDominant }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .relativeClauseNounDominant }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .relativeClauseNounDominant }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .relativeClauseNounDominant }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .relativeClauseNounDominant }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .relnOrInternallyHeaded }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .relativeClauseNounDominant }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .relativeClauseNounDominant }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .relativeClauseNounDominant }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .relativeClauseNounDominant }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .relativeClauseNounDominant }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .relativeClauseNounDominant }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .relativeClauseNounDominant }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .relnOrNrel }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .relativeClauseNounDominant }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .relnOrCorrelative }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .relativeClauseNounDominant }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .relativeClauseNounDominant }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .relnOrCorrelative }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .relativeClauseNounDominant }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .relativeClauseNounDominant }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .relativeClauseNounDominant }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .relnOrNrel }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .relativeClauseNounDominant }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .relativeClauseNounDominant }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .relnOrNrel }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .relativeClauseNounDominant }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .relnOrNrel }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .relativeClauseNounDominant }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .relativeClauseNounDominant }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .relnOrNrel }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .relativeClauseNounDominant }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .relnOrInternallyHeaded }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .relativeClauseNounDominant }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .relativeClauseNounDominant }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .relativeClauseNounDominant }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .relativeClauseNounDominant }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .relativeClauseNounDominant }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .relativeClauseNounDominant }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .relativeClauseNounDominant }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .relativeClauseNounDominant }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .relativeClauseNounDominant }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .relnOrNrel }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .relativeClauseNounDominant }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .relnOrInternallyHeaded }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .relativeClauseNounDominant }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .relativeClauseNounDominant }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .relativeClauseNounDominant }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .relativeClauseNounDominant }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .relnOrInternallyHeaded }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .relnOrNrel }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .relnOrNrel }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .relativeClauseNounDominant }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .relativeClauseNounDominant }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .relativeClauseNounDominant }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .relativeClauseNounDominant }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .relativeClauseNounDominant }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .relnOrNrel }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .relativeClauseNounDominant }
  ]

-- Count verification
theorem total_count : allData.length = 191 := by native_decide

theorem count_relativeClauseNounDominant :
    (allData.filter (·.value == .relativeClauseNounDominant)).length = 141 := by native_decide
theorem count_relnOrNrel :
    (allData.filter (·.value == .relnOrNrel)).length = 29 := by native_decide
theorem count_relnOrInternallyHeaded :
    (allData.filter (·.value == .relnOrInternallyHeaded)).length = 15 := by native_decide
theorem count_relnOrCorrelative :
    (allData.filter (·.value == .relnOrCorrelative)).length = 5 := by native_decide
theorem count_relnOrDoubleHeaded :
    (allData.filter (·.value == .relnOrDoubleHeaded)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F90B
