/-!
# WALS Feature 42A: Pronominal and Adnominal Demonstratives
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 42A`.

Chapter 42, 201 languages.
-/

namespace Core.WALS.F42A

/-- WALS 42A values. -/
inductive PronominalAndAdnominalDemonstratives where
  | identical  -- Identical (143 languages)
  | differentStem  -- Different stem (37 languages)
  | differentInflection  -- Different inflection (21 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 42A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PronominalAndAdnominalDemonstratives
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 42A dataset (201 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .identical }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .identical }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .identical }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .identical }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .differentStem }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .identical }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .identical }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .differentStem }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .identical }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .differentStem }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .identical }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .identical }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .identical }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .identical }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .identical }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .differentStem }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .identical }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .identical }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .identical }
  , { walsCode := "bad", language := "Bade", iso := "bde", value := .differentStem }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .differentStem }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .identical }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .identical }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .differentStem }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .differentInflection }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .differentInflection }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .identical }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .identical }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .identical }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .differentInflection }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .identical }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .identical }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .identical }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .identical }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .identical }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .identical }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .identical }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .identical }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .identical }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .identical }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .identical }
  , { walsCode := "eng", language := "English", iso := "eng", value := .identical }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .differentInflection }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .identical }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .identical }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .identical }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .identical }
  , { walsCode := "fre", language := "French", iso := "fra", value := .differentStem }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .identical }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .differentInflection }
  , { walsCode := "ger", language := "German", iso := "deu", value := .identical }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .identical }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .identical }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .differentStem }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .identical }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .differentStem }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .identical }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .identical }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .identical }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .identical }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .identical }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .identical }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .differentInflection }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .identical }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .identical }
  , { walsCode := "inr", language := "Inuktitut (Aivilingmiutut)", iso := "ike", value := .identical }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .differentStem }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .identical }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .identical }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .differentInflection }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .differentInflection }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .differentStem }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .identical }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .identical }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .differentInflection }
  , { walsCode := "krg", language := "Karanga", iso := "sna", value := .identical }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .identical }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .identical }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .identical }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .differentInflection }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .differentInflection }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .identical }
  , { walsCode := "klb", language := "Kilba", iso := "hbb", value := .differentStem }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .identical }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .identical }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .identical }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .identical }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .identical }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .identical }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .differentStem }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .differentStem }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .identical }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .identical }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .identical }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .identical }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .differentStem }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .identical }
  , { walsCode := "kwm", language := "Kwami", iso := "ksq", value := .identical }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .identical }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .differentStem }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .identical }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .differentStem }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .differentInflection }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .differentInflection }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .identical }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .differentStem }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .identical }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .identical }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .identical }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .differentInflection }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .identical }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .differentStem }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .identical }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .identical }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .differentStem }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .identical }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .differentStem }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .identical }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .identical }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .identical }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .identical }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .identical }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .identical }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .identical }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .identical }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .identical }
  , { walsCode := "mul", language := "Mulao", iso := "mlm", value := .differentStem }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .differentStem }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .identical }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .differentStem }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .identical }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .identical }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .identical }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .identical }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .differentStem }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .differentInflection }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .identical }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .identical }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .identical }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .identical }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .identical }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .identical }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .identical }
  , { walsCode := "put", language := "Paiute (Southern)", iso := "ute", value := .identical }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .identical }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .differentStem }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .identical }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .identical }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .identical }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .differentInflection }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .identical }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .identical }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .differentStem }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .identical }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .identical }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .identical }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .identical }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .identical }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .identical }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .identical }
  , { walsCode := "so", language := "So", iso := "teu", value := .differentStem }
  , { walsCode := "som", language := "Somali", iso := "som", value := .differentInflection }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .identical }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .identical }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .identical }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .identical }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .identical }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .differentInflection }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .differentStem }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .differentInflection }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .identical }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .differentStem }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .identical }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .identical }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .differentInflection }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .identical }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .identical }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .identical }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .identical }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .differentInflection }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .identical }
  , { walsCode := "uri", language := "Urim", iso := "uri", value := .identical }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .identical }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .identical }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .identical }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .differentStem }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .identical }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .identical }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .differentStem }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .identical }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .identical }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .differentStem }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .identical }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .differentStem }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .differentStem }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .identical }
  , { walsCode := "ynk", language := "Yankuntjatjara", iso := "kdd", value := .identical }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .identical }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .identical }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .differentStem }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .identical }
  ]

-- Count verification
theorem total_count : allData.length = 201 := by native_decide

theorem count_identical :
    (allData.filter (·.value == .identical)).length = 143 := by native_decide
theorem count_differentStem :
    (allData.filter (·.value == .differentStem)).length = 37 := by native_decide
theorem count_differentInflection :
    (allData.filter (·.value == .differentInflection)).length = 21 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F42A
