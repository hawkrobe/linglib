/-!
# WALS Feature 47A: Intensifiers and Reflexive Pronouns


Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 47A`.

Chapter 47, 168 languages.
-/

namespace Core.WALS.F47A

/-- WALS 47A values. -/
inductive IntensifierReflexive where
  | identical  -- Identical (94 languages)
  | differentiated  -- Differentiated (74 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 47A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : IntensifierReflexive
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 47A dataset (168 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .differentiated }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .identical }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .identical }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .identical }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .identical }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .differentiated }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .identical }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .identical }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .identical }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .differentiated }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .identical }
  , { walsCode := "bgv", language := "Bagvalal", iso := "kva", value := .identical }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .differentiated }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .differentiated }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .identical }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .identical }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .differentiated }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .identical }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .identical }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .differentiated }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .identical }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .differentiated }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .identical }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .identical }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .differentiated }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .differentiated }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .differentiated }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .identical }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .differentiated }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .identical }
  , { walsCode := "eng", language := "English", iso := "eng", value := .identical }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .identical }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .differentiated }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .differentiated }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .identical }
  , { walsCode := "fre", language := "French", iso := "fra", value := .differentiated }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .identical }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .identical }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .identical }
  , { walsCode := "ger", language := "German", iso := "deu", value := .differentiated }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .identical }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .identical }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .differentiated }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .identical }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .identical }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .identical }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .identical }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .differentiated }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .identical }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .identical }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .differentiated }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .identical }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .identical }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .identical }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .identical }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .differentiated }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .identical }
  , { walsCode := "jun", language := "Juang", iso := "jun", value := .identical }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .identical }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .identical }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .differentiated }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .identical }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .identical }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .differentiated }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .identical }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .differentiated }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .identical }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .differentiated }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .differentiated }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .differentiated }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .differentiated }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .identical }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .identical }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .identical }
  , { walsCode := "ktt", language := "Kott", iso := "", value := .differentiated }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .differentiated }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .differentiated }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .differentiated }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .differentiated }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .differentiated }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .identical }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .differentiated }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .identical }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .identical }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .differentiated }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .differentiated }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .identical }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .identical }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .identical }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .identical }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .identical }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .differentiated }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .differentiated }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .identical }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .identical }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .differentiated }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .identical }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .identical }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .identical }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .identical }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .identical }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .differentiated }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .differentiated }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .identical }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .differentiated }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .differentiated }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .differentiated }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .identical }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .identical }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .differentiated }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .differentiated }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .differentiated }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .identical }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .differentiated }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .identical }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .identical }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .differentiated }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .identical }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .differentiated }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .identical }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .identical }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .differentiated }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .differentiated }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .identical }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .differentiated }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .identical }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .differentiated }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .differentiated }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .differentiated }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .differentiated }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .identical }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .differentiated }
  , { walsCode := "som", language := "Somali", iso := "som", value := .differentiated }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .identical }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .differentiated }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .identical }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .differentiated }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .differentiated }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .identical }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .differentiated }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .identical }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .identical }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .identical }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .identical }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .identical }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .identical }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .identical }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .identical }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .identical }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .identical }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .identical }
  , { walsCode := "urh", language := "Urhobo", iso := "urh", value := .identical }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .differentiated }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .differentiated }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .differentiated }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .identical }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .differentiated }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .identical }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .differentiated }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .identical }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .differentiated }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .identical }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .differentiated }
  , { walsCode := "ydd", language := "Yiddish", iso := "ydd", value := .differentiated }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .identical }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .differentiated }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .differentiated }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .differentiated }
  ]

-- Count verification
theorem total_count : allData.length = 168 := by native_decide

theorem count_identical :
    (allData.filter (·.value == .identical)).length = 94 := by native_decide
theorem count_differentiated :
    (allData.filter (·.value == .differentiated)).length = 74 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F47A
