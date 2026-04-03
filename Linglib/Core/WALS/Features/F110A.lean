import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 110A: Periphrastic Causative Constructions
@cite{song-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 110A`.

Chapter 110, 118 languages.
-/

namespace Core.WALS.F110A

/-- WALS 110A values. -/
inductive PeriphrasticCausativeType where
  | sequentialOnly  -- Sequential but no purposive (35 languages)
  | purposiveOnly  -- Purposive but no sequential (68 languages)
  | both  -- Both (15 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 110A dataset (118 languages). -/
def allData : List (Datapoint PeriphrasticCausativeType) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .purposiveOnly }
  , { walsCode := "aji", language := "Ajië", iso := "aji", value := .purposiveOnly }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .sequentialOnly }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .purposiveOnly }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .purposiveOnly }
  , { walsCode := "atc", language := "Atchin", iso := "upv", value := .sequentialOnly }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .purposiveOnly }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .sequentialOnly }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .sequentialOnly }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .purposiveOnly }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .purposiveOnly }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .purposiveOnly }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .purposiveOnly }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .sequentialOnly }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .sequentialOnly }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .purposiveOnly }
  , { walsCode := "eng", language := "English", iso := "eng", value := .sequentialOnly }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .sequentialOnly }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .sequentialOnly }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .purposiveOnly }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .purposiveOnly }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .purposiveOnly }
  , { walsCode := "ger", language := "German", iso := "deu", value := .sequentialOnly }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .purposiveOnly }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .purposiveOnly }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .sequentialOnly }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .purposiveOnly }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .purposiveOnly }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .sequentialOnly }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .both }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .sequentialOnly }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .purposiveOnly }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .sequentialOnly }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .purposiveOnly }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .both }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .purposiveOnly }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .sequentialOnly }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .purposiveOnly }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .both }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .sequentialOnly }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .sequentialOnly }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .both }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .purposiveOnly }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .sequentialOnly }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .purposiveOnly }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .purposiveOnly }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .sequentialOnly }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .both }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .purposiveOnly }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .both }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .purposiveOnly }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .both }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .purposiveOnly }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .sequentialOnly }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .purposiveOnly }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .sequentialOnly }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .purposiveOnly }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .purposiveOnly }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .purposiveOnly }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .purposiveOnly }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .sequentialOnly }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .purposiveOnly }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .purposiveOnly }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .purposiveOnly }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .sequentialOnly }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .sequentialOnly }
  , { walsCode := "mul", language := "Mulao", iso := "mlm", value := .sequentialOnly }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .purposiveOnly }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .purposiveOnly }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .sequentialOnly }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .sequentialOnly }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .purposiveOnly }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .purposiveOnly }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .purposiveOnly }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .purposiveOnly }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .purposiveOnly }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .sequentialOnly }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .sequentialOnly }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .purposiveOnly }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .purposiveOnly }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .purposiveOnly }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .purposiveOnly }
  , { walsCode := "rej", language := "Rejang", iso := "rej", value := .sequentialOnly }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .purposiveOnly }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .purposiveOnly }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .purposiveOnly }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .purposiveOnly }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .purposiveOnly }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .purposiveOnly }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .both }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .both }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .purposiveOnly }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .sequentialOnly }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .purposiveOnly }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .purposiveOnly }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .both }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .purposiveOnly }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .both }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .sequentialOnly }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .purposiveOnly }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .both }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .purposiveOnly }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .purposiveOnly }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .purposiveOnly }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .both }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .purposiveOnly }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .purposiveOnly }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .purposiveOnly }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .purposiveOnly }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .sequentialOnly }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .sequentialOnly }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .purposiveOnly }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .sequentialOnly }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .purposiveOnly }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .both }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .both }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .purposiveOnly }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .purposiveOnly }
  ]

-- Count verification
theorem total_count : allData.length = 118 := by native_decide

theorem count_sequentialOnly :
    (allData.filter (·.value == .sequentialOnly)).length = 35 := by native_decide
theorem count_purposiveOnly :
    (allData.filter (·.value == .purposiveOnly)).length = 68 := by native_decide
theorem count_both :
    (allData.filter (·.value == .both)).length = 15 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F110A
