/-!
# WALS Feature 123A: Relativization on Obliques
@cite{comrie-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 123A`.

Chapter 123, 112 languages.
-/

namespace Core.WALS.F123A

/-- WALS 123A values. -/
inductive ObliqueRelativization where
  | relativePronoun  -- Relative pronoun (13 languages)
  | nonReduction  -- Non-reduction (14 languages)
  | pronounRetention  -- Pronoun-retention (20 languages)
  | gap  -- Gap (55 languages)
  | notPossible  -- Not possible (10 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 123A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ObliqueRelativization
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 123A dataset (112 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .gap }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .gap }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .relativePronoun }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .gap }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .nonReduction }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .pronounRetention }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .pronounRetention }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .pronounRetention }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .pronounRetention }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .pronounRetention }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .nonReduction }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .gap }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .notPossible }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .notPossible }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .gap }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .gap }
  , { walsCode := "blq", language := "Bole", iso := "bol", value := .pronounRetention }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .relativePronoun }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .gap }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .nonReduction }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .gap }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .gap }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .nonReduction }
  , { walsCode := "eng", language := "English", iso := "eng", value := .relativePronoun }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .nonReduction }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .gap }
  , { walsCode := "ewa", language := "Ewe (Anlo)", iso := "ewe", value := .pronounRetention }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .relativePronoun }
  , { walsCode := "fre", language := "French", iso := "fra", value := .relativePronoun }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .gap }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .pronounRetention }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .relativePronoun }
  , { walsCode := "ger", language := "German", iso := "deu", value := .relativePronoun }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .nonReduction }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .relativePronoun }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .gap }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .pronounRetention }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .pronounRetention }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .pronounRetention }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .nonReduction }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .nonReduction }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .relativePronoun }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .gap }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .nonReduction }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .gap }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .gap }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .gap }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .pronounRetention }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .relativePronoun }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .gap }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .gap }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .gap }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .gap }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .gap }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .pronounRetention }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .gap }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .gap }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .gap }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .gap }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .gap }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .gap }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .gap }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .gap }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .gap }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .pronounRetention }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .gap }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .gap }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .nonReduction }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .pronounRetention }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .relativePronoun }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .nonReduction }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .gap }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .pronounRetention }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .pronounRetention }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .gap }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .gap }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .notPossible }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .gap }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .gap }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .gap }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .notPossible }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .gap }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .gap }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .gap }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .pronounRetention }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .gap }
  , { walsCode := "nbb", language := "Nambas (Big)", iso := "nmb", value := .gap }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .gap }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .gap }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .gap }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .gap }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .pronounRetention }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .gap }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .pronounRetention }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .notPossible }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .gap }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .gap }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .relativePronoun }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .notPossible }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .nonReduction }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .relativePronoun }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .nonReduction }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .notPossible }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .notPossible }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .gap }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .gap }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .gap }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .gap }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .nonReduction }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .notPossible }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .gap }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .notPossible }
  ]

-- Count verification
theorem total_count : allData.length = 112 := by native_decide

theorem count_relativePronoun :
    (allData.filter (·.value == .relativePronoun)).length = 13 := by native_decide
theorem count_nonReduction :
    (allData.filter (·.value == .nonReduction)).length = 14 := by native_decide
theorem count_pronounRetention :
    (allData.filter (·.value == .pronounRetention)).length = 20 := by native_decide
theorem count_gap :
    (allData.filter (·.value == .gap)).length = 55 := by native_decide
theorem count_notPossible :
    (allData.filter (·.value == .notPossible)).length = 10 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F123A
