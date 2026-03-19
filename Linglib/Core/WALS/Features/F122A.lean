import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 122A: Relativization on Subjects
@cite{comrie-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 122A`.

Chapter 122, 166 languages.
-/

namespace Core.WALS.F122A

/-- WALS 122A values. -/
inductive SubjectRelativization where
  | relativePronoun  -- Relative pronoun (12 languages)
  | nonReduction  -- Non-reduction (24 languages)
  | pronounRetention  -- Pronoun-retention (5 languages)
  | gap  -- Gap (125 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 122A dataset (166 languages). -/
def allData : List (Datapoint SubjectRelativization) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .gap }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .gap }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .relativePronoun }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .gap }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .nonReduction }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .gap }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .gap }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .gap }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .pronounRetention }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .gap }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .pronounRetention }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .nonReduction }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .gap }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .gap }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .gap }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .gap }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .gap }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .gap }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .gap }
  , { walsCode := "blq", language := "Bole", iso := "bol", value := .gap }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .gap }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .relativePronoun }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .gap }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .gap }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .nonReduction }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .nonReduction }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .gap }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .gap }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .gap }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .gap }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .gap }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .gap }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .gap }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .nonReduction }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .gap }
  , { walsCode := "eng", language := "English", iso := "eng", value := .relativePronoun }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .nonReduction }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .gap }
  , { walsCode := "ewa", language := "Ewe (Anlo)", iso := "ewe", value := .gap }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .gap }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .relativePronoun }
  , { walsCode := "fre", language := "French", iso := "fra", value := .relativePronoun }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .gap }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .gap }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .gap }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .relativePronoun }
  , { walsCode := "ger", language := "German", iso := "deu", value := .relativePronoun }
  , { walsCode := "gdr", language := "Gidar", iso := "gid", value := .gap }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .gap }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .nonReduction }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .relativePronoun }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .gap }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .gap }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .gap }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .gap }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .nonReduction }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .gap }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .gap }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .relativePronoun }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .gap }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .gap }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .nonReduction }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .gap }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .gap }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .gap }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .gap }
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
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .gap }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .nonReduction }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .gap }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .nonReduction }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .gap }
  , { walsCode := "kjr", language := "Koorete", iso := "kqy", value := .gap }
  , { walsCode := "kko", language := "Koranko", iso := "knk", value := .nonReduction }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .gap }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .gap }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .gap }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .gap }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .gap }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .gap }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .gap }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .gap }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .nonReduction }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .gap }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .relativePronoun }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .nonReduction }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .gap }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .gap }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .gap }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .gap }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .gap }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .gap }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .gap }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .gap }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .gap }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .gap }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .gap }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .nonReduction }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .nonReduction }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .gap }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .gap }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .gap }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .gap }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .gap }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .gap }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .gap }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .gap }
  , { walsCode := "nbb", language := "Nambas (Big)", iso := "nmb", value := .gap }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .gap }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .gap }
  , { walsCode := "nge", language := "Ngemba", iso := "nge", value := .pronounRetention }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .gap }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .gap }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .gap }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .gap }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .gap }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .gap }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .gap }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .gap }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .gap }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .nonReduction }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .gap }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .gap }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .nonReduction }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .gap }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .relativePronoun }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .gap }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .nonReduction }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .gap }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .nonReduction }
  , { walsCode := "so", language := "So", iso := "teu", value := .gap }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .gap }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .gap }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .nonReduction }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .gap }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .gap }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .gap }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .gap }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .gap }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .gap }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .gap }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .nonReduction }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .gap }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .gap }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .nonReduction }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .gap }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .gap }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .gap }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .gap }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .gap }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .gap }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .nonReduction }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .gap }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .pronounRetention }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .gap }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .gap }
  ]

-- Count verification
theorem total_count : allData.length = 166 := by native_decide

theorem count_relativePronoun :
    (allData.filter (·.value == .relativePronoun)).length = 12 := by native_decide
theorem count_nonReduction :
    (allData.filter (·.value == .nonReduction)).length = 24 := by native_decide
theorem count_pronounRetention :
    (allData.filter (·.value == .pronounRetention)).length = 5 := by native_decide
theorem count_gap :
    (allData.filter (·.value == .gap)).length = 125 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F122A
