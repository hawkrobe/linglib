import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144V: Verb-Initial with Preverbal Negative
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144V`.

Chapter 144, 152 languages.
-/

namespace Core.WALS.F144V

/-- WALS 144V values. -/
inductive VerbInitialWithPreverbalNegative where
  | separateWordNoDoubleNegationWordNodoubleneg  -- Separate word, no double negation  Word&NoDoubleNeg (117 languages)
  | prefixNoDoubleNegationPrefixNodoubleneg  -- Prefix, no double negation  Prefix&NoDoubleNeg (11 languages)
  | wordOpt  -- Word&Opt (6 languages)
  | prefixOptdoubleneg  -- Prefix&OptDoubleNeg (1 languages)
  | wordOnlywithanotherneg  -- Word&OnlyWithAnotherNeg (4 languages)
  | prefixOnlywithanotherneg  -- Prefix&OnlyWithAnotherNeg (1 languages)
  | type1Type2  -- Type 1 / Type 2 (4 languages)
  | type3Type6  -- Type 3 / Type 6 (1 languages)
  | noPreverbalNeg  -- No preverbal neg (7 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144V dataset (152 languages). -/
def allData : List (Datapoint VerbInitialWithPreverbalNegative) :=
  [ { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .wordOpt }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .prefixOnlywithanotherneg }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .prefixOptdoubleneg }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .wordOnlywithanotherneg }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .wordOpt }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .type1Type2 }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .noPreverbalNeg }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .wordOnlywithanotherneg }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .type1Type2 }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .noPreverbalNeg }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .wordOnlywithanotherneg }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .noPreverbalNeg }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .type1Type2 }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .noPreverbalNeg }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noPreverbalNeg }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .wordOnlywithanotherneg }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .noPreverbalNeg }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .type3Type6 }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .wordOpt }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .wordOpt }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "so", language := "So", iso := "teu", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .wordOpt }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .noPreverbalNeg }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .wordOpt }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .type1Type2 }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  ]

-- Count verification
theorem total_count : allData.length = 152 := by native_decide

theorem count_separateWordNoDoubleNegationWordNodoubleneg :
    (allData.filter (·.value == .separateWordNoDoubleNegationWordNodoubleneg)).length = 117 := by native_decide
theorem count_prefixNoDoubleNegationPrefixNodoubleneg :
    (allData.filter (·.value == .prefixNoDoubleNegationPrefixNodoubleneg)).length = 11 := by native_decide
theorem count_wordOpt :
    (allData.filter (·.value == .wordOpt)).length = 6 := by native_decide
theorem count_prefixOptdoubleneg :
    (allData.filter (·.value == .prefixOptdoubleneg)).length = 1 := by native_decide
theorem count_wordOnlywithanotherneg :
    (allData.filter (·.value == .wordOnlywithanotherneg)).length = 4 := by native_decide
theorem count_prefixOnlywithanotherneg :
    (allData.filter (·.value == .prefixOnlywithanotherneg)).length = 1 := by native_decide
theorem count_type1Type2 :
    (allData.filter (·.value == .type1Type2)).length = 4 := by native_decide
theorem count_type3Type6 :
    (allData.filter (·.value == .type3Type6)).length = 1 := by native_decide
theorem count_noPreverbalNeg :
    (allData.filter (·.value == .noPreverbalNeg)).length = 7 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144V
