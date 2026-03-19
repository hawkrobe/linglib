/-!
# WALS Feature 144X: Verb-Initial with Clause-Final Negative
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144X`.

Chapter 144, 151 languages.
-/

namespace Core.WALS.F144X

/-- WALS 144X values. -/
inductive VerbInitialWithClauseFinalNegative where
  | nodoubleneg  -- NoDoubleNeg (2 languages)
  | optdoubleneg  -- OptDoubleNeg (1 languages)
  | onlywithanotherneg  -- OnlyWithAnotherNeg (4 languages)
  | noClauseFinalNeg  -- No clause-final neg (144 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144X datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : VerbInitialWithClauseFinalNegative
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144X dataset (151 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .noClauseFinalNeg }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .noClauseFinalNeg }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .noClauseFinalNeg }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .noClauseFinalNeg }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .noClauseFinalNeg }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .noClauseFinalNeg }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .noClauseFinalNeg }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noClauseFinalNeg }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .noClauseFinalNeg }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .noClauseFinalNeg }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .onlywithanotherneg }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noClauseFinalNeg }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .noClauseFinalNeg }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .noClauseFinalNeg }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .noClauseFinalNeg }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .noClauseFinalNeg }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .noClauseFinalNeg }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .noClauseFinalNeg }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .noClauseFinalNeg }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noClauseFinalNeg }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noClauseFinalNeg }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .noClauseFinalNeg }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .noClauseFinalNeg }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .noClauseFinalNeg }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noClauseFinalNeg }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .noClauseFinalNeg }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .noClauseFinalNeg }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .noClauseFinalNeg }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .noClauseFinalNeg }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .noClauseFinalNeg }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .noClauseFinalNeg }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .noClauseFinalNeg }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .noClauseFinalNeg }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .noClauseFinalNeg }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .noClauseFinalNeg }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noClauseFinalNeg }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noClauseFinalNeg }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .noClauseFinalNeg }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .noClauseFinalNeg }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .noClauseFinalNeg }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .noClauseFinalNeg }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noClauseFinalNeg }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .noClauseFinalNeg }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noClauseFinalNeg }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .noClauseFinalNeg }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noClauseFinalNeg }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .onlywithanotherneg }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .noClauseFinalNeg }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .noClauseFinalNeg }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .noClauseFinalNeg }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .noClauseFinalNeg }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .noClauseFinalNeg }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .noClauseFinalNeg }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noClauseFinalNeg }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noClauseFinalNeg }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .noClauseFinalNeg }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .noClauseFinalNeg }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .noClauseFinalNeg }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .noClauseFinalNeg }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noClauseFinalNeg }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .noClauseFinalNeg }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noClauseFinalNeg }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .noClauseFinalNeg }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .noClauseFinalNeg }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .onlywithanotherneg }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .noClauseFinalNeg }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noClauseFinalNeg }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .noClauseFinalNeg }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .noClauseFinalNeg }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .optdoubleneg }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .noClauseFinalNeg }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .noClauseFinalNeg }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .noClauseFinalNeg }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noClauseFinalNeg }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noClauseFinalNeg }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .noClauseFinalNeg }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .noClauseFinalNeg }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .noClauseFinalNeg }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .noClauseFinalNeg }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .nodoubleneg }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noClauseFinalNeg }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .noClauseFinalNeg }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .noClauseFinalNeg }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .noClauseFinalNeg }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .onlywithanotherneg }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .noClauseFinalNeg }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noClauseFinalNeg }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .noClauseFinalNeg }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .noClauseFinalNeg }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .noClauseFinalNeg }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .noClauseFinalNeg }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .noClauseFinalNeg }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noClauseFinalNeg }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .noClauseFinalNeg }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .noClauseFinalNeg }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .noClauseFinalNeg }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noClauseFinalNeg }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noClauseFinalNeg }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noClauseFinalNeg }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noClauseFinalNeg }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noClauseFinalNeg }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .noClauseFinalNeg }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noClauseFinalNeg }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .nodoubleneg }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .noClauseFinalNeg }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noClauseFinalNeg }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noClauseFinalNeg }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .noClauseFinalNeg }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .noClauseFinalNeg }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .noClauseFinalNeg }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noClauseFinalNeg }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .noClauseFinalNeg }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noClauseFinalNeg }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .noClauseFinalNeg }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .noClauseFinalNeg }
  , { walsCode := "so", language := "So", iso := "teu", value := .noClauseFinalNeg }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noClauseFinalNeg }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noClauseFinalNeg }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .noClauseFinalNeg }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .noClauseFinalNeg }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .noClauseFinalNeg }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .noClauseFinalNeg }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .noClauseFinalNeg }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .noClauseFinalNeg }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .noClauseFinalNeg }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .noClauseFinalNeg }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noClauseFinalNeg }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .noClauseFinalNeg }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .noClauseFinalNeg }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .noClauseFinalNeg }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .noClauseFinalNeg }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .noClauseFinalNeg }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noClauseFinalNeg }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noClauseFinalNeg }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .noClauseFinalNeg }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .noClauseFinalNeg }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noClauseFinalNeg }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noClauseFinalNeg }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .noClauseFinalNeg }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .noClauseFinalNeg }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .noClauseFinalNeg }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .noClauseFinalNeg }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .noClauseFinalNeg }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noClauseFinalNeg }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .noClauseFinalNeg }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .noClauseFinalNeg }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .noClauseFinalNeg }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .noClauseFinalNeg }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .noClauseFinalNeg }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noClauseFinalNeg }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .noClauseFinalNeg }
  ]

-- Count verification
theorem total_count : allData.length = 151 := by native_decide

theorem count_nodoubleneg :
    (allData.filter (·.value == .nodoubleneg)).length = 2 := by native_decide
theorem count_optdoubleneg :
    (allData.filter (·.value == .optdoubleneg)).length = 1 := by native_decide
theorem count_onlywithanotherneg :
    (allData.filter (·.value == .onlywithanotherneg)).length = 4 := by native_decide
theorem count_noClauseFinalNeg :
    (allData.filter (·.value == .noClauseFinalNeg)).length = 144 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144X
