/-!
# WALS Feature 144W: Verb-Initial with Negative that is Immediately Postverbal or between Subject and Object
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144W`.

Chapter 144, 151 languages.
-/

namespace Core.WALS.F144W

/-- WALS 144W values. -/
inductive VerbInitialWithNegativeThatIsImmediatelyPostverbalOrBetweenSubjectAndObject where
  | suffixNodoubleneg  -- Suffix&NoDoubleNeg (2 languages)
  | wordOnlywithanotherneg  -- Word&OnlyWithAnotherNeg (5 languages)
  | suffixOptdoubleneg  -- Suffix&OptDoubleNeg (1 languages)
  | suffixOnlywithanotherneg  -- Suffix&OnlyWithAnotherNeg (3 languages)
  | wordbetweensando  -- WordBetweenSAndO (1 languages)
  | none  -- None (139 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144W datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : VerbInitialWithNegativeThatIsImmediatelyPostverbalOrBetweenSubjectAndObject
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144W dataset (151 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .none }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .none }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .none }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .none }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .none }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .none }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .suffixOnlywithanotherneg }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .none }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .none }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .none }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .none }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .none }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .none }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .none }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .none }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .none }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .none }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .none }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .wordOnlywithanotherneg }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .none }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .none }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .none }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .none }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .none }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .none }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .none }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .none }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .none }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .none }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .suffixOnlywithanotherneg }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .none }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .none }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .none }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .none }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .suffixOptdoubleneg }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .none }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .none }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .none }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .none }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .none }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .none }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .none }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .none }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .none }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .none }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .none }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .wordOnlywithanotherneg }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .none }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .none }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .none }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .none }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .none }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .none }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .none }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .none }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .wordOnlywithanotherneg }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .none }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .none }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .none }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .none }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .suffixNodoubleneg }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .none }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .none }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .none }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .none }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .none }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .none }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .none }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .none }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .wordOnlywithanotherneg }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .none }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .none }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .none }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .none }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .none }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .none }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .none }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .none }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .suffixNodoubleneg }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .none }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .none }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .none }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .none }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .none }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .wordOnlywithanotherneg }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .none }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .none }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .none }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .none }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .none }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .none }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .none }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .none }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .none }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .none }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .none }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .none }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .none }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .none }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .none }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .none }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .none }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .none }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .none }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .suffixOnlywithanotherneg }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .none }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .none }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .none }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .none }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .none }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .none }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .none }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .none }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .none }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .none }
  , { walsCode := "so", language := "So", iso := "teu", value := .none }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .none }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .none }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .none }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .none }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .none }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .none }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .none }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .none }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .none }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .none }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .none }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .none }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .none }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .none }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .none }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .none }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .none }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .none }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .none }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .none }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .none }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .none }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .none }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .none }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .wordbetweensando }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .none }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .none }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .none }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .none }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .none }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .none }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .none }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .none }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .none }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .none }
  ]

-- Count verification
theorem total_count : allData.length = 151 := by native_decide

theorem count_suffixNodoubleneg :
    (allData.filter (·.value == .suffixNodoubleneg)).length = 2 := by native_decide
theorem count_wordOnlywithanotherneg :
    (allData.filter (·.value == .wordOnlywithanotherneg)).length = 5 := by native_decide
theorem count_suffixOptdoubleneg :
    (allData.filter (·.value == .suffixOptdoubleneg)).length = 1 := by native_decide
theorem count_suffixOnlywithanotherneg :
    (allData.filter (·.value == .suffixOnlywithanotherneg)).length = 3 := by native_decide
theorem count_wordbetweensando :
    (allData.filter (·.value == .wordbetweensando)).length = 1 := by native_decide
theorem count_none :
    (allData.filter (·.value == .none)).length = 139 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144W
