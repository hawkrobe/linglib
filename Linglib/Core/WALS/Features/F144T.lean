import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144T: The Position of Negative Morphemes in Verb-Initial Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144T`.

Chapter 144, 152 languages.
-/

namespace Core.WALS.F144T

/-- WALS 144T values. -/
inductive PositionOfNegativeMorphemesInVerbInitialLanguages where
  | negvso  -- NegVSO (57 languages)
  | vsnego  -- VSNegO (1 languages)
  | vsoneg  -- VSONeg (1 languages)
  | negvos  -- NegVOS (18 languages)
  | negvsoNegvos  -- NegVSO/NegVOS (11 languages)
  | negvVsVo  -- NegV & VS & VO (16 languages)
  | svoButNegvso  -- SVO but NegVSO (1 languages)
  | negVSo  -- [Neg-V]SO (7 languages)
  | negVOs  -- [Neg-V]OS (2 languages)
  | vNegOs  -- [V-Neg]OS (1 languages)
  | vNegVsVo  -- [V-Neg] & VS &VO (1 languages)
  | negvsoNegVSo  -- NegVSO/[Neg-V]SO (2 languages)
  | negvosNegVOs  -- NegVOS/[Neg-V]OS (1 languages)
  | negvsoSnegvo  -- NegVSO/SNegVO (5 languages)
  | vsonegSvoneg  -- VSONeg/SVONeg (1 languages)
  | negvosNegsvo  -- NegVOS/NegSVO (1 languages)
  | negvosSnegvo  -- NegVOS/SNegVO (2 languages)
  | negVOsSNegVO  -- [Neg-V]OS/S[Neg-V]O (2 languages)
  | negvVsoSvo  -- NegV & VSO/SVO (2 languages)
  | negvVosSvo  -- NegV & VOS/SVO (2 languages)
  | optsingleneg  -- OptSingleNeg (1 languages)
  | obligdoubleneg  -- ObligDoubleNeg (7 languages)
  | optdoubleneg  -- OptDoubleNeg (10 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144T dataset (152 languages). -/
def allData : List (Datapoint PositionOfNegativeMorphemesInVerbInitialLanguages) :=
  [ { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .negvso }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .negvso }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .negvVsVo }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .negvos }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .optdoubleneg }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .negvso }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .obligdoubleneg }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .negvsoSnegvo }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .negvVsVo }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .negvVsoSvo }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .optdoubleneg }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .negvsoSnegvo }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .negvos }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .negvos }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .negvso }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .negvsoSnegvo }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .negvso }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .negvVsoSvo }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .obligdoubleneg }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .negVOs }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .negvso }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .negvso }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .negvso }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .negVSo }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .negvos }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .negVSo }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .negvso }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .negvos }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .negvVsVo }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .optdoubleneg }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .negVOs }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .svoButNegvso }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .negvos }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .negvso }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .optdoubleneg }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .negvosNegsvo }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .negvsoNegvos }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .negvso }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .negvso }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .negvos }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .negvso }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .negvsoSnegvo }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .negVSo }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .negVOsSNegVO }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .negvso }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .negvso }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .obligdoubleneg }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .negvso }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .negvso }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .negvso }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .negvVsVo }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .negvVsVo }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .negvso }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .negvso }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .negvso }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .obligdoubleneg }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .negvso }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .negvso }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .negvsoNegVSo }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .negvVosSvo }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .vNegOs }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .negvos }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .negvso }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .negvso }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .obligdoubleneg }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .negvso }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .negvsoNegvos }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .negvso }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .negvVosSvo }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .optdoubleneg }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .negvos }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .negvsoNegVSo }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .negvVsVo }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .negvso }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .negvos }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .negvso }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .negvso }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .negvso }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .vNegVsVo }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .vsonegSvoneg }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .negvso }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .negvso }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .negvso }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .negvso }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .obligdoubleneg }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .negvsoNegvos }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .negvso }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .negvso }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .negvVsVo }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .negvso }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .negVSo }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .negvos }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .negvos }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .negvso }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .negvso }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .negvso }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .negvVsVo }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .negvsoNegvos }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .optdoubleneg }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .negvos }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .negvsoNegvos }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .negvso }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .negvVsVo }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .vsoneg }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .optdoubleneg }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .negvso }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .optdoubleneg }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .optdoubleneg }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .negvso }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .negvsoNegvos }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .negvVsVo }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .negvsoNegvos }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .negvos }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .negvsoNegvos }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .negvsoNegvos }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .negvso }
  , { walsCode := "so", language := "So", iso := "teu", value := .negvso }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .negvso }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .negvso }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .negvso }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .optdoubleneg }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .negvVsVo }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .negvso }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .negvsoSnegvo }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .negvso }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .negvsoNegvos }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .negvso }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .negvosSnegvo }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .negVSo }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .negVOsSNegVO }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .negvVsVo }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .negvsoNegvos }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .negvso }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .obligdoubleneg }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .negvos }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .negVSo }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .negvos }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .negvosSnegvo }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .negvos }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .negvVsVo }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .negvso }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .vsnego }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .negvos }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .optsingleneg }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .negvVsVo }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .negvso }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .negvVsVo }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .negvso }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .negVSo }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .negvso }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .negvosNegVOs }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .negvVsVo }
  ]

-- Count verification
theorem total_count : allData.length = 152 := by native_decide

theorem count_negvso :
    (allData.filter (·.value == .negvso)).length = 57 := by native_decide
theorem count_vsnego :
    (allData.filter (·.value == .vsnego)).length = 1 := by native_decide
theorem count_vsoneg :
    (allData.filter (·.value == .vsoneg)).length = 1 := by native_decide
theorem count_negvos :
    (allData.filter (·.value == .negvos)).length = 18 := by native_decide
theorem count_negvsoNegvos :
    (allData.filter (·.value == .negvsoNegvos)).length = 11 := by native_decide
theorem count_negvVsVo :
    (allData.filter (·.value == .negvVsVo)).length = 16 := by native_decide
theorem count_svoButNegvso :
    (allData.filter (·.value == .svoButNegvso)).length = 1 := by native_decide
theorem count_negVSo :
    (allData.filter (·.value == .negVSo)).length = 7 := by native_decide
theorem count_negVOs :
    (allData.filter (·.value == .negVOs)).length = 2 := by native_decide
theorem count_vNegOs :
    (allData.filter (·.value == .vNegOs)).length = 1 := by native_decide
theorem count_vNegVsVo :
    (allData.filter (·.value == .vNegVsVo)).length = 1 := by native_decide
theorem count_negvsoNegVSo :
    (allData.filter (·.value == .negvsoNegVSo)).length = 2 := by native_decide
theorem count_negvosNegVOs :
    (allData.filter (·.value == .negvosNegVOs)).length = 1 := by native_decide
theorem count_negvsoSnegvo :
    (allData.filter (·.value == .negvsoSnegvo)).length = 5 := by native_decide
theorem count_vsonegSvoneg :
    (allData.filter (·.value == .vsonegSvoneg)).length = 1 := by native_decide
theorem count_negvosNegsvo :
    (allData.filter (·.value == .negvosNegsvo)).length = 1 := by native_decide
theorem count_negvosSnegvo :
    (allData.filter (·.value == .negvosSnegvo)).length = 2 := by native_decide
theorem count_negVOsSNegVO :
    (allData.filter (·.value == .negVOsSNegVO)).length = 2 := by native_decide
theorem count_negvVsoSvo :
    (allData.filter (·.value == .negvVsoSvo)).length = 2 := by native_decide
theorem count_negvVosSvo :
    (allData.filter (·.value == .negvVosSvo)).length = 2 := by native_decide
theorem count_optsingleneg :
    (allData.filter (·.value == .optsingleneg)).length = 1 := by native_decide
theorem count_obligdoubleneg :
    (allData.filter (·.value == .obligdoubleneg)).length = 7 := by native_decide
theorem count_optdoubleneg :
    (allData.filter (·.value == .optdoubleneg)).length = 10 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144T
