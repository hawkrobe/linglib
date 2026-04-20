import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144L: The Position of Negative Morphemes in SOV Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144L`.

Chapter 144, 573 languages.
-/

namespace Core.WALS.F144L

/-- WALS 144L values. -/
inductive PositionOfNegativeMorphemesInSovLanguages where
  /-- NegSOV (10 languages). -/
  | negsov
  /-- SNegOV (11 languages). -/
  | snegov
  /-- SONegV (64 languages). -/
  | sonegv
  /-- SOVNeg (48 languages). -/
  | sovneg
  /-- SO[Neg-V] (49 languages). -/
  | soNegV
  /-- SO[V-Neg] (128 languages). -/
  | soVNeg
  /-- SVO but SNegOV (3 languages). -/
  | svoButSnegov
  /-- SVO but SONegV (1 languages). -/
  | svoButSonegv
  /-- SVO but SOVNeg (1 languages). -/
  | svoButSovneg
  /-- SVO but SO[V-Neg] (1 languages). -/
  | svoButSoVNeg
  /-- SVO but SO[Neg-V] (1 languages). -/
  | svoButSoNegV
  /-- SVO/SOV but SNegOV (1 languages). -/
  | svoSovButSnegov
  /-- SVO/SOV but SOVNeg (1 languages). -/
  | svoSovButSovneg
  /-- Other NegV (57 languages). -/
  | otherNegv
  /-- More than one construction (54 languages). -/
  | moreThanOneConstruction
  /-- ObligDoubleNeg (45 languages). -/
  | obligdoubleneg
  /-- OptDoubleNeg (31 languages). -/
  | optdoubleneg
  /-- SV&OV&NegV (13 languages). -/
  | svOvNegv
  /-- SV&OV&VNeg (8 languages). -/
  | svOvVneg
  /-- SV&OV&[Neg-V] (14 languages). -/
  | svOvNegV
  /-- SV&OV&[V-Neg] (23 languages). -/
  | svOvVNeg
  /-- SV&OV&ImmedPreverbal (5 languages). -/
  | svOvImmedpreverbal
  /-- SV&OV&InitialNeg (4 languages). -/
  | svOvInitialneg
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint PositionOfNegativeMorphemesInSovLanguages) :=
  [ { walsCode := "aar", iso := "aiw", value := .svOvVNeg }
  , { walsCode := "aba", iso := "aau", value := .sovneg }
  , { walsCode := "abk", iso := "abk", value := .moreThanOneConstruction }
  , { walsCode := "abv", iso := "abz", value := .sovneg }
  , { walsCode := "adg", iso := "adn", value := .optdoubleneg }
  , { walsCode := "ain", iso := "ain", value := .sonegv }
  , { walsCode := "ajg", iso := "ajg", value := .moreThanOneConstruction }
  , { walsCode := "akh", iso := "ahk", value := .sonegv }
  , { walsCode := "all", iso := "nrz", value := .otherNegv }
  , { walsCode := "ala", iso := "amp", value := .sonegv }
  , { walsCode := "aly", iso := "aly", value := .soVNeg }
  , { walsCode := "amn", iso := "amn", value := .obligdoubleneg }
  , { walsCode := "amb", iso := "abt", value := .moreThanOneConstruction }
  , { walsCode := "amt", iso := "adx", value := .svOvNegV }
  , { walsCode := "ame", iso := "aey", value := .optdoubleneg }
  , { walsCode := "amh", iso := "amh", value := .obligdoubleneg }
  , { walsCode := "amx", iso := "imi", value := .obligdoubleneg }
  , { walsCode := "agm", iso := "njm", value := .sovneg }
  , { walsCode := "ang", iso := "agg", value := .soVNeg }
  , { walsCode := "ao", iso := "njo", value := .optdoubleneg }
  , { walsCode := "apw", iso := "apw", value := .obligdoubleneg }
  , { walsCode := "apl", iso := "apy", value := .moreThanOneConstruction }
  , { walsCode := "apt", iso := "apt", value := .soVNeg }
  , { walsCode := "abn", iso := "ard", value := .otherNegv }
  , { walsCode := "ana", iso := "aro", value := .obligdoubleneg }
  , { walsCode := "arc", iso := "aqc", value := .soVNeg }
  , { walsCode := "arm", iso := "hye", value := .moreThanOneConstruction }
  , { walsCode := "arw", iso := "hyw", value := .moreThanOneConstruction }
  , { walsCode := "amp", iso := "aer", value := .soVNeg }
  , { walsCode := "asm", iso := "cns", value := .sovneg }
  , { walsCode := "ass", iso := "asm", value := .soNegV }
  , { walsCode := "ath", iso := "aph", value := .soVNeg }
  , { walsCode := "ava", iso := "ava", value := .sovneg }
  , { walsCode := "awa", iso := "awb", value := .sonegv }
  , { walsCode := "awp", iso := "kwi", value := .obligdoubleneg }
  , { walsCode := "awt", iso := "kmn", value := .soNegV }
  , { walsCode := "aym", iso := "ayr", value := .moreThanOneConstruction }
  , { walsCode := "azi", iso := "azb", value := .soVNeg }
  , { walsCode := "aze", iso := "", value := .soVNeg }
  , { walsCode := "bdm", iso := "bia", value := .otherNegv }
  , { walsCode := "baf", iso := "bfd", value := .obligdoubleneg }
  , { walsCode := "blt", iso := "bft", value := .moreThanOneConstruction }
  , { walsCode := "bam", iso := "bam", value := .snegov }
  , { walsCode := "bao", iso := "peh", value := .otherNegv }
  , { walsCode := "brl", iso := "loy", value := .soNegV }
  , { walsCode := "baa", iso := "bbb", value := .sonegv }
  , { walsCode := "brp", iso := "bpe", value := .snegov }
  , { walsCode := "bsk", iso := "bak", value := .svOvVNeg }
  , { walsCode := "bsq", iso := "eus", value := .sonegv }
  , { walsCode := "bzi", iso := "bvz", value := .sovneg }
  , { walsCode := "baw", iso := "bgr", value := .sovneg }
  , { walsCode := "bej", iso := "bej", value := .soNegV }
  , { walsCode := "bel", iso := "byw", value := .optdoubleneg }
  , { walsCode := "ben", iso := "ben", value := .sovneg }
  , { walsCode := "zag", iso := "zag", value := .soVNeg }
  , { walsCode := "bti", iso := "", value := .soVNeg }
  , { walsCode := "bho", iso := "bho", value := .sonegv }
  , { walsCode := "blx", iso := "bll", value := .optdoubleneg }
  , { walsCode := "bbw", iso := "gup", value := .svOvNegv }
  , { walsCode := "biu", iso := "", value := .soNegV }
  , { walsCode := "boa", iso := "kvg", value := .soVNeg }
  , { walsCode := "bod", iso := "brx", value := .moreThanOneConstruction }
  , { walsCode := "bok", iso := "bqc", value := .optdoubleneg }
  , { walsCode := "bri", iso := "bzd", value := .otherNegv }
  , { walsCode := "bnu", iso := "", value := .svOvInitialneg }
  , { walsCode := "ghr", iso := "bfu", value := .otherNegv }
  , { walsCode := "bua", iso := "bvr", value := .otherNegv }
  , { walsCode := "but", iso := "bxm", value := .soVNeg }
  , { walsCode := "brm", iso := "mya", value := .obligdoubleneg }
  , { walsCode := "bur", iso := "bsk", value := .soNegV }
  , { walsCode := "bus", iso := "bqp", value := .sovneg }
  , { walsCode := "bya", iso := "bee", value := .svOvNegV }
  , { walsCode := "cah", iso := "chl", value := .sonegv }
  , { walsCode := "cml", iso := "rab", value := .obligdoubleneg }
  , { walsCode := "can", iso := "cbu", value := .soVNeg }
  , { walsCode := "cnl", iso := "ram", value := .sovneg }
  , { walsCode := "car", iso := "car", value := .soVNeg }
  , { walsCode := "cde", iso := "mch", value := .soVNeg }
  , { walsCode := "cas", iso := "cbr", value := .soVNeg }
  , { walsCode := "cay", iso := "cbi", value := .soVNeg }
  , { walsCode := "chh", iso := "sgw", value := .soNegV }
  , { walsCode := "cai", iso := "suq", value := .moreThanOneConstruction }
  , { walsCode := "chb", iso := "can", value := .obligdoubleneg }
  , { walsCode := "chg", iso := "nbc", value := .soNegV }
  , { walsCode := "chn", iso := "chx", value := .svOvNegV }
  , { walsCode := "chd", iso := "cdn", value := .otherNegv }
  , { walsCode := "chc", iso := "che", value := .sonegv }
  , { walsCode := "cpn", iso := "cdm", value := .soVNeg }
  , { walsCode := "chi", iso := "cid", value := .optdoubleneg }
  , { walsCode := "cmr", iso := "mrh", value := .svOvVneg }
  , { walsCode := "chs", iso := "csy", value := .svOvVneg }
  , { walsCode := "cti", iso := "ctd", value := .svOvVneg }
  , { walsCode := "cpy", iso := "cap", value := .negsov }
  , { walsCode := "chp", iso := "chp", value := .sovneg }
  , { walsCode := "ctm", iso := "ctm", value := .soVNeg }
  , { walsCode := "cct", iso := "cho", value := .soVNeg }
  , { walsCode := "cln", iso := "cht", value := .soVNeg }
  , { walsCode := "chk", iso := "ckt", value := .svOvNegv }
  , { walsCode := "chv", iso := "chv", value := .soVNeg }
  , { walsCode := "coa", iso := "xcw", value := .soVNeg }
  , { walsCode := "cmn", iso := "com", value := .moreThanOneConstruction }
  , { walsCode := "cui", iso := "cui", value := .obligdoubleneg }
  , { walsCode := "cup", iso := "cup", value := .moreThanOneConstruction }
  , { walsCode := "dag", iso := "dgz", value := .sonegv }
  , { walsCode := "dgr", iso := "dta", value := .otherNegv }
  , { walsCode := "dan", iso := "dnj", value := .otherNegv }
  , { walsCode := "dni", iso := "dni", value := .sovneg }
  , { walsCode := "drm", iso := "drd", value := .soNegV }
  , { walsCode := "des", iso := "des", value := .soVNeg }
  , { walsCode := "deu", iso := "der", value := .soVNeg }
  , { walsCode := "dha", iso := "dsh", value := .obligdoubleneg }
  , { walsCode := "dhm", iso := "dhi", value := .soNegV }
  , { walsCode := "die", iso := "dih", value := .sovneg }
  , { walsCode := "dig", iso := "mhu", value := .soVNeg }
  , { walsCode := "dms", iso := "dis", value := .svOvVNeg }
  , { walsCode := "dim", iso := "dim", value := .soVNeg }
  , { walsCode := "din", iso := "din", value := .svoSovButSnegov }
  , { walsCode := "dja", iso := "dyy", value := .otherNegv }
  , { walsCode := "djp", iso := "dwu", value := .negsov }
  , { walsCode := "dji", iso := "jig", value := .sonegv }
  , { walsCode := "dmk", iso := "dmk", value := .svOvImmedpreverbal }
  , { walsCode := "dds", iso := "dds", value := .soVNeg }
  , { walsCode := "dul", iso := "duu", value := .svOvNegV }
  , { walsCode := "dmi", iso := "dus", value := .moreThanOneConstruction }
  , { walsCode := "dum", iso := "vam", value := .sovneg }
  , { walsCode := "dun", iso := "duc", value := .optdoubleneg }
  , { walsCode := "dut", iso := "nld", value := .moreThanOneConstruction }
  , { walsCode := "dyi", iso := "dbl", value := .svOvImmedpreverbal }
  , { walsCode := "eip", iso := "eip", value := .moreThanOneConstruction }
  , { walsCode := "eka", iso := "ekg", value := .moreThanOneConstruction }
  , { walsCode := "emb", iso := "emp", value := .svOvVNeg }
  , { walsCode := "ene", iso := "", value := .otherNegv }
  , { walsCode := "epe", iso := "sja", value := .soVNeg }
  , { walsCode := "ese", iso := "ese", value := .sovneg }
  , { walsCode := "eud", iso := "", value := .otherNegv }
  , { walsCode := "evn", iso := "eve", value := .obligdoubleneg }
  , { walsCode := "eve", iso := "evn", value := .obligdoubleneg }
  , { walsCode := "fur", iso := "fvr", value := .obligdoubleneg }
  , { walsCode := "gds", iso := "gaj", value := .sonegv }
  , { walsCode := "gah", iso := "gah", value := .soVNeg }
  , { walsCode := "gal", iso := "adl", value := .soVNeg }
  , { walsCode := "gap", iso := "pwg", value := .sonegv }
  , { walsCode := "gar", iso := "grt", value := .soVNeg }
  , { walsCode := "gav", iso := "gvo", value := .svOvInitialneg }
  , { walsCode := "geo", iso := "kat", value := .sonegv }
  , { walsCode := "ger", iso := "deu", value := .moreThanOneConstruction }
  , { walsCode := "gim", iso := "bcq", value := .soVNeg }
  , { walsCode := "god", iso := "gdo", value := .svOvVNeg }
  , { walsCode := "gln", iso := "gvf", value := .soVNeg }
  , { walsCode := "gon", iso := "gno", value := .soVNeg }
  , { walsCode := "goo", iso := "gni", value := .svOvImmedpreverbal }
  , { walsCode := "grb", iso := "grj", value := .svoButSnegov }
  , { walsCode := "grw", iso := "kal", value := .soVNeg }
  , { walsCode := "gug", iso := "ktd", value := .moreThanOneConstruction }
  , { walsCode := "guh", iso := "ghs", value := .optdoubleneg }
  , { walsCode := "guj", iso := "guj", value := .sonegv }
  , { walsCode := "gmw", iso := "gvs", value := .sonegv }
  , { walsCode := "gur", iso := "", value := .soNegV }
  , { walsCode := "guu", iso := "kky", value := .sonegv }
  , { walsCode := "gwa", iso := "gbr", value := .obligdoubleneg }
  , { walsCode := "gyc", iso := "jya", value := .svOvNegV }
  , { walsCode := "hai", iso := "hai", value := .obligdoubleneg }
  , { walsCode := "ham", iso := "hmt", value := .soNegV }
  , { walsCode := "han", iso := "hni", value := .svOvNegv }
  , { walsCode := "har", iso := "tmd", value := .svOvVNeg }
  , { walsCode := "hay", iso := "vay", value := .sonegv }
  , { walsCode := "hid", iso := "hid", value := .soVNeg }
  , { walsCode := "hin", iso := "hin", value := .sonegv }
  , { walsCode := "hma", iso := "hmr", value := .svOvVneg }
  , { walsCode := "hop", iso := "hop", value := .sonegv }
  , { walsCode := "hua", iso := "ygr", value := .soNegV }
  , { walsCode := "hlp", iso := "yuf", value := .optdoubleneg }
  , { walsCode := "hui", iso := "hch", value := .soNegV }
  , { walsCode := "hmi", iso := "hto", value := .soVNeg }
  , { walsCode := "hum", iso := "huu", value := .soVNeg }
  , { walsCode := "hzb", iso := "huz", value := .soVNeg }
  , { walsCode := "hpd", iso := "jup", value := .soVNeg }
  , { walsCode := "isa", iso := "ksi", value := .sovneg }
  , { walsCode := "iau", iso := "tmu", value := .svOvVneg }
  , { walsCode := "idu", iso := "clk", value := .svOvVNeg }
  , { walsCode := "idn", iso := "viv", value := .sonegv }
  , { walsCode := "ijo", iso := "ijc", value := .moreThanOneConstruction }
  , { walsCode := "ika", iso := "arh", value := .soVNeg }
  , { walsCode := "imo", iso := "imn", value := .svOvNegv }
  , { walsCode := "ina", iso := "szp", value := .optdoubleneg }
  , { walsCode := "inn", iso := "ynd", value := .negsov }
  , { walsCode := "irx", iso := "irn", value := .soVNeg }
  , { walsCode := "irq", iso := "irk", value := .soVNeg }
  , { walsCode := "ite", iso := "itl", value := .obligdoubleneg }
  , { walsCode := "iwm", iso := "iwm", value := .sovneg }
  , { walsCode := "jms", iso := "djm", value := .soVNeg }
  , { walsCode := "jpn", iso := "jpn", value := .soVNeg }
  , { walsCode := "jng", iso := "kac", value := .otherNegv }
  , { walsCode := "jiv", iso := "jiv", value := .soVNeg }
  , { walsCode := "joh", iso := "rgk", value := .otherNegv }
  , { walsCode := "kab", iso := "kbd", value := .soVNeg }
  , { walsCode := "kac", iso := "xac", value := .soVNeg }
  , { walsCode := "kng", iso := "kgp", value := .sovneg }
  , { walsCode := "krr", iso := "kxa", value := .sovneg }
  , { walsCode := "kae", iso := "tbd", value := .moreThanOneConstruction }
  , { walsCode := "kmk", iso := "xal", value := .moreThanOneConstruction }
  , { walsCode := "kll", iso := "bco", value := .moreThanOneConstruction }
  , { walsCode := "kma", iso := "kay", value := .optdoubleneg }
  , { walsCode := "kmz", iso := "kms", value := .sovneg }
  , { walsCode := "kms", iso := "xas", value := .otherNegv }
  , { walsCode := "kbo", iso := "kbx", value := .soVNeg }
  , { walsCode := "kmr", iso := "kgq", value := .soVNeg }
  , { walsCode := "xns", iso := "xns", value := .otherNegv }
  , { walsCode := "knd", iso := "kan", value := .soVNeg }
  , { walsCode := "knb", iso := "khd", value := .otherNegv }
  , { walsCode := "knr", iso := "knc", value := .soVNeg }
  , { walsCode := "krc", iso := "krc", value := .moreThanOneConstruction }
  , { walsCode := "kkp", iso := "kaa", value := .soVNeg }
  , { walsCode := "kyr", iso := "yuj", value := .moreThanOneConstruction }
  , { walsCode := "kaa", iso := "arr", value := .sovneg }
  , { walsCode := "kti", iso := "kts", value := .sovneg }
  , { walsCode := "kyz", iso := "kyz", value := .optdoubleneg }
  , { walsCode := "kyp", iso := "txu", value := .sovneg }
  , { walsCode := "kem", iso := "ahg", value := .soVNeg }
  , { walsCode := "ksa", iso := "kee", value := .svOvNegv }
  , { walsCode := "ket", iso := "ket", value := .sonegv }
  , { walsCode := "kew", iso := "kew", value := .soNegV }
  , { walsCode := "khl", iso := "klj", value := .soVNeg }
  , { walsCode := "khg", iso := "klr", value := .optdoubleneg }
  , { walsCode := "kha", iso := "khk", value := .soVNeg }
  , { walsCode := "kmh", iso := "kjl", value := .soNegV }
  , { walsCode := "khd", iso := "khg", value := .soNegV }
  , { walsCode := "knz", iso := "khg", value := .soNegV }
  , { walsCode := "kty", iso := "kca", value := .sonegv }
  , { walsCode := "khr", iso := "khr", value := .svOvNegv }
  , { walsCode := "klw", iso := "klb", value := .optdoubleneg }
  , { walsCode := "kim", iso := "kig", value := .sovneg }
  , { walsCode := "knn", iso := "kfk", value := .sonegv }
  , { walsCode := "kio", iso := "kio", value := .obligdoubleneg }
  , { walsCode := "kie", iso := "geb", value := .sovneg }
  , { walsCode := "kis", iso := "kss", value := .obligdoubleneg }
  , { walsCode := "kiw", iso := "kjd", value := .obligdoubleneg }
  , { walsCode := "kla", iso := "klu", value := .svoButSnegov }
  , { walsCode := "koa", iso := "cku", value := .soVNeg }
  , { walsCode := "kob", iso := "kpw", value := .soVNeg }
  , { walsCode := "kmo", iso := "kpx", value := .soVNeg }
  , { walsCode := "kta", iso := "kqi", value := .soVNeg }
  , { walsCode := "kok", iso := "trp", value := .soVNeg }
  , { walsCode := "kol", iso := "kfb", value := .moreThanOneConstruction }
  , { walsCode := "kmb", iso := "", value := .optdoubleneg }
  , { walsCode := "knw", iso := "mjd", value := .svOvVNeg }
  , { walsCode := "kor", iso := "kor", value := .sonegv }
  , { walsCode := "krw", iso := "khe", value := .obligdoubleneg }
  , { walsCode := "kry", iso := "kpy", value := .obligdoubleneg }
  , { walsCode := "koy", iso := "kff", value := .soVNeg }
  , { walsCode := "kse", iso := "ses", value := .snegov }
  , { walsCode := "krh", iso := "xra", value := .soVNeg }
  , { walsCode := "knc", iso := "uwa", value := .svOvImmedpreverbal }
  , { walsCode := "kya", iso := "gvn", value := .otherNegv }
  , { walsCode := "klg", iso := "kle", value := .moreThanOneConstruction }
  , { walsCode := "kmn", iso := "kue", value := .soVNeg }
  , { walsCode := "kum", iso := "kfy", value := .otherNegv }
  , { walsCode := "kun", iso := "kvn", value := .soVNeg }
  , { walsCode := "knm", iso := "kun", value := .soVNeg }
  , { walsCode := "kmp", iso := "kup", value := .soNegV }
  , { walsCode := "krd", iso := "ckb", value := .soNegV }
  , { walsCode := "kus", iso := "kgg", value := .soVNeg }
  , { walsCode := "thy", iso := "thd", value := .sonegv }
  , { walsCode := "kuv", iso := "kxv", value := .soVNeg }
  , { walsCode := "kwz", iso := "xwa", value := .moreThanOneConstruction }
  , { walsCode := "kwo", iso := "kmo", value := .optdoubleneg }
  , { walsCode := "kwt", iso := "kwo", value := .optdoubleneg }
  , { walsCode := "kgy", iso := "kgy", value := .svOvNegV }
  , { walsCode := "lad", iso := "lbj", value := .moreThanOneConstruction }
  , { walsCode := "lah", iso := "lhu", value := .sonegv }
  , { walsCode := "lai", iso := "cnh", value := .sovneg }
  , { walsCode := "lkt", iso := "lkt", value := .sovneg }
  , { walsCode := "lal", iso := "ywt", value := .otherNegv }
  , { walsCode := "lmn", iso := "lmn", value := .sovneg }
  , { walsCode := "lar", iso := "lrg", value := .svOvNegv }
  , { walsCode := "lav", iso := "lvk", value := .moreThanOneConstruction }
  , { walsCode := "agb", iso := "agb", value := .svoButSoNegV }
  , { walsCode := "ldu", iso := "led", value := .moreThanOneConstruction }
  , { walsCode := "lep", iso := "lep", value := .obligdoubleneg }
  , { walsCode := "lez", iso := "lez", value := .soVNeg }
  , { walsCode := "lho", iso := "lhm", value := .moreThanOneConstruction }
  , { walsCode := "lim", iso := "lif", value := .obligdoubleneg }
  , { walsCode := "lis", iso := "lis", value := .sonegv }
  , { walsCode := "lot", iso := "njh", value := .soNegV }
  , { walsCode := "mab", iso := "mde", value := .optdoubleneg }
  , { walsCode := "mac", iso := "mbc", value := .moreThanOneConstruction }
  , { walsCode := "mag", iso := "mgp", value := .soNegV }
  , { walsCode := "mgi", iso := "mgu", value := .sonegv }
  , { walsCode := "mne", iso := "nmu", value := .soVNeg }
  , { walsCode := "mrs", iso := "zrs", value := .soVNeg }
  , { walsCode := "msn", iso := "mbq", value := .obligdoubleneg }
  , { walsCode := "mai", iso := "mai", value := .svOvImmedpreverbal }
  , { walsCode := "mkj", iso := "mkz", value := .sonegv }
  , { walsCode := "mkl", iso := "mgf", value := .otherNegv }
  , { walsCode := "mlk", iso := "mpb", value := .svOvNegv }
  , { walsCode := "mym", iso := "mal", value := .soVNeg }
  , { walsCode := "mnm", iso := "mva", value := .sonegv }
  , { walsCode := "nmm", iso := "nmm", value := .svOvNegV }
  , { walsCode := "mnc", iso := "mnc", value := .soVNeg }
  , { walsCode := "mdn", iso := "mhq", value := .obligdoubleneg }
  , { walsCode := "mkg", iso := "mnk", value := .snegov }
  , { walsCode := "mgg", iso := "mjg", value := .sonegv }
  , { walsCode := "maw", iso := "mlq", value := .snegov }
  , { walsCode := "man", iso := "mev", value := .snegov }
  , { walsCode := "mns", iso := "mns", value := .sonegv }
  , { walsCode := "mku", iso := "zmr", value := .optdoubleneg }
  , { walsCode := "mhi", iso := "mar", value := .sovneg }
  , { walsCode := "mny", iso := "zmc", value := .negsov }
  , { walsCode := "mar", iso := "mrc", value := .obligdoubleneg }
  , { walsCode := "mrd", iso := "mrz", value := .otherNegv }
  , { walsCode := "mrr", iso := "zmt", value := .otherNegv }
  , { walsCode := "mrh", iso := "mfr", value := .otherNegv }
  , { walsCode := "mru", iso := "mhx", value := .sonegv }
  , { walsCode := "msl", iso := "mls", value := .soVNeg }
  , { walsCode := "mts", iso := "mpq", value := .soVNeg }
  , { walsCode := "mdl", iso := "zml", value := .otherNegv }
  , { walsCode := "mka", iso := "mxx", value := .optdoubleneg }
  , { walsCode := "mbi", iso := "baw", value := .svoButSnegov }
  , { walsCode := "mdw", iso := "mdw", value := .svoButSovneg }
  , { walsCode := "mee", iso := "mym", value := .svoButSoVNeg }
  , { walsCode := "mei", iso := "mni", value := .svOvVNeg }
  , { walsCode := "mek", iso := "skf", value := .sovneg }
  , { walsCode := "mke", iso := "mek", value := .svOvNegV }
  , { walsCode := "mde", iso := "men", value := .otherNegv }
  , { walsCode := "mer", iso := "ulk", value := .otherNegv }
  , { walsCode := "mpt", iso := "mpt", value := .soVNeg }
  , { walsCode := "mii", iso := "", value := .svOvVNeg }
  , { walsCode := "mki", iso := "mik", value := .soVNeg }
  , { walsCode := "mik", iso := "mjw", value := .soVNeg }
  , { walsCode := "msg", iso := "mrg", value := .soVNeg }
  , { walsCode := "mis", iso := "miq", value := .soVNeg }
  , { walsCode := "miz", iso := "lus", value := .sovneg }
  , { walsCode := "mog", iso := "mhj", value := .otherNegv }
  , { walsCode := "mom", iso := "mso", value := .obligdoubleneg }
  , { walsCode := "mkh", iso := "", value := .moreThanOneConstruction }
  , { walsCode := "mni", iso := "mnz", value := .otherNegv }
  , { walsCode := "mno", iso := "mnr", value := .negsov }
  , { walsCode := "mri", iso := "mok", value := .otherNegv }
  , { walsCode := "mtu", iso := "meu", value := .moreThanOneConstruction }
  , { walsCode := "mot", iso := "siw", value := .svOvVNeg }
  , { walsCode := "mui", iso := "bmr", value := .svOvVNeg }
  , { walsCode := "msc", iso := "chb", value := .soVNeg }
  , { walsCode := "mun", iso := "unr", value := .sonegv }
  , { walsCode := "mpa", iso := "mwf", value := .sonegv }
  , { walsCode := "mur", iso := "muz", value := .svoButSonegv }
  , { walsCode := "nab", iso := "naf", value := .sonegv }
  , { walsCode := "nma", iso := "nbi", value := .sovneg }
  , { walsCode := "ngt", iso := "nmf", value := .soNegV }
  , { walsCode := "nze", iso := "nzm", value := .svOvVneg }
  , { walsCode := "nag", iso := "nce", value := .moreThanOneConstruction }
  , { walsCode := "bio", iso := "bio", value := .svOvVNeg }
  , { walsCode := "kho", iso := "naq", value := .sovneg }
  , { walsCode := "nmb", iso := "nab", value := .soVNeg }
  , { walsCode := "nam", iso := "nnm", value := .soNegV }
  , { walsCode := "nnk", iso := "nnk", value := .sovneg }
  , { walsCode := "nph", iso := "npa", value := .optdoubleneg }
  , { walsCode := "nar", iso := "nrb", value := .sonegv }
  , { walsCode := "nas", iso := "nas", value := .moreThanOneConstruction }
  , { walsCode := "nav", iso := "nav", value := .moreThanOneConstruction }
  , { walsCode := "ndj", iso := "djj", value := .svOvInitialneg }
  , { walsCode := "ntu", iso := "yrk", value := .sonegv }
  , { walsCode := "naj", iso := "aij", value := .sonegv }
  , { walsCode := "nep", iso := "npi", value := .soVNeg }
  , { walsCode := "nev", iso := "pia", value := .otherNegv }
  , { walsCode := "nwd", iso := "new", value := .moreThanOneConstruction }
  , { walsCode := "new", iso := "new", value := .soNegV }
  , { walsCode := "ntj", iso := "ntj", value := .soVNeg }
  , { walsCode := "ngj", iso := "nju", value := .svOvNegv }
  , { walsCode := "nga", iso := "nio", value := .sonegv }
  , { walsCode := "ngn", iso := "nid", value := .svOvVNeg }
  , { walsCode := "nti", iso := "niy", value := .moreThanOneConstruction }
  , { walsCode := "ngi", iso := "wyb", value := .svOvInitialneg }
  , { walsCode := "nbr", iso := "gym", value := .otherNegv }
  , { walsCode := "nsn", iso := "nsz", value := .svOvVNeg }
  , { walsCode := "niv", iso := "niv", value := .optdoubleneg }
  , { walsCode := "noc", iso := "njb", value := .soVNeg }
  , { walsCode := "nbd", iso := "dgl", value := .soVNeg }
  , { walsCode := "nku", iso := "xnz", value := .soVNeg }
  , { walsCode := "nue", iso := "nus", value := .svoSovButSovneg }
  , { walsCode := "yi", iso := "iii", value := .otherNegv }
  , { walsCode := "nyk", iso := "tpq", value := .otherNegv }
  , { walsCode := "nyi", iso := "nyi", value := .sonegv }
  , { walsCode := "nis", iso := "njz", value := .svOvVNeg }
  , { walsCode := "oir", iso := "xal", value := .otherNegv }
  , { walsCode := "oks", iso := "opm", value := .sonegv }
  , { walsCode := "omh", iso := "oma", value := .soVNeg }
  , { walsCode := "ong", iso := "oon", value := .sovneg }
  , { walsCode := "ori", iso := "tag", value := .soNegV }
  , { walsCode := "oya", iso := "ory", value := .soVNeg }
  , { walsCode := "ork", iso := "oaa", value := .svOvNegV }
  , { walsCode := "oro", iso := "okv", value := .moreThanOneConstruction }
  , { walsCode := "orh", iso := "hae", value := .obligdoubleneg }
  , { walsCode := "orw", iso := "ssn", value := .obligdoubleneg }
  , { walsCode := "osa", iso := "osa", value := .sovneg }
  , { walsCode := "oss", iso := "oss", value := .otherNegv }
  , { walsCode := "pno", iso := "pao", value := .negsov }
  , { walsCode := "pan", iso := "pan", value := .sonegv }
  , { walsCode := "psh", iso := "pst", value := .soNegV }
  , { walsCode := "ptt", iso := "lae", value := .soNegV }
  , { walsCode := "ptw", iso := "pwi", value := .svOvVNeg }
  , { walsCode := "paw", iso := "pwa", value := .moreThanOneConstruction }
  , { walsCode := "prs", iso := "pes", value := .soNegV }
  , { walsCode := "pia", iso := "pid", value := .svOvVNeg }
  , { walsCode := "pba", iso := "pia", value := .moreThanOneConstruction }
  , { walsCode := "prh", iso := "myp", value := .soVNeg }
  , { walsCode := "pis", iso := "psa", value := .obligdoubleneg }
  , { walsCode := "pit", iso := "pjt", value := .moreThanOneConstruction }
  , { walsCode := "pme", iso := "peb", value := .soVNeg }
  , { walsCode := "pso", iso := "pom", value := .obligdoubleneg }
  , { walsCode := "pra", iso := "prn", value := .moreThanOneConstruction }
  , { walsCode := "pum", iso := "pmi", value := .moreThanOneConstruction }
  , { walsCode := "pun", iso := "wdj", value := .otherNegv }
  , { walsCode := "prk", iso := "prx", value := .soVNeg }
  , { walsCode := "pae", iso := "pbb", value := .soVNeg }
  , { walsCode := "qaw", iso := "alc", value := .svOvVneg }
  , { walsCode := "qhu", iso := "qub", value := .obligdoubleneg }
  , { walsCode := "qim", iso := "qvi", value := .moreThanOneConstruction }
  , { walsCode := "ram", iso := "rma", value := .moreThanOneConstruction }
  , { walsCode := "rpa", iso := "bod", value := .otherNegv }
  , { walsCode := "rao", iso := "rao", value := .soVNeg }
  , { walsCode := "ras", iso := "ras", value := .soNegV }
  , { walsCode := "rwa", iso := "rwo", value := .otherNegv }
  , { walsCode := "raw", iso := "raw", value := .sonegv }
  , { walsCode := "rem", iso := "bfw", value := .svOvNegV }
  , { walsCode := "res", iso := "rgr", value := .negsov }
  , { walsCode := "ret", iso := "tnc", value := .soVNeg }
  , { walsCode := "rik", iso := "rkb", value := .otherNegv }
  , { walsCode := "rum", iso := "klq", value := .soVNeg }
  , { walsCode := "run", iso := "rou", value := .optdoubleneg }
  , { walsCode := "slb", iso := "sbe", value := .snegov }
  , { walsCode := "syu", iso := "sll", value := .soVNeg }
  , { walsCode := "sdw", iso := "sad", value := .soVNeg }
  , { walsCode := "sta", iso := "sce", value := .otherNegv }
  , { walsCode := "stl", iso := "sat", value := .sonegv }
  , { walsCode := "snm", iso := "xsu", value := .sovneg }
  , { walsCode := "src", iso := "srs", value := .otherNegv }
  , { walsCode := "sar", iso := "dju", value := .moreThanOneConstruction }
  , { walsCode := "svs", iso := "svs", value := .otherNegv }
  , { walsCode := "sem", iso := "nsm", value := .svOvVNeg }
  , { walsCode := "sme", iso := "sif", value := .sovneg }
  , { walsCode := "smn", iso := "mus", value := .soVNeg }
  , { walsCode := "snt", iso := "set", value := .soNegV }
  , { walsCode := "ser", iso := "sei", value := .soNegV }
  , { walsCode := "shb", iso := "sbf", value := .sovneg }
  , { walsCode := "shh", iso := "mcd", value := .soVNeg }
  , { walsCode := "skw", iso := "swv", value := .otherNegv }
  , { walsCode := "she", iso := "xsr", value := .soNegV }
  , { walsCode := "sna", iso := "scl", value := .sonegv }
  , { walsCode := "shk", iso := "shp", value := .soVNeg }
  , { walsCode := "shi", iso := "shb", value := .sovneg }
  , { walsCode := "sia", iso := "snp", value := .soVNeg }
  , { walsCode := "sid", iso := "sid", value := .sonegv }
  , { walsCode := "skk", iso := "sip", value := .svOvVneg }
  , { walsCode := "sil", iso := "dau", value := .sonegv }
  , { walsCode := "sng", iso := "snc", value := .sonegv }
  , { walsCode := "sin", iso := "snn", value := .svOvVNeg }
  , { walsCode := "sro", iso := "ssd", value := .sovneg }
  , { walsCode := "sla", iso := "den", value := .sovneg }
  , { walsCode := "sod", iso := "gru", value := .soNegV }
  , { walsCode := "som", iso := "som", value := .sonegv }
  , { walsCode := "snn", iso := "snk", value := .snegov }
  , { walsCode := "srb", iso := "", value := .soNegV }
  , { walsCode := "tou", iso := "wib", value := .svOvNegv }
  , { walsCode := "sue", iso := "sue", value := .otherNegv }
  , { walsCode := "sup", iso := "spp", value := .optdoubleneg }
  , { walsCode := "tba", iso := "sst", value := .soVNeg }
  , { walsCode := "tbl", iso := "tnm", value := .obligdoubleneg }
  , { walsCode := "tac", iso := "tna", value := .optdoubleneg }
  , { walsCode := "trr", iso := "tbg", value := .negsov }
  , { walsCode := "taj", iso := "tgk", value := .soNegV }
  , { walsCode := "tkl", iso := "tkm", value := .otherNegv }
  , { walsCode := "tak", iso := "tbc", value := .sonegv }
  , { walsCode := "tma", iso := "tma", value := .soVNeg }
  , { walsCode := "tam", iso := "taj", value := .sonegv }
  , { walsCode := "tml", iso := "tam", value := .soVNeg }
  , { walsCode := "tnc", iso := "tcb", value := .obligdoubleneg }
  , { walsCode := "tpt", iso := "tpj", value := .soVNeg }
  , { walsCode := "tce", iso := "tar", value := .otherNegv }
  , { walsCode := "twe", iso := "tac", value := .otherNegv }
  , { walsCode := "tao", iso := "tro", value := .soVNeg }
  , { walsCode := "tar", iso := "tae", value := .optdoubleneg }
  , { walsCode := "tau", iso := "tya", value := .sonegv }
  , { walsCode := "taw", iso := "tbo", value := .otherNegv }
  , { walsCode := "tel", iso := "tel", value := .soVNeg }
  , { walsCode := "tny", iso := "kza", value := .svOvNegv }
  , { walsCode := "trb", iso := "tfr", value := .sovneg }
  , { walsCode := "thn", iso := "thf", value := .soNegV }
  , { walsCode := "thu", iso := "tdh", value := .obligdoubleneg }
  , { walsCode := "tdr", iso := "bod", value := .soNegV }
  , { walsCode := "tmo", iso := "bod", value := .moreThanOneConstruction }
  , { walsCode := "tis", iso := "bod", value := .svOvNegV }
  , { walsCode := "tib", iso := "bod", value := .soNegV }
  , { walsCode := "tig", iso := "tir", value := .obligdoubleneg }
  , { walsCode := "tgr", iso := "tig", value := .soNegV }
  , { walsCode := "tja", iso := "dih", value := .optdoubleneg }
  , { walsCode := "trm", iso := "suq", value := .obligdoubleneg }
  , { walsCode := "twn", iso := "twf", value := .moreThanOneConstruction }
  , { walsCode := "tli", iso := "tli", value := .sonegv }
  , { walsCode := "tlo", iso := "tlb", value := .soVNeg }
  , { walsCode := "tod", iso := "sbu", value := .soNegV }
  ]

private def allData_1 : List (Datapoint PositionOfNegativeMorphemesInSovLanguages) :=
  [ { walsCode := "ton", iso := "tqw", value := .moreThanOneConstruction }
  , { walsCode := "tru", iso := "tpy", value := .moreThanOneConstruction }
  , { walsCode := "tsf", iso := "cof", value := .soVNeg }
  , { walsCode := "tsz", iso := "ddo", value := .sovneg }
  , { walsCode := "tgl", iso := "tsj", value := .optdoubleneg }
  , { walsCode := "ttu", iso := "bbl", value := .sonegv }
  , { walsCode := "tbu", iso := "", value := .soVNeg }
  , { walsCode := "tuc", iso := "tuo", value := .svOvVNeg }
  , { walsCode := "tul", iso := "tcy", value := .soVNeg }
  , { walsCode := "tnn", iso := "tvu", value := .snegov }
  , { walsCode := "tun", iso := "tun", value := .soVNeg }
  , { walsCode := "tur", iso := "tur", value := .soVNeg }
  , { walsCode := "tte", iso := "tta", value := .obligdoubleneg }
  , { walsCode := "tuv", iso := "tyv", value := .soVNeg }
  , { walsCode := "tuy", iso := "tue", value := .soVNeg }
  , { walsCode := "tye", iso := "woa", value := .obligdoubleneg }
  , { walsCode := "tsh", iso := "par", value := .optdoubleneg }
  , { walsCode := "uby", iso := "uby", value := .moreThanOneConstruction }
  , { walsCode := "udi", iso := "udi", value := .soNegV }
  , { walsCode := "udh", iso := "ude", value := .sonegv }
  , { walsCode := "udm", iso := "udm", value := .sovneg }
  , { walsCode := "una", iso := "mtg", value := .sonegv }
  , { walsCode := "urd", iso := "urd", value := .sonegv }
  , { walsCode := "uru", iso := "ure", value := .svOvNegv }
  , { walsCode := "urk", iso := "urb", value := .sovneg }
  , { walsCode := "usa", iso := "wnu", value := .sonegv }
  , { walsCode := "usr", iso := "usa", value := .soNegV }
  , { walsCode := "uyg", iso := "uig", value := .soVNeg }
  , { walsCode := "uzb", iso := "", value := .soVNeg }
  , { walsCode := "vai", iso := "vai", value := .snegov }
  , { walsCode := "wag", iso := "waq", value := .sonegv }
  , { walsCode := "wah", iso := "", value := .otherNegv }
  , { walsCode := "wak", iso := "wbl", value := .sonegv }
  , { walsCode := "wbn", iso := "wms", value := .soVNeg }
  , { walsCode := "wme", iso := "wme", value := .soNegV }
  , { walsCode := "wna", iso := "wan", value := .sovneg }
  , { walsCode := "wao", iso := "auc", value := .soVNeg }
  , { walsCode := "wap", iso := "wao", value := .soVNeg }
  , { walsCode := "wra", iso := "wba", value := .svOvVNeg }
  , { walsCode := "wlw", iso := "wrb", value := .negsov }
  , { walsCode := "was", iso := "was", value := .soVNeg }
  , { walsCode := "wsk", iso := "wsk", value := .sonegv }
  , { walsCode := "wtm", iso := "wax", value := .svOvNegV }
  , { walsCode := "wau", iso := "noa", value := .svOvVNeg }
  , { walsCode := "way", iso := "oym", value := .obligdoubleneg }
  , { walsCode := "wed", iso := "wed", value := .otherNegv }
  , { walsCode := "wic", iso := "wic", value := .moreThanOneConstruction }
  , { walsCode := "wmu", iso := "wim", value := .otherNegv }
  , { walsCode := "woi", iso := "woi", value := .optdoubleneg }
  , { walsCode := "wly", iso := "wal", value := .soVNeg }
  , { walsCode := "wom", iso := "wmx", value := .sovneg }
  , { walsCode := "ygr", iso := "ygr", value := .soNegV }
  , { walsCode := "ykt", iso := "sah", value := .soVNeg }
  , { walsCode := "yam", iso := "yaa", value := .soVNeg }
  , { walsCode := "ybi", iso := "ybi", value := .svOvNegV }
  , { walsCode := "yqy", iso := "jaq", value := .obligdoubleneg }
  , { walsCode := "yaq", iso := "yaq", value := .snegov }
  , { walsCode := "yar", iso := "yrb", value := .soVNeg }
  , { walsCode := "yei", iso := "jei", value := .otherNegv }
  , { walsCode := "ylm", iso := "jel", value := .otherNegv }
  , { walsCode := "yiw", iso := "ywq", value := .otherNegv }
  , { walsCode := "yid", iso := "yii", value := .sonegv }
  , { walsCode := "yim", iso := "yee", value := .svOvNegV }
  , { walsCode := "yuc", iso := "yuc", value := .otherNegv }
  , { walsCode := "yko", iso := "yux", value := .soNegV }
  , { walsCode := "ytu", iso := "ykg", value := .soNegV }
  , { walsCode := "yuw", iso := "kld", value := .negsov }
  , { walsCode := "zay", iso := "zay", value := .soVNeg }
  , { walsCode := "zaz", iso := "diq", value := .soNegV }
  , { walsCode := "zun", iso := "zun", value := .obligdoubleneg }
  , { walsCode := "rgc", iso := "jya", value := .soNegV }
  , { walsCode := "eme", iso := "eme", value := .obligdoubleneg }
  , { walsCode := "omi", iso := "aom", value := .svOvNegv }
  ]

/-- Complete WALS 144L dataset (573 languages). -/
def allData : List (Datapoint PositionOfNegativeMorphemesInSovLanguages) := allData_0 ++ allData_1

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144L
