import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144R: SONegV Order
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144R`.

Chapter 144, 411 languages.
-/

namespace Datasets.WALS.F144R

/-- WALS 144R values. -/
inductive SonegvOrder where
  /-- Word&NoDoubleNeg (76 languages). -/
  | wordNodoubleneg
  /-- Prefix&NoDoubleNeg (60 languages). -/
  | prefixNodoubleneg
  /-- Word&OptDoubleNeg (1 languages). -/
  | wordOptdoubleneg
  /-- Prefix&OptDoubleNeg (3 languages). -/
  | prefixOptdoubleneg
  /-- Word&OnlyWithAnotherNeg (11 languages). -/
  | wordOnlywithanotherneg
  /-- Prefix&OnlyWithAnotherNeg (21 languages). -/
  | prefixOnlywithanotherneg
  /-- Type 1 / Type 2 (1 languages). -/
  | type1Type2
  /-- No SONegV (238 languages). -/
  | noSonegv
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144R dataset (411 languages). -/
def allData : List (Datapoint SonegvOrder) :=
  [ { walsCode := "aba", iso := "aau", value := .noSonegv }
  , { walsCode := "abk", iso := "abk", value := .prefixNodoubleneg }
  , { walsCode := "abv", iso := "abz", value := .noSonegv }
  , { walsCode := "adg", iso := "adn", value := .noSonegv }
  , { walsCode := "ain", iso := "ain", value := .wordNodoubleneg }
  , { walsCode := "akh", iso := "ahk", value := .wordNodoubleneg }
  , { walsCode := "ala", iso := "amp", value := .wordNodoubleneg }
  , { walsCode := "aly", iso := "aly", value := .noSonegv }
  , { walsCode := "ame", iso := "aey", value := .wordOptdoubleneg }
  , { walsCode := "amh", iso := "amh", value := .prefixOnlywithanotherneg }
  , { walsCode := "agm", iso := "njm", value := .noSonegv }
  , { walsCode := "ang", iso := "agg", value := .noSonegv }
  , { walsCode := "ao", iso := "njo", value := .prefixOptdoubleneg }
  , { walsCode := "apw", iso := "apw", value := .wordOnlywithanotherneg }
  , { walsCode := "apl", iso := "apy", value := .noSonegv }
  , { walsCode := "apt", iso := "apt", value := .noSonegv }
  , { walsCode := "arc", iso := "aqc", value := .noSonegv }
  , { walsCode := "arm", iso := "hye", value := .type1Type2 }
  , { walsCode := "arw", iso := "hyw", value := .prefixNodoubleneg }
  , { walsCode := "amp", iso := "aer", value := .noSonegv }
  , { walsCode := "asm", iso := "cns", value := .noSonegv }
  , { walsCode := "ass", iso := "asm", value := .prefixNodoubleneg }
  , { walsCode := "ath", iso := "aph", value := .noSonegv }
  , { walsCode := "ava", iso := "ava", value := .noSonegv }
  , { walsCode := "awa", iso := "awb", value := .wordNodoubleneg }
  , { walsCode := "awp", iso := "kwi", value := .wordOnlywithanotherneg }
  , { walsCode := "awt", iso := "kmn", value := .prefixNodoubleneg }
  , { walsCode := "aym", iso := "ayr", value := .wordNodoubleneg }
  , { walsCode := "azi", iso := "azb", value := .noSonegv }
  , { walsCode := "aze", iso := "", value := .noSonegv }
  , { walsCode := "baf", iso := "bfd", value := .noSonegv }
  , { walsCode := "bam", iso := "bam", value := .noSonegv }
  , { walsCode := "brl", iso := "loy", value := .prefixNodoubleneg }
  , { walsCode := "baa", iso := "bbb", value := .wordNodoubleneg }
  , { walsCode := "brp", iso := "bpe", value := .noSonegv }
  , { walsCode := "bsq", iso := "eus", value := .wordNodoubleneg }
  , { walsCode := "bzi", iso := "bvz", value := .noSonegv }
  , { walsCode := "baw", iso := "bgr", value := .noSonegv }
  , { walsCode := "bej", iso := "bej", value := .prefixNodoubleneg }
  , { walsCode := "ben", iso := "ben", value := .noSonegv }
  , { walsCode := "zag", iso := "zag", value := .noSonegv }
  , { walsCode := "bti", iso := "", value := .noSonegv }
  , { walsCode := "bho", iso := "bho", value := .wordNodoubleneg }
  , { walsCode := "blx", iso := "bll", value := .prefixOnlywithanotherneg }
  , { walsCode := "biu", iso := "", value := .prefixNodoubleneg }
  , { walsCode := "boa", iso := "kvg", value := .noSonegv }
  , { walsCode := "bok", iso := "bqc", value := .noSonegv }
  , { walsCode := "but", iso := "bxm", value := .noSonegv }
  , { walsCode := "brm", iso := "mya", value := .prefixOnlywithanotherneg }
  , { walsCode := "bur", iso := "bsk", value := .prefixNodoubleneg }
  , { walsCode := "bus", iso := "bqp", value := .noSonegv }
  , { walsCode := "cah", iso := "chl", value := .wordNodoubleneg }
  , { walsCode := "cml", iso := "rab", value := .prefixOnlywithanotherneg }
  , { walsCode := "can", iso := "cbu", value := .noSonegv }
  , { walsCode := "cnl", iso := "ram", value := .noSonegv }
  , { walsCode := "car", iso := "car", value := .noSonegv }
  , { walsCode := "cde", iso := "mch", value := .noSonegv }
  , { walsCode := "cas", iso := "cbr", value := .noSonegv }
  , { walsCode := "cay", iso := "cbi", value := .noSonegv }
  , { walsCode := "chh", iso := "sgw", value := .prefixNodoubleneg }
  , { walsCode := "cai", iso := "suq", value := .wordNodoubleneg }
  , { walsCode := "chb", iso := "can", value := .prefixOnlywithanotherneg }
  , { walsCode := "chg", iso := "nbc", value := .prefixNodoubleneg }
  , { walsCode := "chc", iso := "che", value := .wordNodoubleneg }
  , { walsCode := "cpn", iso := "cdm", value := .noSonegv }
  , { walsCode := "cpy", iso := "cap", value := .noSonegv }
  , { walsCode := "chp", iso := "chp", value := .noSonegv }
  , { walsCode := "ctm", iso := "ctm", value := .noSonegv }
  , { walsCode := "cct", iso := "cho", value := .noSonegv }
  , { walsCode := "cln", iso := "cht", value := .noSonegv }
  , { walsCode := "chv", iso := "chv", value := .noSonegv }
  , { walsCode := "coa", iso := "xcw", value := .noSonegv }
  , { walsCode := "cmn", iso := "com", value := .wordNodoubleneg }
  , { walsCode := "cui", iso := "cui", value := .noSonegv }
  , { walsCode := "cup", iso := "cup", value := .noSonegv }
  , { walsCode := "dag", iso := "dgz", value := .wordNodoubleneg }
  , { walsCode := "dni", iso := "dni", value := .noSonegv }
  , { walsCode := "drm", iso := "drd", value := .prefixNodoubleneg }
  , { walsCode := "des", iso := "des", value := .noSonegv }
  , { walsCode := "deu", iso := "der", value := .noSonegv }
  , { walsCode := "dhm", iso := "dhi", value := .prefixNodoubleneg }
  , { walsCode := "die", iso := "dih", value := .noSonegv }
  , { walsCode := "dig", iso := "mhu", value := .noSonegv }
  , { walsCode := "dim", iso := "dim", value := .noSonegv }
  , { walsCode := "din", iso := "din", value := .noSonegv }
  , { walsCode := "djp", iso := "dwu", value := .noSonegv }
  , { walsCode := "dji", iso := "jig", value := .wordNodoubleneg }
  , { walsCode := "dds", iso := "dds", value := .noSonegv }
  , { walsCode := "dum", iso := "vam", value := .noSonegv }
  , { walsCode := "dun", iso := "duc", value := .wordOnlywithanotherneg }
  , { walsCode := "dut", iso := "nld", value := .wordNodoubleneg }
  , { walsCode := "eip", iso := "eip", value := .wordNodoubleneg }
  , { walsCode := "epe", iso := "sja", value := .noSonegv }
  , { walsCode := "ese", iso := "ese", value := .noSonegv }
  , { walsCode := "eve", iso := "evn", value := .wordOnlywithanotherneg }
  , { walsCode := "fur", iso := "fvr", value := .prefixOnlywithanotherneg }
  , { walsCode := "gds", iso := "gaj", value := .wordNodoubleneg }
  , { walsCode := "gah", iso := "gah", value := .noSonegv }
  , { walsCode := "gal", iso := "adl", value := .noSonegv }
  , { walsCode := "gap", iso := "pwg", value := .wordNodoubleneg }
  , { walsCode := "gar", iso := "grt", value := .noSonegv }
  , { walsCode := "geo", iso := "kat", value := .wordNodoubleneg }
  , { walsCode := "ger", iso := "deu", value := .wordNodoubleneg }
  , { walsCode := "gim", iso := "bcq", value := .noSonegv }
  , { walsCode := "gln", iso := "gvf", value := .noSonegv }
  , { walsCode := "gon", iso := "gno", value := .noSonegv }
  , { walsCode := "grb", iso := "grj", value := .noSonegv }
  , { walsCode := "grw", iso := "kal", value := .noSonegv }
  , { walsCode := "guj", iso := "guj", value := .wordNodoubleneg }
  , { walsCode := "gmw", iso := "gvs", value := .wordNodoubleneg }
  , { walsCode := "gur", iso := "", value := .prefixNodoubleneg }
  , { walsCode := "guu", iso := "kky", value := .wordNodoubleneg }
  , { walsCode := "gwa", iso := "gbr", value := .noSonegv }
  , { walsCode := "hai", iso := "hai", value := .noSonegv }
  , { walsCode := "ham", iso := "hmt", value := .prefixNodoubleneg }
  , { walsCode := "hay", iso := "vay", value := .wordNodoubleneg }
  , { walsCode := "hid", iso := "hid", value := .noSonegv }
  , { walsCode := "hin", iso := "hin", value := .wordNodoubleneg }
  , { walsCode := "hop", iso := "hop", value := .wordNodoubleneg }
  , { walsCode := "hua", iso := "ygr", value := .prefixNodoubleneg }
  , { walsCode := "hlp", iso := "yuf", value := .wordOnlywithanotherneg }
  , { walsCode := "hui", iso := "hch", value := .prefixNodoubleneg }
  , { walsCode := "hmi", iso := "hto", value := .noSonegv }
  , { walsCode := "hum", iso := "huu", value := .noSonegv }
  , { walsCode := "hzb", iso := "huz", value := .noSonegv }
  , { walsCode := "hpd", iso := "jup", value := .noSonegv }
  , { walsCode := "isa", iso := "ksi", value := .noSonegv }
  , { walsCode := "idn", iso := "viv", value := .wordNodoubleneg }
  , { walsCode := "ijo", iso := "ijc", value := .noSonegv }
  , { walsCode := "ika", iso := "arh", value := .noSonegv }
  , { walsCode := "inn", iso := "ynd", value := .noSonegv }
  , { walsCode := "irx", iso := "irn", value := .noSonegv }
  , { walsCode := "irq", iso := "irk", value := .noSonegv }
  , { walsCode := "iwm", iso := "iwm", value := .noSonegv }
  , { walsCode := "jms", iso := "djm", value := .noSonegv }
  , { walsCode := "jpn", iso := "jpn", value := .noSonegv }
  , { walsCode := "jiv", iso := "jiv", value := .noSonegv }
  , { walsCode := "kab", iso := "kbd", value := .noSonegv }
  , { walsCode := "kac", iso := "xac", value := .noSonegv }
  , { walsCode := "kng", iso := "kgp", value := .noSonegv }
  , { walsCode := "krr", iso := "kxa", value := .noSonegv }
  , { walsCode := "kae", iso := "tbd", value := .wordNodoubleneg }
  , { walsCode := "kll", iso := "bco", value := .prefixNodoubleneg }
  , { walsCode := "kma", iso := "kay", value := .prefixOnlywithanotherneg }
  , { walsCode := "kmz", iso := "kms", value := .noSonegv }
  , { walsCode := "kbo", iso := "kbx", value := .noSonegv }
  , { walsCode := "kmr", iso := "kgq", value := .noSonegv }
  , { walsCode := "knd", iso := "kan", value := .noSonegv }
  , { walsCode := "knr", iso := "knc", value := .noSonegv }
  , { walsCode := "krc", iso := "krc", value := .noSonegv }
  , { walsCode := "kkp", iso := "kaa", value := .noSonegv }
  , { walsCode := "kyr", iso := "yuj", value := .noSonegv }
  , { walsCode := "kaa", iso := "arr", value := .noSonegv }
  , { walsCode := "kti", iso := "kts", value := .noSonegv }
  , { walsCode := "kyz", iso := "kyz", value := .noSonegv }
  , { walsCode := "kyp", iso := "txu", value := .noSonegv }
  , { walsCode := "kem", iso := "ahg", value := .noSonegv }
  , { walsCode := "ket", iso := "ket", value := .wordNodoubleneg }
  , { walsCode := "kew", iso := "kew", value := .prefixNodoubleneg }
  , { walsCode := "khl", iso := "klj", value := .noSonegv }
  , { walsCode := "khg", iso := "klr", value := .prefixOptdoubleneg }
  , { walsCode := "kha", iso := "khk", value := .noSonegv }
  , { walsCode := "kmh", iso := "kjl", value := .prefixNodoubleneg }
  , { walsCode := "khd", iso := "khg", value := .prefixNodoubleneg }
  , { walsCode := "knz", iso := "khg", value := .prefixNodoubleneg }
  , { walsCode := "kty", iso := "kca", value := .wordNodoubleneg }
  , { walsCode := "klw", iso := "klb", value := .wordOnlywithanotherneg }
  , { walsCode := "kim", iso := "kig", value := .noSonegv }
  , { walsCode := "knn", iso := "kfk", value := .wordNodoubleneg }
  , { walsCode := "kio", iso := "kio", value := .noSonegv }
  , { walsCode := "kie", iso := "geb", value := .noSonegv }
  , { walsCode := "kis", iso := "kss", value := .noSonegv }
  , { walsCode := "kiw", iso := "kjd", value := .wordOnlywithanotherneg }
  , { walsCode := "kla", iso := "klu", value := .noSonegv }
  , { walsCode := "koa", iso := "cku", value := .noSonegv }
  , { walsCode := "kob", iso := "kpw", value := .noSonegv }
  , { walsCode := "kmo", iso := "kpx", value := .noSonegv }
  , { walsCode := "kta", iso := "kqi", value := .noSonegv }
  , { walsCode := "kok", iso := "trp", value := .noSonegv }
  , { walsCode := "kol", iso := "kfb", value := .noSonegv }
  , { walsCode := "kmb", iso := "", value := .prefixOnlywithanotherneg }
  , { walsCode := "kor", iso := "kor", value := .wordNodoubleneg }
  , { walsCode := "krw", iso := "khe", value := .prefixOnlywithanotherneg }
  , { walsCode := "kry", iso := "kpy", value := .prefixOnlywithanotherneg }
  , { walsCode := "koy", iso := "kff", value := .noSonegv }
  , { walsCode := "kse", iso := "ses", value := .noSonegv }
  , { walsCode := "krh", iso := "xra", value := .noSonegv }
  , { walsCode := "kmn", iso := "kue", value := .noSonegv }
  , { walsCode := "kun", iso := "kvn", value := .noSonegv }
  , { walsCode := "knm", iso := "kun", value := .noSonegv }
  , { walsCode := "kmp", iso := "kup", value := .prefixNodoubleneg }
  , { walsCode := "krd", iso := "ckb", value := .prefixNodoubleneg }
  , { walsCode := "kus", iso := "kgg", value := .noSonegv }
  , { walsCode := "thy", iso := "thd", value := .wordNodoubleneg }
  , { walsCode := "kuv", iso := "kxv", value := .noSonegv }
  , { walsCode := "kwz", iso := "xwa", value := .noSonegv }
  , { walsCode := "kwt", iso := "kwo", value := .noSonegv }
  , { walsCode := "lad", iso := "lbj", value := .prefixNodoubleneg }
  , { walsCode := "lah", iso := "lhu", value := .wordNodoubleneg }
  , { walsCode := "lai", iso := "cnh", value := .noSonegv }
  , { walsCode := "lkt", iso := "lkt", value := .noSonegv }
  , { walsCode := "lmn", iso := "lmn", value := .noSonegv }
  , { walsCode := "lav", iso := "lvk", value := .noSonegv }
  , { walsCode := "agb", iso := "agb", value := .prefixNodoubleneg }
  , { walsCode := "ldu", iso := "led", value := .noSonegv }
  , { walsCode := "lep", iso := "lep", value := .prefixOnlywithanotherneg }
  , { walsCode := "lez", iso := "lez", value := .noSonegv }
  , { walsCode := "lis", iso := "lis", value := .wordNodoubleneg }
  , { walsCode := "lot", iso := "njh", value := .prefixNodoubleneg }
  , { walsCode := "mab", iso := "mde", value := .noSonegv }
  , { walsCode := "mac", iso := "mbc", value := .noSonegv }
  , { walsCode := "mag", iso := "mgp", value := .prefixNodoubleneg }
  , { walsCode := "mgi", iso := "mgu", value := .wordNodoubleneg }
  , { walsCode := "mne", iso := "nmu", value := .noSonegv }
  , { walsCode := "mrs", iso := "zrs", value := .noSonegv }
  , { walsCode := "mkj", iso := "mkz", value := .wordNodoubleneg }
  , { walsCode := "mym", iso := "mal", value := .noSonegv }
  , { walsCode := "mnm", iso := "mva", value := .wordNodoubleneg }
  , { walsCode := "mnc", iso := "mnc", value := .noSonegv }
  , { walsCode := "mdn", iso := "mhq", value := .prefixOnlywithanotherneg }
  , { walsCode := "mkg", iso := "mnk", value := .noSonegv }
  , { walsCode := "mgg", iso := "mjg", value := .wordNodoubleneg }
  , { walsCode := "maw", iso := "mlq", value := .noSonegv }
  , { walsCode := "man", iso := "mev", value := .noSonegv }
  , { walsCode := "mns", iso := "mns", value := .wordNodoubleneg }
  , { walsCode := "mku", iso := "zmr", value := .noSonegv }
  , { walsCode := "mhi", iso := "mar", value := .noSonegv }
  , { walsCode := "mny", iso := "zmc", value := .noSonegv }
  , { walsCode := "mar", iso := "mrc", value := .prefixOnlywithanotherneg }
  , { walsCode := "mru", iso := "mhx", value := .wordNodoubleneg }
  , { walsCode := "msl", iso := "mls", value := .noSonegv }
  , { walsCode := "mts", iso := "mpq", value := .noSonegv }
  , { walsCode := "mka", iso := "mxx", value := .noSonegv }
  , { walsCode := "mbi", iso := "baw", value := .noSonegv }
  , { walsCode := "mdw", iso := "mdw", value := .noSonegv }
  , { walsCode := "mee", iso := "mym", value := .noSonegv }
  , { walsCode := "mek", iso := "skf", value := .noSonegv }
  , { walsCode := "mpt", iso := "mpt", value := .noSonegv }
  , { walsCode := "mki", iso := "mik", value := .noSonegv }
  , { walsCode := "mik", iso := "mjw", value := .noSonegv }
  , { walsCode := "msg", iso := "mrg", value := .noSonegv }
  , { walsCode := "mis", iso := "miq", value := .noSonegv }
  , { walsCode := "miz", iso := "lus", value := .noSonegv }
  , { walsCode := "mkh", iso := "", value := .noSonegv }
  , { walsCode := "mno", iso := "mnr", value := .noSonegv }
  , { walsCode := "msc", iso := "chb", value := .noSonegv }
  , { walsCode := "mun", iso := "unr", value := .wordNodoubleneg }
  , { walsCode := "mpa", iso := "mwf", value := .wordNodoubleneg }
  , { walsCode := "mur", iso := "muz", value := .wordNodoubleneg }
  , { walsCode := "nab", iso := "naf", value := .wordNodoubleneg }
  , { walsCode := "nma", iso := "nbi", value := .noSonegv }
  , { walsCode := "ngt", iso := "nmf", value := .prefixNodoubleneg }
  , { walsCode := "kho", iso := "naq", value := .noSonegv }
  , { walsCode := "nmb", iso := "nab", value := .noSonegv }
  , { walsCode := "nam", iso := "nnm", value := .prefixNodoubleneg }
  , { walsCode := "nnk", iso := "nnk", value := .noSonegv }
  , { walsCode := "nar", iso := "nrb", value := .wordNodoubleneg }
  , { walsCode := "nas", iso := "nas", value := .noSonegv }
  , { walsCode := "nav", iso := "nav", value := .wordNodoubleneg }
  , { walsCode := "ntu", iso := "yrk", value := .wordNodoubleneg }
  , { walsCode := "naj", iso := "aij", value := .wordNodoubleneg }
  , { walsCode := "nep", iso := "npi", value := .noSonegv }
  , { walsCode := "nwd", iso := "new", value := .prefixNodoubleneg }
  , { walsCode := "new", iso := "new", value := .prefixNodoubleneg }
  , { walsCode := "ntj", iso := "ntj", value := .noSonegv }
  , { walsCode := "nga", iso := "nio", value := .wordNodoubleneg }
  , { walsCode := "nti", iso := "niy", value := .noSonegv }
  , { walsCode := "niv", iso := "niv", value := .noSonegv }
  , { walsCode := "noc", iso := "njb", value := .noSonegv }
  , { walsCode := "nbd", iso := "dgl", value := .noSonegv }
  , { walsCode := "nku", iso := "xnz", value := .noSonegv }
  , { walsCode := "nue", iso := "nus", value := .noSonegv }
  , { walsCode := "nyi", iso := "nyi", value := .wordNodoubleneg }
  , { walsCode := "oks", iso := "opm", value := .wordNodoubleneg }
  , { walsCode := "omh", iso := "oma", value := .noSonegv }
  , { walsCode := "ong", iso := "oon", value := .noSonegv }
  , { walsCode := "ori", iso := "tag", value := .prefixNodoubleneg }
  , { walsCode := "oya", iso := "ory", value := .noSonegv }
  , { walsCode := "orh", iso := "hae", value := .prefixOnlywithanotherneg }
  , { walsCode := "osa", iso := "osa", value := .noSonegv }
  , { walsCode := "pno", iso := "pao", value := .noSonegv }
  , { walsCode := "pan", iso := "pan", value := .wordNodoubleneg }
  , { walsCode := "psh", iso := "pst", value := .prefixNodoubleneg }
  , { walsCode := "ptt", iso := "lae", value := .prefixNodoubleneg }
  , { walsCode := "paw", iso := "pwa", value := .noSonegv }
  , { walsCode := "prs", iso := "pes", value := .prefixNodoubleneg }
  , { walsCode := "pba", iso := "pia", value := .wordNodoubleneg }
  , { walsCode := "prh", iso := "myp", value := .noSonegv }
  , { walsCode := "pme", iso := "peb", value := .noSonegv }
  , { walsCode := "pra", iso := "prn", value := .prefixNodoubleneg }
  , { walsCode := "pum", iso := "pmi", value := .prefixNodoubleneg }
  , { walsCode := "prk", iso := "prx", value := .noSonegv }
  , { walsCode := "pae", iso := "pbb", value := .noSonegv }
  , { walsCode := "qim", iso := "qvi", value := .wordNodoubleneg }
  , { walsCode := "ram", iso := "rma", value := .wordNodoubleneg }
  , { walsCode := "rao", iso := "rao", value := .noSonegv }
  , { walsCode := "ras", iso := "ras", value := .prefixNodoubleneg }
  , { walsCode := "raw", iso := "raw", value := .wordNodoubleneg }
  , { walsCode := "res", iso := "rgr", value := .noSonegv }
  , { walsCode := "ret", iso := "tnc", value := .noSonegv }
  , { walsCode := "rum", iso := "klq", value := .noSonegv }
  , { walsCode := "slb", iso := "sbe", value := .noSonegv }
  , { walsCode := "syu", iso := "sll", value := .noSonegv }
  , { walsCode := "sdw", iso := "sad", value := .noSonegv }
  , { walsCode := "stl", iso := "sat", value := .wordNodoubleneg }
  , { walsCode := "snm", iso := "xsu", value := .noSonegv }
  , { walsCode := "sar", iso := "dju", value := .prefixNodoubleneg }
  , { walsCode := "sme", iso := "sif", value := .noSonegv }
  , { walsCode := "smn", iso := "mus", value := .noSonegv }
  , { walsCode := "snt", iso := "set", value := .prefixNodoubleneg }
  , { walsCode := "ser", iso := "sei", value := .prefixNodoubleneg }
  , { walsCode := "shb", iso := "sbf", value := .noSonegv }
  , { walsCode := "shh", iso := "mcd", value := .noSonegv }
  , { walsCode := "she", iso := "xsr", value := .prefixNodoubleneg }
  , { walsCode := "sna", iso := "scl", value := .wordNodoubleneg }
  , { walsCode := "shk", iso := "shp", value := .noSonegv }
  , { walsCode := "shi", iso := "shb", value := .noSonegv }
  , { walsCode := "sia", iso := "snp", value := .noSonegv }
  , { walsCode := "sid", iso := "sid", value := .wordNodoubleneg }
  , { walsCode := "sil", iso := "dau", value := .wordNodoubleneg }
  , { walsCode := "sng", iso := "snc", value := .wordNodoubleneg }
  , { walsCode := "sro", iso := "ssd", value := .noSonegv }
  , { walsCode := "sla", iso := "den", value := .noSonegv }
  , { walsCode := "sod", iso := "gru", value := .prefixNodoubleneg }
  , { walsCode := "som", iso := "som", value := .wordNodoubleneg }
  , { walsCode := "snn", iso := "snk", value := .noSonegv }
  , { walsCode := "srb", iso := "", value := .prefixNodoubleneg }
  , { walsCode := "sup", iso := "spp", value := .noSonegv }
  , { walsCode := "tba", iso := "sst", value := .noSonegv }
  , { walsCode := "tbl", iso := "tnm", value := .prefixOnlywithanotherneg }
  , { walsCode := "trr", iso := "tbg", value := .noSonegv }
  , { walsCode := "taj", iso := "tgk", value := .prefixNodoubleneg }
  , { walsCode := "tak", iso := "tbc", value := .wordNodoubleneg }
  , { walsCode := "tma", iso := "tma", value := .noSonegv }
  , { walsCode := "tam", iso := "taj", value := .wordNodoubleneg }
  , { walsCode := "tml", iso := "tam", value := .noSonegv }
  , { walsCode := "tpt", iso := "tpj", value := .noSonegv }
  , { walsCode := "tao", iso := "tro", value := .noSonegv }
  , { walsCode := "tar", iso := "tae", value := .prefixOnlywithanotherneg }
  , { walsCode := "tau", iso := "tya", value := .wordNodoubleneg }
  , { walsCode := "tel", iso := "tel", value := .noSonegv }
  , { walsCode := "trb", iso := "tfr", value := .noSonegv }
  , { walsCode := "thn", iso := "thf", value := .prefixNodoubleneg }
  , { walsCode := "thu", iso := "tdh", value := .wordOnlywithanotherneg }
  , { walsCode := "tdr", iso := "bod", value := .prefixNodoubleneg }
  , { walsCode := "tib", iso := "bod", value := .prefixNodoubleneg }
  , { walsCode := "tig", iso := "tir", value := .prefixOnlywithanotherneg }
  , { walsCode := "tgr", iso := "tig", value := .prefixNodoubleneg }
  , { walsCode := "tja", iso := "dih", value := .wordOnlywithanotherneg }
  , { walsCode := "trm", iso := "suq", value := .wordOnlywithanotherneg }
  , { walsCode := "twn", iso := "twf", value := .prefixNodoubleneg }
  , { walsCode := "tli", iso := "tli", value := .wordNodoubleneg }
  , { walsCode := "tlo", iso := "tlb", value := .noSonegv }
  , { walsCode := "tod", iso := "sbu", value := .prefixNodoubleneg }
  , { walsCode := "ton", iso := "tqw", value := .noSonegv }
  , { walsCode := "tru", iso := "tpy", value := .noSonegv }
  , { walsCode := "tsf", iso := "cof", value := .noSonegv }
  , { walsCode := "tsz", iso := "ddo", value := .noSonegv }
  , { walsCode := "tgl", iso := "tsj", value := .prefixOptdoubleneg }
  , { walsCode := "ttu", iso := "bbl", value := .wordNodoubleneg }
  , { walsCode := "tbu", iso := "", value := .noSonegv }
  , { walsCode := "tul", iso := "tcy", value := .noSonegv }
  , { walsCode := "tnn", iso := "tvu", value := .noSonegv }
  , { walsCode := "tun", iso := "tun", value := .noSonegv }
  , { walsCode := "tur", iso := "tur", value := .noSonegv }
  , { walsCode := "tte", iso := "tta", value := .prefixOnlywithanotherneg }
  , { walsCode := "tuv", iso := "tyv", value := .noSonegv }
  , { walsCode := "tuy", iso := "tue", value := .noSonegv }
  , { walsCode := "tye", iso := "woa", value := .wordOnlywithanotherneg }
  , { walsCode := "tsh", iso := "par", value := .noSonegv }
  , { walsCode := "uby", iso := "uby", value := .prefixNodoubleneg }
  , { walsCode := "udi", iso := "udi", value := .prefixNodoubleneg }
  , { walsCode := "udh", iso := "ude", value := .wordNodoubleneg }
  , { walsCode := "udm", iso := "udm", value := .noSonegv }
  , { walsCode := "una", iso := "mtg", value := .wordNodoubleneg }
  , { walsCode := "urd", iso := "urd", value := .wordNodoubleneg }
  , { walsCode := "urk", iso := "urb", value := .noSonegv }
  , { walsCode := "usa", iso := "wnu", value := .wordNodoubleneg }
  , { walsCode := "usr", iso := "usa", value := .prefixNodoubleneg }
  , { walsCode := "uyg", iso := "uig", value := .noSonegv }
  , { walsCode := "uzb", iso := "", value := .noSonegv }
  , { walsCode := "vai", iso := "vai", value := .noSonegv }
  , { walsCode := "wag", iso := "waq", value := .wordNodoubleneg }
  , { walsCode := "wak", iso := "wbl", value := .wordNodoubleneg }
  , { walsCode := "wbn", iso := "wms", value := .noSonegv }
  , { walsCode := "wme", iso := "wme", value := .prefixNodoubleneg }
  , { walsCode := "wna", iso := "wan", value := .noSonegv }
  , { walsCode := "wao", iso := "auc", value := .noSonegv }
  , { walsCode := "wap", iso := "wao", value := .noSonegv }
  , { walsCode := "wlw", iso := "wrb", value := .noSonegv }
  , { walsCode := "was", iso := "was", value := .noSonegv }
  , { walsCode := "wsk", iso := "wsk", value := .wordNodoubleneg }
  , { walsCode := "way", iso := "oym", value := .prefixOnlywithanotherneg }
  , { walsCode := "wic", iso := "wic", value := .noSonegv }
  , { walsCode := "wly", iso := "wal", value := .noSonegv }
  , { walsCode := "wom", iso := "wmx", value := .noSonegv }
  , { walsCode := "ygr", iso := "ygr", value := .prefixNodoubleneg }
  , { walsCode := "ykt", iso := "sah", value := .noSonegv }
  , { walsCode := "yam", iso := "yaa", value := .noSonegv }
  , { walsCode := "yqy", iso := "jaq", value := .prefixOnlywithanotherneg }
  , { walsCode := "yaq", iso := "yaq", value := .noSonegv }
  , { walsCode := "yar", iso := "yrb", value := .noSonegv }
  , { walsCode := "yid", iso := "yii", value := .wordNodoubleneg }
  , { walsCode := "yko", iso := "yux", value := .prefixNodoubleneg }
  , { walsCode := "ytu", iso := "ykg", value := .prefixNodoubleneg }
  , { walsCode := "yuw", iso := "kld", value := .noSonegv }
  , { walsCode := "zay", iso := "zay", value := .noSonegv }
  , { walsCode := "zaz", iso := "diq", value := .prefixNodoubleneg }
  , { walsCode := "zun", iso := "zun", value := .noSonegv }
  , { walsCode := "rgc", iso := "jya", value := .prefixNodoubleneg }
  , { walsCode := "eme", iso := "eme", value := .prefixOnlywithanotherneg }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144R
