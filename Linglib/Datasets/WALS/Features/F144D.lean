import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144D: The Position of Negative Morphemes in SVO Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144D`.

Chapter 144, 463 languages.
-/

namespace Datasets.WALS.F144D

/-- WALS 144D values. -/
inductive PositionOfNegativeMorphemesInSvoLanguages where
  /-- NegSVO (4 languages). -/
  | negsvo
  /-- SNegVO (111 languages). -/
  | snegvo
  /-- SVNegO (2 languages). -/
  | svnego
  /-- SVONeg (81 languages). -/
  | svoneg
  /-- S[Neg-V]O (67 languages). -/
  | sNegVO
  /-- S[V-Neg]O (12 languages). -/
  | sVNegO
  /-- SVO&Tone (1 languages). -/
  | svoTone
  /-- VSO but NegSVO (6 languages). -/
  | vsoButNegsvo
  /-- SVO/SOV but SVONeg (5 languages). -/
  | svoSovButSvoneg
  /-- SOV/SOV but SNegVO (1 languages). -/
  | sovSovButSnegvo
  /-- Other NegV (26 languages). -/
  | otherNegv
  /-- Other VNeg (8 languages). -/
  | otherVneg
  /-- More than one construction (48 languages). -/
  | moreThanOneConstruction
  /-- ObligNeg (56 languages). -/
  | obligneg
  /-- OptNeg (35 languages). -/
  | optneg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144D dataset (463 languages). -/
def allData : List (Datapoint PositionOfNegativeMorphemesInSvoLanguages) :=
  [ { walsCode := "xam", iso := "xam", value := .otherNegv }
  , { walsCode := "huc", iso := "huc", value := .snegvo }
  , { walsCode := "abi", iso := "axb", value := .otherNegv }
  , { walsCode := "abu", iso := "kgr", value := .obligneg }
  , { walsCode := "acg", iso := "aca", value := .snegvo }
  , { walsCode := "acl", iso := "ach", value := .moreThanOneConstruction }
  , { walsCode := "acm", iso := "acv", value := .otherNegv }
  , { walsCode := "adi", iso := "adj", value := .sVNegO }
  , { walsCode := "adz", iso := "adz", value := .optneg }
  , { walsCode := "agh", iso := "agq", value := .moreThanOneConstruction }
  , { walsCode := "aja", iso := "aja", value := .svoneg }
  , { walsCode := "ajg", iso := "ajg", value := .moreThanOneConstruction }
  , { walsCode := "akn", iso := "aka", value := .sNegVO }
  , { walsCode := "alb", iso := "sqi", value := .snegvo }
  , { walsCode := "aln", iso := "alp", value := .svoneg }
  , { walsCode := "aml", iso := "omb", value := .obligneg }
  , { walsCode := "amq", iso := "amk", value := .svoneg }
  , { walsCode := "anc", iso := "anc", value := .svoneg }
  , { walsCode := "anu", iso := "cko", value := .svnego }
  , { walsCode := "ane", iso := "anz", value := .svoneg }
  , { walsCode := "apu", iso := "apu", value := .moreThanOneConstruction }
  , { walsCode := "aeg", iso := "arz", value := .optneg }
  , { walsCode := "arg", iso := "afb", value := .snegvo }
  , { walsCode := "arq", iso := "acm", value := .sNegVO }
  , { walsCode := "arj", iso := "afb", value := .snegvo }
  , { walsCode := "asy", iso := "apc", value := .moreThanOneConstruction }
  , { walsCode := "aab", iso := "aah", value := .svoneg }
  , { walsCode := "arp", iso := "ape", value := .optneg }
  , { walsCode := "arm", iso := "hye", value := .moreThanOneConstruction }
  , { walsCode := "alk", iso := "apr", value := .svoneg }
  , { walsCode := "aro", iso := "aia", value := .snegvo }
  , { walsCode := "au", iso := "avt", value := .moreThanOneConstruction }
  , { walsCode := "bbl", iso := "bvx", value := .sNegVO }
  , { walsCode := "bab", iso := "bav", value := .obligneg }
  , { walsCode := "bag", iso := "bmi", value := .svoneg }
  , { walsCode := "bgr", iso := "fuu", value := .svoneg }
  , { walsCode := "bai", iso := "bca", value := .snegvo }
  , { walsCode := "bwc", iso := "bdr", value := .moreThanOneConstruction }
  , { walsCode := "bak", iso := "bkc", value := .svoneg }
  , { walsCode := "bka", iso := "bdh", value := .svoneg }
  , { walsCode := "bku", iso := "bri", value := .sNegVO }
  , { walsCode := "blz", iso := "", value := .sNegVO }
  , { walsCode := "bvi", iso := "", value := .snegvo }
  , { walsCode := "bnn", iso := "bcm", value := .snegvo }
  , { walsCode := "ble", iso := "bci", value := .obligneg }
  , { walsCode := "bar", iso := "bfa", value := .snegvo }
  , { walsCode := "bae", iso := "bae", value := .snegvo }
  , { walsCode := "bas", iso := "bas", value := .otherVneg }
  , { walsCode := "bkr", iso := "btx", value := .moreThanOneConstruction }
  , { walsCode := "bch", iso := "shy", value := .moreThanOneConstruction }
  , { walsCode := "brf", iso := "rif", value := .snegvo }
  , { walsCode := "ber", iso := "wti", value := .sNegVO }
  , { walsCode := "bik", iso := "bhw", value := .svoneg }
  , { walsCode := "bid", iso := "bid", value := .obligneg }
  , { walsCode := "bia", iso := "bip", value := .sNegVO }
  , { walsCode := "bmb", iso := "bim", value := .optneg }
  , { walsCode := "bni", iso := "bin", value := .snegvo }
  , { walsCode := "bii", iso := "bzr", value := .moreThanOneConstruction }
  , { walsCode := "bir", iso := "bom", value := .svoneg }
  , { walsCode := "bob", iso := "bni", value := .obligneg }
  , { walsCode := "bol", iso := "bli", value := .optneg }
  , { walsCode := "bgo", iso := "bot", value := .optneg }
  , { walsCode := "btk", iso := "lbk", value := .moreThanOneConstruction }
  , { walsCode := "bra", iso := "brb", value := .snegvo }
  , { walsCode := "bre", iso := "bre", value := .obligneg }
  , { walsCode := "bud", iso := "bdm", value := .svoneg }
  , { walsCode := "bug", iso := "bug", value := .otherNegv }
  , { walsCode := "bul", iso := "bul", value := .snegvo }
  , { walsCode := "buy", iso := "bwu", value := .obligneg }
  , { walsCode := "bum", iso := "tkw", value := .svoneg }
  , { walsCode := "pnu", iso := "buh", value := .otherNegv }
  , { walsCode := "brn", iso := "bds", value := .sVNegO }
  , { walsCode := "bsh", iso := "buf", value := .sNegVO }
  , { walsCode := "cnt", iso := "yue", value := .snegvo }
  , { walsCode := "ctl", iso := "cat", value := .optneg }
  , { walsCode := "cga", iso := "old", value := .sNegVO }
  , { walsCode := "cai", iso := "suq", value := .moreThanOneConstruction }
  , { walsCode := "chw", iso := "cja", value := .svoneg }
  , { walsCode := "cic", iso := "nya", value := .sNegVO }
  , { walsCode := "cmy", iso := "chf", value := .snegvo }
  , { walsCode := "chr", iso := "crw", value := .optneg }
  , { walsCode := "coc", iso := "cod", value := .negsvo }
  , { walsCode := "cop", iso := "cop", value := .optneg }
  , { walsCode := "cze", iso := "ces", value := .sNegVO }
  , { walsCode := "dga", iso := "dga", value := .snegvo }
  , { walsCode := "dgb", iso := "dag", value := .snegvo }
  , { walsCode := "dsh", iso := "dan", value := .moreThanOneConstruction }
  , { walsCode := "deg", iso := "deg", value := .obligneg }
  , { walsCode := "dio", iso := "dyo", value := .sVNegO }
  , { walsCode := "dgo", iso := "doo", value := .svoSovButSvoneg }
  , { walsCode := "doy", iso := "dow", value := .obligneg }
  , { walsCode := "dre", iso := "dhv", value := .moreThanOneConstruction }
  , { walsCode := "dua", iso := "dua", value := .snegvo }
  , { walsCode := "duk", iso := "dud", value := .svoneg }
  , { walsCode := "dma", iso := "dma", value := .optneg }
  , { walsCode := "dut", iso := "nld", value := .moreThanOneConstruction }
  , { walsCode := "ebi", iso := "igb", value := .snegvo }
  , { walsCode := "erk", iso := "erk", value := .obligneg }
  , { walsCode := "ega", iso := "ega", value := .svoneg }
  , { walsCode := "eko", iso := "eko", value := .obligneg }
  , { walsCode := "egn", iso := "enn", value := .svoTone }
  , { walsCode := "eno", iso := "eno", value := .otherNegv }
  , { walsCode := "eng", iso := "eng", value := .snegvo }
  , { walsCode := "err", iso := "erg", value := .sNegVO }
  , { walsCode := "est", iso := "ekk", value := .snegvo }
  , { walsCode := "ewe", iso := "ewe", value := .obligneg }
  , { walsCode := "ewo", iso := "ewo", value := .optneg }
  , { walsCode := "fin", iso := "fin", value := .snegvo }
  , { walsCode := "fon", iso := "fon", value := .snegvo }
  , { walsCode := "fre", iso := "fra", value := .optneg }
  , { walsCode := "fua", iso := "fub", value := .sVNegO }
  , { walsCode := "fut", iso := "fut", value := .snegvo }
  , { walsCode := "fye", iso := "pym", value := .optneg }
  , { walsCode := "gbs", iso := "gso", value := .svoneg }
  , { walsCode := "gbb", iso := "gbp", value := .optneg }
  , { walsCode := "gla", iso := "gqu", value := .svoneg }
  , { walsCode := "ger", iso := "deu", value := .moreThanOneConstruction }
  , { walsCode := "goe", iso := "ank", value := .svoneg }
  , { walsCode := "gok", iso := "gkn", value := .snegvo }
  , { walsCode := "grk", iso := "ell", value := .moreThanOneConstruction }
  , { walsCode := "gua", iso := "gug", value := .obligneg }
  , { walsCode := "gud", iso := "gde", value := .vsoButNegsvo }
  , { walsCode := "gul", iso := "kcm", value := .svoneg }
  , { walsCode := "gmz", iso := "guk", value := .otherVneg }
  , { walsCode := "gnb", iso := "wlg", value := .obligneg }
  , { walsCode := "gwa", iso := "gbr", value := .obligneg }
  , { walsCode := "gwo", iso := "kcg", value := .svoneg }
  , { walsCode := "ga", iso := "gaa", value := .sVNegO }
  , { walsCode := "gku", iso := "pue", value := .moreThanOneConstruction }
  , { walsCode := "hak", iso := "hak", value := .snegvo }
  , { walsCode := "hal", iso := "hla", value := .obligneg }
  , { walsCode := "hat", iso := "had", value := .svoneg }
  , { walsCode := "hau", iso := "hau", value := .optneg }
  , { walsCode := "hya", iso := "hay", value := .sNegVO }
  , { walsCode := "heb", iso := "heb", value := .snegvo }
  , { walsCode := "heh", iso := "heh", value := .sNegVO }
  , { walsCode := "lic", iso := "lic", value := .snegvo }
  , { walsCode := "hmo", iso := "hnj", value := .snegvo }
  , { walsCode := "hol", iso := "hoo", value := .sNegVO }
  , { walsCode := "htc", iso := "hus", value := .snegvo }
  , { walsCode := "hve", iso := "huv", value := .otherNegv }
  , { walsCode := "hnd", iso := "hke", value := .sNegVO }
  , { walsCode := "hun", iso := "hun", value := .sovSovButSnegvo }
  , { walsCode := "iaa", iso := "iai", value := .snegvo }
  , { walsCode := "iba", iso := "iba", value := .otherNegv }
  , { walsCode := "ice", iso := "isl", value := .moreThanOneConstruction }
  , { walsCode := "mxe", iso := "mxe", value := .optneg }
  , { walsCode := "ifm", iso := "ifm", value := .obligneg }
  , { walsCode := "ige", iso := "ige", value := .svoneg }
  , { walsCode := "ila", iso := "ilb", value := .sNegVO }
  , { walsCode := "ina", iso := "szp", value := .optneg }
  , { walsCode := "ind", iso := "ind", value := .snegvo }
  , { walsCode := "igs", iso := "tbi", value := .svoneg }
  , { walsCode := "iqu", iso := "iqu", value := .negsvo }
  , { walsCode := "irr", iso := "irh", value := .svoneg }
  , { walsCode := "ita", iso := "ita", value := .snegvo }
  , { walsCode := "kwy", iso := "yom", value := .obligneg }
  , { walsCode := "jar", iso := "izr", value := .svoneg }
  , { walsCode := "izi", iso := "izz", value := .obligneg }
  , { walsCode := "jab", iso := "jae", value := .svoneg }
  , { walsCode := "juk", iso := "jbu", value := .svoneg }
  , { walsCode := "jmo", iso := "bex", value := .svoneg }
  , { walsCode := "juh", iso := "ktz", value := .snegvo }
  , { walsCode := "kby", iso := "kbp", value := .sNegVO }
  , { walsCode := "kdw", iso := "kbc", value := .sNegVO }
  , { walsCode := "kad", iso := "xtc", value := .otherNegv }
  , { walsCode := "kba", iso := "kam", value := .sNegVO }
  , { walsCode := "kan", iso := "ogo", value := .snegvo }
  , { walsCode := "knk", iso := "kna", value := .obligneg }
  , { walsCode := "kar", iso := "kah", value := .svoneg }
  , { walsCode := "kbw", iso := "bwe", value := .obligneg }
  , { walsCode := "kpw", iso := "kjp", value := .svoneg }
  , { walsCode := "ksg", iso := "ksw", value := .obligneg }
  , { walsCode := "kas", iso := "kas", value := .sVNegO }
  , { walsCode := "ksn", iso := "cog", value := .snegvo }
  , { walsCode := "ktc", iso := "xtc", value := .otherNegv }
  , { walsCode := "ktl", iso := "kcr", value := .obligneg }
  , { walsCode := "kau", iso := "pss", value := .otherVneg }
  , { walsCode := "kyl", iso := "eky", value := .svoneg }
  , { walsCode := "kel", iso := "sbc", value := .svoneg }
  , { walsCode := "ken", iso := "kyq", value := .svoneg }
  , { walsCode := "ker", iso := "ker", value := .svoneg }
  , { walsCode := "khs", iso := "kha", value := .snegvo }
  , { walsCode := "khm", iso := "khm", value := .snegvo }
  , { walsCode := "kmu", iso := "kjg", value := .otherNegv }
  , { walsCode := "khn", iso := "kkh", value := .otherNegv }
  , { walsCode := "kik", iso := "kik", value := .sNegVO }
  , { walsCode := "klv", iso := "kij", value := .moreThanOneConstruction }
  , { walsCode := "kil", iso := "lub", value := .sNegVO }
  , { walsCode := "kga", iso := "zga", value := .sNegVO }
  , { walsCode := "kin", iso := "kin", value := .sNegVO }
  , { walsCode := "kir", iso := "cme", value := .snegvo }
  , { walsCode := "kis", iso := "kss", value := .obligneg }
  , { walsCode := "koe", iso := "xwg", value := .moreThanOneConstruction }
  , { walsCode := "xbi", iso := "xbi", value := .snegvo }
  , { walsCode := "kzy", iso := "kpv", value := .snegvo }
  , { walsCode := "kom", iso := "xom", value := .snegvo }
  , { walsCode := "kon", iso := "kng", value := .obligneg }
  , { walsCode := "kni", iso := "kma", value := .snegvo }
  , { walsCode := "kfe", iso := "kfz", value := .snegvo }
  , { walsCode := "kos", iso := "kos", value := .snegvo }
  , { walsCode := "kch", iso := "khq", value := .snegvo }
  , { walsCode := "kre", iso := "krs", value := .optneg }
  , { walsCode := "kwa", iso := "kwd", value := .snegvo }
  , { walsCode := "kwn", iso := "kwn", value := .otherNegv }
  , { walsCode := "kwz", iso := "xwa", value := .moreThanOneConstruction }
  , { walsCode := "laa", iso := "gdm", value := .svoneg }
  , { walsCode := "lab", iso := "lbu", value := .svoneg }
  , { walsCode := "lac", iso := "lac", value := .moreThanOneConstruction }
  , { walsCode := "lag", iso := "kot", value := .svoneg }
  , { walsCode := "lmh", iso := "slp", value := .svoneg }
  , { walsCode := "lmu", iso := "lmu", value := .obligneg }
  , { walsCode := "lmp", iso := "ljp", value := .sNegVO }
  , { walsCode := "lgi", iso := "lag", value := .sNegVO }
  , { walsCode := "lan", iso := "laj", value := .snegvo }
  , { walsCode := "lao", iso := "lao", value := .snegvo }
  , { walsCode := "lat", iso := "lav", value := .sNegVO }
  , { walsCode := "leb", iso := "agh", value := .sNegVO }
  , { walsCode := "leg", iso := "lea", value := .sNegVO }
  , { walsCode := "lel", iso := "lln", value := .svoneg }
  , { walsCode := "llm", iso := "lef", value := .sNegVO }
  , { walsCode := "len", iso := "tnl", value := .obligneg }
  , { walsCode := "ldu", iso := "led", value := .moreThanOneConstruction }
  , { walsCode := "let", iso := "lti", value := .sNegVO }
  , { walsCode := "lew", iso := "lww", value := .optneg }
  , { walsCode := "lnd", iso := "liy", value := .obligneg }
  , { walsCode := "lin", iso := "lin", value := .svoneg }
  , { walsCode := "lit", iso := "lit", value := .sNegVO }
  , { walsCode := "lgt", iso := "log", value := .svoSovButSvoneg }
  , { walsCode := "ara", iso := "arw", value := .otherVneg }
  , { walsCode := "ldo", iso := "bdu", value := .sNegVO }
  , { walsCode := "lon", iso := "los", value := .svoneg }
  , { walsCode := "lou", iso := "loj", value := .obligneg }
  , { walsCode := "luc", iso := "lch", value := .sNegVO }
  , { walsCode := "lug", iso := "lgg", value := .svoSovButSvoneg }
  , { walsCode := "lbu", iso := "lun", value := .obligneg }
  , { walsCode := "luo", iso := "luo", value := .moreThanOneConstruction }
  , { walsCode := "kkv", iso := "khl", value := .svoneg }
  , { walsCode := "luv", iso := "lue", value := .obligneg }
  , { walsCode := "ma", iso := "msj", value := .obligneg }
  , { walsCode := "mad", iso := "mhi", value := .svoSovButSvoneg }
  , { walsCode := "mcd", iso := "mkd", value := .snegvo }
  , { walsCode := "mda", iso := "mxu", value := .svoneg }
  , { walsCode := "mae", iso := "mmw", value := .snegvo }
  , { walsCode := "maj", iso := "mpe", value := .vsoButNegsvo }
  , { walsCode := "mkz", iso := "mcp", value := .obligneg }
  , { walsCode := "mkd", iso := "kde", value := .sNegVO }
  , { walsCode := "mua", iso := "mgh", value := .sNegVO }
  , { walsCode := "mlu", iso := "mgl", value := .svoneg }
  , { walsCode := "mlg", iso := "", value := .sVNegO }
  , { walsCode := "mmv", iso := "mdi", value := .sNegVO }
  , { walsCode := "mnd", iso := "cmn", value := .snegvo }
  , { walsCode := "mmb", iso := "mna", value := .svoneg }
  , { walsCode := "mbt", iso := "mdj", value := .moreThanOneConstruction }
  , { walsCode := "mao", iso := "mri", value := .vsoButNegsvo }
  , { walsCode := "map", iso := "arn", value := .sVNegO }
  , { walsCode := "mrg", iso := "mrt", value := .svoneg }
  , { walsCode := "mrq", iso := "", value := .vsoButNegsvo }
  , { walsCode := "mrt", iso := "vma", value := .snegvo }
  , { walsCode := "mas", iso := "mcn", value := .svoneg }
  , { walsCode := "msk", iso := "jle", value := .obligneg }
  , { walsCode := "mtb", iso := "mgw", value := .moreThanOneConstruction }
  , { walsCode := "mau", iso := "mph", value := .snegvo }
  , { walsCode := "may", iso := "ayz", value := .svoneg }
  , { walsCode := "myg", iso := "mdm", value := .svoneg }
  , { walsCode := "mba", iso := "mfc", value := .otherVneg }
  , { walsCode := "mhu", iso := "lnb", value := .snegvo }
  , { walsCode := "mbr", iso := "mpk", value := .svoneg }
  , { walsCode := "mby", iso := "myb", value := .svoneg }
  , { walsCode := "mbe", iso := "mdt", value := .optneg }
  , { walsCode := "mdo", iso := "gmm", value := .svoneg }
  , { walsCode := "mbm", iso := "mdd", value := .svoneg }
  , { walsCode := "meh", iso := "gdq", value := .moreThanOneConstruction }
  , { walsCode := "mea", iso := "mej", value := .svoneg }
  , { walsCode := "mie", iso := "ium", value := .otherNegv }
  , { walsCode := "hna", iso := "hna", value := .svoneg }
  , { walsCode := "miy", iso := "mkf", value := .obligneg }
  , { walsCode := "mcv", iso := "moc", value := .sNegVO }
  , { walsCode := "mok", iso := "mkj", value := .snegvo }
  , { walsCode := "mon", iso := "mnw", value := .snegvo }
  , { walsCode := "mga", iso := "ndt", value := .moreThanOneConstruction }
  , { walsCode := "moo", iso := "mos", value := .obligneg }
  , { walsCode := "mor", iso := "mhz", value := .svoneg }
  , { walsCode := "moe", iso := "myv", value := .otherNegv }
  , { walsCode := "mro", iso := "mor", value := .snegvo }
  , { walsCode := "mou", iso := "mgd", value := .svoSovButSvoneg }
  , { walsCode := "mos", iso := "cas", value := .moreThanOneConstruction }
  , { walsCode := "mpu", iso := "akc", value := .svoneg }
  , { walsCode := "aoj", iso := "aoj", value := .obligneg }
  , { walsCode := "mum", iso := "mzm", value := .optneg }
  , { walsCode := "mna", iso := "mnb", value := .snegvo }
  , { walsCode := "mdg", iso := "mua", value := .svoneg }
  , { walsCode := "mgk", iso := "mhk", value := .optneg }
  , { walsCode := "mup", iso := "sur", value := .optneg }
  , { walsCode := "mgu", iso := "mug", value := .svoneg }
  , { walsCode := "msm", iso := "msu", value := .otherVneg }
  , { walsCode := "mus", iso := "emi", value := .snegvo }
  , { walsCode := "mut", iso := "css", value := .snegvo }
  , { walsCode := "mwe", iso := "mwe", value := .sNegVO }
  , { walsCode := "mwo", iso := "mlv", value := .obligneg }
  , { walsCode := "nad", iso := "mbj", value := .moreThanOneConstruction }
  , { walsCode := "nhm", iso := "ncl", value := .snegvo }
  , { walsCode := "nht", iso := "nhg", value := .otherNegv }
  , { walsCode := "nak", iso := "nak", value := .snegvo }
  , { walsCode := "nal", iso := "nal", value := .snegvo }
  , { walsCode := "ncm", iso := "bud", value := .snegvo }
  , { walsCode := "ndb", iso := "nde", value := .obligneg }
  , { walsCode := "ndo", iso := "ndo", value := .otherNegv }
  , { walsCode := "ndu", iso := "nmd", value := .obligneg }
  , { walsCode := "ndt", iso := "ndv", value := .sVNegO }
  , { walsCode := "ndy", iso := "djk", value := .snegvo }
  , { walsCode := "neh", iso := "nsn", value := .snegvo }
  , { walsCode := "nne", iso := "nen", value := .snegvo }
  , { walsCode := "ngd", iso := "nxg", value := .otherNegv }
  , { walsCode := "ngm", iso := "sba", value := .svoneg }
  , { walsCode := "ngw", iso := "nxn", value := .negsvo }
  , { walsCode := "nbm", iso := "nbm", value := .svoneg }
  , { walsCode := "nti", iso := "niy", value := .moreThanOneConstruction }
  , { walsCode := "ngz", iso := "ngi", value := .svoneg }
  , { walsCode := "ngo", iso := "ngo", value := .moreThanOneConstruction }
  , { walsCode := "ngu", iso := "llp", value := .snegvo }
  , { walsCode := "nke", iso := "isi", value := .optneg }
  , { walsCode := "nkn", iso := "nko", value := .sNegVO }
  , { walsCode := "nko", iso := "cgg", value := .sNegVO }
  , { walsCode := "non", iso := "nhu", value := .obligneg }
  , { walsCode := "noo", iso := "snf", value := .sVNegO }
  , { walsCode := "nor", iso := "nor", value := .moreThanOneConstruction }
  , { walsCode := "nse", iso := "nse", value := .moreThanOneConstruction }
  , { walsCode := "nto", iso := "nto", value := .sNegVO }
  , { walsCode := "nua", iso := "nxl", value := .svoneg }
  , { walsCode := "nun", iso := "nut", value := .snegvo }
  , { walsCode := "nup", iso := "nup", value := .svoneg }
  , { walsCode := "nza", iso := "nzk", value := .svoneg }
  , { walsCode := "obo", iso := "ann", value := .sNegVO }
  , { walsCode := "ocu", iso := "ocu", value := .sNegVO }
  , { walsCode := "obg", iso := "ogu", value := .sNegVO }
  , { walsCode := "olo", iso := "ong", value := .svoneg }
  , { walsCode := "one", iso := "aun", value := .optneg }
  , { walsCode := "otr", iso := "otr", value := .obligneg }
  , { walsCode := "paa", iso := "pqa", value := .optneg }
  , { walsCode := "pkn", iso := "drl", value := .negsvo }
  , { walsCode := "pms", iso := "pma", value := .sNegVO }
  , { walsCode := "pal", iso := "pau", value := .snegvo }
  , { walsCode := "plg", iso := "pll", value := .snegvo }
  , { walsCode := "png", iso := "pbr", value := .sNegVO }
  , { walsCode := "pre", iso := "asa", value := .sNegVO }
  , { walsCode := "pat", iso := "ptp", value := .svoneg }
  , { walsCode := "plh", iso := "plh", value := .optneg }
  , { walsCode := "pau", iso := "pad", value := .moreThanOneConstruction }
  , { walsCode := "per", iso := "pip", value := .obligneg }
  , { walsCode := "pga", iso := "plg", value := .sNegVO }
  , { walsCode := "pog", iso := "poy", value := .otherVneg }
  , { walsCode := "poh", iso := "pon", value := .snegvo }
  , { walsCode := "pol", iso := "pol", value := .snegvo }
  , { walsCode := "zqs", iso := "poi", value := .snegvo }
  , { walsCode := "psw", iso := "psw", value := .sNegVO }
  , { walsCode := "por", iso := "por", value := .snegvo }
  , { walsCode := "pul", iso := "puw", value := .snegvo }
  , { walsCode := "pur", iso := "tsz", value := .otherNegv }
  , { walsCode := "rag", iso := "lml", value := .obligneg }
  , { walsCode := "rim", iso := "rim", value := .sNegVO }
  , { walsCode := "rwe", iso := "rmw", value := .optneg }
  , { walsCode := "rom", iso := "ron", value := .snegvo }
  , { walsCode := "rsu", iso := "roh", value := .otherVneg }
  , { walsCode := "ron", iso := "cla", value := .svoneg }
  , { walsCode := "rot", iso := "rtm", value := .obligneg }
  , { walsCode := "rny", iso := "nyn", value := .sNegVO }
  , { walsCode := "rru", iso := "nyo", value := .sNegVO }
  , { walsCode := "rus", iso := "rus", value := .snegvo }
  , { walsCode := "sno", iso := "sme", value := .otherNegv }
  , { walsCode := "sah", iso := "saj", value := .moreThanOneConstruction }
  , { walsCode := "sak", iso := "sku", value := .sNegVO }
  , { walsCode := "sal", iso := "sln", value := .obligneg }
  , { walsCode := "san", iso := "sag", value := .svoneg }
  , { walsCode := "sgu", iso := "snq", value := .sNegVO }
  , { walsCode := "sap", iso := "spu", value := .snegvo }
  , { walsCode := "srd", iso := "sro", value := .snegvo }
  , { walsCode := "sed", iso := "sed", value := .snegvo }
  , { walsCode := "sgl", iso := "szg", value := .obligneg }
  , { walsCode := "scr", iso := "hbs", value := .otherNegv }
  , { walsCode := "ses", iso := "sot", value := .otherNegv }
  , { walsCode := "shm", iso := "ksb", value := .sNegVO }
  , { walsCode := "sht", iso := "shj", value := .svoneg }
  , { walsCode := "shl", iso := "shk", value := .snegvo }
  , { walsCode := "shn", iso := "sna", value := .sNegVO }
  , { walsCode := "sir", iso := "sjr", value := .snegvo }
  , { walsCode := "sio", iso := "xsi", value := .svoneg }
  , { walsCode := "ssa", iso := "sil", value := .snegvo }
  , { walsCode := "sis", iso := "baa", value := .snegvo }
  , { walsCode := "slo", iso := "slv", value := .snegvo }
  , { walsCode := "sob", iso := "sob", value := .snegvo }
  , { walsCode := "son", iso := "sov", value := .otherNegv }
  , { walsCode := "stn", iso := "nso", value := .obligneg }
  , { walsCode := "sgb", iso := "mnx", value := .svoneg }
  , { walsCode := "spa", iso := "spa", value := .snegvo }
  , { walsCode := "sre", iso := "kpm", value := .snegvo }
  , { walsCode := "sti", iso := "", value := .snegvo }
  , { walsCode := "sud", iso := "tgo", value := .otherNegv }
  , { walsCode := "skm", iso := "suk", value := .obligneg }
  , { walsCode := "sul", iso := "sua", value := .sNegVO }
  , { walsCode := "sun", iso := "sun", value := .snegvo }
  , { walsCode := "swa", iso := "swh", value := .sNegVO }
  , { walsCode := "swe", iso := "swe", value := .moreThanOneConstruction }
  , { walsCode := "tab", iso := "mky", value := .svoneg }
  , { walsCode := "tbw", iso := "tap", value := .sNegVO }
  , { walsCode := "taf", iso := "sps", value := .snegvo }
  , { walsCode := "tal", iso := "tlj", value := .sNegVO }
  , { walsCode := "tmm", iso := "mla", value := .snegvo }
  , { walsCode := "tan", iso := "tan", value := .sVNegO }
  , { walsCode := "tmn", iso := "teq", value := .optneg }
  , { walsCode := "tmr", iso := "tea", value := .snegvo }
  , { walsCode := "tne", iso := "tem", value := .sVNegO }
  , { walsCode := "ten", iso := "tex", value := .vsoButNegsvo }
  , { walsCode := "teo", iso := "tio", value := .obligneg }
  , { walsCode := "tee", iso := "tee", value := .moreThanOneConstruction }
  , { walsCode := "tep", iso := "tpt", value := .otherNegv }
  , { walsCode := "ter", iso := "ttr", value := .optneg }
  , { walsCode := "tes", iso := "teo", value := .vsoButNegsvo }
  , { walsCode := "tet", iso := "tll", value := .sNegVO }
  , { walsCode := "ttn", iso := "tet", value := .snegvo }
  , { walsCode := "tha", iso := "tha", value := .snegvo }
  , { walsCode := "tid", iso := "tvo", value := .optneg }
  , { walsCode := "tgk", iso := "tgc", value := .snegvo }
  , { walsCode := "tin", iso := "cir", value := .moreThanOneConstruction }
  , { walsCode := "tiv", iso := "tiv", value := .svoneg }
  , { walsCode := "twn", iso := "twf", value := .moreThanOneConstruction }
  , { walsCode := "tiw", iso := "tiw", value := .snegvo }
  , { walsCode := "tob", iso := "tob", value := .moreThanOneConstruction }
  , { walsCode := "tla", iso := "ksd", value := .otherNegv }
  , { walsCode := "toz", iso := "toi", value := .sNegVO }
  , { walsCode := "ton", iso := "tqw", value := .moreThanOneConstruction }
  , { walsCode := "tru", iso := "tpy", value := .moreThanOneConstruction }
  , { walsCode := "tki", iso := "bag", value := .sNegVO }
  , { walsCode := "tpr", iso := "tui", value := .svoneg }
  , { walsCode := "tzu", iso := "tzj", value := .moreThanOneConstruction }
  , { walsCode := "ukr", iso := "ukr", value := .snegvo }
  , { walsCode := "uld", iso := "udl", value := .svoneg }
  , { walsCode := "uli", iso := "uli", value := .snegvo }
  , { walsCode := "url", iso := "urk", value := .snegvo }
  , { walsCode := "urt", iso := "urt", value := .optneg }
  , { walsCode := "ven", iso := "ven", value := .sNegVO }
  , { walsCode := "vie", iso := "vie", value := .snegvo }
  , { walsCode := "vnm", iso := "vnm", value := .obligneg }
  , { walsCode := "wal", iso := "van", value := .snegvo }
  , { walsCode := "wrk", iso := "gae", value := .obligneg }
  , { walsCode := "wrm", iso := "wsa", value := .svoneg }
  , { walsCode := "wrn", iso := "wnd", value := .optneg }
  , { walsCode := "wma", iso := "mqs", value := .svoneg }
  , { walsCode := "wch", iso := "mzh", value := .moreThanOneConstruction }
  , { walsCode := "wol", iso := "woe", value := .snegvo }
  , { walsCode := "wlf", iso := "wol", value := .moreThanOneConstruction }
  , { walsCode := "xho", iso := "xho", value := .sNegVO }
  , { walsCode := "xar", iso := "ane", value := .snegvo }
  , { walsCode := "yao", iso := "yao", value := .sNegVO }
  , { walsCode := "yin", iso := "yij", value := .snegvo }
  , { walsCode := "yng", iso := "yia", value := .snegvo }
  , { walsCode := "yor", iso := "yor", value := .snegvo }
  , { walsCode := "yuk", iso := "gcd", value := .obligneg }
  , { walsCode := "yul", iso := "yul", value := .svnego }
  , { walsCode := "zan", iso := "zne", value := .obligneg }
  , { walsCode := "zpr", iso := "zro", value := .obligneg }
  , { walsCode := "zch", iso := "zoh", value := .optneg }
  , { walsCode := "zul", iso := "zul", value := .optneg }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144D
