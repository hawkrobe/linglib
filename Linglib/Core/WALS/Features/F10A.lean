import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 10A: Vowel Nasalization
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 10A`.

Chapter 10, 244 languages.
-/

namespace Core.WALS.F10A

/-- WALS 10A values. -/
inductive VowelNasalization where
  /-- Contrast present (64 languages). -/
  | present
  /-- Contrast absent (180 languages). -/
  | absent
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 10A dataset (244 languages). -/
def allData : List (Datapoint VowelNasalization) :=
  [ { walsCode := "xoo", iso := "nmn", value := .absent }
  , { walsCode := "abi", iso := "axb", value := .absent }
  , { walsCode := "abk", iso := "abk", value := .absent }
  , { walsCode := "aco", iso := "kjq", value := .absent }
  , { walsCode := "ain", iso := "ain", value := .absent }
  , { walsCode := "aka", iso := "axk", value := .absent }
  , { walsCode := "ala", iso := "amp", value := .absent }
  , { walsCode := "amc", iso := "amc", value := .present }
  , { walsCode := "ame", iso := "aey", value := .absent }
  , { walsCode := "ao", iso := "njo", value := .absent }
  , { walsCode := "apu", iso := "apu", value := .present }
  , { walsCode := "aeg", iso := "arz", value := .absent }
  , { walsCode := "ana", iso := "aro", value := .absent }
  , { walsCode := "arp", iso := "ape", value := .absent }
  , { walsCode := "arm", iso := "hye", value := .absent }
  , { walsCode := "asm", iso := "cns", value := .absent }
  , { walsCode := "avt", iso := "avn", value := .present }
  , { walsCode := "awp", iso := "kwi", value := .absent }
  , { walsCode := "bfi", iso := "ksf", value := .absent }
  , { walsCode := "bag", iso := "bmi", value := .present }
  , { walsCode := "blz", iso := "", value := .absent }
  , { walsCode := "ban", iso := "bcw", value := .absent }
  , { walsCode := "ble", iso := "bci", value := .present }
  , { walsCode := "brs", iso := "bsn", value := .present }
  , { walsCode := "bsr", iso := "bsc", value := .absent }
  , { walsCode := "bsq", iso := "eus", value := .absent }
  , { walsCode := "bkr", iso := "btx", value := .absent }
  , { walsCode := "bma", iso := "tzm", value := .absent }
  , { walsCode := "bfd", iso := "bif", value := .absent }
  , { walsCode := "brh", iso := "brh", value := .absent }
  , { walsCode := "buy", iso := "bwu", value := .present }
  , { walsCode := "brm", iso := "mya", value := .absent }
  , { walsCode := "bur", iso := "bsk", value := .present }
  , { walsCode := "cah", iso := "chl", value := .absent }
  , { walsCode := "car", iso := "car", value := .absent }
  , { walsCode := "cyv", iso := "cyb", value := .present }
  , { walsCode := "cha", iso := "cha", value := .absent }
  , { walsCode := "chq", iso := "chq", value := .present }
  , { walsCode := "ctm", iso := "ctm", value := .absent }
  , { walsCode := "chk", iso := "ckt", value := .absent }
  , { walsCode := "ccp", iso := "coc", value := .absent }
  , { walsCode := "cmn", iso := "com", value := .absent }
  , { walsCode := "coo", iso := "csz", value := .absent }
  , { walsCode := "cre", iso := "crk", value := .absent }
  , { walsCode := "dag", iso := "dgz", value := .absent }
  , { walsCode := "dga", iso := "dga", value := .present }
  , { walsCode := "dgb", iso := "dag", value := .absent }
  , { walsCode := "day", iso := "dai", value := .present }
  , { walsCode := "doy", iso := "dow", value := .present }
  , { walsCode := "dre", iso := "dhv", value := .absent }
  , { walsCode := "ebi", iso := "igb", value := .absent }
  , { walsCode := "ega", iso := "ega", value := .absent }
  , { walsCode := "eip", iso := "eip", value := .absent }
  , { walsCode := "eka", iso := "ekg", value := .absent }
  , { walsCode := "ora", iso := "ema", value := .present }
  , { walsCode := "eng", iso := "eng", value := .absent }
  , { walsCode := "epe", iso := "sja", value := .present }
  , { walsCode := "eve", iso := "evn", value := .absent }
  , { walsCode := "fij", iso := "fij", value := .absent }
  , { walsCode := "fin", iso := "fin", value := .absent }
  , { walsCode := "fre", iso := "fra", value := .present }
  , { walsCode := "fus", iso := "fuc", value := .absent }
  , { walsCode := "fur", iso := "fvr", value := .absent }
  , { walsCode := "gad", iso := "ged", value := .absent }
  , { walsCode := "gar", iso := "grt", value := .absent }
  , { walsCode := "gbk", iso := "gya", value := .present }
  , { walsCode := "geo", iso := "kat", value := .absent }
  , { walsCode := "ger", iso := "deu", value := .absent }
  , { walsCode := "goo", iso := "gni", value := .absent }
  , { walsCode := "grb", iso := "grj", value := .present }
  , { walsCode := "grk", iso := "ell", value := .absent }
  , { walsCode := "grw", iso := "kal", value := .absent }
  , { walsCode := "gua", iso := "gug", value := .present }
  , { walsCode := "gir", iso := "glj", value := .present }
  , { walsCode := "grm", iso := "gux", value := .present }
  , { walsCode := "hai", iso := "hai", value := .absent }
  , { walsCode := "hrs", iso := "hss", value := .absent }
  , { walsCode := "hau", iso := "hau", value := .absent }
  , { walsCode := "hay", iso := "vay", value := .present }
  , { walsCode := "heb", iso := "heb", value := .absent }
  , { walsCode := "hin", iso := "hin", value := .present }
  , { walsCode := "hix", iso := "hix", value := .absent }
  , { walsCode := "hun", iso := "hun", value := .absent }
  , { walsCode := "hzb", iso := "huz", value := .present }
  , { walsCode := "igb", iso := "ibo", value := .absent }
  , { walsCode := "ila", iso := "ilb", value := .absent }
  , { walsCode := "imo", iso := "imn", value := .absent }
  , { walsCode := "ind", iso := "ind", value := .absent }
  , { walsCode := "ing", iso := "inh", value := .absent }
  , { walsCode := "irq", iso := "irk", value := .absent }
  , { walsCode := "iri", iso := "gle", value := .absent }
  , { walsCode := "jak", iso := "jac", value := .absent }
  , { walsCode := "jpn", iso := "jpn", value := .absent }
  , { walsCode := "jaq", iso := "jqr", value := .absent }
  , { walsCode := "kng", iso := "kgp", value := .present }
  , { walsCode := "kan", iso := "ogo", value := .present }
  , { walsCode := "knd", iso := "kan", value := .absent }
  , { walsCode := "knr", iso := "knc", value := .absent }
  , { walsCode := "krk", iso := "kyh", value := .present }
  , { walsCode := "kyl", iso := "eky", value := .absent }
  , { walsCode := "kay", iso := "gyd", value := .absent }
  , { walsCode := "kem", iso := "ahg", value := .absent }
  , { walsCode := "ket", iso := "ket", value := .absent }
  , { walsCode := "kha", iso := "khk", value := .absent }
  , { walsCode := "khs", iso := "kha", value := .absent }
  , { walsCode := "khm", iso := "khm", value := .absent }
  , { walsCode := "kmu", iso := "kjg", value := .absent }
  , { walsCode := "klv", iso := "kij", value := .absent }
  , { walsCode := "krb", iso := "gil", value := .absent }
  , { walsCode := "kis", iso := "kss", value := .absent }
  , { walsCode := "koa", iso := "cku", value := .present }
  , { walsCode := "kob", iso := "kpw", value := .absent }
  , { walsCode := "kon", iso := "kng", value := .absent }
  , { walsCode := "kor", iso := "kor", value := .absent }
  , { walsCode := "kfe", iso := "kfz", value := .present }
  , { walsCode := "krw", iso := "khe", value := .absent }
  , { walsCode := "ksp", iso := "kia", value := .present }
  , { walsCode := "ktk", iso := "aal", value := .absent }
  , { walsCode := "kch", iso := "khq", value := .present }
  , { walsCode := "kro", iso := "kgo", value := .absent }
  , { walsCode := "knm", iso := "kun", value := .absent }
  , { walsCode := "kut", iso := "kut", value := .absent }
  , { walsCode := "kwk", iso := "kwk", value := .absent }
  , { walsCode := "kwb", iso := "kwe", value := .absent }
  , { walsCode := "laa", iso := "gdm", value := .absent }
  , { walsCode := "lad", iso := "lbj", value := .absent }
  , { walsCode := "lak", iso := "lbe", value := .absent }
  , { walsCode := "lkt", iso := "lkt", value := .present }
  , { walsCode := "lam", iso := "lme", value := .absent }
  , { walsCode := "lan", iso := "laj", value := .present }
  , { walsCode := "lat", iso := "lav", value := .absent }
  , { walsCode := "lav", iso := "lvk", value := .absent }
  , { walsCode := "lez", iso := "lez", value := .absent }
  , { walsCode := "lok", iso := "lok", value := .present }
  , { walsCode := "mab", iso := "mde", value := .present }
  , { walsCode := "mdz", iso := "mda", value := .present }
  , { walsCode := "mal", iso := "plt", value := .absent }
  , { walsCode := "mnd", iso := "cmn", value := .absent }
  , { walsCode := "mdk", iso := "mnk", value := .absent }
  , { walsCode := "myi", iso := "mpc", value := .absent }
  , { walsCode := "mao", iso := "mri", value := .absent }
  , { walsCode := "map", iso := "arn", value := .absent }
  , { walsCode := "mku", iso := "zmr", value := .absent }
  , { walsCode := "mar", iso := "mrc", value := .absent }
  , { walsCode := "mrt", iso := "vma", value := .absent }
  , { walsCode := "mau", iso := "mph", value := .absent }
  , { walsCode := "may", iso := "ayz", value := .absent }
  , { walsCode := "mby", iso := "myb", value := .present }
  , { walsCode := "mdo", iso := "gmm", value := .present }
  , { walsCode := "mei", iso := "mni", value := .absent }
  , { walsCode := "mid", iso := "mei", value := .absent }
  , { walsCode := "mss", iso := "skd", value := .absent }
  , { walsCode := "mxc", iso := "mig", value := .present }
  , { walsCode := "moo", iso := "mos", value := .present }
  , { walsCode := "mul", iso := "mlm", value := .absent }
  , { walsCode := "mnu", iso := "mji", value := .absent }
  , { walsCode := "mun", iso := "unr", value := .present }
  , { walsCode := "mrl", iso := "mur", value := .absent }
  , { walsCode := "nhn", iso := "ncj", value := .absent }
  , { walsCode := "kho", iso := "naq", value := .absent }
  , { walsCode := "nav", iso := "nav", value := .present }
  , { walsCode := "ndy", iso := "djk", value := .absent }
  , { walsCode := "ntu", iso := "yrk", value := .absent }
  , { walsCode := "nez", iso := "nez", value := .absent }
  , { walsCode := "ntj", iso := "ntj", value := .absent }
  , { walsCode := "nti", iso := "niy", value := .absent }
  , { walsCode := "ngi", iso := "wyb", value := .absent }
  , { walsCode := "niv", iso := "niv", value := .absent }
  , { walsCode := "nko", iso := "cgg", value := .absent }
  , { walsCode := "nug", iso := "nuy", value := .absent }
  , { walsCode := "oca", iso := "oca", value := .present }
  , { walsCode := "oku", iso := "oku", value := .absent }
  , { walsCode := "ong", iso := "oon", value := .absent }
  , { walsCode := "orh", iso := "hae", value := .absent }
  , { walsCode := "otm", iso := "ote", value := .present }
  , { walsCode := "pms", iso := "pma", value := .absent }
  , { walsCode := "pai", iso := "pwn", value := .absent }
  , { walsCode := "psm", iso := "pqm", value := .absent }
  , { walsCode := "pau", iso := "pad", value := .absent }
  , { walsCode := "paw", iso := "pwa", value := .present }
  , { walsCode := "prs", iso := "pes", value := .absent }
  , { walsCode := "prh", iso := "myp", value := .absent }
  , { walsCode := "pod", iso := "pbi", value := .absent }
  , { walsCode := "pme", iso := "peb", value := .absent }
  , { walsCode := "zqs", iso := "poi", value := .absent }
  , { walsCode := "qaw", iso := "alc", value := .absent }
  , { walsCode := "qim", iso := "qvi", value := .absent }
  , { walsCode := "ram", iso := "rma", value := .absent }
  , { walsCode := "rap", iso := "rap", value := .absent }
  , { walsCode := "rus", iso := "rus", value := .absent }
  , { walsCode := "san", iso := "sag", value := .present }
  , { walsCode := "snm", iso := "xsu", value := .present }
  , { walsCode := "sel", iso := "ona", value := .absent }
  , { walsCode := "sml", iso := "sza", value := .present }
  , { walsCode := "snd", iso := "sef", value := .present }
  , { walsCode := "snc", iso := "see", value := .present }
  , { walsCode := "sla", iso := "den", value := .present }
  , { walsCode := "spa", iso := "spa", value := .absent }
  , { walsCode := "squ", iso := "squ", value := .absent }
  , { walsCode := "sue", iso := "sue", value := .absent }
  , { walsCode := "sup", iso := "spp", value := .present }
  , { walsCode := "swa", iso := "swh", value := .absent }
  , { walsCode := "tab", iso := "mky", value := .absent }
  , { walsCode := "tbl", iso := "tnm", value := .absent }
  , { walsCode := "tag", iso := "tgl", value := .absent }
  , { walsCode := "tne", iso := "tem", value := .present }
  , { walsCode := "trb", iso := "tfr", value := .present }
  , { walsCode := "tha", iso := "tha", value := .absent }
  , { walsCode := "tik", iso := "tik", value := .absent }
  , { walsCode := "tiw", iso := "tiw", value := .absent }
  , { walsCode := "tli", iso := "tli", value := .absent }
  , { walsCode := "dts", iso := "dts", value := .present }
  , { walsCode := "tru", iso := "tpy", value := .absent }
  , { walsCode := "tsi", iso := "tsi", value := .absent }
  , { walsCode := "tuk", iso := "", value := .absent }
  , { walsCode := "tmk", iso := "tmc", value := .present }
  , { walsCode := "tun", iso := "tun", value := .absent }
  , { walsCode := "tur", iso := "tur", value := .absent }
  , { walsCode := "kgl", iso := "ubu", value := .absent }
  , { walsCode := "ung", iso := "ung", value := .absent }
  , { walsCode := "urk", iso := "urb", value := .present }
  , { walsCode := "usa", iso := "wnu", value := .absent }
  , { walsCode := "vie", iso := "vie", value := .absent }
  , { walsCode := "wam", iso := "wmb", value := .absent }
  , { walsCode := "wra", iso := "wba", value := .present }
  , { walsCode := "wrd", iso := "wrr", value := .absent }
  , { walsCode := "war", iso := "pav", value := .present }
  , { walsCode := "wic", iso := "wic", value := .absent }
  , { walsCode := "wch", iso := "mzh", value := .absent }
  , { walsCode := "wlf", iso := "wol", value := .absent }
  , { walsCode := "wmn", iso := "wem", value := .present }
  , { walsCode := "xas", iso := "kao", value := .absent }
  , { walsCode := "yag", iso := "yad", value := .present }
  , { walsCode := "yaq", iso := "yaq", value := .absent }
  , { walsCode := "yem", iso := "ybb", value := .absent }
  , { walsCode := "yid", iso := "yii", value := .absent }
  , { walsCode := "yim", iso := "yee", value := .absent }
  , { walsCode := "yor", iso := "yor", value := .present }
  , { walsCode := "yuc", iso := "yuc", value := .present }
  , { walsCode := "yko", iso := "yux", value := .absent }
  , { walsCode := "ykp", iso := "yup", value := .present }
  , { walsCode := "ypk", iso := "esu", value := .absent }
  , { walsCode := "yur", iso := "yur", value := .absent }
  , { walsCode := "zul", iso := "zul", value := .absent }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F10A
