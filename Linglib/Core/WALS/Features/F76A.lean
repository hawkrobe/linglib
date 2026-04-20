import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 76A: Overlap between Situational and Epistemic Modal Marking
@cite{vanbogaert-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 76A`.

Chapter 76, 207 languages.
-/

namespace Core.WALS.F76A

/-- WALS 76A values. -/
inductive ModalOverlap where
  /-- Overlap for both possibility and necessity (36 languages). -/
  | overlapForBothPossibilityAndNecessity
  /-- Overlap for either possibility or necessity (66 languages). -/
  | overlapForEitherPossibilityOrNecessity
  /-- No overlap (105 languages). -/
  | noOverlap
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 76A dataset (207 languages). -/
def allData : List (Datapoint ModalOverlap) :=
  [ { walsCode := "abk", iso := "abk", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ace", iso := "ace", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "aco", iso := "kjq", value := .noOverlap }
  , { walsCode := "ain", iso := "ain", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "akn", iso := "aka", value := .noOverlap }
  , { walsCode := "alb", iso := "sqi", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ame", iso := "aey", value := .noOverlap }
  , { walsCode := "amh", iso := "amh", value := .noOverlap }
  , { walsCode := "aeg", iso := "arz", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "arg", iso := "afb", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "amr", iso := "ary", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ana", iso := "aro", value := .noOverlap }
  , { walsCode := "arm", iso := "hye", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "asm", iso := "cns", value := .noOverlap }
  , { walsCode := "awp", iso := "kwi", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "aym", iso := "ayr", value := .noOverlap }
  , { walsCode := "bab", iso := "bav", value := .noOverlap }
  , { walsCode := "bal", iso := "ban", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "bam", iso := "bam", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "brs", iso := "bsn", value := .noOverlap }
  , { walsCode := "bsq", iso := "eus", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "bkr", iso := "btx", value := .noOverlap }
  , { walsCode := "baw", iso := "bgr", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "brh", iso := "brh", value := .noOverlap }
  , { walsCode := "brm", iso := "mya", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "cnt", iso := "yue", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ctl", iso := "cat", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "cyv", iso := "cyb", value := .noOverlap }
  , { walsCode := "cha", iso := "cha", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "chk", iso := "ckt", value := .noOverlap }
  , { walsCode := "coo", iso := "csz", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "cre", iso := "crk", value := .noOverlap }
  , { walsCode := "dag", iso := "dgz", value := .noOverlap }
  , { walsCode := "dni", iso := "dni", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "dsh", iso := "dan", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "die", iso := "dih", value := .noOverlap }
  , { walsCode := "dre", iso := "dhv", value := .noOverlap }
  , { walsCode := "dut", iso := "nld", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "eka", iso := "ekg", value := .noOverlap }
  , { walsCode := "eng", iso := "eng", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "eve", iso := "evn", value := .noOverlap }
  , { walsCode := "ewe", iso := "ewe", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "far", iso := "fao", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "fij", iso := "fij", value := .noOverlap }
  , { walsCode := "fin", iso := "fin", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "fre", iso := "fra", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "fua", iso := "fub", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "fue", iso := "fud", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "gar", iso := "grt", value := .noOverlap }
  , { walsCode := "geo", iso := "kat", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ger", iso := "deu", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "grk", iso := "ell", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "grw", iso := "kal", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "hai", iso := "hai", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ham", iso := "hmt", value := .noOverlap }
  , { walsCode := "hau", iso := "hau", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "haw", iso := "haw", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "heb", iso := "heb", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "hin", iso := "hin", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "hun", iso := "hun", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "hzb", iso := "huz", value := .noOverlap }
  , { walsCode := "ice", iso := "isl", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "igb", iso := "ibo", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ika", iso := "arh", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "imo", iso := "imn", value := .noOverlap }
  , { walsCode := "ind", iso := "ind", value := .noOverlap }
  , { walsCode := "irq", iso := "irk", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "iri", iso := "gle", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "ita", iso := "ita", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "jak", iso := "jac", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "jpn", iso := "jpn", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kam", iso := "xbr", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "knd", iso := "kan", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "knr", iso := "knc", value := .noOverlap }
  , { walsCode := "kas", iso := "kas", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "kay", iso := "gyd", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ker", iso := "ker", value := .noOverlap }
  , { walsCode := "ket", iso := "ket", value := .noOverlap }
  , { walsCode := "kha", iso := "khk", value := .noOverlap }
  , { walsCode := "kty", iso := "kca", value := .noOverlap }
  , { walsCode := "khs", iso := "kha", value := .noOverlap }
  , { walsCode := "kmu", iso := "kjg", value := .noOverlap }
  , { walsCode := "klv", iso := "kij", value := .noOverlap }
  , { walsCode := "kio", iso := "kio", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "koa", iso := "cku", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kob", iso := "kpw", value := .noOverlap }
  , { walsCode := "kol", iso := "kfb", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kor", iso := "kor", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kfe", iso := "kfz", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kse", iso := "ses", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kui", iso := "kxu", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "kut", iso := "kut", value := .noOverlap }
  , { walsCode := "lad", iso := "lbj", value := .noOverlap }
  , { walsCode := "lak", iso := "lbe", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "lkt", iso := "lkt", value := .noOverlap }
  , { walsCode := "lan", iso := "laj", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "lat", iso := "lav", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "lav", iso := "lvk", value := .noOverlap }
  , { walsCode := "lep", iso := "lep", value := .noOverlap }
  , { walsCode := "lez", iso := "lez", value := .noOverlap }
  , { walsCode := "lin", iso := "lin", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "lit", iso := "lit", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "mab", iso := "mde", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "mcd", iso := "mkd", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "mai", iso := "mai", value := .noOverlap }
  , { walsCode := "mal", iso := "plt", value := .noOverlap }
  , { walsCode := "mym", iso := "mal", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "mlt", iso := "mlt", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "mnd", iso := "cmn", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "myi", iso := "mpc", value := .noOverlap }
  , { walsCode := "mns", iso := "mns", value := .noOverlap }
  , { walsCode := "mao", iso := "mri", value := .noOverlap }
  , { walsCode := "map", iso := "arn", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "mku", iso := "zmr", value := .noOverlap }
  , { walsCode := "mhi", iso := "mar", value := .noOverlap }
  , { walsCode := "mrd", iso := "mrz", value := .noOverlap }
  , { walsCode := "meh", iso := "gdq", value := .noOverlap }
  , { walsCode := "mei", iso := "mni", value := .noOverlap }
  , { walsCode := "mie", iso := "ium", value := .noOverlap }
  , { walsCode := "mss", iso := "skd", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "mxc", iso := "mig", value := .noOverlap }
  , { walsCode := "mok", iso := "mkj", value := .noOverlap }
  , { walsCode := "mna", iso := "mnb", value := .noOverlap }
  , { walsCode := "mdg", iso := "mua", value := .noOverlap }
  , { walsCode := "mun", iso := "unr", value := .noOverlap }
  , { walsCode := "nma", iso := "nbi", value := .noOverlap }
  , { walsCode := "ngt", iso := "nmf", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "nht", iso := "nhg", value := .noOverlap }
  , { walsCode := "kho", iso := "naq", value := .noOverlap }
  , { walsCode := "nav", iso := "nav", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "ndy", iso := "djk", value := .noOverlap }
  , { walsCode := "ntu", iso := "yrk", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "nez", iso := "nez", value := .noOverlap }
  , { walsCode := "ngi", iso := "wyb", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "niv", iso := "niv", value := .noOverlap }
  , { walsCode := "nko", iso := "cgg", value := .noOverlap }
  , { walsCode := "nug", iso := "nuy", value := .noOverlap }
  , { walsCode := "ond", iso := "one", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "orh", iso := "hae", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "otm", iso := "ote", value := .noOverlap }
  , { walsCode := "pai", iso := "pwn", value := .noOverlap }
  , { walsCode := "pan", iso := "pan", value := .noOverlap }
  , { walsCode := "psm", iso := "pqm", value := .noOverlap }
  , { walsCode := "pau", iso := "pad", value := .noOverlap }
  , { walsCode := "prs", iso := "pes", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "pba", iso := "pia", value := .noOverlap }
  , { walsCode := "pit", iso := "pjt", value := .noOverlap }
  , { walsCode := "pol", iso := "pol", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "pso", iso := "pom", value := .noOverlap }
  , { walsCode := "por", iso := "por", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "qim", iso := "qvi", value := .noOverlap }
  , { walsCode := "rap", iso := "rap", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "rka", iso := "rmy", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "rom", iso := "ron", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "rus", iso := "rus", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "sno", iso := "sme", value := .noOverlap }
  , { walsCode := "smt", iso := "uma", value := .noOverlap }
  , { walsCode := "san", iso := "sag", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "snm", iso := "xsu", value := .noOverlap }
  , { walsCode := "sel", iso := "ona", value := .noOverlap }
  , { walsCode := "sml", iso := "sza", value := .noOverlap }
  , { walsCode := "scr", iso := "hbs", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "shk", iso := "shp", value := .noOverlap }
  , { walsCode := "sla", iso := "den", value := .noOverlap }
  , { walsCode := "slo", iso := "slv", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "som", iso := "som", value := .noOverlap }
  , { walsCode := "spa", iso := "spa", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "squ", iso := "squ", value := .noOverlap }
  , { walsCode := "sup", iso := "spp", value := .noOverlap }
  , { walsCode := "swa", iso := "swh", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "swe", iso := "swe", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "tab", iso := "mky", value := .noOverlap }
  , { walsCode := "tag", iso := "tgl", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "tml", iso := "tam", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "tel", iso := "tel", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "teo", iso := "tio", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "tha", iso := "tha", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "tgr", iso := "tig", value := .noOverlap }
  , { walsCode := "tli", iso := "tli", value := .noOverlap }
  , { walsCode := "tor", iso := "rth", value := .noOverlap }
  , { walsCode := "tru", iso := "tpy", value := .noOverlap }
  , { walsCode := "tuk", iso := "", value := .noOverlap }
  , { walsCode := "tur", iso := "tur", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "tvl", iso := "tvl", value := .noOverlap }
  , { walsCode := "tuv", iso := "tyv", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "udh", iso := "ude", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "una", iso := "mtg", value := .noOverlap }
  , { walsCode := "ung", iso := "ung", value := .noOverlap }
  , { walsCode := "usa", iso := "wnu", value := .noOverlap }
  , { walsCode := "uzb", iso := "", value := .noOverlap }
  , { walsCode := "vie", iso := "vie", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "vot", iso := "vot", value := .noOverlap }
  , { walsCode := "wam", iso := "wmb", value := .noOverlap }
  , { walsCode := "wra", iso := "wba", value := .noOverlap }
  , { walsCode := "wel", iso := "cym", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "wch", iso := "mzh", value := .noOverlap }
  , { walsCode := "wlf", iso := "wol", value := .overlapForEitherPossibilityOrNecessity }
  , { walsCode := "yaq", iso := "yaq", value := .noOverlap }
  , { walsCode := "yim", iso := "yee", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "yor", iso := "yor", value := .overlapForBothPossibilityAndNecessity }
  , { walsCode := "yuc", iso := "yuc", value := .noOverlap }
  , { walsCode := "yko", iso := "yux", value := .noOverlap }
  , { walsCode := "ypk", iso := "esu", value := .noOverlap }
  , { walsCode := "yur", iso := "yur", value := .noOverlap }
  , { walsCode := "zya", iso := "zav", value := .noOverlap }
  , { walsCode := "zqc", iso := "zoc", value := .noOverlap }
  , { walsCode := "zul", iso := "zul", value := .overlapForEitherPossibilityOrNecessity }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F76A
