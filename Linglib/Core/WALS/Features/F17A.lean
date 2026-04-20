import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 17A: Rhythm Types
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 17A`.

Chapter 17, 323 languages.
-/

namespace Core.WALS.F17A

/-- WALS 17A values. -/
inductive RhythmTypes where
  /-- Trochaic (153 languages). -/
  | trochaic
  /-- Iambic (31 languages). -/
  | iambic
  /-- Dual: both trochaic and iambic (4 languages). -/
  | dualBothTrochaicAndIambic
  /-- Undetermined (37 languages). -/
  | undetermined
  /-- No rhythmic stress (98 languages). -/
  | noRhythmicStress
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 17A dataset (323 languages). -/
def allData : List (Datapoint RhythmTypes) :=
  [ { walsCode := "ace", iso := "ace", value := .trochaic }
  , { walsCode := "agu", iso := "agu", value := .noRhythmicStress }
  , { walsCode := "akl", iso := "akl", value := .iambic }
  , { walsCode := "aln", iso := "alp", value := .noRhythmicStress }
  , { walsCode := "atq", iso := "ems", value := .undetermined }
  , { walsCode := "aly", iso := "aly", value := .trochaic }
  , { walsCode := "ame", iso := "aey", value := .noRhythmicStress }
  , { walsCode := "agt", iso := "awg", value := .trochaic }
  , { walsCode := "apu", iso := "apu", value := .trochaic }
  , { walsCode := "abe", iso := "apc", value := .trochaic }
  , { walsCode := "ael", iso := "ayl", value := .iambic }
  , { walsCode := "aeg", iso := "arz", value := .trochaic }
  , { walsCode := "arv", iso := "ajp", value := .trochaic }
  , { walsCode := "apa", iso := "ajp", value := .trochaic }
  , { walsCode := "asy", iso := "apc", value := .trochaic }
  , { walsCode := "arc", iso := "aqc", value := .noRhythmicStress }
  , { walsCode := "arm", iso := "hye", value := .undetermined }
  , { walsCode := "awe", iso := "are", value := .trochaic }
  , { walsCode := "asm", iso := "cns", value := .iambic }
  , { walsCode := "ava", iso := "ava", value := .noRhythmicStress }
  , { walsCode := "awd", iso := "awa", value := .noRhythmicStress }
  , { walsCode := "awt", iso := "kmn", value := .trochaic }
  , { walsCode := "bdm", iso := "bia", value := .trochaic }
  , { walsCode := "bgv", iso := "kva", value := .noRhythmicStress }
  , { walsCode := "blk", iso := "blz", value := .trochaic }
  , { walsCode := "bbm", iso := "ptu", value := .noRhythmicStress }
  , { walsCode := "bna", iso := "jaa", value := .trochaic }
  , { walsCode := "bwa", iso := "bdy", value := .undetermined }
  , { walsCode := "bgg", iso := "bgz", value := .undetermined }
  , { walsCode := "bnt", iso := "bnq", value := .noRhythmicStress }
  , { walsCode := "bsk", iso := "bak", value := .noRhythmicStress }
  , { walsCode := "bqi", iso := "eus", value := .undetermined }
  , { walsCode := "bqb", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqg", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqh", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bql", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqn", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqo", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqr", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqs", iso := "eus", value := .undetermined }
  , { walsCode := "bso", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bqz", iso := "eus", value := .noRhythmicStress }
  , { walsCode := "bto", iso := "bbc", value := .trochaic }
  , { walsCode := "ben", iso := "ben", value := .noRhythmicStress }
  , { walsCode := "bho", iso := "bho", value := .undetermined }
  , { walsCode := "bkl", iso := "bcl", value := .trochaic }
  , { walsCode := "bbw", iso := "gup", value := .noRhythmicStress }
  , { walsCode := "bua", iso := "bvr", value := .noRhythmicStress }
  , { walsCode := "bur", iso := "bsk", value := .trochaic }
  , { walsCode := "cah", iso := "chl", value := .trochaic }
  , { walsCode := "cap", iso := "kaq", value := .trochaic }
  , { walsCode := "ctl", iso := "cat", value := .noRhythmicStress }
  , { walsCode := "cav", iso := "cav", value := .trochaic }
  , { walsCode := "cyg", iso := "cay", value := .iambic }
  , { walsCode := "cyv", iso := "cyb", value := .trochaic }
  , { walsCode := "ceb", iso := "ceb", value := .iambic }
  , { walsCode := "cha", iso := "cha", value := .undetermined }
  , { walsCode := "cya", iso := "ctp", value := .noRhythmicStress }
  , { walsCode := "cct", iso := "cho", value := .iambic }
  , { walsCode := "chv", iso := "chv", value := .noRhythmicStress }
  , { walsCode := "cmn", iso := "com", value := .trochaic }
  , { walsCode := "coo", iso := "csz", value := .noRhythmicStress }
  , { walsCode := "crn", iso := "cor", value := .trochaic }
  , { walsCode := "cre", iso := "crk", value := .trochaic }
  , { walsCode := "crk", iso := "mus", value := .iambic }
  , { walsCode := "cub", iso := "cub", value := .noRhythmicStress }
  , { walsCode := "cze", iso := "ces", value := .trochaic }
  , { walsCode := "dak", iso := "dak", value := .noRhythmicStress }
  , { walsCode := "dni", iso := "dni", value := .trochaic }
  , { walsCode := "dri", iso := "prs", value := .trochaic }
  , { walsCode := "dhw", iso := "tbh", value := .noRhythmicStress }
  , { walsCode := "dhu", iso := "dhu", value := .noRhythmicStress }
  , { walsCode := "die", iso := "dih", value := .undetermined }
  , { walsCode := "diy", iso := "dif", value := .trochaic }
  , { walsCode := "djr", iso := "ddj", value := .noRhythmicStress }
  , { walsCode := "dji", iso := "jig", value := .trochaic }
  , { walsCode := "dob", iso := "kvo", value := .noRhythmicStress }
  , { walsCode := "dou", iso := "tds", value := .noRhythmicStress }
  , { walsCode := "dre", iso := "dhv", value := .trochaic }
  , { walsCode := "dut", iso := "nld", value := .trochaic }
  , { walsCode := "dyi", iso := "dbl", value := .trochaic }
  , { walsCode := "eka", iso := "ekg", value := .noRhythmicStress }
  , { walsCode := "eng", iso := "eng", value := .trochaic }
  , { walsCode := "ese", iso := "ese", value := .trochaic }
  , { walsCode := "est", iso := "ekk", value := .trochaic }
  , { walsCode := "eve", iso := "evn", value := .iambic }
  , { walsCode := "far", iso := "fao", value := .undetermined }
  , { walsCode := "fij", iso := "fij", value := .trochaic }
  , { walsCode := "fin", iso := "fin", value := .trochaic }
  , { walsCode := "for", iso := "for", value := .noRhythmicStress }
  , { walsCode := "fre", iso := "fra", value := .undetermined }
  , { walsCode := "glp", iso := "dhg", value := .undetermined }
  , { walsCode := "gae", iso := "gla", value := .undetermined }
  , { walsCode := "gll", iso := "gbi", value := .noRhythmicStress }
  , { walsCode := "grr", iso := "wrk", value := .trochaic }
  , { walsCode := "gay", iso := "gay", value := .trochaic }
  , { walsCode := "geo", iso := "kat", value := .trochaic }
  , { walsCode := "ger", iso := "deu", value := .trochaic }
  , { walsCode := "gid", iso := "gih", value := .undetermined }
  , { walsCode := "god", iso := "gdo", value := .noRhythmicStress }
  , { walsCode := "goo", iso := "gni", value := .trochaic }
  , { walsCode := "gor", iso := "gow", value := .noRhythmicStress }
  , { walsCode := "grb", iso := "grj", value := .noRhythmicStress }
  , { walsCode := "grk", iso := "ell", value := .trochaic }
  , { walsCode := "grw", iso := "kal", value := .undetermined }
  , { walsCode := "gug", iso := "ktd", value := .trochaic }
  , { walsCode := "guu", iso := "kky", value := .trochaic }
  , { walsCode := "hno", iso := "hdn", value := .iambic }
  , { walsCode := "hnn", iso := "hnn", value := .undetermined }
  , { walsCode := "haw", iso := "haw", value := .trochaic }
  , { walsCode := "heb", iso := "heb", value := .trochaic }
  , { walsCode := "hix", iso := "hix", value := .iambic }
  , { walsCode := "hop", iso := "hop", value := .undetermined }
  , { walsCode := "htc", iso := "hus", value := .noRhythmicStress }
  , { walsCode := "hun", iso := "hun", value := .trochaic }
  , { walsCode := "iaa", iso := "iai", value := .trochaic }
  , { walsCode := "ice", iso := "isl", value := .trochaic }
  , { walsCode := "ind", iso := "ind", value := .trochaic }
  , { walsCode := "iga", iso := "inb", value := .trochaic }
  , { walsCode := "irq", iso := "irk", value := .noRhythmicStress }
  , { walsCode := "irr", iso := "irh", value := .noRhythmicStress }
  , { walsCode := "iri", iso := "gle", value := .undetermined }
  , { walsCode := "ita", iso := "ita", value := .undetermined }
  , { walsCode := "jaq", iso := "jqr", value := .trochaic }
  , { walsCode := "jav", iso := "jav", value := .undetermined }
  , { walsCode := "kal", iso := "gwc", value := .noRhythmicStress }
  , { walsCode := "kgu", iso := "ktg", value := .trochaic }
  , { walsCode := "kra", iso := "leu", value := .undetermined }
  , { walsCode := "krl", iso := "krl", value := .trochaic }
  , { walsCode := "kaj", iso := "bpp", value := .trochaic }
  , { walsCode := "kay", iso := "gyd", value := .trochaic }
  , { walsCode := "kei", iso := "kei", value := .trochaic }
  , { walsCode := "ker", iso := "ker", value := .noRhythmicStress }
  , { walsCode := "ktn", iso := "xte", value := .noRhythmicStress }
  , { walsCode := "kew", iso := "kew", value := .noRhythmicStress }
  , { walsCode := "kha", iso := "khk", value := .noRhythmicStress }
  , { walsCode := "khm", iso := "khm", value := .undetermined }
  , { walsCode := "ksr", iso := "kje", value := .trochaic }
  , { walsCode := "klm", iso := "kla", value := .trochaic }
  , { walsCode := "kob", iso := "kpw", value := .noRhythmicStress }
  , { walsCode := "kop", iso := "koi", value := .noRhythmicStress }
  , { walsCode := "kon", iso := "kng", value := .trochaic }
  , { walsCode := "kjo", iso := "kjc", value := .trochaic }
  , { walsCode := "kfe", iso := "kfz", value := .noRhythmicStress }
  , { walsCode := "koy", iso := "kff", value := .undetermined }
  , { walsCode := "kro", iso := "kgo", value := .undetermined }
  , { walsCode := "kya", iso := "gvn", value := .trochaic }
  , { walsCode := "knm", iso := "kun", value := .undetermined }
  , { walsCode := "kut", iso := "kut", value := .trochaic }
  , { walsCode := "kuu", iso := "kuy", value := .trochaic }
  , { walsCode := "lar", iso := "lrg", value := .trochaic }
  , { walsCode := "lrk", iso := "alo", value := .dualBothTrochaicAndIambic }
  , { walsCode := "lat", iso := "lav", value := .noRhythmicStress }
  , { walsCode := "lav", iso := "lvk", value := .trochaic }
  , { walsCode := "len", iso := "tnl", value := .trochaic }
  , { walsCode := "let", iso := "lti", value := .trochaic }
  , { walsCode := "lit", iso := "lit", value := .undetermined }
  , { walsCode := "liv", iso := "liv", value := .trochaic }
  , { walsCode := "ara", iso := "arw", value := .trochaic }
  , { walsCode := "luv", iso := "lue", value := .trochaic }
  , { walsCode := "mcd", iso := "mkd", value := .noRhythmicStress }
  , { walsCode := "mac", iso := "mbc", value := .iambic }
  , { walsCode := "mdm", iso := "dmd", value := .trochaic }
  , { walsCode := "mne", iso := "nmu", value := .trochaic }
  , { walsCode := "mrs", iso := "zrs", value := .trochaic }
  , { walsCode := "mai", iso := "mai", value := .trochaic }
  , { walsCode := "mlc", iso := "mcm", value := .trochaic }
  , { walsCode := "mal", iso := "plt", value := .noRhythmicStress }
  , { walsCode := "mlk", iso := "mpb", value := .trochaic }
  , { walsCode := "mym", iso := "mal", value := .undetermined }
  , { walsCode := "mlt", iso := "mlt", value := .undetermined }
  , { walsCode := "mnm", iso := "mva", value := .trochaic }
  , { walsCode := "myi", iso := "mpc", value := .trochaic }
  , { walsCode := "mns", iso := "mns", value := .trochaic }
  , { walsCode := "mnj", iso := "mpj", value := .trochaic }
  , { walsCode := "map", iso := "arn", value := .iambic }
  , { walsCode := "mku", iso := "zmr", value := .trochaic }
  , { walsCode := "mny", iso := "zmc", value := .trochaic }
  , { walsCode := "mah", iso := "mrj", value := .noRhythmicStress }
  , { walsCode := "mme", iso := "mhr", value := .noRhythmicStress }
  , { walsCode := "mar", iso := "mrc", value := .noRhythmicStress }
  , { walsCode := "mrd", iso := "mrz", value := .iambic }
  , { walsCode := "mrt", iso := "vma", value := .trochaic }
  , { walsCode := "mau", iso := "mph", value := .trochaic }
  , { walsCode := "may", iso := "ayz", value := .trochaic }
  , { walsCode := "myy", iso := "xyj", value := .trochaic }
  , { walsCode := "men", iso := "mez", value := .iambic }
  , { walsCode := "mta", iso := "sdo", value := .trochaic }
  , { walsCode := "mea", iso := "mej", value := .noRhythmicStress }
  , { walsCode := "mwn", iso := "nsq", value := .iambic }
  , { walsCode := "mss", iso := "skd", value := .trochaic }
  , { walsCode := "moh", iso := "moh", value := .noRhythmicStress }
  , { walsCode := "mmo", iso := "mdf", value := .noRhythmicStress }
  , { walsCode := "mna", iso := "mnb", value := .trochaic }
  , { walsCode := "mse", iso := "umu", value := .iambic }
  , { walsCode := "mrw", iso := "zmu", value := .trochaic }
  , { walsCode := "nbb", iso := "nmb", value := .iambic }
  , { walsCode := "ntu", iso := "yrk", value := .trochaic }
  , { walsCode := "nne", iso := "nen", value := .trochaic }
  , { walsCode := "ngl", iso := "nig", value := .trochaic }
  , { walsCode := "nkb", iso := "ngk", value := .trochaic }
  , { walsCode := "ngr", iso := "nay", value := .trochaic }
  , { walsCode := "ngi", iso := "wyb", value := .trochaic }
  , { walsCode := "nin", iso := "niz", value := .trochaic }
  , { walsCode := "nor", iso := "nor", value := .undetermined }
  , { walsCode := "nua", iso := "nxl", value := .trochaic }
  , { walsCode := "nbd", iso := "dgl", value := .undetermined }
  , { walsCode := "nug", iso := "nuy", value := .trochaic }
  , { walsCode := "nbo", iso := "now", value := .noRhythmicStress }
  , { walsCode := "nya", iso := "nyt", value := .trochaic }
  , { walsCode := "nju", iso := "nys", value := .trochaic }
  , { walsCode := "obk", iso := "afz", value := .noRhythmicStress }
  , { walsCode := "olm", iso := "nij", value := .noRhythmicStress }
  , { walsCode := "ond", iso := "one", value := .noRhythmicStress }
  , { walsCode := "ono", iso := "ons", value := .trochaic }
  , { walsCode := "oss", iso := "oss", value := .noRhythmicStress }
  , { walsCode := "pkn", iso := "drl", value := .trochaic }
  , { walsCode := "put", iso := "ute", value := .iambic }
  , { walsCode := "pai", iso := "pwn", value := .noRhythmicStress }
  , { walsCode := "psh", iso := "pst", value := .noRhythmicStress }
  , { walsCode := "psm", iso := "pqm", value := .iambic }
  , { walsCode := "pin", iso := "piu", value := .trochaic }
  , { walsCode := "pir", iso := "pib", value := .trochaic }
  , { walsCode := "pit", iso := "pjt", value := .trochaic }
  , { walsCode := "ppi", iso := "pit", value := .trochaic }
  , { walsCode := "pkm", iso := "poh", value := .noRhythmicStress }
  , { walsCode := "pol", iso := "pol", value := .trochaic }
  , { walsCode := "pme", iso := "peb", value := .iambic }
  , { walsCode := "pul", iso := "puw", value := .undetermined }
  , { walsCode := "que", iso := "yum", value := .noRhythmicStress }
  , { walsCode := "ram", iso := "rma", value := .trochaic }
  , { walsCode := "rap", iso := "rap", value := .undetermined }
  , { walsCode := "rit", iso := "rit", value := .noRhythmicStress }
  , { walsCode := "rti", iso := "twu", value := .trochaic }
  , { walsCode := "rot", iso := "rtm", value := .noRhythmicStress }
  , { walsCode := "rus", iso := "rus", value := .noRhythmicStress }
  , { walsCode := "sno", iso := "sme", value := .trochaic }
  , { walsCode := "snm", iso := "xsu", value := .trochaic }
  , { walsCode := "swi", iso := "szw", value := .noRhythmicStress }
  , { walsCode := "sed", iso := "sed", value := .noRhythmicStress }
  , { walsCode := "sru", iso := "slu", value := .trochaic }
  , { walsCode := "sly", iso := "sly", value := .noRhythmicStress }
  , { walsCode := "slp", iso := "spl", value := .trochaic }
  , { walsCode := "skp", iso := "sel", value := .trochaic }
  , { walsCode := "sml", iso := "sza", value := .noRhythmicStress }
  , { walsCode := "snc", iso := "see", value := .iambic }
  , { walsCode := "snt", iso := "set", value := .trochaic }
  , { walsCode := "scr", iso := "hbs", value := .noRhythmicStress }
  , { walsCode := "ser", iso := "sei", value := .undetermined }
  , { walsCode := "shi", iso := "shb", value := .iambic }
  , { walsCode := "skr", iso := "tty", value := .noRhythmicStress }
  , { walsCode := "sio", iso := "xsi", value := .noRhythmicStress }
  , { walsCode := "sla", iso := "den", value := .noRhythmicStress }
  , { walsCode := "svk", iso := "slk", value := .trochaic }
  , { walsCode := "slo", iso := "slv", value := .noRhythmicStress }
  , { walsCode := "srb", iso := "", value := .trochaic }
  , { walsCode := "sea", iso := "tvk", value := .noRhythmicStress }
  , { walsCode := "spa", iso := "spa", value := .trochaic }
  , { walsCode := "squ", iso := "squ", value := .noRhythmicStress }
  , { walsCode := "sto", iso := "sto", value := .noRhythmicStress }
  , { walsCode := "swe", iso := "swe", value := .noRhythmicStress }
  , { walsCode := "tab", iso := "mky", value := .trochaic }
  , { walsCode := "tac", iso := "tna", value := .trochaic }
  , { walsCode := "tag", iso := "tgl", value := .trochaic }
  , { walsCode := "tah", iso := "tah", value := .noRhythmicStress }
  , { walsCode := "tns", iso := "nwi", value := .trochaic }
  , { walsCode := "tgw", iso := "txn", value := .trochaic }
  , { walsCode := "tas", iso := "shi", value := .noRhythmicStress }
  , { walsCode := "taw", iso := "tbo", value := .trochaic }
  , { walsCode := "tps", iso := "stp", value := .trochaic }
  , { walsCode := "tgk", iso := "tgc", value := .noRhythmicStress }
  , { walsCode := "tmc", iso := "tjm", value := .trochaic }
  , { walsCode := "try", iso := "tiy", value := .trochaic }
  , { walsCode := "tiw", iso := "tiw", value := .trochaic }
  , { walsCode := "tng", iso := "ton", value := .trochaic }
  , { walsCode := "tsa", iso := "tkr", value := .noRhythmicStress }
  , { walsCode := "tua", iso := "pmt", value := .noRhythmicStress }
  , { walsCode := "tuk", iso := "", value := .trochaic }
  , { walsCode := "tun", iso := "tun", value := .noRhythmicStress }
  , { walsCode := "tur", iso := "tur", value := .noRhythmicStress }
  , { walsCode := "tbb", iso := "tub", value := .trochaic }
  , { walsCode := "tsh", iso := "par", value := .trochaic }
  , { walsCode := "unm", iso := "unm", value := .iambic }
  , { walsCode := "ung", iso := "ung", value := .undetermined }
  , { walsCode := "urk", iso := "urb", value := .iambic }
  , { walsCode := "uzn", iso := "uzn", value := .trochaic }
  , { walsCode := "vot", iso := "vot", value := .trochaic }
  , { walsCode := "wah", iso := "", value := .iambic }
  , { walsCode := "wlm", iso := "wmt", value := .trochaic }
  , { walsCode := "wam", iso := "wmb", value := .trochaic }
  , { walsCode := "wan", iso := "xwk", value := .trochaic }
  , { walsCode := "wao", iso := "auc", value := .trochaic }
  , { walsCode := "wra", iso := "wba", value := .trochaic }
  , { walsCode := "wrd", iso := "wrr", value := .trochaic }
  , { walsCode := "war", iso := "pav", value := .noRhythmicStress }
  , { walsCode := "wrl", iso := "wbp", value := .trochaic }
  , { walsCode := "wrg", iso := "wgy", value := .trochaic }
  , { walsCode := "wer", iso := "wer", value := .iambic }
  , { walsCode := "wet", iso := "lex", value := .undetermined }
  , { walsCode := "wic", iso := "wic", value := .dualBothTrochaicAndIambic }
  , { walsCode := "wch", iso := "mzh", value := .trochaic }
  , { walsCode := "wnb", iso := "win", value := .iambic }
  , { walsCode := "wiy", iso := "wiy", value := .noRhythmicStress }
  , { walsCode := "woi", iso := "woi", value := .noRhythmicStress }
  , { walsCode := "ymd", iso := "jmd", value := .noRhythmicStress }
  , { walsCode := "yan", iso := "ynn", value := .noRhythmicStress }
  , { walsCode := "yny", iso := "jao", value := .trochaic }
  , { walsCode := "yap", iso := "yap", value := .undetermined }
  , { walsCode := "yaq", iso := "yaq", value := .trochaic }
  , { walsCode := "yzv", iso := "kpv", value := .noRhythmicStress }
  , { walsCode := "yel", iso := "yle", value := .trochaic }
  , { walsCode := "yid", iso := "yii", value := .dualBothTrochaicAndIambic }
  , { walsCode := "yim", iso := "yee", value := .trochaic }
  , { walsCode := "yin", iso := "yij", value := .trochaic }
  , { walsCode := "yir", iso := "yyr", value := .noRhythmicStress }
  , { walsCode := "yuc", iso := "yuc", value := .undetermined }
  , { walsCode := "ypk", iso := "esu", value := .iambic }
  , { walsCode := "ych", iso := "esu", value := .iambic }
  , { walsCode := "yun", iso := "esu", value := .iambic }
  , { walsCode := "ysl", iso := "ess", value := .iambic }
  , { walsCode := "yuw", iso := "kld", value := .dualBothTrochaicAndIambic }
  , { walsCode := "zqc", iso := "zoc", value := .trochaic }
  , { walsCode := "zul", iso := "zul", value := .trochaic }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F17A
