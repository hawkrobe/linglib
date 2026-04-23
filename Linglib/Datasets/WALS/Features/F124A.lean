import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 124A: 'Want' Complement Subjects
@cite{cristofaro-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 124A`.

Chapter 124, 283 languages.
-/

namespace Datasets.WALS.F124A

/-- WALS 124A values. -/
inductive WantComplementSubject where
  /-- Subject is left implicit (144 languages). -/
  | subjectIsLeftImplicit
  /-- Subject is expressed overtly (72 languages). -/
  | subjectIsExpressedOvertly
  /-- Both construction types exist (14 languages). -/
  | bothConstructionTypesExist
  /-- Desiderative verbal affix (45 languages). -/
  | desiderativeVerbalAffix
  /-- Desiderative particle (8 languages). -/
  | desiderativeParticle
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 124A dataset (283 languages). -/
def allData : List (Datapoint WantComplementSubject) :=
  [ { walsCode := "abk", iso := "abk", value := .subjectIsExpressedOvertly }
  , { walsCode := "abu", iso := "kgr", value := .subjectIsExpressedOvertly }
  , { walsCode := "ace", iso := "ace", value := .subjectIsLeftImplicit }
  , { walsCode := "aga", iso := "agd", value := .desiderativeVerbalAffix }
  , { walsCode := "ain", iso := "ain", value := .subjectIsLeftImplicit }
  , { walsCode := "akh", iso := "ahk", value := .subjectIsLeftImplicit }
  , { walsCode := "all", iso := "nrz", value := .subjectIsExpressedOvertly }
  , { walsCode := "alb", iso := "sqi", value := .subjectIsExpressedOvertly }
  , { walsCode := "ale", iso := "ale", value := .desiderativeVerbalAffix }
  , { walsCode := "aly", iso := "aly", value := .subjectIsLeftImplicit }
  , { walsCode := "aml", iso := "omb", value := .bothConstructionTypesExist }
  , { walsCode := "ame", iso := "aey", value := .subjectIsExpressedOvertly }
  , { walsCode := "ano", iso := "nun", value := .subjectIsLeftImplicit }
  , { walsCode := "apj", iso := "apj", value := .subjectIsExpressedOvertly }
  , { walsCode := "apu", iso := "apu", value := .desiderativeVerbalAffix }
  , { walsCode := "aeg", iso := "arz", value := .subjectIsExpressedOvertly }
  , { walsCode := "ana", iso := "aro", value := .desiderativeVerbalAffix }
  , { walsCode := "amp", iso := "aer", value := .subjectIsLeftImplicit }
  , { walsCode := "ass", iso := "asm", value := .subjectIsLeftImplicit }
  , { walsCode := "awp", iso := "kwi", value := .desiderativeVerbalAffix }
  , { walsCode := "bab", iso := "bav", value := .subjectIsLeftImplicit }
  , { walsCode := "bag", iso := "bmi", value := .subjectIsExpressedOvertly }
  , { walsCode := "bak", iso := "bkc", value := .subjectIsLeftImplicit }
  , { walsCode := "bvi", iso := "", value := .subjectIsLeftImplicit }
  , { walsCode := "bae", iso := "bae", value := .subjectIsExpressedOvertly }
  , { walsCode := "baw", iso := "bgr", value := .subjectIsLeftImplicit }
  , { walsCode := "ben", iso := "ben", value := .subjectIsLeftImplicit }
  , { walsCode := "bma", iso := "tzm", value := .subjectIsExpressedOvertly }
  , { walsCode := "bbw", iso := "gup", value := .subjectIsExpressedOvertly }
  , { walsCode := "biu", iso := "", value := .subjectIsLeftImplicit }
  , { walsCode := "bla", iso := "bla", value := .subjectIsExpressedOvertly }
  , { walsCode := "boz", iso := "boz", value := .subjectIsLeftImplicit }
  , { walsCode := "bud", iso := "bdm", value := .subjectIsExpressedOvertly }
  , { walsCode := "bul", iso := "bul", value := .subjectIsExpressedOvertly }
  , { walsCode := "brm", iso := "mya", value := .subjectIsLeftImplicit }
  , { walsCode := "cnl", iso := "ram", value := .subjectIsLeftImplicit }
  , { walsCode := "cnt", iso := "yue", value := .subjectIsLeftImplicit }
  , { walsCode := "cha", iso := "cha", value := .subjectIsLeftImplicit }
  , { walsCode := "chn", iso := "chx", value := .subjectIsLeftImplicit }
  , { walsCode := "cic", iso := "nya", value := .subjectIsLeftImplicit }
  , { walsCode := "cch", iso := "coz", value := .subjectIsExpressedOvertly }
  , { walsCode := "chk", iso := "ckt", value := .desiderativeVerbalAffix }
  , { walsCode := "cmn", iso := "com", value := .subjectIsLeftImplicit }
  , { walsCode := "cop", iso := "cop", value := .subjectIsLeftImplicit }
  , { walsCode := "dgb", iso := "dag", value := .subjectIsExpressedOvertly }
  , { walsCode := "dgr", iso := "dta", value := .subjectIsLeftImplicit }
  , { walsCode := "drg", iso := "dar", value := .subjectIsLeftImplicit }
  , { walsCode := "dha", iso := "dsh", value := .subjectIsLeftImplicit }
  , { walsCode := "dhb", iso := "xgm", value := .subjectIsLeftImplicit }
  , { walsCode := "dhi", iso := "div", value := .subjectIsLeftImplicit }
  , { walsCode := "die", iso := "dih", value := .subjectIsExpressedOvertly }
  , { walsCode := "dre", iso := "dhv", value := .subjectIsLeftImplicit }
  , { walsCode := "eng", iso := "eng", value := .subjectIsLeftImplicit }
  , { walsCode := "epe", iso := "sja", value := .subjectIsLeftImplicit }
  , { walsCode := "err", iso := "erg", value := .subjectIsLeftImplicit }
  , { walsCode := "eve", iso := "evn", value := .desiderativeVerbalAffix }
  , { walsCode := "ewe", iso := "ewe", value := .subjectIsExpressedOvertly }
  , { walsCode := "fij", iso := "fij", value := .desiderativeParticle }
  , { walsCode := "fin", iso := "fin", value := .subjectIsLeftImplicit }
  , { walsCode := "fon", iso := "fon", value := .bothConstructionTypesExist }
  , { walsCode := "fre", iso := "fra", value := .subjectIsLeftImplicit }
  , { walsCode := "gar", iso := "grt", value := .subjectIsLeftImplicit }
  , { walsCode := "gel", iso := "nlg", value := .subjectIsLeftImplicit }
  , { walsCode := "geo", iso := "kat", value := .bothConstructionTypesExist }
  , { walsCode := "ger", iso := "deu", value := .subjectIsLeftImplicit }
  , { walsCode := "gol", iso := "gol", value := .subjectIsExpressedOvertly }
  , { walsCode := "grk", iso := "ell", value := .subjectIsExpressedOvertly }
  , { walsCode := "gua", iso := "gug", value := .desiderativeVerbalAffix }
  , { walsCode := "guu", iso := "kky", value := .subjectIsLeftImplicit }
  , { walsCode := "hat", iso := "had", value := .subjectIsExpressedOvertly }
  , { walsCode := "hau", iso := "hau", value := .subjectIsExpressedOvertly }
  , { walsCode := "heb", iso := "heb", value := .subjectIsLeftImplicit }
  , { walsCode := "hin", iso := "hin", value := .subjectIsLeftImplicit }
  , { walsCode := "hix", iso := "hix", value := .subjectIsLeftImplicit }
  , { walsCode := "hma", iso := "hmr", value := .subjectIsLeftImplicit }
  , { walsCode := "hmo", iso := "hnj", value := .subjectIsLeftImplicit }
  , { walsCode := "hoa", iso := "hoa", value := .subjectIsLeftImplicit }
  , { walsCode := "hum", iso := "huu", value := .desiderativeVerbalAffix }
  , { walsCode := "hun", iso := "hun", value := .subjectIsLeftImplicit }
  , { walsCode := "hzb", iso := "huz", value := .subjectIsLeftImplicit }
  , { walsCode := "ik", iso := "ikx", value := .subjectIsLeftImplicit }
  , { walsCode := "ika", iso := "arh", value := .subjectIsLeftImplicit }
  , { walsCode := "imo", iso := "imn", value := .subjectIsLeftImplicit }
  , { walsCode := "ind", iso := "ind", value := .subjectIsLeftImplicit }
  , { walsCode := "irq", iso := "irk", value := .subjectIsLeftImplicit }
  , { walsCode := "itz", iso := "itz", value := .desiderativeParticle }
  , { walsCode := "jab", iso := "jae", value := .subjectIsExpressedOvertly }
  , { walsCode := "jak", iso := "jac", value := .subjectIsExpressedOvertly }
  , { walsCode := "jam", iso := "djd", value := .desiderativeVerbalAffix }
  , { walsCode := "jpn", iso := "jpn", value := .desiderativeVerbalAffix }
  , { walsCode := "jel", iso := "jek", value := .subjectIsExpressedOvertly }
  , { walsCode := "juh", iso := "ktz", value := .bothConstructionTypesExist }
  , { walsCode := "klq", iso := "kmh", value := .subjectIsExpressedOvertly }
  , { walsCode := "kgu", iso := "ktg", value := .subjectIsExpressedOvertly }
  , { walsCode := "kma", iso := "kay", value := .desiderativeVerbalAffix }
  , { walsCode := "kam", iso := "xbr", value := .subjectIsLeftImplicit }
  , { walsCode := "kan", iso := "ogo", value := .subjectIsLeftImplicit }
  , { walsCode := "knd", iso := "kan", value := .subjectIsLeftImplicit }
  , { walsCode := "kao", iso := "kyj", value := .subjectIsLeftImplicit }
  , { walsCode := "kas", iso := "kas", value := .subjectIsLeftImplicit }
  , { walsCode := "kyl", iso := "eky", value := .subjectIsLeftImplicit }
  , { walsCode := "kay", iso := "gyd", value := .desiderativeVerbalAffix }
  , { walsCode := "kem", iso := "ahg", value := .subjectIsLeftImplicit }
  , { walsCode := "ker", iso := "ker", value := .subjectIsLeftImplicit }
  , { walsCode := "ket", iso := "ket", value := .subjectIsLeftImplicit }
  , { walsCode := "kty", iso := "kca", value := .subjectIsLeftImplicit }
  , { walsCode := "khm", iso := "khm", value := .subjectIsLeftImplicit }
  , { walsCode := "kmu", iso := "kjg", value := .subjectIsLeftImplicit }
  , { walsCode := "klv", iso := "kij", value := .subjectIsExpressedOvertly }
  , { walsCode := "krb", iso := "gil", value := .subjectIsLeftImplicit }
  , { walsCode := "kob", iso := "kpw", value := .desiderativeVerbalAffix }
  , { walsCode := "kod", iso := "kfa", value := .subjectIsLeftImplicit }
  , { walsCode := "kon", iso := "kng", value := .subjectIsLeftImplicit }
  , { walsCode := "kor", iso := "kor", value := .subjectIsLeftImplicit }
  , { walsCode := "kfe", iso := "kfz", value := .bothConstructionTypesExist }
  , { walsCode := "krw", iso := "khe", value := .desiderativeParticle }
  , { walsCode := "kse", iso := "ses", value := .subjectIsExpressedOvertly }
  , { walsCode := "kro", iso := "kgo", value := .subjectIsLeftImplicit }
  , { walsCode := "kya", iso := "gvn", value := .subjectIsLeftImplicit }
  , { walsCode := "kuk", iso := "bfa", value := .subjectIsLeftImplicit }
  , { walsCode := "kug", iso := "cmn", value := .subjectIsLeftImplicit }
  , { walsCode := "kut", iso := "kut", value := .subjectIsExpressedOvertly }
  , { walsCode := "kwa", iso := "kwd", value := .subjectIsExpressedOvertly }
  , { walsCode := "kwk", iso := "kwk", value := .desiderativeVerbalAffix }
  , { walsCode := "kyk", iso := "kyc", value := .desiderativeVerbalAffix }
  , { walsCode := "lad", iso := "lbj", value := .desiderativeVerbalAffix }
  , { walsCode := "lak", iso := "lbe", value := .subjectIsLeftImplicit }
  , { walsCode := "lan", iso := "laj", value := .subjectIsLeftImplicit }
  , { walsCode := "lat", iso := "lav", value := .subjectIsLeftImplicit }
  , { walsCode := "lel", iso := "lln", value := .subjectIsLeftImplicit }
  , { walsCode := "lep", iso := "lep", value := .subjectIsLeftImplicit }
  , { walsCode := "lez", iso := "lez", value := .subjectIsLeftImplicit }
  , { walsCode := "lil", iso := "lil", value := .subjectIsLeftImplicit }
  , { walsCode := "lml", iso := "lmc", value := .subjectIsExpressedOvertly }
  , { walsCode := "lin", iso := "lin", value := .bothConstructionTypesExist }
  , { walsCode := "ara", iso := "arw", value := .desiderativeVerbalAffix }
  , { walsCode := "lgu", iso := "lgu", value := .subjectIsLeftImplicit }
  , { walsCode := "luv", iso := "lue", value := .subjectIsLeftImplicit }
  , { walsCode := "mad", iso := "mhi", value := .subjectIsLeftImplicit }
  , { walsCode := "mle", iso := "mdy", value := .subjectIsLeftImplicit }
  , { walsCode := "mac", iso := "mbc", value := .desiderativeVerbalAffix }
  , { walsCode := "mdr", iso := "mad", value := .subjectIsLeftImplicit }
  , { walsCode := "mak", iso := "myh", value := .desiderativeVerbalAffix }
  , { walsCode := "mam", iso := "mam", value := .subjectIsExpressedOvertly }
  , { walsCode := "mnd", iso := "cmn", value := .subjectIsLeftImplicit }
  , { walsCode := "mao", iso := "mri", value := .subjectIsLeftImplicit }
  , { walsCode := "map", iso := "arn", value := .desiderativeParticle }
  , { walsCode := "mku", iso := "zmr", value := .desiderativeVerbalAffix }
  , { walsCode := "mhi", iso := "mar", value := .subjectIsLeftImplicit }
  , { walsCode := "mar", iso := "mrc", value := .subjectIsExpressedOvertly }
  , { walsCode := "mrt", iso := "vma", value := .subjectIsLeftImplicit }
  , { walsCode := "mts", iso := "mpq", value := .desiderativeVerbalAffix }
  , { walsCode := "may", iso := "ayz", value := .subjectIsExpressedOvertly }
  , { walsCode := "mby", iso := "myb", value := .bothConstructionTypesExist }
  , { walsCode := "mbi", iso := "baw", value := .subjectIsLeftImplicit }
  , { walsCode := "meh", iso := "gdq", value := .subjectIsExpressedOvertly }
  , { walsCode := "mei", iso := "mni", value := .subjectIsLeftImplicit }
  , { walsCode := "mde", iso := "men", value := .subjectIsExpressedOvertly }
  , { walsCode := "mid", iso := "mei", value := .subjectIsLeftImplicit }
  , { walsCode := "mis", iso := "miq", value := .subjectIsLeftImplicit }
  , { walsCode := "mxc", iso := "mig", value := .subjectIsExpressedOvertly }
  , { walsCode := "miy", iso := "mkf", value := .bothConstructionTypesExist }
  , { walsCode := "mcv", iso := "moc", value := .desiderativeVerbalAffix }
  , { walsCode := "moh", iso := "moh", value := .subjectIsExpressedOvertly }
  , { walsCode := "mno", iso := "mnr", value := .subjectIsLeftImplicit }
  , { walsCode := "mos", iso := "cas", value := .subjectIsLeftImplicit }
  , { walsCode := "mup", iso := "sur", value := .subjectIsLeftImplicit }
  , { walsCode := "mrl", iso := "mur", value := .subjectIsExpressedOvertly }
  , { walsCode := "nab", iso := "naf", value := .desiderativeVerbalAffix }
  , { walsCode := "nmi", iso := "nhx", value := .desiderativeVerbalAffix }
  , { walsCode := "nht", iso := "nhg", value := .subjectIsExpressedOvertly }
  , { walsCode := "kho", iso := "naq", value := .subjectIsLeftImplicit }
  , { walsCode := "nmb", iso := "nab", value := .desiderativeVerbalAffix }
  , { walsCode := "nph", iso := "npa", value := .subjectIsLeftImplicit }
  , { walsCode := "nav", iso := "nav", value := .subjectIsExpressedOvertly }
  , { walsCode := "ndb", iso := "nde", value := .subjectIsLeftImplicit }
  , { walsCode := "ngl", iso := "nig", value := .desiderativeVerbalAffix }
  , { walsCode := "nti", iso := "niy", value := .subjectIsExpressedOvertly }
  , { walsCode := "ngi", iso := "wyb", value := .subjectIsLeftImplicit }
  , { walsCode := "nbr", iso := "gym", value := .desiderativeParticle }
  , { walsCode := "nha", iso := "nha", value := .subjectIsLeftImplicit }
  , { walsCode := "nia", iso := "nia", value := .subjectIsExpressedOvertly }
  , { walsCode := "niu", iso := "niu", value := .subjectIsLeftImplicit }
  , { walsCode := "nko", iso := "cgg", value := .subjectIsLeftImplicit }
  , { walsCode := "nse", iso := "nse", value := .subjectIsLeftImplicit }
  , { walsCode := "nua", iso := "nxl", value := .subjectIsExpressedOvertly }
  , { walsCode := "ood", iso := "ood", value := .desiderativeVerbalAffix }
  , { walsCode := "obo", iso := "ann", value := .bothConstructionTypesExist }
  , { walsCode := "oji", iso := "", value := .desiderativeVerbalAffix }
  , { walsCode := "olu", iso := "plo", value := .desiderativeVerbalAffix }
  , { walsCode := "orh", iso := "hae", value := .bothConstructionTypesExist }
  , { walsCode := "otm", iso := "ote", value := .subjectIsExpressedOvertly }
  , { walsCode := "pms", iso := "pma", value := .subjectIsExpressedOvertly }
  , { walsCode := "pno", iso := "pao", value := .desiderativeVerbalAffix }
  , { walsCode := "pal", iso := "pau", value := .subjectIsLeftImplicit }
  , { walsCode := "pny", iso := "pnw", value := .subjectIsLeftImplicit }
  , { walsCode := "ptt", iso := "lae", value := .subjectIsLeftImplicit }
  , { walsCode := "pec", iso := "pay", value := .subjectIsLeftImplicit }
  , { walsCode := "per", iso := "pip", value := .bothConstructionTypesExist }
  , { walsCode := "prs", iso := "pes", value := .subjectIsExpressedOvertly }
  , { walsCode := "pga", iso := "plg", value := .subjectIsExpressedOvertly }
  , { walsCode := "prh", iso := "myp", value := .desiderativeVerbalAffix }
  , { walsCode := "pit", iso := "pjt", value := .subjectIsLeftImplicit }
  , { walsCode := "pop", iso := "pbe", value := .subjectIsExpressedOvertly }
  , { walsCode := "pul", iso := "puw", value := .subjectIsLeftImplicit }
  , { walsCode := "pur", iso := "tsz", value := .subjectIsLeftImplicit }
  , { walsCode := "pae", iso := "pbb", value := .subjectIsLeftImplicit }
  , { walsCode := "qaf", iso := "aar", value := .subjectIsExpressedOvertly }
  , { walsCode := "qia", iso := "", value := .desiderativeVerbalAffix }
  , { walsCode := "qhu", iso := "qub", value := .subjectIsLeftImplicit }
  , { walsCode := "qim", iso := "qvi", value := .subjectIsLeftImplicit }
  , { walsCode := "rag", iso := "lml", value := .subjectIsExpressedOvertly }
  , { walsCode := "ram", iso := "rma", value := .subjectIsLeftImplicit }
  , { walsCode := "rap", iso := "rap", value := .subjectIsLeftImplicit }
  , { walsCode := "raw", iso := "raw", value := .subjectIsLeftImplicit }
  , { walsCode := "ret", iso := "tnc", value := .subjectIsLeftImplicit }
  , { walsCode := "rom", iso := "ron", value := .subjectIsExpressedOvertly }
  , { walsCode := "rus", iso := "rus", value := .subjectIsLeftImplicit }
  , { walsCode := "sno", iso := "sme", value := .subjectIsLeftImplicit }
  , { walsCode := "slb", iso := "sbe", value := .subjectIsExpressedOvertly }
  , { walsCode := "syu", iso := "sll", value := .subjectIsExpressedOvertly }
  , { walsCode := "sam", iso := "smo", value := .desiderativeParticle }
  , { walsCode := "san", iso := "sag", value := .subjectIsLeftImplicit }
  , { walsCode := "sap", iso := "spu", value := .subjectIsLeftImplicit }
  , { walsCode := "sed", iso := "sed", value := .subjectIsLeftImplicit }
  , { walsCode := "see", iso := "trv", value := .desiderativeVerbalAffix }
  , { walsCode := "ser", iso := "sei", value := .subjectIsLeftImplicit }
  , { walsCode := "shk", iso := "shp", value := .desiderativeVerbalAffix }
  , { walsCode := "sho", iso := "shh", value := .desiderativeVerbalAffix }
  , { walsCode := "sir", iso := "sjr", value := .subjectIsExpressedOvertly }
  , { walsCode := "sla", iso := "den", value := .subjectIsExpressedOvertly }
  , { walsCode := "som", iso := "som", value := .subjectIsExpressedOvertly }
  , { walsCode := "soq", iso := "sqt", value := .subjectIsExpressedOvertly }
  , { walsCode := "spa", iso := "spa", value := .subjectIsLeftImplicit }
  , { walsCode := "squ", iso := "squ", value := .subjectIsExpressedOvertly }
  , { walsCode := "sue", iso := "sue", value := .subjectIsLeftImplicit }
  , { walsCode := "sun", iso := "sun", value := .subjectIsLeftImplicit }
  , { walsCode := "sup", iso := "spp", value := .subjectIsLeftImplicit }
  , { walsCode := "tab", iso := "mky", value := .subjectIsExpressedOvertly }
  , { walsCode := "tag", iso := "tgl", value := .subjectIsLeftImplicit }
  , { walsCode := "tmm", iso := "mla", value := .subjectIsExpressedOvertly }
  , { walsCode := "tau", iso := "tya", value := .subjectIsLeftImplicit }
  , { walsCode := "ten", iso := "tex", value := .subjectIsExpressedOvertly }
  , { walsCode := "tps", iso := "stp", value := .desiderativeVerbalAffix }
  , { walsCode := "trb", iso := "tfr", value := .bothConstructionTypesExist }
  , { walsCode := "trt", iso := "tft", value := .bothConstructionTypesExist }
  , { walsCode := "ttn", iso := "tet", value := .subjectIsExpressedOvertly }
  , { walsCode := "tha", iso := "tha", value := .subjectIsLeftImplicit }
  , { walsCode := "tib", iso := "bod", value := .subjectIsLeftImplicit }
  , { walsCode := "tid", iso := "tvo", value := .subjectIsLeftImplicit }
  , { walsCode := "tja", iso := "dih", value := .subjectIsExpressedOvertly }
  , { walsCode := "tob", iso := "tob", value := .desiderativeVerbalAffix }
  , { walsCode := "tru", iso := "tpy", value := .subjectIsLeftImplicit }
  , { walsCode := "tsi", iso := "tsi", value := .subjectIsExpressedOvertly }
  , { walsCode := "tgn", iso := "tzn", value := .desiderativeVerbalAffix }
  , { walsCode := "tuk", iso := "", value := .bothConstructionTypesExist }
  , { walsCode := "tur", iso := "tur", value := .subjectIsLeftImplicit }
  , { walsCode := "tzu", iso := "tzj", value := .subjectIsExpressedOvertly }
  , { walsCode := "udh", iso := "ude", value := .desiderativeVerbalAffix }
  , { walsCode := "udm", iso := "udm", value := .subjectIsLeftImplicit }
  , { walsCode := "uku", iso := "kuu", value := .desiderativeParticle }
  , { walsCode := "urk", iso := "urb", value := .desiderativeParticle }
  , { walsCode := "vie", iso := "vie", value := .subjectIsLeftImplicit }
  , { walsCode := "wal", iso := "van", value := .subjectIsExpressedOvertly }
  , { walsCode := "wam", iso := "wmb", value := .subjectIsLeftImplicit }
  , { walsCode := "wra", iso := "wba", value := .subjectIsLeftImplicit }
  , { walsCode := "wrm", iso := "wsa", value := .subjectIsExpressedOvertly }
  , { walsCode := "wch", iso := "mzh", value := .subjectIsExpressedOvertly }
  , { walsCode := "wlf", iso := "wol", value := .subjectIsLeftImplicit }
  , { walsCode := "yag", iso := "yad", value := .subjectIsLeftImplicit }
  , { walsCode := "ynk", iso := "kdd", value := .subjectIsLeftImplicit }
  , { walsCode := "yaq", iso := "yaq", value := .desiderativeVerbalAffix }
  , { walsCode := "ywr", iso := "ywr", value := .subjectIsExpressedOvertly }
  , { walsCode := "yey", iso := "yey", value := .subjectIsLeftImplicit }
  , { walsCode := "yim", iso := "yee", value := .subjectIsLeftImplicit }
  , { walsCode := "yir", iso := "yyr", value := .desiderativeVerbalAffix }
  , { walsCode := "yor", iso := "yor", value := .subjectIsLeftImplicit }
  , { walsCode := "yko", iso := "yux", value := .subjectIsLeftImplicit }
  , { walsCode := "ytu", iso := "ykg", value := .desiderativeVerbalAffix }
  , { walsCode := "ypk", iso := "esu", value := .desiderativeVerbalAffix }
  , { walsCode := "zaq", iso := "zpi", value := .subjectIsExpressedOvertly }
  , { walsCode := "zch", iso := "zoh", value := .desiderativeVerbalAffix }
  , { walsCode := "zul", iso := "zul", value := .subjectIsLeftImplicit }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F124A
