import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 34A: Occurrence of Nominal Plurality
@cite{haspelmath-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 34A`.

Chapter 34, 291 languages.
-/

namespace Datasets.WALS.F34A

/-- WALS 34A values. -/
inductive PluralityOccurrence where
  /-- No nominal plural (28 languages). -/
  | noNominalPlural
  /-- Only human nouns, optional (20 languages). -/
  | onlyHumanNounsOptional
  /-- Only human nouns, obligatory (40 languages). -/
  | onlyHumanNounsObligatory
  /-- All nouns, always optional (55 languages). -/
  | allNounsAlwaysOptional
  /-- All nouns, optional in inanimates (15 languages). -/
  | allNounsOptionalInInanimates
  /-- All nouns, always obligatory (133 languages). -/
  | allNounsAlwaysObligatory
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 34A dataset (291 languages). -/
def allData : List (Datapoint PluralityOccurrence) :=
  [ { walsCode := "abk", iso := "abk", value := .allNounsAlwaysObligatory }
  , { walsCode := "abu", iso := "kgr", value := .noNominalPlural }
  , { walsCode := "ace", iso := "ace", value := .noNominalPlural }
  , { walsCode := "aco", iso := "kjq", value := .allNounsAlwaysOptional }
  , { walsCode := "ady", iso := "ady", value := .allNounsAlwaysObligatory }
  , { walsCode := "ain", iso := "ain", value := .allNounsAlwaysOptional }
  , { walsCode := "ala", iso := "amp", value := .allNounsAlwaysObligatory }
  , { walsCode := "aly", iso := "aly", value := .allNounsAlwaysOptional }
  , { walsCode := "aml", iso := "omb", value := .onlyHumanNounsOptional }
  , { walsCode := "ame", iso := "aey", value := .onlyHumanNounsObligatory }
  , { walsCode := "ano", iso := "nun", value := .onlyHumanNounsOptional }
  , { walsCode := "apu", iso := "apu", value := .allNounsAlwaysObligatory }
  , { walsCode := "aeg", iso := "arz", value := .allNounsAlwaysObligatory }
  , { walsCode := "arm", iso := "hye", value := .allNounsAlwaysObligatory }
  , { walsCode := "amp", iso := "aer", value := .allNounsAlwaysOptional }
  , { walsCode := "blj", iso := "koe", value := .allNounsAlwaysObligatory }
  , { walsCode := "bab", iso := "bav", value := .allNounsAlwaysObligatory }
  , { walsCode := "bag", iso := "bmi", value := .allNounsAlwaysObligatory }
  , { walsCode := "bak", iso := "bkc", value := .allNounsAlwaysOptional }
  , { walsCode := "bao", iso := "peh", value := .allNounsAlwaysObligatory }
  , { walsCode := "brs", iso := "bsn", value := .allNounsAlwaysObligatory }
  , { walsCode := "bae", iso := "bae", value := .allNounsAlwaysOptional }
  , { walsCode := "bsq", iso := "eus", value := .allNounsAlwaysObligatory }
  , { walsCode := "baw", iso := "bgr", value := .allNounsAlwaysOptional }
  , { walsCode := "bel", iso := "byw", value := .allNounsOptionalInInanimates }
  , { walsCode := "bbw", iso := "gup", value := .onlyHumanNounsOptional }
  , { walsCode := "bii", iso := "bzr", value := .noNominalPlural }
  , { walsCode := "bla", iso := "bla", value := .allNounsAlwaysObligatory }
  , { walsCode := "boz", iso := "boz", value := .allNounsAlwaysOptional }
  , { walsCode := "brh", iso := "brh", value := .allNounsAlwaysObligatory }
  , { walsCode := "bkt", iso := "bkk", value := .allNounsAlwaysOptional }
  , { walsCode := "bud", iso := "bdm", value := .allNounsAlwaysObligatory }
  , { walsCode := "but", iso := "bxm", value := .allNounsOptionalInInanimates }
  , { walsCode := "bur", iso := "bsk", value := .allNounsAlwaysObligatory }
  , { walsCode := "cha", iso := "cha", value := .onlyHumanNounsOptional }
  , { walsCode := "chn", iso := "chx", value := .allNounsAlwaysOptional }
  , { walsCode := "cmh", iso := "ute", value := .onlyHumanNounsObligatory }
  , { walsCode := "cic", iso := "nya", value := .allNounsAlwaysObligatory }
  , { walsCode := "chi", iso := "cid", value := .noNominalPlural }
  , { walsCode := "ctm", iso := "ctm", value := .onlyHumanNounsObligatory }
  , { walsCode := "chk", iso := "ckt", value := .allNounsAlwaysObligatory }
  , { walsCode := "chv", iso := "chv", value := .allNounsOptionalInInanimates }
  , { walsCode := "ccp", iso := "coc", value := .onlyHumanNounsObligatory }
  , { walsCode := "cmn", iso := "com", value := .onlyHumanNounsObligatory }
  , { walsCode := "coo", iso := "csz", value := .onlyHumanNounsObligatory }
  , { walsCode := "cop", iso := "cop", value := .allNounsAlwaysObligatory }
  , { walsCode := "cre", iso := "crk", value := .allNounsAlwaysObligatory }
  , { walsCode := "dgb", iso := "dag", value := .allNounsAlwaysObligatory }
  , { walsCode := "dgr", iso := "dta", value := .onlyHumanNounsOptional }
  , { walsCode := "dah", iso := "dal", value := .allNounsAlwaysObligatory }
  , { walsCode := "drg", iso := "dar", value := .allNounsAlwaysObligatory }
  , { walsCode := "deg", iso := "deg", value := .allNounsAlwaysObligatory }
  , { walsCode := "dha", iso := "dsh", value := .allNounsAlwaysObligatory }
  , { walsCode := "dhi", iso := "div", value := .allNounsOptionalInInanimates }
  , { walsCode := "did", iso := "did", value := .allNounsAlwaysObligatory }
  , { walsCode := "dja", iso := "dyy", value := .allNounsAlwaysOptional }
  , { walsCode := "dji", iso := "jig", value := .allNounsAlwaysOptional }
  , { walsCode := "doy", iso := "dow", value := .allNounsOptionalInInanimates }
  , { walsCode := "dug", iso := "gwd", value := .allNounsAlwaysObligatory }
  , { walsCode := "dut", iso := "nld", value := .allNounsAlwaysObligatory }
  , { walsCode := "dyi", iso := "dbl", value := .allNounsOptionalInInanimates }
  , { walsCode := "eng", iso := "eng", value := .allNounsAlwaysObligatory }
  , { walsCode := "epe", iso := "sja", value := .onlyHumanNounsObligatory }
  , { walsCode := "err", iso := "erg", value := .allNounsAlwaysObligatory }
  , { walsCode := "eve", iso := "evn", value := .allNounsAlwaysObligatory }
  , { walsCode := "fin", iso := "fin", value := .allNounsAlwaysObligatory }
  , { walsCode := "fon", iso := "fon", value := .allNounsAlwaysObligatory }
  , { walsCode := "fre", iso := "fra", value := .allNounsAlwaysObligatory }
  , { walsCode := "fye", iso := "pym", value := .allNounsAlwaysObligatory }
  , { walsCode := "gaa", iso := "gbu", value := .onlyHumanNounsObligatory }
  , { walsCode := "gap", iso := "pwg", value := .onlyHumanNounsObligatory }
  , { walsCode := "gar", iso := "grt", value := .allNounsAlwaysOptional }
  , { walsCode := "geo", iso := "kat", value := .allNounsAlwaysObligatory }
  , { walsCode := "ger", iso := "deu", value := .allNounsAlwaysObligatory }
  , { walsCode := "gol", iso := "gol", value := .allNounsAlwaysObligatory }
  , { walsCode := "grb", iso := "grj", value := .allNounsAlwaysObligatory }
  , { walsCode := "grk", iso := "ell", value := .allNounsAlwaysObligatory }
  , { walsCode := "grw", iso := "kal", value := .allNounsAlwaysObligatory }
  , { walsCode := "gua", iso := "gug", value := .onlyHumanNounsOptional }
  , { walsCode := "guj", iso := "guj", value := .allNounsAlwaysObligatory }
  , { walsCode := "grg", iso := "gge", value := .noNominalPlural }
  , { walsCode := "gus", iso := "guz", value := .allNounsAlwaysObligatory }
  , { walsCode := "hat", iso := "had", value := .onlyHumanNounsOptional }
  , { walsCode := "hau", iso := "hau", value := .allNounsAlwaysObligatory }
  , { walsCode := "hdi", iso := "xed", value := .allNounsAlwaysOptional }
  , { walsCode := "heb", iso := "heb", value := .allNounsAlwaysObligatory }
  , { walsCode := "hin", iso := "hin", value := .allNounsAlwaysObligatory }
  , { walsCode := "hix", iso := "hix", value := .onlyHumanNounsOptional }
  , { walsCode := "hma", iso := "hmr", value := .allNounsAlwaysOptional }
  , { walsCode := "hmo", iso := "hnj", value := .noNominalPlural }
  , { walsCode := "hoa", iso := "hoa", value := .allNounsAlwaysObligatory }
  , { walsCode := "hun", iso := "hun", value := .allNounsAlwaysObligatory }
  , { walsCode := "hzb", iso := "huz", value := .allNounsAlwaysObligatory }
  , { walsCode := "ice", iso := "isl", value := .allNounsAlwaysObligatory }
  , { walsCode := "ik", iso := "ikx", value := .allNounsAlwaysObligatory }
  , { walsCode := "imo", iso := "imn", value := .noNominalPlural }
  , { walsCode := "ind", iso := "ind", value := .allNounsAlwaysOptional }
  , { walsCode := "irq", iso := "irk", value := .allNounsAlwaysObligatory }
  , { walsCode := "iri", iso := "gle", value := .allNounsAlwaysObligatory }
  , { walsCode := "ita", iso := "ita", value := .allNounsAlwaysObligatory }
  , { walsCode := "itz", iso := "itz", value := .allNounsAlwaysObligatory }
  , { walsCode := "jak", iso := "jac", value := .allNounsAlwaysOptional }
  , { walsCode := "jam", iso := "djd", value := .onlyHumanNounsObligatory }
  , { walsCode := "jpn", iso := "jpn", value := .onlyHumanNounsOptional }
  , { walsCode := "juh", iso := "ktz", value := .allNounsAlwaysObligatory }
  , { walsCode := "kgu", iso := "ktg", value := .onlyHumanNounsObligatory }
  , { walsCode := "kma", iso := "kay", value := .onlyHumanNounsObligatory }
  , { walsCode := "kan", iso := "ogo", value := .noNominalPlural }
  , { walsCode := "knd", iso := "kan", value := .allNounsOptionalInInanimates }
  , { walsCode := "knr", iso := "knc", value := .allNounsAlwaysObligatory }
  , { walsCode := "kay", iso := "gyd", value := .noNominalPlural }
  , { walsCode := "kem", iso := "ahg", value := .allNounsAlwaysObligatory }
  , { walsCode := "ket", iso := "ket", value := .allNounsAlwaysObligatory }
  , { walsCode := "kha", iso := "khk", value := .allNounsAlwaysOptional }
  , { walsCode := "kmh", iso := "kjl", value := .allNounsAlwaysObligatory }
  , { walsCode := "khm", iso := "khm", value := .allNounsAlwaysOptional }
  , { walsCode := "koa", iso := "cku", value := .onlyHumanNounsOptional }
  , { walsCode := "kob", iso := "kpw", value := .onlyHumanNounsObligatory }
  , { walsCode := "kod", iso := "kfa", value := .onlyHumanNounsObligatory }
  , { walsCode := "kol", iso := "kfb", value := .allNounsAlwaysObligatory }
  , { walsCode := "kmb", iso := "", value := .noNominalPlural }
  , { walsCode := "kda", iso := "kfc", value := .allNounsAlwaysObligatory }
  , { walsCode := "kkn", iso := "knn", value := .allNounsAlwaysObligatory }
  , { walsCode := "kku", iso := "kfq", value := .onlyHumanNounsObligatory }
  , { walsCode := "kfe", iso := "kfz", value := .allNounsAlwaysObligatory }
  , { walsCode := "krw", iso := "khe", value := .onlyHumanNounsObligatory }
  , { walsCode := "kch", iso := "khq", value := .allNounsAlwaysObligatory }
  , { walsCode := "kro", iso := "kgo", value := .allNounsAlwaysObligatory }
  , { walsCode := "kya", iso := "gvn", value := .allNounsAlwaysOptional }
  , { walsCode := "kuk", iso := "bfa", value := .allNounsAlwaysObligatory }
  , { walsCode := "kuo", iso := "kto", value := .allNounsAlwaysObligatory }
  , { walsCode := "krd", iso := "ckb", value := .allNounsAlwaysObligatory }
  , { walsCode := "kut", iso := "kut", value := .onlyHumanNounsObligatory }
  , { walsCode := "kwa", iso := "kwd", value := .allNounsAlwaysOptional }
  , { walsCode := "kat", iso := "kmg", value := .onlyHumanNounsOptional }
  , { walsCode := "lak", iso := "lbe", value := .allNounsAlwaysObligatory }
  , { walsCode := "lmg", iso := "hia", value := .allNounsAlwaysOptional }
  , { walsCode := "lan", iso := "laj", value := .onlyHumanNounsObligatory }
  , { walsCode := "lat", iso := "lav", value := .allNounsAlwaysObligatory }
  , { walsCode := "lav", iso := "lvk", value := .allNounsAlwaysObligatory }
  , { walsCode := "laz", iso := "lzz", value := .allNounsOptionalInInanimates }
  , { walsCode := "lel", iso := "lln", value := .onlyHumanNounsObligatory }
  , { walsCode := "lep", iso := "lep", value := .allNounsAlwaysObligatory }
  , { walsCode := "lez", iso := "lez", value := .allNounsAlwaysObligatory }
  , { walsCode := "lil", iso := "lil", value := .allNounsAlwaysObligatory }
  , { walsCode := "lml", iso := "lmc", value := .noNominalPlural }
  , { walsCode := "lit", iso := "lit", value := .allNounsAlwaysObligatory }
  , { walsCode := "ara", iso := "arw", value := .allNounsOptionalInInanimates }
  , { walsCode := "lug", iso := "lgg", value := .allNounsOptionalInInanimates }
  , { walsCode := "luv", iso := "lue", value := .allNounsAlwaysObligatory }
  , { walsCode := "mad", iso := "mhi", value := .onlyHumanNounsObligatory }
  , { walsCode := "mac", iso := "mbc", value := .allNounsOptionalInInanimates }
  , { walsCode := "mdm", iso := "dmd", value := .noNominalPlural }
  , { walsCode := "mdr", iso := "mad", value := .allNounsAlwaysOptional }
  , { walsCode := "mpr", iso := "", value := .allNounsAlwaysOptional }
  , { walsCode := "maj", iso := "mpe", value := .allNounsAlwaysObligatory }
  , { walsCode := "mym", iso := "mal", value := .allNounsAlwaysObligatory }
  , { walsCode := "mlt", iso := "mlt", value := .allNounsAlwaysObligatory }
  , { walsCode := "mto", iso := "kmj", value := .onlyHumanNounsObligatory }
  , { walsCode := "mam", iso := "mam", value := .allNounsAlwaysOptional }
  , { walsCode := "mnm", iso := "mva", value := .noNominalPlural }
  , { walsCode := "mnd", iso := "cmn", value := .onlyHumanNounsOptional }
  , { walsCode := "mgg", iso := "mjg", value := .allNounsAlwaysOptional }
  , { walsCode := "mao", iso := "mri", value := .allNounsAlwaysObligatory }
  , { walsCode := "map", iso := "arn", value := .noNominalPlural }
  , { walsCode := "mku", iso := "zmr", value := .noNominalPlural }
  , { walsCode := "mar", iso := "mrc", value := .onlyHumanNounsOptional }
  , { walsCode := "mts", iso := "mpq", value := .onlyHumanNounsObligatory }
  , { walsCode := "myr", iso := "mcf", value := .onlyHumanNounsOptional }
  , { walsCode := "may", iso := "ayz", value := .noNominalPlural }
  , { walsCode := "meh", iso := "gdq", value := .allNounsOptionalInInanimates }
  , { walsCode := "mid", iso := "mei", value := .allNounsAlwaysOptional }
  , { walsCode := "mig", iso := "mmy", value := .allNounsAlwaysObligatory }
  , { walsCode := "mxc", iso := "mig", value := .allNounsAlwaysOptional }
  , { walsCode := "miy", iso := "mkf", value := .allNounsAlwaysObligatory }
  , { walsCode := "mog", iso := "mhj", value := .allNounsAlwaysOptional }
  , { walsCode := "mok", iso := "mkj", value := .allNounsAlwaysObligatory }
  , { walsCode := "mos", iso := "cas", value := .allNounsOptionalInInanimates }
  , { walsCode := "mdg", iso := "mua", value := .allNounsAlwaysObligatory }
  , { walsCode := "nab", iso := "naf", value := .allNounsAlwaysOptional }
  , { walsCode := "nmi", iso := "nhx", value := .allNounsAlwaysObligatory }
  , { walsCode := "nph", iso := "npa", value := .allNounsAlwaysOptional }
  , { walsCode := "ndb", iso := "nde", value := .allNounsAlwaysObligatory }
  , { walsCode := "nep", iso := "npi", value := .allNounsAlwaysOptional }
  , { walsCode := "new", iso := "new", value := .onlyHumanNounsObligatory }
  , { walsCode := "ngl", iso := "nig", value := .onlyHumanNounsOptional }
  , { walsCode := "nti", iso := "niy", value := .onlyHumanNounsObligatory }
  , { walsCode := "ngi", iso := "wyb", value := .allNounsAlwaysOptional }
  , { walsCode := "nha", iso := "nha", value := .allNounsAlwaysOptional }
  , { walsCode := "nia", iso := "nia", value := .noNominalPlural }
  , { walsCode := "niu", iso := "niu", value := .allNounsAlwaysObligatory }
  , { walsCode := "niv", iso := "niv", value := .allNounsAlwaysOptional }
  , { walsCode := "nse", iso := "nse", value := .allNounsAlwaysObligatory }
  , { walsCode := "nua", iso := "nxl", value := .allNounsAlwaysObligatory }
  , { walsCode := "nbd", iso := "dgl", value := .allNounsAlwaysObligatory }
  , { walsCode := "oji", iso := "", value := .allNounsAlwaysObligatory }
  , { walsCode := "olu", iso := "plo", value := .allNounsAlwaysOptional }
  , { walsCode := "oya", iso := "ory", value := .allNounsAlwaysOptional }
  , { walsCode := "orh", iso := "hae", value := .onlyHumanNounsOptional }
  , { walsCode := "pno", iso := "pao", value := .allNounsOptionalInInanimates }
  , { walsCode := "pal", iso := "pau", value := .onlyHumanNounsObligatory }
  , { walsCode := "pan", iso := "pan", value := .allNounsAlwaysObligatory }
  , { walsCode := "ptt", iso := "lae", value := .allNounsAlwaysObligatory }
  , { walsCode := "per", iso := "pip", value := .onlyHumanNounsObligatory }
  , { walsCode := "pga", iso := "plg", value := .allNounsAlwaysObligatory }
  , { walsCode := "prh", iso := "myp", value := .noNominalPlural }
  , { walsCode := "pmc", iso := "poo", value := .onlyHumanNounsOptional }
  , { walsCode := "pme", iso := "peb", value := .onlyHumanNounsObligatory }
  , { walsCode := "por", iso := "por", value := .allNounsAlwaysObligatory }
  , { walsCode := "qaf", iso := "aar", value := .allNounsAlwaysObligatory }
  , { walsCode := "qia", iso := "", value := .allNounsAlwaysOptional }
  , { walsCode := "qim", iso := "qvi", value := .allNounsAlwaysObligatory }
  , { walsCode := "ram", iso := "rma", value := .onlyHumanNounsObligatory }
  , { walsCode := "rap", iso := "rap", value := .allNounsAlwaysOptional }
  , { walsCode := "ret", iso := "tnc", value := .onlyHumanNounsObligatory }
  , { walsCode := "rom", iso := "ron", value := .allNounsAlwaysObligatory }
  , { walsCode := "rot", iso := "rtm", value := .onlyHumanNounsObligatory }
  , { walsCode := "rus", iso := "rus", value := .allNounsAlwaysObligatory }
  , { walsCode := "ski", iso := "sjd", value := .allNounsAlwaysObligatory }
  , { walsCode := "sno", iso := "sme", value := .allNounsAlwaysObligatory }
  , { walsCode := "slb", iso := "sbe", value := .onlyHumanNounsObligatory }
  , { walsCode := "syu", iso := "sll", value := .noNominalPlural }
  , { walsCode := "sdw", iso := "sad", value := .onlyHumanNounsObligatory }
  , { walsCode := "sgu", iso := "snq", value := .allNounsAlwaysObligatory }
  , { walsCode := "sed", iso := "sed", value := .onlyHumanNounsObligatory }
  , { walsCode := "skp", iso := "sel", value := .allNounsAlwaysObligatory }
  , { walsCode := "scr", iso := "hbs", value := .allNounsAlwaysObligatory }
  , { walsCode := "shk", iso := "shp", value := .allNounsAlwaysOptional }
  , { walsCode := "sho", iso := "shh", value := .allNounsAlwaysObligatory }
  , { walsCode := "sir", iso := "sjr", value := .allNounsAlwaysObligatory }
  , { walsCode := "som", iso := "som", value := .allNounsAlwaysObligatory }
  , { walsCode := "son", iso := "sov", value := .noNominalPlural }
  , { walsCode := "soq", iso := "sqt", value := .allNounsAlwaysObligatory }
  , { walsCode := "sea", iso := "tvk", value := .allNounsAlwaysOptional }
  , { walsCode := "spa", iso := "spa", value := .allNounsAlwaysObligatory }
  , { walsCode := "sud", iso := "tgo", value := .onlyHumanNounsObligatory }
  , { walsCode := "sue", iso := "sue", value := .onlyHumanNounsOptional }
  , { walsCode := "sun", iso := "sun", value := .allNounsAlwaysOptional }
  , { walsCode := "sup", iso := "spp", value := .allNounsAlwaysObligatory }
  , { walsCode := "swa", iso := "swh", value := .allNounsAlwaysObligatory }
  , { walsCode := "swe", iso := "swe", value := .allNounsAlwaysObligatory }
  , { walsCode := "tab", iso := "mky", value := .onlyHumanNounsObligatory }
  , { walsCode := "tag", iso := "tgl", value := .allNounsAlwaysOptional }
  , { walsCode := "taf", iso := "sps", value := .allNounsAlwaysObligatory }
  , { walsCode := "tkl", iso := "tkm", value := .allNounsAlwaysOptional }
  , { walsCode := "tmm", iso := "mla", value := .onlyHumanNounsObligatory }
  , { walsCode := "tml", iso := "tam", value := .allNounsOptionalInInanimates }
  , { walsCode := "tau", iso := "tya", value := .allNounsAlwaysOptional }
  , { walsCode := "tpn", iso := "ntp", value := .allNounsAlwaysObligatory }
  , { walsCode := "tps", iso := "stp", value := .allNounsAlwaysObligatory }
  , { walsCode := "trb", iso := "tfr", value := .allNounsAlwaysOptional }
  , { walsCode := "ttn", iso := "tet", value := .allNounsAlwaysOptional }
  , { walsCode := "tis", iso := "bod", value := .noNominalPlural }
  , { walsCode := "tib", iso := "bod", value := .allNounsAlwaysOptional }
  , { walsCode := "tid", iso := "tvo", value := .noNominalPlural }
  , { walsCode := "tig", iso := "tir", value := .allNounsAlwaysObligatory }
  , { walsCode := "tja", iso := "dih", value := .onlyHumanNounsObligatory }
  , { walsCode := "tik", iso := "tik", value := .allNounsAlwaysObligatory }
  , { walsCode := "tin", iso := "cir", value := .onlyHumanNounsObligatory }
  , { walsCode := "tiw", iso := "tiw", value := .onlyHumanNounsObligatory }
  , { walsCode := "tlo", iso := "tlb", value := .noNominalPlural }
  , { walsCode := "trw", iso := "trw", value := .allNounsAlwaysObligatory }
  , { walsCode := "tru", iso := "tpy", value := .onlyHumanNounsObligatory }
  , { walsCode := "tgn", iso := "tzn", value := .allNounsAlwaysObligatory }
  , { walsCode := "tur", iso := "tur", value := .allNounsAlwaysObligatory }
  , { walsCode := "tvl", iso := "tvl", value := .allNounsAlwaysObligatory }
  , { walsCode := "tzu", iso := "tzj", value := .allNounsAlwaysObligatory }
  , { walsCode := "udh", iso := "ude", value := .onlyHumanNounsOptional }
  , { walsCode := "udm", iso := "udm", value := .allNounsAlwaysObligatory }
  , { walsCode := "uli", iso := "uli", value := .allNounsAlwaysOptional }
  , { walsCode := "usa", iso := "wnu", value := .noNominalPlural }
  , { walsCode := "vie", iso := "vie", value := .allNounsAlwaysOptional }
  , { walsCode := "wam", iso := "wmb", value := .allNounsAlwaysOptional }
  , { walsCode := "wrd", iso := "wrr", value := .allNounsAlwaysOptional }
  , { walsCode := "wir", iso := "wgu", value := .noNominalPlural }
  , { walsCode := "yny", iso := "jao", value := .onlyHumanNounsOptional }
  , { walsCode := "yaq", iso := "yaq", value := .allNounsAlwaysObligatory }
  , { walsCode := "ywl", iso := "yok", value := .allNounsAlwaysOptional }
  , { walsCode := "ywr", iso := "ywr", value := .allNounsAlwaysOptional }
  , { walsCode := "yey", iso := "yey", value := .allNounsAlwaysObligatory }
  , { walsCode := "yid", iso := "yii", value := .noNominalPlural }
  , { walsCode := "yim", iso := "yee", value := .allNounsAlwaysObligatory }
  , { walsCode := "yng", iso := "yia", value := .noNominalPlural }
  , { walsCode := "yor", iso := "yor", value := .allNounsAlwaysOptional }
  , { walsCode := "ypk", iso := "esu", value := .allNounsAlwaysObligatory }
  , { walsCode := "zaq", iso := "zpi", value := .noNominalPlural }
  , { walsCode := "zay", iso := "zay", value := .allNounsAlwaysObligatory }
  , { walsCode := "zaz", iso := "diq", value := .allNounsAlwaysObligatory }
  , { walsCode := "zch", iso := "zoh", value := .allNounsAlwaysObligatory }
  , { walsCode := "zul", iso := "zul", value := .allNounsAlwaysObligatory }
  , { walsCode := "zun", iso := "zun", value := .allNounsAlwaysObligatory }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F34A
