import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 46A: Indefinite Pronouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 46A`.

Chapter 46, 326 languages.
-/

namespace Datasets.WALS.F46A

/-- WALS 46A values. -/
inductive IndefinitePronouns where
  /-- Interrogative-based (194 languages). -/
  | interrogativeBased
  /-- Generic-noun-based (85 languages). -/
  | genericNounBased
  /-- Special (22 languages). -/
  | special
  /-- Mixed (23 languages). -/
  | mixed
  /-- Existential construction (2 languages). -/
  | existentialConstruction
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 46A dataset (326 languages). -/
def allData : List (Datapoint IndefinitePronouns) :=
  [ { walsCode := "abk", iso := "abk", value := .special }
  , { walsCode := "abu", iso := "kgr", value := .genericNounBased }
  , { walsCode := "ace", iso := "ace", value := .interrogativeBased }
  , { walsCode := "aco", iso := "kjq", value := .interrogativeBased }
  , { walsCode := "ain", iso := "ain", value := .interrogativeBased }
  , { walsCode := "abm", iso := "akz", value := .interrogativeBased }
  , { walsCode := "aso", iso := "alt", value := .interrogativeBased }
  , { walsCode := "aly", iso := "aly", value := .interrogativeBased }
  , { walsCode := "aml", iso := "omb", value := .genericNounBased }
  , { walsCode := "ame", iso := "aey", value := .genericNounBased }
  , { walsCode := "amu", iso := "ame", value := .interrogativeBased }
  , { walsCode := "agt", iso := "awg", value := .interrogativeBased }
  , { walsCode := "ano", iso := "nun", value := .genericNounBased }
  , { walsCode := "aeg", iso := "arz", value := .genericNounBased }
  , { walsCode := "ana", iso := "aro", value := .interrogativeBased }
  , { walsCode := "amp", iso := "aer", value := .genericNounBased }
  , { walsCode := "ass", iso := "asm", value := .interrogativeBased }
  , { walsCode := "atc", iso := "upv", value := .interrogativeBased }
  , { walsCode := "awp", iso := "kwi", value := .interrogativeBased }
  , { walsCode := "aze", iso := "", value := .interrogativeBased }
  , { walsCode := "bab", iso := "bav", value := .genericNounBased }
  , { walsCode := "bdm", iso := "bia", value := .interrogativeBased }
  , { walsCode := "bag", iso := "bmi", value := .genericNounBased }
  , { walsCode := "bak", iso := "bkc", value := .genericNounBased }
  , { walsCode := "bam", iso := "bam", value := .genericNounBased }
  , { walsCode := "bao", iso := "peh", value := .interrogativeBased }
  , { walsCode := "bsk", iso := "bak", value := .interrogativeBased }
  , { walsCode := "bsq", iso := "eus", value := .interrogativeBased }
  , { walsCode := "baw", iso := "bgr", value := .interrogativeBased }
  , { walsCode := "blr", iso := "bel", value := .interrogativeBased }
  , { walsCode := "bbw", iso := "gup", value := .mixed }
  , { walsCode := "boz", iso := "boz", value := .mixed }
  , { walsCode := "brh", iso := "brh", value := .special }
  , { walsCode := "bud", iso := "bdm", value := .genericNounBased }
  , { walsCode := "bug", iso := "bug", value := .interrogativeBased }
  , { walsCode := "bul", iso := "bul", value := .interrogativeBased }
  , { walsCode := "but", iso := "bxm", value := .interrogativeBased }
  , { walsCode := "bur", iso := "bsk", value := .interrogativeBased }
  , { walsCode := "cah", iso := "chl", value := .interrogativeBased }
  , { walsCode := "cnl", iso := "ram", value := .interrogativeBased }
  , { walsCode := "cnt", iso := "yue", value := .special }
  , { walsCode := "chn", iso := "chx", value := .interrogativeBased }
  , { walsCode := "cic", iso := "nya", value := .genericNounBased }
  , { walsCode := "ctm", iso := "ctm", value := .interrogativeBased }
  , { walsCode := "cch", iso := "coz", value := .interrogativeBased }
  , { walsCode := "chk", iso := "ckt", value := .interrogativeBased }
  , { walsCode := "chv", iso := "chv", value := .interrogativeBased }
  , { walsCode := "cmn", iso := "com", value := .interrogativeBased }
  , { walsCode := "coo", iso := "csz", value := .interrogativeBased }
  , { walsCode := "crk", iso := "mus", value := .interrogativeBased }
  , { walsCode := "cri", iso := "crh", value := .mixed }
  , { walsCode := "dgb", iso := "dag", value := .genericNounBased }
  , { walsCode := "diy", iso := "dif", value := .interrogativeBased }
  , { walsCode := "dja", iso := "dyy", value := .interrogativeBased }
  , { walsCode := "djp", iso := "dwu", value := .interrogativeBased }
  , { walsCode := "djr", iso := "ddj", value := .interrogativeBased }
  , { walsCode := "dji", iso := "jig", value := .interrogativeBased }
  , { walsCode := "doy", iso := "dow", value := .genericNounBased }
  , { walsCode := "dut", iso := "nld", value := .special }
  , { walsCode := "dyi", iso := "dbl", value := .interrogativeBased }
  , { walsCode := "ene", iso := "", value := .interrogativeBased }
  , { walsCode := "eng", iso := "eng", value := .genericNounBased }
  , { walsCode := "err", iso := "erg", value := .genericNounBased }
  , { walsCode := "est", iso := "ekk", value := .interrogativeBased }
  , { walsCode := "evn", iso := "eve", value := .interrogativeBased }
  , { walsCode := "eve", iso := "evn", value := .interrogativeBased }
  , { walsCode := "ewe", iso := "ewe", value := .genericNounBased }
  , { walsCode := "fin", iso := "fin", value := .special }
  , { walsCode := "fon", iso := "fon", value := .genericNounBased }
  , { walsCode := "fre", iso := "fra", value := .genericNounBased }
  , { walsCode := "ful", iso := "fun", value := .interrogativeBased }
  , { walsCode := "fue", iso := "fud", value := .genericNounBased }
  , { walsCode := "gaa", iso := "gbu", value := .interrogativeBased }
  , { walsCode := "gag", iso := "gag", value := .interrogativeBased }
  , { walsCode := "gam", iso := "gmv", value := .genericNounBased }
  , { walsCode := "gar", iso := "grt", value := .interrogativeBased }
  , { walsCode := "gbb", iso := "gbp", value := .genericNounBased }
  , { walsCode := "geo", iso := "kat", value := .interrogativeBased }
  , { walsCode := "ger", iso := "deu", value := .mixed }
  , { walsCode := "goa", iso := "guc", value := .interrogativeBased }
  , { walsCode := "gol", iso := "gol", value := .genericNounBased }
  , { walsCode := "goo", iso := "gni", value := .interrogativeBased }
  , { walsCode := "grk", iso := "ell", value := .interrogativeBased }
  , { walsCode := "grw", iso := "kal", value := .interrogativeBased }
  , { walsCode := "gua", iso := "gug", value := .mixed }
  , { walsCode := "gum", iso := "kgs", value := .interrogativeBased }
  , { walsCode := "grg", iso := "gge", value := .interrogativeBased }
  , { walsCode := "guu", iso := "kky", value := .interrogativeBased }
  , { walsCode := "hau", iso := "hau", value := .genericNounBased }
  , { walsCode := "hay", iso := "vay", value := .interrogativeBased }
  , { walsCode := "heb", iso := "heb", value := .interrogativeBased }
  , { walsCode := "hin", iso := "hin", value := .special }
  , { walsCode := "hmo", iso := "hnj", value := .interrogativeBased }
  , { walsCode := "htc", iso := "hus", value := .interrogativeBased }
  , { walsCode := "hun", iso := "hun", value := .interrogativeBased }
  , { walsCode := "hzb", iso := "huz", value := .interrogativeBased }
  , { walsCode := "hup", iso := "hup", value := .interrogativeBased }
  , { walsCode := "ibi", iso := "ibb", value := .genericNounBased }
  , { walsCode := "ice", iso := "isl", value := .interrogativeBased }
  , { walsCode := "ilo", iso := "ilo", value := .genericNounBased }
  , { walsCode := "ind", iso := "ind", value := .genericNounBased }
  , { walsCode := "irq", iso := "irk", value := .genericNounBased }
  , { walsCode := "iri", iso := "gle", value := .genericNounBased }
  , { walsCode := "ita", iso := "ita", value := .genericNounBased }
  , { walsCode := "itz", iso := "itz", value := .interrogativeBased }
  , { walsCode := "jak", iso := "jac", value := .interrogativeBased }
  , { walsCode := "jam", iso := "djd", value := .interrogativeBased }
  , { walsCode := "jpn", iso := "jpn", value := .interrogativeBased }
  , { walsCode := "jaq", iso := "jqr", value := .interrogativeBased }
  , { walsCode := "kng", iso := "kgp", value := .interrogativeBased }
  , { walsCode := "klq", iso := "kmh", value := .genericNounBased }
  , { walsCode := "kgu", iso := "ktg", value := .special }
  , { walsCode := "kma", iso := "kay", value := .interrogativeBased }
  , { walsCode := "kan", iso := "ogo", value := .genericNounBased }
  , { walsCode := "knd", iso := "kan", value := .interrogativeBased }
  , { walsCode := "krc", iso := "krc", value := .interrogativeBased }
  , { walsCode := "krm", iso := "kdr", value := .interrogativeBased }
  , { walsCode := "kkp", iso := "kaa", value := .special }
  , { walsCode := "krl", iso := "krl", value := .interrogativeBased }
  , { walsCode := "krk", iso := "kyh", value := .interrogativeBased }
  , { walsCode := "kas", iso := "kas", value := .special }
  , { walsCode := "kay", iso := "gyd", value := .interrogativeBased }
  , { walsCode := "kaz", iso := "kaz", value := .mixed }
  , { walsCode := "krq", iso := "krk", value := .special }
  , { walsCode := "ket", iso := "ket", value := .interrogativeBased }
  , { walsCode := "khk", iso := "kjh", value := .interrogativeBased }
  , { walsCode := "kmh", iso := "kjl", value := .interrogativeBased }
  , { walsCode := "kty", iso := "kca", value := .interrogativeBased }
  , { walsCode := "khs", iso := "kha", value := .interrogativeBased }
  , { walsCode := "khm", iso := "khm", value := .mixed }
  , { walsCode := "kmu", iso := "kjg", value := .special }
  , { walsCode := "klv", iso := "kij", value := .mixed }
  , { walsCode := "kio", iso := "kio", value := .interrogativeBased }
  , { walsCode := "kgz", iso := "kir", value := .interrogativeBased }
  , { walsCode := "koa", iso := "cku", value := .interrogativeBased }
  , { walsCode := "kob", iso := "kpw", value := .genericNounBased }
  , { walsCode := "kod", iso := "kfa", value := .interrogativeBased }
  , { walsCode := "kop", iso := "koi", value := .interrogativeBased }
  , { walsCode := "kzy", iso := "kpv", value := .interrogativeBased }
  , { walsCode := "kor", iso := "kor", value := .interrogativeBased }
  , { walsCode := "kku", iso := "kfq", value := .interrogativeBased }
  , { walsCode := "kfe", iso := "kfz", value := .genericNounBased }
  , { walsCode := "kry", iso := "kpy", value := .interrogativeBased }
  , { walsCode := "kse", iso := "ses", value := .genericNounBased }
  , { walsCode := "ksi", iso := "puo", value := .interrogativeBased }
  , { walsCode := "knc", iso := "uwa", value := .interrogativeBased }
  , { walsCode := "kya", iso := "gvn", value := .genericNounBased }
  , { walsCode := "kji", iso := "kmr", value := .genericNounBased }
  , { walsCode := "kut", iso := "kut", value := .interrogativeBased }
  , { walsCode := "kwr", iso := "tnk", value := .genericNounBased }
  , { walsCode := "kyk", iso := "kyc", value := .genericNounBased }
  , { walsCode := "kat", iso := "kmg", value := .genericNounBased }
  , { walsCode := "lak", iso := "lbe", value := .interrogativeBased }
  , { walsCode := "lkt", iso := "lkt", value := .interrogativeBased }
  , { walsCode := "lan", iso := "laj", value := .genericNounBased }
  , { walsCode := "lat", iso := "lav", value := .interrogativeBased }
  , { walsCode := "lav", iso := "lvk", value := .genericNounBased }
  , { walsCode := "lel", iso := "lln", value := .genericNounBased }
  , { walsCode := "lez", iso := "lez", value := .interrogativeBased }
  , { walsCode := "lil", iso := "lil", value := .interrogativeBased }
  , { walsCode := "lml", iso := "lmc", value := .interrogativeBased }
  , { walsCode := "lit", iso := "lit", value := .interrogativeBased }
  , { walsCode := "lgu", iso := "lgu", value := .genericNounBased }
  , { walsCode := "lug", iso := "lgg", value := .genericNounBased }
  , { walsCode := "mle", iso := "mdy", value := .genericNounBased }
  , { walsCode := "mac", iso := "mbc", value := .interrogativeBased }
  , { walsCode := "mai", iso := "mai", value := .interrogativeBased }
  , { walsCode := "mak", iso := "myh", value := .special }
  , { walsCode := "mal", iso := "plt", value := .genericNounBased }
  , { walsCode := "mlk", iso := "mpb", value := .interrogativeBased }
  , { walsCode := "mym", iso := "mal", value := .interrogativeBased }
  , { walsCode := "mlg", iso := "", value := .mixed }
  , { walsCode := "mlt", iso := "mlt", value := .genericNounBased }
  , { walsCode := "mnd", iso := "cmn", value := .mixed }
  , { walsCode := "myi", iso := "mpc", value := .interrogativeBased }
  , { walsCode := "mns", iso := "mns", value := .special }
  , { walsCode := "mao", iso := "mri", value := .mixed }
  , { walsCode := "mra", iso := "mec", value := .interrogativeBased }
  , { walsCode := "mhi", iso := "mar", value := .interrogativeBased }
  , { walsCode := "mrg", iso := "mrt", value := .genericNounBased }
  , { walsCode := "mah", iso := "mrj", value := .interrogativeBased }
  , { walsCode := "mme", iso := "mhr", value := .interrogativeBased }
  , { walsCode := "mar", iso := "mrc", value := .interrogativeBased }
  , { walsCode := "mrh", iso := "mfr", value := .interrogativeBased }
  , { walsCode := "msh", iso := "mah", value := .genericNounBased }
  , { walsCode := "mrt", iso := "vma", value := .interrogativeBased }
  , { walsCode := "sum", iso := "yan", value := .genericNounBased }
  , { walsCode := "may", iso := "ayz", value := .genericNounBased }
  , { walsCode := "mby", iso := "myb", value := .genericNounBased }
  , { walsCode := "mbi", iso := "baw", value := .genericNounBased }
  , { walsCode := "mei", iso := "mni", value := .interrogativeBased }
  , { walsCode := "mde", iso := "men", value := .genericNounBased }
  , { walsCode := "mic", iso := "mic", value := .interrogativeBased }
  , { walsCode := "mis", iso := "miq", value := .genericNounBased }
  , { walsCode := "mss", iso := "skd", value := .interrogativeBased }
  , { walsCode := "mcv", iso := "moc", value := .existentialConstruction }
  , { walsCode := "moe", iso := "myv", value := .interrogativeBased }
  , { walsCode := "mmo", iso := "mdf", value := .interrogativeBased }
  , { walsCode := "mos", iso := "cas", value := .mixed }
  , { walsCode := "mun", iso := "unr", value := .interrogativeBased }
  , { walsCode := "mrw", iso := "zmu", value := .interrogativeBased }
  , { walsCode := "mgu", iso := "mug", value := .genericNounBased }
  , { walsCode := "nht", iso := "nhg", value := .interrogativeBased }
  , { walsCode := "nai", iso := "gld", value := .interrogativeBased }
  , { walsCode := "nav", iso := "nav", value := .interrogativeBased }
  , { walsCode := "ndb", iso := "nde", value := .genericNounBased }
  , { walsCode := "ndj", iso := "djj", value := .interrogativeBased }
  , { walsCode := "neg", iso := "neg", value := .interrogativeBased }
  , { walsCode := "nel", iso := "nee", value := .special }
  , { walsCode := "ntu", iso := "yrk", value := .interrogativeBased }
  , { walsCode := "nwd", iso := "new", value := .interrogativeBased }
  , { walsCode := "nez", iso := "nez", value := .interrogativeBased }
  , { walsCode := "nga", iso := "nio", value := .interrogativeBased }
  , { walsCode := "ngn", iso := "nid", value := .interrogativeBased }
  , { walsCode := "ngk", iso := "nam", value := .interrogativeBased }
  , { walsCode := "nti", iso := "niy", value := .genericNounBased }
  , { walsCode := "ngi", iso := "wyb", value := .interrogativeBased }
  , { walsCode := "nha", iso := "nha", value := .interrogativeBased }
  , { walsCode := "nro", iso := "nhr", value := .mixed }
  , { walsCode := "nia", iso := "nia", value := .mixed }
  , { walsCode := "nsg", iso := "ncg", value := .interrogativeBased }
  , { walsCode := "niu", iso := "niu", value := .genericNounBased }
  , { walsCode := "niv", iso := "niv", value := .interrogativeBased }
  , { walsCode := "nko", iso := "cgg", value := .genericNounBased }
  , { walsCode := "nog", iso := "nog", value := .mixed }
  , { walsCode := "nto", iso := "nto", value := .genericNounBased }
  , { walsCode := "nbd", iso := "dgl", value := .genericNounBased }
  , { walsCode := "nug", iso := "nuy", value := .interrogativeBased }
  , { walsCode := "ood", iso := "ood", value := .special }
  , { walsCode := "oji", iso := "", value := .special }
  , { walsCode := "orl", iso := "oro", value := .genericNounBased }
  , { walsCode := "orh", iso := "hae", value := .genericNounBased }
  , { walsCode := "oss", iso := "oss", value := .interrogativeBased }
  , { walsCode := "pkn", iso := "drl", value := .interrogativeBased }
  , { walsCode := "pms", iso := "pma", value := .genericNounBased }
  , { walsCode := "pno", iso := "pao", value := .interrogativeBased }
  , { walsCode := "pal", iso := "pau", value := .genericNounBased }
  , { walsCode := "pan", iso := "pan", value := .special }
  , { walsCode := "pny", iso := "pnw", value := .interrogativeBased }
  , { walsCode := "psh", iso := "pst", value := .interrogativeBased }
  , { walsCode := "psm", iso := "pqm", value := .interrogativeBased }
  , { walsCode := "prs", iso := "pes", value := .genericNounBased }
  , { walsCode := "prh", iso := "myp", value := .mixed }
  , { walsCode := "ppi", iso := "pit", value := .interrogativeBased }
  , { walsCode := "pol", iso := "pol", value := .interrogativeBased }
  , { walsCode := "por", iso := "por", value := .mixed }
  , { walsCode := "pur", iso := "tsz", value := .interrogativeBased }
  , { walsCode := "pae", iso := "pbb", value := .interrogativeBased }
  , { walsCode := "qia", iso := "", value := .genericNounBased }
  , { walsCode := "qhu", iso := "qub", value := .interrogativeBased }
  , { walsCode := "qim", iso := "qvi", value := .interrogativeBased }
  , { walsCode := "rom", iso := "ron", value := .interrogativeBased }
  , { walsCode := "rus", iso := "rus", value := .interrogativeBased }
  , { walsCode := "ski", iso := "sjd", value := .interrogativeBased }
  , { walsCode := "sno", iso := "sme", value := .interrogativeBased }
  , { walsCode := "sam", iso := "smo", value := .genericNounBased }
  , { walsCode := "san", iso := "sag", value := .genericNounBased }
  , { walsCode := "stl", iso := "sat", value := .interrogativeBased }
  , { walsCode := "see", iso := "trv", value := .genericNounBased }
  , { walsCode := "skp", iso := "sel", value := .interrogativeBased }
  , { walsCode := "sml", iso := "sza", value := .mixed }
  , { walsCode := "scr", iso := "hbs", value := .interrogativeBased }
  , { walsCode := "shk", iso := "shp", value := .interrogativeBased }
  , { walsCode := "shr", iso := "cjs", value := .interrogativeBased }
  , { walsCode := "sho", iso := "shh", value := .interrogativeBased }
  , { walsCode := "siu", iso := "sis", value := .interrogativeBased }
  , { walsCode := "sla", iso := "den", value := .genericNounBased }
  , { walsCode := "som", iso := "som", value := .genericNounBased }
  , { walsCode := "spa", iso := "spa", value := .special }
  , { walsCode := "squ", iso := "squ", value := .interrogativeBased }
  , { walsCode := "swa", iso := "swh", value := .genericNounBased }
  , { walsCode := "swe", iso := "swe", value := .special }
  , { walsCode := "tab", iso := "mky", value := .interrogativeBased }
  , { walsCode := "tag", iso := "tgl", value := .existentialConstruction }
  , { walsCode := "taj", iso := "tgk", value := .interrogativeBased }
  , { walsCode := "tkl", iso := "tkm", value := .interrogativeBased }
  , { walsCode := "tml", iso := "tam", value := .interrogativeBased }
  , { walsCode := "tmu", iso := "ttt", value := .genericNounBased }
  , { walsCode := "tvo", iso := "tat", value := .interrogativeBased }
  , { walsCode := "tpn", iso := "ntp", value := .mixed }
  , { walsCode := "tps", iso := "stp", value := .interrogativeBased }
  , { walsCode := "tha", iso := "tha", value := .interrogativeBased }
  , { walsCode := "tis", iso := "bod", value := .genericNounBased }
  , { walsCode := "tid", iso := "tvo", value := .genericNounBased }
  , { walsCode := "tja", iso := "dih", value := .interrogativeBased }
  , { walsCode := "tiw", iso := "tiw", value := .interrogativeBased }
  , { walsCode := "tms", iso := "dto", value := .genericNounBased }
  , { walsCode := "ton", iso := "tqw", value := .interrogativeBased }
  , { walsCode := "txj", iso := "too", value := .interrogativeBased }
  , { walsCode := "tru", iso := "tpy", value := .genericNounBased }
  , { walsCode := "tst", iso := "huq", value := .interrogativeBased }
  , { walsCode := "tun", iso := "tun", value := .interrogativeBased }
  , { walsCode := "tur", iso := "tur", value := .genericNounBased }
  , { walsCode := "tkm", iso := "tuk", value := .mixed }
  , { walsCode := "tvl", iso := "tvl", value := .genericNounBased }
  , { walsCode := "tuv", iso := "tyv", value := .interrogativeBased }
  , { walsCode := "udh", iso := "ude", value := .interrogativeBased }
  , { walsCode := "udm", iso := "udm", value := .interrogativeBased }
  , { walsCode := "ukr", iso := "ukr", value := .interrogativeBased }
  , { walsCode := "uku", iso := "kuu", value := .interrogativeBased }
  , { walsCode := "urk", iso := "urb", value := .mixed }
  , { walsCode := "usa", iso := "wnu", value := .genericNounBased }
  , { walsCode := "uzb", iso := "", value := .interrogativeBased }
  , { walsCode := "vie", iso := "vie", value := .interrogativeBased }
  , { walsCode := "wam", iso := "wmb", value := .interrogativeBased }
  , { walsCode := "wra", iso := "wba", value := .mixed }
  , { walsCode := "wry", iso := "wrz", value := .interrogativeBased }
  , { walsCode := "wrd", iso := "wrr", value := .interrogativeBased }
  , { walsCode := "wrn", iso := "wnd", value := .interrogativeBased }
  , { walsCode := "wic", iso := "wic", value := .interrogativeBased }
  , { walsCode := "wmu", iso := "wim", value := .interrogativeBased }
  , { walsCode := "yag", iso := "yad", value := .special }
  , { walsCode := "ykt", iso := "sah", value := .interrogativeBased }
  , { walsCode := "ynk", iso := "kdd", value := .mixed }
  , { walsCode := "yap", iso := "yap", value := .genericNounBased }
  , { walsCode := "yaq", iso := "yaq", value := .interrogativeBased }
  , { walsCode := "ywr", iso := "ywr", value := .special }
  , { walsCode := "yid", iso := "yii", value := .interrogativeBased }
  , { walsCode := "yin", iso := "yij", value := .interrogativeBased }
  , { walsCode := "yng", iso := "yia", value := .interrogativeBased }
  , { walsCode := "yor", iso := "yor", value := .genericNounBased }
  , { walsCode := "yko", iso := "yux", value := .interrogativeBased }
  , { walsCode := "ypk", iso := "esu", value := .interrogativeBased }
  , { walsCode := "yuw", iso := "kld", value := .interrogativeBased }
  , { walsCode := "zaz", iso := "diq", value := .special }
  , { walsCode := "zun", iso := "zun", value := .interrogativeBased }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F46A
