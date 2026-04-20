import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 52A: Comitatives and Instrumentals
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 52A`.

Chapter 52, 322 languages.
-/

namespace Core.WALS.F52A

/-- WALS 52A values. -/
inductive ComitativesAndInstrumentals where
  /-- Identity (76 languages). -/
  | identity
  /-- Differentiation (213 languages). -/
  | differentiation
  /-- Mixed (33 languages). -/
  | mixed
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 52A dataset (322 languages). -/
def allData : List (Datapoint ComitativesAndInstrumentals) :=
  [ { walsCode := "xam", iso := "xam", value := .identity }
  , { walsCode := "abk", iso := "abk", value := .differentiation }
  , { walsCode := "acg", iso := "aca", value := .differentiation }
  , { walsCode := "acl", iso := "ach", value := .identity }
  , { walsCode := "aco", iso := "kjq", value := .differentiation }
  , { walsCode := "afr", iso := "afr", value := .identity }
  , { walsCode := "ain", iso := "ain", value := .differentiation }
  , { walsCode := "ala", iso := "amp", value := .differentiation }
  , { walsCode := "alb", iso := "sqi", value := .identity }
  , { walsCode := "ale", iso := "ale", value := .mixed }
  , { walsCode := "aly", iso := "aly", value := .differentiation }
  , { walsCode := "ame", iso := "aey", value := .differentiation }
  , { walsCode := "adk", iso := "ano", value := .identity }
  , { walsCode := "agt", iso := "awg", value := .differentiation }
  , { walsCode := "aeg", iso := "arz", value := .differentiation }
  , { walsCode := "arg", iso := "afb", value := .differentiation }
  , { walsCode := "arp", iso := "ape", value := .differentiation }
  , { walsCode := "arm", iso := "hye", value := .differentiation }
  , { walsCode := "arr", iso := "", value := .differentiation }
  , { walsCode := "auy", iso := "auy", value := .differentiation }
  , { walsCode := "ava", iso := "ava", value := .differentiation }
  , { walsCode := "awt", iso := "kmn", value := .identity }
  , { walsCode := "aym", iso := "ayr", value := .identity }
  , { walsCode := "bag", iso := "bmi", value := .differentiation }
  , { walsCode := "bak", iso := "bkc", value := .identity }
  , { walsCode := "bam", iso := "bam", value := .mixed }
  , { walsCode := "brs", iso := "bsn", value := .identity }
  , { walsCode := "bar", iso := "bfa", value := .identity }
  , { walsCode := "bsq", iso := "eus", value := .differentiation }
  , { walsCode := "bma", iso := "tzm", value := .differentiation }
  , { walsCode := "bou", iso := "oua", value := .differentiation }
  , { walsCode := "bkl", iso := "bcl", value := .identity }
  , { walsCode := "bnm", iso := "bjr", value := .differentiation }
  , { walsCode := "bis", iso := "bib", value := .differentiation }
  , { walsCode := "bla", iso := "bla", value := .differentiation }
  , { walsCode := "brh", iso := "brh", value := .differentiation }
  , { walsCode := "bre", iso := "bre", value := .identity }
  , { walsCode := "bur", iso := "bsk", value := .differentiation }
  , { walsCode := "car", iso := "car", value := .differentiation }
  , { walsCode := "ctl", iso := "cat", value := .identity }
  , { walsCode := "cmh", iso := "ute", value := .differentiation }
  , { walsCode := "cle", iso := "cle", value := .identity }
  , { walsCode := "crg", iso := "gui", value := .differentiation }
  , { walsCode := "cch", iso := "coz", value := .identity }
  , { walsCode := "col", iso := "ctu", value := .identity }
  , { walsCode := "chk", iso := "ckt", value := .differentiation }
  , { walsCode := "ccp", iso := "coc", value := .identity }
  , { walsCode := "cog", iso := "kog", value := .differentiation }
  , { walsCode := "cmn", iso := "com", value := .differentiation }
  , { walsCode := "com", iso := "swb", value := .differentiation }
  , { walsCode := "cmx", iso := "coo", value := .identity }
  , { walsCode := "coo", iso := "csz", value := .mixed }
  , { walsCode := "cor", iso := "crn", value := .differentiation }
  , { walsCode := "cem", iso := "cam", value := .differentiation }
  , { walsCode := "dgr", iso := "dta", value := .differentiation }
  , { walsCode := "dah", iso := "dal", value := .differentiation }
  , { walsCode := "dam", iso := "mbp", value := .differentiation }
  , { walsCode := "dni", iso := "dni", value := .differentiation }
  , { walsCode := "dsh", iso := "dan", value := .identity }
  , { walsCode := "des", iso := "des", value := .differentiation }
  , { walsCode := "dre", iso := "dhv", value := .differentiation }
  , { walsCode := "dug", iso := "gwd", value := .differentiation }
  , { walsCode := "dmi", iso := "dus", value := .differentiation }
  , { walsCode := "efi", iso := "efi", value := .differentiation }
  , { walsCode := "ena", iso := "enq", value := .differentiation }
  , { walsCode := "eng", iso := "eng", value := .identity }
  , { walsCode := "est", iso := "ekk", value := .identity }
  , { walsCode := "evn", iso := "eve", value := .differentiation }
  , { walsCode := "eve", iso := "evn", value := .differentiation }
  , { walsCode := "ewe", iso := "ewe", value := .identity }
  , { walsCode := "fij", iso := "fij", value := .differentiation }
  , { walsCode := "fin", iso := "fin", value := .differentiation }
  , { walsCode := "fon", iso := "fon", value := .mixed }
  , { walsCode := "fre", iso := "fra", value := .identity }
  , { walsCode := "fni", iso := "fuv", value := .differentiation }
  , { walsCode := "fur", iso := "fvr", value := .identity }
  , { walsCode := "fut", iso := "fut", value := .identity }
  , { walsCode := "gds", iso := "gaj", value := .differentiation }
  , { walsCode := "grf", iso := "cab", value := .mixed }
  , { walsCode := "gbb", iso := "gbp", value := .identity }
  , { walsCode := "geo", iso := "kat", value := .mixed }
  , { walsCode := "ger", iso := "deu", value := .identity }
  , { walsCode := "goa", iso := "guc", value := .differentiation }
  , { walsCode := "gol", iso := "gol", value := .differentiation }
  , { walsCode := "gon", iso := "gno", value := .differentiation }
  , { walsCode := "goo", iso := "gni", value := .differentiation }
  , { walsCode := "grk", iso := "ell", value := .identity }
  , { walsCode := "grw", iso := "kal", value := .differentiation }
  , { walsCode := "gua", iso := "gug", value := .differentiation }
  , { walsCode := "grj", iso := "var", value := .differentiation }
  , { walsCode := "gum", iso := "kgs", value := .differentiation }
  , { walsCode := "gnn", iso := "gww", value := .differentiation }
  , { walsCode := "guu", iso := "kky", value := .differentiation }
  , { walsCode := "hai", iso := "hai", value := .mixed }
  , { walsCode := "hau", iso := "hau", value := .identity }
  , { walsCode := "haw", iso := "haw", value := .mixed }
  , { walsCode := "heb", iso := "heb", value := .identity }
  , { walsCode := "hin", iso := "hin", value := .differentiation }
  , { walsCode := "hix", iso := "hix", value := .differentiation }
  , { walsCode := "ho", iso := "hoc", value := .differentiation }
  , { walsCode := "hua", iso := "ygr", value := .differentiation }
  , { walsCode := "hve", iso := "huv", value := .differentiation }
  , { walsCode := "hui", iso := "hch", value := .differentiation }
  , { walsCode := "hun", iso := "hun", value := .mixed }
  , { walsCode := "hzb", iso := "huz", value := .differentiation }
  , { walsCode := "hup", iso := "hup", value := .differentiation }
  , { walsCode := "ice", iso := "isl", value := .mixed }
  , { walsCode := "ila", iso := "ilb", value := .identity }
  , { walsCode := "imo", iso := "imn", value := .differentiation }
  , { walsCode := "ind", iso := "ind", value := .mixed }
  , { walsCode := "iga", iso := "inb", value := .identity }
  , { walsCode := "irq", iso := "irk", value := .mixed }
  , { walsCode := "iri", iso := "gle", value := .identity }
  , { walsCode := "ita", iso := "ita", value := .identity }
  , { walsCode := "ite", iso := "itl", value := .differentiation }
  , { walsCode := "jak", iso := "jac", value := .differentiation }
  , { walsCode := "jpn", iso := "jpn", value := .differentiation }
  , { walsCode := "juh", iso := "ktz", value := .identity }
  , { walsCode := "kng", iso := "kgp", value := .differentiation }
  , { walsCode := "kms", iso := "xas", value := .identity }
  , { walsCode := "kam", iso := "xbr", value := .differentiation }
  , { walsCode := "kwe", iso := "knj", value := .differentiation }
  , { walsCode := "knd", iso := "kan", value := .differentiation }
  , { walsCode := "knr", iso := "knc", value := .differentiation }
  , { walsCode := "krk", iso := "kyh", value := .differentiation }
  , { walsCode := "kay", iso := "gyd", value := .differentiation }
  , { walsCode := "ker", iso := "ker", value := .identity }
  , { walsCode := "ket", iso := "ket", value := .identity }
  , { walsCode := "khl", iso := "klj", value := .identity }
  , { walsCode := "kha", iso := "khk", value := .differentiation }
  , { walsCode := "kty", iso := "kca", value := .identity }
  , { walsCode := "khr", iso := "khr", value := .differentiation }
  , { walsCode := "khs", iso := "kha", value := .differentiation }
  , { walsCode := "khm", iso := "khm", value := .differentiation }
  , { walsCode := "klv", iso := "kij", value := .differentiation }
  , { walsCode := "kin", iso := "kin", value := .differentiation }
  , { walsCode := "kis", iso := "kss", value := .identity }
  , { walsCode := "koa", iso := "cku", value := .differentiation }
  , { walsCode := "kob", iso := "kpw", value := .differentiation }
  , { walsCode := "koi", iso := "kbk", value := .differentiation }
  , { walsCode := "kzy", iso := "kpv", value := .mixed }
  , { walsCode := "kor", iso := "kor", value := .differentiation }
  , { walsCode := "kry", iso := "kpy", value := .differentiation }
  , { walsCode := "ktt", iso := "", value := .differentiation }
  , { walsCode := "koy", iso := "kff", value := .mixed }
  , { walsCode := "kch", iso := "khq", value := .mixed }
  , { walsCode := "kro", iso := "kgo", value := .differentiation }
  , { walsCode := "knm", iso := "kun", value := .differentiation }
  , { walsCode := "kur", iso := "kru", value := .differentiation }
  , { walsCode := "kwr", iso := "tnk", value := .identity }
  , { walsCode := "kwm", iso := "ksq", value := .differentiation }
  , { walsCode := "kxo", iso := "xuu", value := .differentiation }
  , { walsCode := "kat", iso := "kmg", value := .differentiation }
  , { walsCode := "lad", iso := "lbj", value := .differentiation }
  , { walsCode := "ldn", iso := "lld", value := .identity }
  , { walsCode := "lah", iso := "lhu", value := .differentiation }
  , { walsCode := "lak", iso := "lbe", value := .differentiation }
  , { walsCode := "lkt", iso := "lkt", value := .differentiation }
  , { walsCode := "lan", iso := "laj", value := .mixed }
  , { walsCode := "lat", iso := "lav", value := .identity }
  , { walsCode := "laz", iso := "lzz", value := .differentiation }
  , { walsCode := "les", iso := "les", value := .differentiation }
  , { walsCode := "lez", iso := "lez", value := .differentiation }
  , { walsCode := "lim", iso := "lif", value := .differentiation }
  , { walsCode := "lit", iso := "lit", value := .mixed }
  , { walsCode := "lga", iso := "ojv", value := .identity }
  , { walsCode := "lug", iso := "lgg", value := .differentiation }
  , { walsCode := "lui", iso := "lui", value := .differentiation }
  , { walsCode := "luo", iso := "luo", value := .differentiation }
  , { walsCode := "mne", iso := "nmu", value := .differentiation }
  , { walsCode := "mlt", iso := "mlt", value := .differentiation }
  , { walsCode := "mmv", iso := "mdi", value := .differentiation }
  , { walsCode := "mnc", iso := "mnc", value := .differentiation }
  , { walsCode := "mnd", iso := "cmn", value := .differentiation }
  , { walsCode := "myi", iso := "mpc", value := .differentiation }
  , { walsCode := "mgg", iso := "mjg", value := .differentiation }
  , { walsCode := "maw", iso := "mlq", value := .differentiation }
  , { walsCode := "mjk", iso := "mfv", value := .differentiation }
  , { walsCode := "mns", iso := "mns", value := .mixed }
  , { walsCode := "mao", iso := "mri", value := .differentiation }
  , { walsCode := "map", iso := "arn", value := .differentiation }
  , { walsCode := "mhi", iso := "mar", value := .identity }
  , { walsCode := "mrg", iso := "mrt", value := .differentiation }
  , { walsCode := "mah", iso := "mrj", value := .differentiation }
  , { walsCode := "mrd", iso := "mrz", value := .differentiation }
  , { walsCode := "msh", iso := "mah", value := .differentiation }
  , { walsCode := "mrt", iso := "vma", value := .differentiation }
  , { walsCode := "msl", iso := "mls", value := .identity }
  , { walsCode := "myo", iso := "mfy", value := .differentiation }
  , { walsCode := "mzc", iso := "maq", value := .identity }
  , { walsCode := "mhu", iso := "lnb", value := .identity }
  , { walsCode := "mei", iso := "mni", value := .differentiation }
  , { walsCode := "mxa", iso := "mib", value := .identity }
  , { walsCode := "mog", iso := "mhj", value := .identity }
  , { walsCode := "mok", iso := "mkj", value := .identity }
  , { walsCode := "moa", iso := "mte", value := .differentiation }
  , { walsCode := "mun", iso := "unr", value := .differentiation }
  , { walsCode := "mup", iso := "sur", value := .differentiation }
  , { walsCode := "mrw", iso := "zmu", value := .differentiation }
  , { walsCode := "nah", iso := "nll", value := .differentiation }
  , { walsCode := "nmi", iso := "nhx", value := .differentiation }
  , { walsCode := "kho", iso := "naq", value := .identity }
  , { walsCode := "nan", iso := "niq", value := .differentiation }
  , { walsCode := "nav", iso := "nav", value := .differentiation }
  , { walsCode := "ntu", iso := "yrk", value := .mixed }
  , { walsCode := "nwd", iso := "new", value := .differentiation }
  , { walsCode := "ngl", iso := "nig", value := .mixed }
  , { walsCode := "nti", iso := "niy", value := .differentiation }
  , { walsCode := "ngi", iso := "wyb", value := .differentiation }
  , { walsCode := "niv", iso := "niv", value := .differentiation }
  , { walsCode := "nob", iso := "fia", value := .differentiation }
  , { walsCode := "nor", iso := "nor", value := .identity }
  , { walsCode := "nkr", iso := "nkr", value := .differentiation }
  , { walsCode := "nya", iso := "nyt", value := .differentiation }
  , { walsCode := "nyu", iso := "nyv", value := .mixed }
  , { walsCode := "orh", iso := "hae", value := .differentiation }
  , { walsCode := "owc", iso := "gaz", value := .mixed }
  , { walsCode := "ots", iso := "otm", value := .differentiation }
  , { walsCode := "pai", iso := "pwn", value := .differentiation }
  , { walsCode := "pal", iso := "pau", value := .differentiation }
  , { walsCode := "pen", iso := "peg", value := .mixed }
  , { walsCode := "per", iso := "pip", value := .differentiation }
  , { walsCode := "prs", iso := "pes", value := .identity }
  , { walsCode := "pia", iso := "pid", value := .differentiation }
  , { walsCode := "pip", iso := "ppl", value := .identity }
  , { walsCode := "prh", iso := "myp", value := .differentiation }
  , { walsCode := "ppi", iso := "pit", value := .differentiation }
  , { walsCode := "pol", iso := "pol", value := .differentiation }
  , { walsCode := "psj", iso := "poe", value := .differentiation }
  , { walsCode := "por", iso := "por", value := .identity }
  , { walsCode := "pur", iso := "tsz", value := .differentiation }
  , { walsCode := "pae", iso := "pbb", value := .differentiation }
  , { walsCode := "qaw", iso := "alc", value := .differentiation }
  , { walsCode := "qay", iso := "quy", value := .mixed }
  , { walsCode := "qim", iso := "qvi", value := .identity }
  , { walsCode := "qch", iso := "quc", value := .differentiation }
  , { walsCode := "rap", iso := "rap", value := .differentiation }
  , { walsCode := "rbu", iso := "rmn", value := .identity }
  , { walsCode := "rom", iso := "ron", value := .identity }
  , { walsCode := "rmc", iso := "roh", value := .identity }
  , { walsCode := "rus", iso := "rus", value := .mixed }
  , { walsCode := "sno", iso := "sme", value := .identity }
  , { walsCode := "slb", iso := "sbe", value := .differentiation }
  , { walsCode := "syu", iso := "sll", value := .differentiation }
  , { walsCode := "sam", iso := "smo", value := .differentiation }
  , { walsCode := "san", iso := "sag", value := .identity }
  , { walsCode := "srm", iso := "srm", value := .mixed }
  , { walsCode := "slp", iso := "spl", value := .differentiation }
  , { walsCode := "ssh", iso := "bwo", value := .differentiation }
  , { walsCode := "shn", iso := "sna", value := .differentiation }
  , { walsCode := "siu", iso := "sis", value := .differentiation }
  , { walsCode := "sla", iso := "den", value := .differentiation }
  , { walsCode := "so", iso := "teu", value := .differentiation }
  , { walsCode := "som", iso := "som", value := .differentiation }
  , { walsCode := "sor", iso := "srb", value := .identity }
  , { walsCode := "srl", iso := "dsb", value := .identity }
  , { walsCode := "sre", iso := "kpm", value := .mixed }
  , { walsCode := "sup", iso := "spp", value := .mixed }
  , { walsCode := "sus", iso := "sus", value := .identity }
  , { walsCode := "swa", iso := "swh", value := .differentiation }
  , { walsCode := "swe", iso := "swe", value := .identity }
  , { walsCode := "tbs", iso := "tab", value := .differentiation }
  , { walsCode := "tag", iso := "tgl", value := .differentiation }
  , { walsCode := "tah", iso := "tah", value := .differentiation }
  , { walsCode := "trr", iso := "tbg", value := .differentiation }
  , { walsCode := "tkl", iso := "tkm", value := .mixed }
  , { walsCode := "tml", iso := "tam", value := .differentiation }
  , { walsCode := "tas", iso := "shi", value := .differentiation }
  , { walsCode := "tau", iso := "tya", value := .differentiation }
  , { walsCode := "tel", iso := "tel", value := .differentiation }
  , { walsCode := "ter", iso := "ttr", value := .identity }
  , { walsCode := "tha", iso := "tha", value := .differentiation }
  , { walsCode := "tgk", iso := "tgc", value := .identity }
  , { walsCode := "tik", iso := "tik", value := .identity }
  , { walsCode := "tin", iso := "cir", value := .differentiation }
  , { walsCode := "tlp", iso := "tcf", value := .identity }
  , { walsCode := "tli", iso := "tli", value := .differentiation }
  , { walsCode := "tke", iso := "tkl", value := .differentiation }
  , { walsCode := "tng", iso := "ton", value := .differentiation }
  , { walsCode := "toq", iso := "mlu", value := .differentiation }
  , { walsCode := "txj", iso := "too", value := .differentiation }
  , { walsCode := "tri", iso := "trc", value := .differentiation }
  , { walsCode := "tru", iso := "tpy", value := .differentiation }
  , { walsCode := "tug", iso := "thv", value := .differentiation }
  , { walsCode := "tbu", iso := "", value := .differentiation }
  , { walsCode := "tup", iso := "tpn", value := .differentiation }
  , { walsCode := "tur", iso := "tur", value := .identity }
  , { walsCode := "uby", iso := "uby", value := .differentiation }
  , { walsCode := "udi", iso := "udi", value := .differentiation }
  , { walsCode := "udm", iso := "udm", value := .identity }
  , { walsCode := "una", iso := "mtg", value := .differentiation }
  , { walsCode := "uhi", iso := "urf", value := .differentiation }
  , { walsCode := "url", iso := "urk", value := .identity }
  , { walsCode := "urd", iso := "urd", value := .differentiation }
  , { walsCode := "urk", iso := "urb", value := .differentiation }
  , { walsCode := "usr", iso := "usa", value := .differentiation }
  , { walsCode := "uzb", iso := "", value := .mixed }
  , { walsCode := "vai", iso := "vai", value := .differentiation }
  , { walsCode := "ven", iso := "ven", value := .differentiation }
  , { walsCode := "vot", iso := "vot", value := .mixed }
  , { walsCode := "wan", iso := "xwk", value := .differentiation }
  , { walsCode := "wra", iso := "wba", value := .differentiation }
  , { walsCode := "wrg", iso := "wgy", value := .differentiation }
  , { walsCode := "wrw", iso := "wwr", value := .differentiation }
  , { walsCode := "wsk", iso := "wsk", value := .differentiation }
  , { walsCode := "way", iso := "oym", value := .differentiation }
  , { walsCode := "wel", iso := "cym", value := .mixed }
  , { walsCode := "wch", iso := "mzh", value := .differentiation }
  , { walsCode := "win", iso := "wnw", value := .differentiation }
  , { walsCode := "bah", iso := "xir", value := .differentiation }
  , { walsCode := "ykt", iso := "sah", value := .differentiation }
  , { walsCode := "yaq", iso := "yaq", value := .differentiation }
  , { walsCode := "yel", iso := "yle", value := .differentiation }
  , { walsCode := "yir", iso := "yyr", value := .differentiation }
  , { walsCode := "yor", iso := "yor", value := .differentiation }
  , { walsCode := "yct", iso := "yua", value := .identity }
  , { walsCode := "yko", iso := "yux", value := .differentiation }
  , { walsCode := "yuk", iso := "gcd", value := .differentiation }
  , { walsCode := "ypk", iso := "esu", value := .differentiation }
  , { walsCode := "zya", iso := "zav", value := .mixed }
  , { walsCode := "zaz", iso := "diq", value := .identity }
  , { walsCode := "zch", iso := "zoh", value := .differentiation }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F52A
