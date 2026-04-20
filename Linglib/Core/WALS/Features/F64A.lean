import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 64A: Nominal and Verbal Conjunction
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 64A`.

Chapter 64, 301 languages.
-/

namespace Core.WALS.F64A

/-- WALS 64A values. -/
inductive NominalAndVerbalConjunction where
  /-- Identity (161 languages). -/
  | identity
  /-- Differentiation (125 languages). -/
  | differentiation
  /-- Both expressed by juxtaposition (15 languages). -/
  | bothExpressedByJuxtaposition
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 64A dataset (301 languages). -/
def allData : List (Datapoint NominalAndVerbalConjunction) :=
  [ { walsCode := "abk", iso := "abk", value := .identity }
  , { walsCode := "abu", iso := "kgr", value := .identity }
  , { walsCode := "ace", iso := "ace", value := .identity }
  , { walsCode := "aco", iso := "kjq", value := .identity }
  , { walsCode := "aga", iso := "agd", value := .differentiation }
  , { walsCode := "ain", iso := "ain", value := .differentiation }
  , { walsCode := "ala", iso := "amp", value := .differentiation }
  , { walsCode := "aly", iso := "aly", value := .differentiation }
  , { walsCode := "aml", iso := "omb", value := .identity }
  , { walsCode := "ame", iso := "aey", value := .differentiation }
  , { walsCode := "apu", iso := "apu", value := .bothExpressedByJuxtaposition }
  , { walsCode := "aeg", iso := "arz", value := .identity }
  , { walsCode := "ana", iso := "aro", value := .bothExpressedByJuxtaposition }
  , { walsCode := "alk", iso := "apr", value := .identity }
  , { walsCode := "amp", iso := "aer", value := .bothExpressedByJuxtaposition }
  , { walsCode := "bab", iso := "bav", value := .differentiation }
  , { walsCode := "bdm", iso := "bia", value := .differentiation }
  , { walsCode := "bag", iso := "bmi", value := .differentiation }
  , { walsCode := "bak", iso := "bkc", value := .differentiation }
  , { walsCode := "bvi", iso := "", value := .differentiation }
  , { walsCode := "bnn", iso := "bcm", value := .differentiation }
  , { walsCode := "bsq", iso := "eus", value := .identity }
  , { walsCode := "bkr", iso := "btx", value := .identity }
  , { walsCode := "baw", iso := "bgr", value := .identity }
  , { walsCode := "bma", iso := "tzm", value := .differentiation }
  , { walsCode := "bbw", iso := "gup", value := .identity }
  , { walsCode := "boz", iso := "boz", value := .identity }
  , { walsCode := "brh", iso := "brh", value := .identity }
  , { walsCode := "bkt", iso := "bkk", value := .differentiation }
  , { walsCode := "bud", iso := "bdm", value := .differentiation }
  , { walsCode := "bum", iso := "tkw", value := .identity }
  , { walsCode := "bur", iso := "bsk", value := .identity }
  , { walsCode := "bus", iso := "bqp", value := .differentiation }
  , { walsCode := "cah", iso := "chl", value := .identity }
  , { walsCode := "cnl", iso := "ram", value := .differentiation }
  , { walsCode := "cnt", iso := "yue", value := .differentiation }
  , { walsCode := "cyg", iso := "cay", value := .differentiation }
  , { walsCode := "cha", iso := "cha", value := .identity }
  , { walsCode := "chc", iso := "che", value := .identity }
  , { walsCode := "cmh", iso := "ute", value := .differentiation }
  , { walsCode := "cic", iso := "nya", value := .identity }
  , { walsCode := "cch", iso := "coz", value := .differentiation }
  , { walsCode := "chk", iso := "ckt", value := .identity }
  , { walsCode := "coa", iso := "xcw", value := .identity }
  , { walsCode := "coo", iso := "csz", value := .identity }
  , { walsCode := "cop", iso := "cop", value := .differentiation }
  , { walsCode := "dgb", iso := "dag", value := .differentiation }
  , { walsCode := "drg", iso := "dar", value := .identity }
  , { walsCode := "deg", iso := "deg", value := .differentiation }
  , { walsCode := "dha", iso := "dsh", value := .differentiation }
  , { walsCode := "dhi", iso := "div", value := .differentiation }
  , { walsCode := "dja", iso := "dyy", value := .differentiation }
  , { walsCode := "doy", iso := "dow", value := .differentiation }
  , { walsCode := "dre", iso := "dhv", value := .differentiation }
  , { walsCode := "dug", iso := "gwd", value := .identity }
  , { walsCode := "eng", iso := "eng", value := .identity }
  , { walsCode := "err", iso := "erg", value := .identity }
  , { walsCode := "eve", iso := "evn", value := .identity }
  , { walsCode := "ewo", iso := "ewo", value := .differentiation }
  , { walsCode := "fij", iso := "fij", value := .differentiation }
  , { walsCode := "fin", iso := "fin", value := .identity }
  , { walsCode := "fon", iso := "fon", value := .differentiation }
  , { walsCode := "fre", iso := "fra", value := .identity }
  , { walsCode := "gap", iso := "pwg", value := .identity }
  , { walsCode := "gar", iso := "grt", value := .identity }
  , { walsCode := "geo", iso := "kat", value := .identity }
  , { walsCode := "ger", iso := "deu", value := .identity }
  , { walsCode := "gol", iso := "gol", value := .identity }
  , { walsCode := "goo", iso := "gni", value := .bothExpressedByJuxtaposition }
  , { walsCode := "grk", iso := "ell", value := .identity }
  , { walsCode := "grw", iso := "kal", value := .identity }
  , { walsCode := "gua", iso := "gug", value := .identity }
  , { walsCode := "guj", iso := "guj", value := .identity }
  , { walsCode := "gnb", iso := "wlg", value := .identity }
  , { walsCode := "grg", iso := "gge", value := .identity }
  , { walsCode := "hai", iso := "hai", value := .differentiation }
  , { walsCode := "ham", iso := "hmt", value := .differentiation }
  , { walsCode := "hat", iso := "had", value := .differentiation }
  , { walsCode := "hau", iso := "hau", value := .differentiation }
  , { walsCode := "haw", iso := "haw", value := .identity }
  , { walsCode := "heb", iso := "heb", value := .identity }
  , { walsCode := "hin", iso := "hin", value := .identity }
  , { walsCode := "hix", iso := "hix", value := .bothExpressedByJuxtaposition }
  , { walsCode := "hmo", iso := "hnj", value := .identity }
  , { walsCode := "hoa", iso := "hoa", value := .differentiation }
  , { walsCode := "hun", iso := "hun", value := .identity }
  , { walsCode := "hzb", iso := "huz", value := .identity }
  , { walsCode := "ika", iso := "arh", value := .differentiation }
  , { walsCode := "imo", iso := "imn", value := .differentiation }
  , { walsCode := "ind", iso := "ind", value := .identity }
  , { walsCode := "irq", iso := "irk", value := .identity }
  , { walsCode := "ita", iso := "ita", value := .identity }
  , { walsCode := "itz", iso := "itz", value := .identity }
  , { walsCode := "jab", iso := "jae", value := .identity }
  , { walsCode := "jak", iso := "jac", value := .differentiation }
  , { walsCode := "jam", iso := "djd", value := .bothExpressedByJuxtaposition }
  , { walsCode := "jpn", iso := "jpn", value := .differentiation }
  , { walsCode := "juh", iso := "ktz", value := .differentiation }
  , { walsCode := "krr", iso := "kxa", value := .differentiation }
  , { walsCode := "kgu", iso := "ktg", value := .identity }
  , { walsCode := "kma", iso := "kay", value := .differentiation }
  , { walsCode := "kam", iso := "xbr", value := .identity }
  , { walsCode := "kan", iso := "ogo", value := .differentiation }
  , { walsCode := "knd", iso := "kan", value := .differentiation }
  , { walsCode := "knr", iso := "knc", value := .differentiation }
  , { walsCode := "kpw", iso := "kjp", value := .identity }
  , { walsCode := "krk", iso := "kyh", value := .differentiation }
  , { walsCode := "kas", iso := "kas", value := .identity }
  , { walsCode := "ker", iso := "ker", value := .identity }
  , { walsCode := "ket", iso := "ket", value := .identity }
  , { walsCode := "kmh", iso := "kjl", value := .identity }
  , { walsCode := "kty", iso := "kca", value := .differentiation }
  , { walsCode := "khs", iso := "kha", value := .identity }
  , { walsCode := "kmu", iso := "kjg", value := .differentiation }
  , { walsCode := "krb", iso := "gil", value := .differentiation }
  , { walsCode := "koa", iso := "cku", value := .differentiation }
  , { walsCode := "kob", iso := "kpw", value := .differentiation }
  , { walsCode := "kol", iso := "kfb", value := .identity }
  , { walsCode := "kmb", iso := "", value := .differentiation }
  , { walsCode := "kor", iso := "kor", value := .differentiation }
  , { walsCode := "kku", iso := "kfq", value := .identity }
  , { walsCode := "kfe", iso := "kfz", value := .differentiation }
  , { walsCode := "krw", iso := "khe", value := .identity }
  , { walsCode := "kse", iso := "ses", value := .differentiation }
  , { walsCode := "kro", iso := "kgo", value := .differentiation }
  , { walsCode := "knc", iso := "uwa", value := .bothExpressedByJuxtaposition }
  , { walsCode := "kuk", iso := "bfa", value := .identity }
  , { walsCode := "kuo", iso := "kto", value := .identity }
  , { walsCode := "kut", iso := "kut", value := .identity }
  , { walsCode := "kwa", iso := "kwd", value := .identity }
  , { walsCode := "kat", iso := "kmg", value := .identity }
  , { walsCode := "lai", iso := "cnh", value := .differentiation }
  , { walsCode := "lak", iso := "lbe", value := .identity }
  , { walsCode := "lkt", iso := "lkt", value := .identity }
  , { walsCode := "lmg", iso := "hia", value := .differentiation }
  , { walsCode := "lan", iso := "laj", value := .differentiation }
  , { walsCode := "lat", iso := "lav", value := .identity }
  , { walsCode := "lav", iso := "lvk", value := .identity }
  , { walsCode := "laz", iso := "lzz", value := .identity }
  , { walsCode := "lel", iso := "lln", value := .differentiation }
  , { walsCode := "lep", iso := "lep", value := .differentiation }
  , { walsCode := "lez", iso := "lez", value := .identity }
  , { walsCode := "lil", iso := "lil", value := .differentiation }
  , { walsCode := "ara", iso := "arw", value := .identity }
  , { walsCode := "lgu", iso := "lgu", value := .identity }
  , { walsCode := "lug", iso := "lgg", value := .differentiation }
  , { walsCode := "luv", iso := "lue", value := .differentiation }
  , { walsCode := "mad", iso := "mhi", value := .differentiation }
  , { walsCode := "mle", iso := "mdy", value := .differentiation }
  , { walsCode := "mdr", iso := "mad", value := .identity }
  , { walsCode := "mai", iso := "mai", value := .identity }
  , { walsCode := "mym", iso := "mal", value := .identity }
  , { walsCode := "mam", iso := "mam", value := .identity }
  , { walsCode := "mnd", iso := "cmn", value := .differentiation }
  , { walsCode := "myi", iso := "mpc", value := .differentiation }
  , { walsCode := "mgg", iso := "mjg", value := .differentiation }
  , { walsCode := "mao", iso := "mri", value := .differentiation }
  , { walsCode := "map", iso := "arn", value := .identity }
  , { walsCode := "mhi", iso := "mar", value := .identity }
  , { walsCode := "mar", iso := "mrc", value := .differentiation }
  , { walsCode := "mrq", iso := "", value := .differentiation }
  , { walsCode := "myr", iso := "mcf", value := .bothExpressedByJuxtaposition }
  , { walsCode := "may", iso := "ayz", value := .identity }
  , { walsCode := "mby", iso := "myb", value := .differentiation }
  , { walsCode := "mbi", iso := "baw", value := .differentiation }
  , { walsCode := "mei", iso := "mni", value := .differentiation }
  , { walsCode := "mid", iso := "mei", value := .differentiation }
  , { walsCode := "mxc", iso := "mig", value := .identity }
  , { walsCode := "miy", iso := "mkf", value := .differentiation }
  , { walsCode := "mcv", iso := "moc", value := .identity }
  , { walsCode := "moh", iso := "moh", value := .identity }
  , { walsCode := "mbo", iso := "mxk", value := .identity }
  , { walsCode := "mos", iso := "cas", value := .identity }
  , { walsCode := "mun", iso := "unr", value := .identity }
  , { walsCode := "mup", iso := "sur", value := .differentiation }
  , { walsCode := "mgu", iso := "mug", value := .differentiation }
  , { walsCode := "mus", iso := "emi", value := .identity }
  , { walsCode := "nab", iso := "naf", value := .identity }
  , { walsCode := "nag", iso := "nce", value := .differentiation }
  , { walsCode := "nmi", iso := "nhx", value := .identity }
  , { walsCode := "nht", iso := "nhg", value := .identity }
  , { walsCode := "kho", iso := "naq", value := .identity }
  , { walsCode := "nmb", iso := "nab", value := .identity }
  , { walsCode := "nav", iso := "nav", value := .identity }
  , { walsCode := "ndb", iso := "nde", value := .identity }
  , { walsCode := "ndj", iso := "djj", value := .identity }
  , { walsCode := "nel", iso := "nee", value := .identity }
  , { walsCode := "nep", iso := "npi", value := .identity }
  , { walsCode := "nwd", iso := "new", value := .differentiation }
  , { walsCode := "nez", iso := "nez", value := .differentiation }
  , { walsCode := "ngl", iso := "nig", value := .identity }
  , { walsCode := "nha", iso := "nha", value := .bothExpressedByJuxtaposition }
  , { walsCode := "nia", iso := "nia", value := .identity }
  , { walsCode := "nsg", iso := "ncg", value := .differentiation }
  , { walsCode := "nif", iso := "num", value := .identity }
  , { walsCode := "niu", iso := "niu", value := .identity }
  , { walsCode := "niv", iso := "niv", value := .differentiation }
  , { walsCode := "nko", iso := "cgg", value := .differentiation }
  , { walsCode := "nse", iso := "nse", value := .differentiation }
  , { walsCode := "nua", iso := "nxl", value := .identity }
  , { walsCode := "ood", iso := "ood", value := .identity }
  , { walsCode := "obo", iso := "ann", value := .identity }
  , { walsCode := "oji", iso := "", value := .identity }
  , { walsCode := "orh", iso := "hae", value := .differentiation }
  , { walsCode := "otm", iso := "ote", value := .identity }
  , { walsCode := "pms", iso := "pma", value := .differentiation }
  , { walsCode := "pno", iso := "pao", value := .differentiation }
  , { walsCode := "pai", iso := "pwn", value := .differentiation }
  , { walsCode := "pal", iso := "pau", value := .identity }
  , { walsCode := "psm", iso := "pqm", value := .identity }
  , { walsCode := "pec", iso := "pay", value := .differentiation }
  , { walsCode := "per", iso := "pip", value := .differentiation }
  , { walsCode := "prs", iso := "pes", value := .identity }
  , { walsCode := "prh", iso := "myp", value := .identity }
  , { walsCode := "pit", iso := "pjt", value := .identity }
  , { walsCode := "pop", iso := "pbe", value := .identity }
  , { walsCode := "pul", iso := "puw", value := .identity }
  , { walsCode := "pur", iso := "tsz", value := .identity }
  , { walsCode := "pae", iso := "pbb", value := .differentiation }
  , { walsCode := "qaf", iso := "aar", value := .differentiation }
  , { walsCode := "qia", iso := "", value := .identity }
  , { walsCode := "qhu", iso := "qub", value := .bothExpressedByJuxtaposition }
  , { walsCode := "qim", iso := "qvi", value := .identity }
  , { walsCode := "ret", iso := "tnc", value := .differentiation }
  , { walsCode := "rot", iso := "rtm", value := .identity }
  , { walsCode := "rus", iso := "rus", value := .identity }
  , { walsCode := "ski", iso := "sjd", value := .identity }
  , { walsCode := "sno", iso := "sme", value := .identity }
  , { walsCode := "syu", iso := "sll", value := .differentiation }
  , { walsCode := "san", iso := "sag", value := .identity }
  , { walsCode := "sgu", iso := "snq", value := .differentiation }
  , { walsCode := "snm", iso := "xsu", value := .bothExpressedByJuxtaposition }
  , { walsCode := "skp", iso := "sel", value := .identity }
  , { walsCode := "snt", iso := "set", value := .differentiation }
  , { walsCode := "sho", iso := "shh", value := .differentiation }
  , { walsCode := "sir", iso := "sjr", value := .identity }
  , { walsCode := "siu", iso := "sis", value := .identity }
  , { walsCode := "sla", iso := "den", value := .differentiation }
  , { walsCode := "so", iso := "teu", value := .differentiation }
  , { walsCode := "som", iso := "som", value := .differentiation }
  , { walsCode := "sea", iso := "tvk", value := .differentiation }
  , { walsCode := "spa", iso := "spa", value := .identity }
  , { walsCode := "squ", iso := "squ", value := .identity }
  , { walsCode := "sud", iso := "tgo", value := .identity }
  , { walsCode := "sue", iso := "sue", value := .identity }
  , { walsCode := "sun", iso := "sun", value := .identity }
  , { walsCode := "sup", iso := "spp", value := .differentiation }
  , { walsCode := "tab", iso := "mky", value := .identity }
  , { walsCode := "tag", iso := "tgl", value := .identity }
  , { walsCode := "taf", iso := "sps", value := .identity }
  , { walsCode := "tmm", iso := "mla", value := .differentiation }
  , { walsCode := "tml", iso := "tam", value := .differentiation }
  , { walsCode := "tao", iso := "tro", value := .differentiation }
  , { walsCode := "tau", iso := "tya", value := .differentiation }
  , { walsCode := "tps", iso := "stp", value := .identity }
  , { walsCode := "trb", iso := "tfr", value := .differentiation }
  , { walsCode := "ttn", iso := "tet", value := .identity }
  , { walsCode := "tha", iso := "tha", value := .identity }
  , { walsCode := "tho", iso := "thp", value := .identity }
  , { walsCode := "tis", iso := "bod", value := .identity }
  , { walsCode := "tid", iso := "tvo", value := .identity }
  , { walsCode := "tig", iso := "tir", value := .differentiation }
  , { walsCode := "tik", iso := "tik", value := .identity }
  , { walsCode := "tin", iso := "cir", value := .identity }
  , { walsCode := "tiw", iso := "tiw", value := .bothExpressedByJuxtaposition }
  , { walsCode := "tlo", iso := "tlb", value := .identity }
  , { walsCode := "tms", iso := "dto", value := .differentiation }
  , { walsCode := "txj", iso := "too", value := .identity }
  , { walsCode := "tru", iso := "tpy", value := .differentiation }
  , { walsCode := "tst", iso := "huq", value := .differentiation }
  , { walsCode := "tgn", iso := "tzn", value := .identity }
  , { walsCode := "tuk", iso := "", value := .identity }
  , { walsCode := "tur", iso := "tur", value := .identity }
  , { walsCode := "tvl", iso := "tvl", value := .differentiation }
  , { walsCode := "tzu", iso := "tzj", value := .identity }
  , { walsCode := "udh", iso := "ude", value := .identity }
  , { walsCode := "udm", iso := "udm", value := .identity }
  , { walsCode := "uli", iso := "uli", value := .identity }
  , { walsCode := "uku", iso := "kuu", value := .differentiation }
  , { walsCode := "urk", iso := "urb", value := .differentiation }
  , { walsCode := "usa", iso := "wnu", value := .identity }
  , { walsCode := "vaf", iso := "vaf", value := .identity }
  , { walsCode := "vie", iso := "vie", value := .identity }
  , { walsCode := "wal", iso := "van", value := .identity }
  , { walsCode := "wra", iso := "wba", value := .bothExpressedByJuxtaposition }
  , { walsCode := "wrd", iso := "wrr", value := .differentiation }
  , { walsCode := "war", iso := "pav", value := .identity }
  , { walsCode := "wch", iso := "mzh", value := .differentiation }
  , { walsCode := "wlf", iso := "wol", value := .differentiation }
  , { walsCode := "yag", iso := "yad", value := .bothExpressedByJuxtaposition }
  , { walsCode := "yaq", iso := "yaq", value := .identity }
  , { walsCode := "ywl", iso := "yok", value := .identity }
  , { walsCode := "ywr", iso := "ywr", value := .identity }
  , { walsCode := "yid", iso := "yii", value := .differentiation }
  , { walsCode := "yim", iso := "yee", value := .bothExpressedByJuxtaposition }
  , { walsCode := "yor", iso := "yor", value := .differentiation }
  , { walsCode := "yko", iso := "yux", value := .differentiation }
  , { walsCode := "zaq", iso := "zpi", value := .identity }
  , { walsCode := "zch", iso := "zoh", value := .identity }
  , { walsCode := "zul", iso := "zul", value := .differentiation }
  , { walsCode := "zun", iso := "zun", value := .differentiation }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F64A
