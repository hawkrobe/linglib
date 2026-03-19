import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144D: The Position of Negative Morphemes in SVO Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144D`.

Chapter 144, 463 languages.
-/

namespace Core.WALS.F144D

/-- WALS 144D values. -/
inductive PositionOfNegativeMorphemesInSvoLanguages where
  | negsvo  -- NegSVO (4 languages)
  | snegvo  -- SNegVO (111 languages)
  | svnego  -- SVNegO (2 languages)
  | svoneg  -- SVONeg (81 languages)
  | sNegVO  -- S[Neg-V]O (67 languages)
  | sVNegO  -- S[V-Neg]O (12 languages)
  | svoTone  -- SVO&Tone (1 languages)
  | vsoButNegsvo  -- VSO but NegSVO (6 languages)
  | svoSovButSvoneg  -- SVO/SOV but SVONeg (5 languages)
  | sovSovButSnegvo  -- SOV/SOV but SNegVO (1 languages)
  | otherNegv  -- Other NegV (26 languages)
  | otherVneg  -- Other VNeg (8 languages)
  | moreThanOneConstruction  -- More than one construction (48 languages)
  | obligneg  -- ObligNeg (56 languages)
  | optneg  -- OptNeg (35 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144D dataset (463 languages). -/
def allData : List (Datapoint PositionOfNegativeMorphemesInSvoLanguages) :=
  [ { walsCode := "xam", language := "/Xam", iso := "xam", value := .otherNegv }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .snegvo }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .otherNegv }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .obligneg }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .snegvo }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .moreThanOneConstruction }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .otherNegv }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .sVNegO }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .optneg }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .moreThanOneConstruction }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .svoneg }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .moreThanOneConstruction }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .sNegVO }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .snegvo }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .svoneg }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .obligneg }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .svoneg }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .svoneg }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .svnego }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .svoneg }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .moreThanOneConstruction }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .optneg }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .snegvo }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .sNegVO }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .snegvo }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .moreThanOneConstruction }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .svoneg }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .optneg }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .moreThanOneConstruction }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .svoneg }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .snegvo }
  , { walsCode := "au", language := "Au", iso := "avt", value := .moreThanOneConstruction }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .sNegVO }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .obligneg }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .svoneg }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .svoneg }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .snegvo }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .moreThanOneConstruction }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .svoneg }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .svoneg }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .sNegVO }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .sNegVO }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .snegvo }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .snegvo }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .obligneg }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .snegvo }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .snegvo }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .otherVneg }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .moreThanOneConstruction }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .moreThanOneConstruction }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .snegvo }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .sNegVO }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .svoneg }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .obligneg }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .sNegVO }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .optneg }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .snegvo }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .moreThanOneConstruction }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .svoneg }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .obligneg }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .optneg }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .optneg }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .moreThanOneConstruction }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .snegvo }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .obligneg }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .svoneg }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .otherNegv }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .snegvo }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .obligneg }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .svoneg }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .otherNegv }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .sVNegO }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .sNegVO }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .snegvo }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .optneg }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .sNegVO }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .moreThanOneConstruction }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .svoneg }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .sNegVO }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .snegvo }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .optneg }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .negsvo }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .optneg }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .sNegVO }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .snegvo }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .snegvo }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .moreThanOneConstruction }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .obligneg }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .sVNegO }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .svoSovButSvoneg }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .obligneg }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .moreThanOneConstruction }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .snegvo }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .svoneg }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .optneg }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .moreThanOneConstruction }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .snegvo }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .obligneg }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .svoneg }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .obligneg }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .svoTone }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .otherNegv }
  , { walsCode := "eng", language := "English", iso := "eng", value := .snegvo }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .sNegVO }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .snegvo }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .obligneg }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .optneg }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .snegvo }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .snegvo }
  , { walsCode := "fre", language := "French", iso := "fra", value := .optneg }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .sVNegO }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .snegvo }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .optneg }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .svoneg }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .optneg }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .svoneg }
  , { walsCode := "ger", language := "German", iso := "deu", value := .moreThanOneConstruction }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .svoneg }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .snegvo }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .moreThanOneConstruction }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .obligneg }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .vsoButNegsvo }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .svoneg }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .otherVneg }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .obligneg }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .obligneg }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .svoneg }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .sVNegO }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .moreThanOneConstruction }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .snegvo }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .obligneg }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .svoneg }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .optneg }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .sNegVO }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .snegvo }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .sNegVO }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .snegvo }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .snegvo }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .sNegVO }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .snegvo }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .otherNegv }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .sNegVO }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .sovSovButSnegvo }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .snegvo }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .otherNegv }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .moreThanOneConstruction }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .optneg }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .obligneg }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .svoneg }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .sNegVO }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .optneg }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .snegvo }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .svoneg }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .negsvo }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .svoneg }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .snegvo }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .obligneg }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .svoneg }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .obligneg }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .svoneg }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .svoneg }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .svoneg }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .snegvo }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .sNegVO }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .sNegVO }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .otherNegv }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .sNegVO }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .snegvo }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .obligneg }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .svoneg }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .obligneg }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .svoneg }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .obligneg }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .sVNegO }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .snegvo }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .otherNegv }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .obligneg }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .otherVneg }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .svoneg }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .svoneg }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .svoneg }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .svoneg }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .snegvo }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .snegvo }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .otherNegv }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .otherNegv }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .sNegVO }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .moreThanOneConstruction }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .sNegVO }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .sNegVO }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .sNegVO }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .snegvo }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .obligneg }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .moreThanOneConstruction }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .snegvo }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .snegvo }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .snegvo }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .obligneg }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .snegvo }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .snegvo }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .snegvo }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .snegvo }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .optneg }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .snegvo }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .otherNegv }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .moreThanOneConstruction }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .svoneg }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .svoneg }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .moreThanOneConstruction }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .svoneg }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .svoneg }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .obligneg }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .sNegVO }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .sNegVO }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .snegvo }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .snegvo }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .sNegVO }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .sNegVO }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .sNegVO }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .svoneg }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .sNegVO }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .obligneg }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .moreThanOneConstruction }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .sNegVO }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .optneg }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .obligneg }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .svoneg }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .sNegVO }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .svoSovButSvoneg }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .otherVneg }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .sNegVO }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .svoneg }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .obligneg }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .sNegVO }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .svoSovButSvoneg }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .obligneg }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .moreThanOneConstruction }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .svoneg }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .obligneg }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .obligneg }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .svoSovButSvoneg }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .snegvo }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .svoneg }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .snegvo }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .vsoButNegsvo }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .obligneg }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .sNegVO }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .sNegVO }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .svoneg }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .sVNegO }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .sNegVO }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .snegvo }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .svoneg }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .moreThanOneConstruction }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .vsoButNegsvo }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .sVNegO }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .svoneg }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .vsoButNegsvo }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .snegvo }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .svoneg }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .obligneg }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .moreThanOneConstruction }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .snegvo }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .svoneg }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .svoneg }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .otherVneg }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .snegvo }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .svoneg }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .svoneg }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .optneg }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .svoneg }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .svoneg }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .moreThanOneConstruction }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .svoneg }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .otherNegv }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .svoneg }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .obligneg }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .sNegVO }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .snegvo }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .snegvo }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .moreThanOneConstruction }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .obligneg }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .svoneg }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .otherNegv }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .snegvo }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .svoSovButSvoneg }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .moreThanOneConstruction }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .svoneg }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .obligneg }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .optneg }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .snegvo }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .svoneg }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .optneg }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .optneg }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .svoneg }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .otherVneg }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .snegvo }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .snegvo }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .sNegVO }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .obligneg }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .moreThanOneConstruction }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .snegvo }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .otherNegv }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .snegvo }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .snegvo }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .snegvo }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .obligneg }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .otherNegv }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .obligneg }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .sVNegO }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .snegvo }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .snegvo }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .snegvo }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .otherNegv }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .svoneg }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .negsvo }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .svoneg }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .moreThanOneConstruction }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .svoneg }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .moreThanOneConstruction }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .snegvo }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .optneg }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .sNegVO }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .sNegVO }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .obligneg }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .sVNegO }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .moreThanOneConstruction }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .moreThanOneConstruction }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .sNegVO }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .svoneg }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .snegvo }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .svoneg }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .svoneg }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .sNegVO }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .sNegVO }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .sNegVO }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .svoneg }
  , { walsCode := "one", language := "One", iso := "aun", value := .optneg }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .obligneg }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .optneg }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .negsvo }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .sNegVO }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .snegvo }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .snegvo }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .sNegVO }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .sNegVO }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .svoneg }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .optneg }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .moreThanOneConstruction }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .obligneg }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .sNegVO }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .otherVneg }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .snegvo }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .snegvo }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .snegvo }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .sNegVO }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .snegvo }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .snegvo }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .otherNegv }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .obligneg }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .sNegVO }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .optneg }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .snegvo }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .otherVneg }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .svoneg }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .obligneg }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .sNegVO }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .sNegVO }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .snegvo }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .otherNegv }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .moreThanOneConstruction }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .sNegVO }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .obligneg }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .svoneg }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .sNegVO }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .snegvo }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .snegvo }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .snegvo }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .obligneg }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .otherNegv }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .otherNegv }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .sNegVO }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .svoneg }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .snegvo }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .sNegVO }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .snegvo }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .svoneg }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .snegvo }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .snegvo }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .snegvo }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .snegvo }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .otherNegv }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .obligneg }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .svoneg }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .snegvo }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .snegvo }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .snegvo }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .otherNegv }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .obligneg }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .sNegVO }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .snegvo }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .sNegVO }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .moreThanOneConstruction }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .svoneg }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .sNegVO }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .snegvo }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .sNegVO }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .snegvo }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .sVNegO }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .optneg }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .snegvo }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .sVNegO }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .vsoButNegsvo }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .obligneg }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .moreThanOneConstruction }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .otherNegv }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .optneg }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .vsoButNegsvo }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .sNegVO }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .snegvo }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .snegvo }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .optneg }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .snegvo }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .moreThanOneConstruction }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .svoneg }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .moreThanOneConstruction }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .snegvo }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .moreThanOneConstruction }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .otherNegv }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .sNegVO }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .moreThanOneConstruction }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .moreThanOneConstruction }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .sNegVO }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .svoneg }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .moreThanOneConstruction }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .snegvo }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .svoneg }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .snegvo }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .snegvo }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .optneg }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .sNegVO }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .snegvo }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .obligneg }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .snegvo }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .obligneg }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .svoneg }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .optneg }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .svoneg }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .moreThanOneConstruction }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .snegvo }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .moreThanOneConstruction }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .sNegVO }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .snegvo }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .sNegVO }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .snegvo }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .snegvo }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .snegvo }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .obligneg }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .svnego }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .obligneg }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .obligneg }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .optneg }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .optneg }
  ]

-- Count verification
theorem total_count : allData.length = 463 := by native_decide

theorem count_negsvo :
    (allData.filter (·.value == .negsvo)).length = 4 := by native_decide
theorem count_snegvo :
    (allData.filter (·.value == .snegvo)).length = 111 := by native_decide
theorem count_svnego :
    (allData.filter (·.value == .svnego)).length = 2 := by native_decide
theorem count_svoneg :
    (allData.filter (·.value == .svoneg)).length = 81 := by native_decide
theorem count_sNegVO :
    (allData.filter (·.value == .sNegVO)).length = 67 := by native_decide
theorem count_sVNegO :
    (allData.filter (·.value == .sVNegO)).length = 12 := by native_decide
theorem count_svoTone :
    (allData.filter (·.value == .svoTone)).length = 1 := by native_decide
theorem count_vsoButNegsvo :
    (allData.filter (·.value == .vsoButNegsvo)).length = 6 := by native_decide
theorem count_svoSovButSvoneg :
    (allData.filter (·.value == .svoSovButSvoneg)).length = 5 := by native_decide
theorem count_sovSovButSnegvo :
    (allData.filter (·.value == .sovSovButSnegvo)).length = 1 := by native_decide
theorem count_otherNegv :
    (allData.filter (·.value == .otherNegv)).length = 26 := by native_decide
theorem count_otherVneg :
    (allData.filter (·.value == .otherVneg)).length = 8 := by native_decide
theorem count_moreThanOneConstruction :
    (allData.filter (·.value == .moreThanOneConstruction)).length = 48 := by native_decide
theorem count_obligneg :
    (allData.filter (·.value == .obligneg)).length = 56 := by native_decide
theorem count_optneg :
    (allData.filter (·.value == .optneg)).length = 35 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144D
