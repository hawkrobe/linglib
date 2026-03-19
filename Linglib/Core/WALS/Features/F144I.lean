/-!
# WALS Feature 144I: SNegVO Order
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144I`.

Chapter 144, 421 languages.
-/

namespace Core.WALS.F144I

/-- WALS 144I values. -/
inductive SnegvoOrder where
  | wordNodoubleneg  -- Word&NoDoubleNeg (134 languages)
  | prefixNodoubleneg  -- Prefix&NoDoubleNeg (72 languages)
  | wordOptdoubleneg  -- Word&OptDoubleNeg (9 languages)
  | prefixOptdoubleneg  -- Prefix&OptDoubleNeg (5 languages)
  | wordOnlywithanotherneg  -- Word&OnlyWithAnotherNeg (41 languages)
  | prefixOnlywithanotherneg  -- Prefix&OnlyWithAnotherNeg (16 languages)
  | type1Type2  -- Type 1 / Type 2 (2 languages)
  | noSnegvo  -- No SNegVO (142 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144I datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : SnegvoOrder
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144I dataset (421 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .wordNodoubleneg }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .wordOnlywithanotherneg }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .wordNodoubleneg }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .noSnegvo }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .prefixOptdoubleneg }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .wordNodoubleneg }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .noSnegvo }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .prefixNodoubleneg }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .wordNodoubleneg }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noSnegvo }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .wordOnlywithanotherneg }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .noSnegvo }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .noSnegvo }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .noSnegvo }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noSnegvo }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .wordNodoubleneg }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .type1Type2 }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .wordNodoubleneg }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .prefixNodoubleneg }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .wordNodoubleneg }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .wordNodoubleneg }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .noSnegvo }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .wordOptdoubleneg }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .wordNodoubleneg }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .noSnegvo }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .wordNodoubleneg }
  , { walsCode := "au", language := "Au", iso := "avt", value := .wordNodoubleneg }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .prefixNodoubleneg }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .wordOnlywithanotherneg }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noSnegvo }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .noSnegvo }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .wordNodoubleneg }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .noSnegvo }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .noSnegvo }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .prefixNodoubleneg }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .prefixNodoubleneg }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .wordNodoubleneg }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .wordNodoubleneg }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .noSnegvo }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .wordNodoubleneg }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .wordNodoubleneg }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .noSnegvo }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .wordNodoubleneg }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .wordNodoubleneg }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .wordNodoubleneg }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .prefixNodoubleneg }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .noSnegvo }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .prefixNodoubleneg }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .wordOptdoubleneg }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .wordNodoubleneg }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .wordNodoubleneg }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .noSnegvo }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .wordOnlywithanotherneg }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .prefixOptdoubleneg }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .wordOnlywithanotherneg }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .wordNodoubleneg }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .wordOnlywithanotherneg }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .noSnegvo }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .wordNodoubleneg }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .wordOnlywithanotherneg }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .noSnegvo }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .noSnegvo }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .prefixNodoubleneg }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .wordNodoubleneg }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .wordOptdoubleneg }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .prefixNodoubleneg }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .wordNodoubleneg }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .noSnegvo }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .prefixNodoubleneg }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .wordNodoubleneg }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .wordOptdoubleneg }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .noSnegvo }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .prefixOptdoubleneg }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .prefixNodoubleneg }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .wordNodoubleneg }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .wordNodoubleneg }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .wordNodoubleneg }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .prefixOnlywithanotherneg }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noSnegvo }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .noSnegvo }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .wordOnlywithanotherneg }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noSnegvo }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .wordNodoubleneg }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .noSnegvo }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .wordOnlywithanotherneg }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noSnegvo }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .wordNodoubleneg }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .wordOnlywithanotherneg }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .noSnegvo }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .prefixOnlywithanotherneg }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noSnegvo }
  , { walsCode := "eng", language := "English", iso := "eng", value := .wordNodoubleneg }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .prefixNodoubleneg }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .wordNodoubleneg }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .wordOnlywithanotherneg }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .wordOptdoubleneg }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .wordNodoubleneg }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .wordNodoubleneg }
  , { walsCode := "fre", language := "French", iso := "fra", value := .wordOnlywithanotherneg }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .noSnegvo }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .wordNodoubleneg }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .noSnegvo }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .noSnegvo }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .wordOnlywithanotherneg }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .noSnegvo }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noSnegvo }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .noSnegvo }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .wordNodoubleneg }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .wordNodoubleneg }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .wordOnlywithanotherneg }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .noSnegvo }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .noSnegvo }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .noSnegvo }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .type1Type2 }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .wordOnlywithanotherneg }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .noSnegvo }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .noSnegvo }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .prefixNodoubleneg }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .wordNodoubleneg }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .wordOnlywithanotherneg }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noSnegvo }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .wordOptdoubleneg }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .prefixNodoubleneg }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .wordNodoubleneg }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .prefixNodoubleneg }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .wordNodoubleneg }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .wordNodoubleneg }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .prefixNodoubleneg }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .wordNodoubleneg }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .prefixNodoubleneg }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .wordNodoubleneg }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .wordNodoubleneg }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .wordNodoubleneg }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .prefixOnlywithanotherneg }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .noSnegvo }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .prefixNodoubleneg }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .wordNodoubleneg }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .noSnegvo }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .noSnegvo }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noSnegvo }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .wordNodoubleneg }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .prefixOnlywithanotherneg }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .noSnegvo }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .wordOnlywithanotherneg }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .noSnegvo }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .noSnegvo }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .noSnegvo }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .wordNodoubleneg }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .prefixNodoubleneg }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .prefixNodoubleneg }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .prefixNodoubleneg }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .wordNodoubleneg }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .wordOnlywithanotherneg }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .noSnegvo }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .prefixOnlywithanotherneg }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .noSnegvo }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .wordOnlywithanotherneg }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noSnegvo }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .wordNodoubleneg }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .wordOnlywithanotherneg }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .noSnegvo }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noSnegvo }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .noSnegvo }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .noSnegvo }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noSnegvo }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .wordNodoubleneg }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .wordNodoubleneg }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .prefixNodoubleneg }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .prefixNodoubleneg }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .prefixNodoubleneg }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .prefixNodoubleneg }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .wordNodoubleneg }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noSnegvo }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .wordNodoubleneg }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .wordNodoubleneg }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .wordNodoubleneg }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .wordOnlywithanotherneg }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .wordNodoubleneg }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .wordNodoubleneg }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .wordNodoubleneg }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .wordNodoubleneg }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .wordOnlywithanotherneg }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .wordNodoubleneg }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noSnegvo }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .noSnegvo }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .noSnegvo }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .noSnegvo }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noSnegvo }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .wordOnlywithanotherneg }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .prefixNodoubleneg }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .prefixNodoubleneg }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .wordNodoubleneg }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .wordNodoubleneg }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .prefixNodoubleneg }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .prefixNodoubleneg }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .prefixNodoubleneg }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .noSnegvo }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .prefixNodoubleneg }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .prefixOnlywithanotherneg }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .noSnegvo }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .prefixNodoubleneg }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .noSnegvo }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .prefixOnlywithanotherneg }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .noSnegvo }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .prefixNodoubleneg }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .noSnegvo }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .noSnegvo }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .prefixNodoubleneg }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .noSnegvo }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .wordOnlywithanotherneg }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .prefixNodoubleneg }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noSnegvo }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .prefixOnlywithanotherneg }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .wordNodoubleneg }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noSnegvo }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .wordOnlywithanotherneg }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .prefixOnlywithanotherneg }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noSnegvo }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .wordNodoubleneg }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .noSnegvo }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .wordNodoubleneg }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .noSnegvo }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .prefixOnlywithanotherneg }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .prefixNodoubleneg }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .prefixNodoubleneg }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .noSnegvo }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .noSnegvo }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .prefixNodoubleneg }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .wordNodoubleneg }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .noSnegvo }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .noSnegvo }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noSnegvo }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noSnegvo }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .noSnegvo }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .noSnegvo }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .wordNodoubleneg }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .noSnegvo }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .noSnegvo }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .noSnegvo }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .wordNodoubleneg }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noSnegvo }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .noSnegvo }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .noSnegvo }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .wordNodoubleneg }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .noSnegvo }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .noSnegvo }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .wordOnlywithanotherneg }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .noSnegvo }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .noSnegvo }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noSnegvo }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .noSnegvo }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .noSnegvo }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .wordOnlywithanotherneg }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .prefixNodoubleneg }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .wordNodoubleneg }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .wordNodoubleneg }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .wordOnlywithanotherneg }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .noSnegvo }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .wordNodoubleneg }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .noSnegvo }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .wordNodoubleneg }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .noSnegvo }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .wordOnlywithanotherneg }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .wordNodoubleneg }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .noSnegvo }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .wordOnlywithanotherneg }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .noSnegvo }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .noSnegvo }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .noSnegvo }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .wordNodoubleneg }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .wordNodoubleneg }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .prefixNodoubleneg }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .wordOnlywithanotherneg }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .noSnegvo }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .wordNodoubleneg }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .wordNodoubleneg }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .wordNodoubleneg }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .wordNodoubleneg }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .prefixOnlywithanotherneg }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .prefixOnlywithanotherneg }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .noSnegvo }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .wordNodoubleneg }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .wordNodoubleneg }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .wordNodoubleneg }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .noSnegvo }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .noSnegvo }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .noSnegvo }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noSnegvo }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .noSnegvo }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .prefixNodoubleneg }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .wordNodoubleneg }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .wordOptdoubleneg }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .prefixNodoubleneg }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .prefixNodoubleneg }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .wordOnlywithanotherneg }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .noSnegvo }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .wordNodoubleneg }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .prefixNodoubleneg }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .prefixNodoubleneg }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .noSnegvo }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .wordNodoubleneg }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noSnegvo }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .noSnegvo }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .prefixNodoubleneg }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .prefixNodoubleneg }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .prefixNodoubleneg }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .noSnegvo }
  , { walsCode := "one", language := "One", iso := "aun", value := .wordOnlywithanotherneg }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .wordOnlywithanotherneg }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .noSnegvo }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .prefixNodoubleneg }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .wordNodoubleneg }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .wordNodoubleneg }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .prefixNodoubleneg }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .prefixNodoubleneg }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .noSnegvo }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .wordOptdoubleneg }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .wordNodoubleneg }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .wordOnlywithanotherneg }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .prefixNodoubleneg }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .noSnegvo }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .wordNodoubleneg }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .wordNodoubleneg }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .wordNodoubleneg }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .prefixNodoubleneg }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .wordNodoubleneg }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .wordNodoubleneg }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .prefixNodoubleneg }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .wordNodoubleneg }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .noSnegvo }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .noSnegvo }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .wordOnlywithanotherneg }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .prefixNodoubleneg }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .prefixNodoubleneg }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .wordNodoubleneg }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noSnegvo }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .prefixNodoubleneg }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .prefixOnlywithanotherneg }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noSnegvo }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .prefixNodoubleneg }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .wordNodoubleneg }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .wordNodoubleneg }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .wordNodoubleneg }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .prefixOnlywithanotherneg }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .prefixNodoubleneg }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .noSnegvo }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .wordNodoubleneg }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .prefixNodoubleneg }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .wordNodoubleneg }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .noSnegvo }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .wordNodoubleneg }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .wordNodoubleneg }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .wordNodoubleneg }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .wordNodoubleneg }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .wordOnlywithanotherneg }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .noSnegvo }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .wordNodoubleneg }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .wordNodoubleneg }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .wordNodoubleneg }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .prefixOnlywithanotherneg }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .prefixNodoubleneg }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .wordNodoubleneg }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .prefixNodoubleneg }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .wordNodoubleneg }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noSnegvo }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .prefixNodoubleneg }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .wordNodoubleneg }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .prefixNodoubleneg }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .wordNodoubleneg }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .noSnegvo }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .noSnegvo }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .wordNodoubleneg }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .noSnegvo }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .noSnegvo }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .wordOnlywithanotherneg }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .wordNodoubleneg }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .wordOnlywithanotherneg }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .noSnegvo }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .prefixNodoubleneg }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .wordNodoubleneg }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .wordNodoubleneg }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .wordOnlywithanotherneg }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .wordNodoubleneg }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .wordNodoubleneg }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .noSnegvo }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .prefixNodoubleneg }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .wordNodoubleneg }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .prefixNodoubleneg }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .prefixNodoubleneg }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noSnegvo }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noSnegvo }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .prefixNodoubleneg }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .noSnegvo }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .wordNodoubleneg }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .wordNodoubleneg }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .noSnegvo }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .wordNodoubleneg }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .wordNodoubleneg }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .wordOptdoubleneg }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .prefixNodoubleneg }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .wordNodoubleneg }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .prefixOnlywithanotherneg }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .wordNodoubleneg }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .wordOnlywithanotherneg }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .noSnegvo }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .prefixOptdoubleneg }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noSnegvo }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .wordNodoubleneg }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .wordNodoubleneg }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .wordNodoubleneg }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .prefixNodoubleneg }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .wordNodoubleneg }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .prefixNodoubleneg }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .wordNodoubleneg }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .wordNodoubleneg }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .wordNodoubleneg }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noSnegvo }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .noSnegvo }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .noSnegvo }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .noSnegvo }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .prefixOptdoubleneg }
  ]

-- Count verification
theorem total_count : allData.length = 421 := by native_decide

theorem count_wordNodoubleneg :
    (allData.filter (·.value == .wordNodoubleneg)).length = 134 := by native_decide
theorem count_prefixNodoubleneg :
    (allData.filter (·.value == .prefixNodoubleneg)).length = 72 := by native_decide
theorem count_wordOptdoubleneg :
    (allData.filter (·.value == .wordOptdoubleneg)).length = 9 := by native_decide
theorem count_prefixOptdoubleneg :
    (allData.filter (·.value == .prefixOptdoubleneg)).length = 5 := by native_decide
theorem count_wordOnlywithanotherneg :
    (allData.filter (·.value == .wordOnlywithanotherneg)).length = 41 := by native_decide
theorem count_prefixOnlywithanotherneg :
    (allData.filter (·.value == .prefixOnlywithanotherneg)).length = 16 := by native_decide
theorem count_type1Type2 :
    (allData.filter (·.value == .type1Type2)).length = 2 := by native_decide
theorem count_noSnegvo :
    (allData.filter (·.value == .noSnegvo)).length = 142 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144I
