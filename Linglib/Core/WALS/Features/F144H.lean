/-!
# WALS Feature 144H: NegSVO Order
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144H`.

Chapter 144, 420 languages.
-/

namespace Core.WALS.F144H

/-- WALS 144H values. -/
inductive NegsvoOrder where
  | nodoubleneg  -- NoDoubleNeg (19 languages)
  | optdoubleneg  -- OptDoubleNeg (1 languages)
  | onlywithanotherneg  -- OnlyWithAnotherNeg (8 languages)
  | noNegsvo  -- No NegSVO (392 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144H datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : NegsvoOrder
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144H dataset (420 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .noNegsvo }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noNegsvo }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .noNegsvo }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .noNegsvo }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noNegsvo }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .noNegsvo }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .noNegsvo }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noNegsvo }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noNegsvo }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noNegsvo }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .noNegsvo }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .noNegsvo }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .noNegsvo }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .noNegsvo }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noNegsvo }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .nodoubleneg }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noNegsvo }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .noNegsvo }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .noNegsvo }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .noNegsvo }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noNegsvo }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .noNegsvo }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noNegsvo }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noNegsvo }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .noNegsvo }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .noNegsvo }
  , { walsCode := "au", language := "Au", iso := "avt", value := .noNegsvo }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .noNegsvo }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .noNegsvo }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noNegsvo }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .noNegsvo }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .noNegsvo }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .noNegsvo }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .noNegsvo }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .noNegsvo }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .noNegsvo }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .noNegsvo }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .noNegsvo }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .noNegsvo }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noNegsvo }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .noNegsvo }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .noNegsvo }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noNegsvo }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .noNegsvo }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .noNegsvo }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .noNegsvo }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .noNegsvo }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .noNegsvo }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .noNegsvo }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .noNegsvo }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .nodoubleneg }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .noNegsvo }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .noNegsvo }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .noNegsvo }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .noNegsvo }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .noNegsvo }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .noNegsvo }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .noNegsvo }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noNegsvo }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .noNegsvo }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .noNegsvo }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .noNegsvo }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .noNegsvo }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noNegsvo }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noNegsvo }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .noNegsvo }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .noNegsvo }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .noNegsvo }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .noNegsvo }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .noNegsvo }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noNegsvo }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .nodoubleneg }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .onlywithanotherneg }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .noNegsvo }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .noNegsvo }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .noNegsvo }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .noNegsvo }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .noNegsvo }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noNegsvo }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .noNegsvo }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .noNegsvo }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .nodoubleneg }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .noNegsvo }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .noNegsvo }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .noNegsvo }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noNegsvo }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .noNegsvo }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .noNegsvo }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .noNegsvo }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .noNegsvo }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noNegsvo }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noNegsvo }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .noNegsvo }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .noNegsvo }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noNegsvo }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .noNegsvo }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noNegsvo }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .noNegsvo }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noNegsvo }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .noNegsvo }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .noNegsvo }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .onlywithanotherneg }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .noNegsvo }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .noNegsvo }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .noNegsvo }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noNegsvo }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .noNegsvo }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .noNegsvo }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noNegsvo }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noNegsvo }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .nodoubleneg }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .noNegsvo }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .noNegsvo }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .noNegsvo }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noNegsvo }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .noNegsvo }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .noNegsvo }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noNegsvo }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .noNegsvo }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .noNegsvo }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noNegsvo }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noNegsvo }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .noNegsvo }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noNegsvo }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .noNegsvo }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .noNegsvo }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noNegsvo }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .noNegsvo }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noNegsvo }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .noNegsvo }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noNegsvo }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noNegsvo }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noNegsvo }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .noNegsvo }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .noNegsvo }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .noNegsvo }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noNegsvo }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .noNegsvo }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .nodoubleneg }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noNegsvo }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noNegsvo }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .noNegsvo }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .noNegsvo }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .noNegsvo }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .noNegsvo }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .noNegsvo }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .noNegsvo }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noNegsvo }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .noNegsvo }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .noNegsvo }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .noNegsvo }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .noNegsvo }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .noNegsvo }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .noNegsvo }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .noNegsvo }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .noNegsvo }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .noNegsvo }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noNegsvo }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .noNegsvo }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .noNegsvo }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .noNegsvo }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noNegsvo }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .noNegsvo }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .noNegsvo }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noNegsvo }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noNegsvo }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noNegsvo }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .noNegsvo }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .noNegsvo }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .noNegsvo }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .noNegsvo }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .noNegsvo }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noNegsvo }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .noNegsvo }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .noNegsvo }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .noNegsvo }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noNegsvo }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .noNegsvo }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noNegsvo }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noNegsvo }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noNegsvo }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .onlywithanotherneg }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .noNegsvo }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noNegsvo }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .noNegsvo }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .noNegsvo }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .noNegsvo }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noNegsvo }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .noNegsvo }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .noNegsvo }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .noNegsvo }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noNegsvo }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noNegsvo }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noNegsvo }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .noNegsvo }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .noNegsvo }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .noNegsvo }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .noNegsvo }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .noNegsvo }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .noNegsvo }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .noNegsvo }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .noNegsvo }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .noNegsvo }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .noNegsvo }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .noNegsvo }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .noNegsvo }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .noNegsvo }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .noNegsvo }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .noNegsvo }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .noNegsvo }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .noNegsvo }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noNegsvo }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .noNegsvo }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .nodoubleneg }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noNegsvo }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noNegsvo }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .noNegsvo }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noNegsvo }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .noNegsvo }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .noNegsvo }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .noNegsvo }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .nodoubleneg }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .noNegsvo }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .noNegsvo }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .noNegsvo }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .noNegsvo }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .noNegsvo }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .noNegsvo }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noNegsvo }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .noNegsvo }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .nodoubleneg }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .nodoubleneg }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noNegsvo }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .noNegsvo }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .nodoubleneg }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noNegsvo }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .noNegsvo }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .onlywithanotherneg }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .noNegsvo }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noNegsvo }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noNegsvo }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .noNegsvo }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .noNegsvo }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .noNegsvo }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .noNegsvo }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .noNegsvo }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .noNegsvo }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .noNegsvo }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .noNegsvo }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noNegsvo }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .noNegsvo }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .noNegsvo }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .noNegsvo }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .noNegsvo }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noNegsvo }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .noNegsvo }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .noNegsvo }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .noNegsvo }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .noNegsvo }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .noNegsvo }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .nodoubleneg }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .noNegsvo }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noNegsvo }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noNegsvo }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .noNegsvo }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .noNegsvo }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .onlywithanotherneg }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .noNegsvo }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .noNegsvo }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .noNegsvo }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .noNegsvo }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .noNegsvo }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .noNegsvo }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .nodoubleneg }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .noNegsvo }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noNegsvo }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .noNegsvo }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .noNegsvo }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .noNegsvo }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .noNegsvo }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .noNegsvo }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noNegsvo }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .noNegsvo }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .noNegsvo }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .noNegsvo }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .nodoubleneg }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .noNegsvo }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .nodoubleneg }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .noNegsvo }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .noNegsvo }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .noNegsvo }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .noNegsvo }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .noNegsvo }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noNegsvo }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .onlywithanotherneg }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .noNegsvo }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .noNegsvo }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .noNegsvo }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .noNegsvo }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .noNegsvo }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noNegsvo }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noNegsvo }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .noNegsvo }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .noNegsvo }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .noNegsvo }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .noNegsvo }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .noNegsvo }
  , { walsCode := "one", language := "One", iso := "aun", value := .noNegsvo }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .noNegsvo }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .nodoubleneg }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noNegsvo }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noNegsvo }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .noNegsvo }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .noNegsvo }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .noNegsvo }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .noNegsvo }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .noNegsvo }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .nodoubleneg }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .noNegsvo }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .noNegsvo }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .noNegsvo }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noNegsvo }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noNegsvo }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .noNegsvo }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .noNegsvo }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .noNegsvo }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .noNegsvo }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .noNegsvo }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noNegsvo }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .noNegsvo }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .noNegsvo }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .noNegsvo }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .noNegsvo }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .noNegsvo }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noNegsvo }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noNegsvo }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .noNegsvo }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noNegsvo }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .noNegsvo }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .noNegsvo }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .noNegsvo }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .noNegsvo }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .noNegsvo }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .noNegsvo }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .noNegsvo }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .noNegsvo }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .noNegsvo }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .noNegsvo }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .noNegsvo }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .noNegsvo }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .noNegsvo }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .noNegsvo }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .noNegsvo }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .noNegsvo }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .noNegsvo }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noNegsvo }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .noNegsvo }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .noNegsvo }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .noNegsvo }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noNegsvo }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noNegsvo }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noNegsvo }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .noNegsvo }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noNegsvo }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .noNegsvo }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .noNegsvo }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .noNegsvo }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .noNegsvo }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .noNegsvo }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .optdoubleneg }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .noNegsvo }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .noNegsvo }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .nodoubleneg }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .noNegsvo }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .noNegsvo }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .noNegsvo }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .nodoubleneg }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .noNegsvo }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .noNegsvo }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noNegsvo }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noNegsvo }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noNegsvo }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noNegsvo }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .noNegsvo }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noNegsvo }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noNegsvo }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .noNegsvo }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .noNegsvo }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noNegsvo }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noNegsvo }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .noNegsvo }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .noNegsvo }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noNegsvo }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .noNegsvo }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .noNegsvo }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noNegsvo }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noNegsvo }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .noNegsvo }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .noNegsvo }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noNegsvo }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .noNegsvo }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .noNegsvo }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .noNegsvo }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .noNegsvo }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .noNegsvo }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noNegsvo }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noNegsvo }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .noNegsvo }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .noNegsvo }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .noNegsvo }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .noNegsvo }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .noNegsvo }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .noNegsvo }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .noNegsvo }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noNegsvo }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .onlywithanotherneg }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .noNegsvo }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .noNegsvo }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .onlywithanotherneg }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noNegsvo }
  ]

-- Count verification
theorem total_count : allData.length = 420 := by native_decide

theorem count_nodoubleneg :
    (allData.filter (·.value == .nodoubleneg)).length = 19 := by native_decide
theorem count_optdoubleneg :
    (allData.filter (·.value == .optdoubleneg)).length = 1 := by native_decide
theorem count_onlywithanotherneg :
    (allData.filter (·.value == .onlywithanotherneg)).length = 8 := by native_decide
theorem count_noNegsvo :
    (allData.filter (·.value == .noNegsvo)).length = 392 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144H
