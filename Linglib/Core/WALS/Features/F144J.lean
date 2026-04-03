import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144J: SVNegO Order
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144J`.

Chapter 144, 446 languages.
-/

namespace Core.WALS.F144J

/-- WALS 144J values. -/
inductive SvnegoOrder where
  | wordNodoubleneg  -- Word&NoDoubleNeg (15 languages)
  | suffixNodoubleneg  -- Suffix&NoDoubleNeg (19 languages)
  | wordOptdoubleneg  -- Word&OptDoubleNeg (5 languages)
  | suffixOptdoubleneg  -- Suffix&OptDoubleNeg (2 languages)
  | wordOnlywithanotherneg  -- Word&OnlyWithAnotherNeg (15 languages)
  | suffixOnlywithanotherneg  -- Suffix&OnlyWithAnotherNeg (17 languages)
  | noSvnego  -- No SVNegO (373 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 144J dataset (446 languages). -/
def allData : List (Datapoint SvnegoOrder) :=
  [ { walsCode := "xam", language := "/Xam", iso := "xam", value := .noSvnego }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .noSvnego }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noSvnego }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noSvnego }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .noSvnego }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .noSvnego }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .suffixNodoubleneg }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noSvnego }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .wordNodoubleneg }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .noSvnego }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noSvnego }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noSvnego }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noSvnego }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .wordOnlywithanotherneg }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .noSvnego }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .noSvnego }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .wordNodoubleneg }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noSvnego }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noSvnego }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .suffixOnlywithanotherneg }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .noSvnego }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .noSvnego }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .noSvnego }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noSvnego }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .noSvnego }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noSvnego }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noSvnego }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .noSvnego }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .noSvnego }
  , { walsCode := "au", language := "Au", iso := "avt", value := .noSvnego }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .noSvnego }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .noSvnego }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noSvnego }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .noSvnego }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .noSvnego }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .noSvnego }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .noSvnego }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .noSvnego }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .noSvnego }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .noSvnego }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .noSvnego }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .noSvnego }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .wordOnlywithanotherneg }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noSvnego }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .noSvnego }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noSvnego }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .noSvnego }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .noSvnego }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .noSvnego }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .noSvnego }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .noSvnego }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .noSvnego }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .noSvnego }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .wordNodoubleneg }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .noSvnego }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .noSvnego }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .noSvnego }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .noSvnego }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .noSvnego }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .noSvnego }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .wordOnlywithanotherneg }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .noSvnego }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .noSvnego }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noSvnego }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .noSvnego }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .noSvnego }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .noSvnego }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .suffixNodoubleneg }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .noSvnego }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noSvnego }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .wordOnlywithanotherneg }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .noSvnego }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .noSvnego }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .noSvnego }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .noSvnego }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .noSvnego }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noSvnego }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .noSvnego }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .wordOnlywithanotherneg }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .noSvnego }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .noSvnego }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .noSvnego }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .wordNodoubleneg }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .noSvnego }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .suffixNodoubleneg }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .noSvnego }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .suffixOnlywithanotherneg }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noSvnego }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .noSvnego }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .noSvnego }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .wordOptdoubleneg }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noSvnego }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .noSvnego }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .noSvnego }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .noSvnego }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .suffixOnlywithanotherneg }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noSvnego }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .noSvnego }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noSvnego }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .noSvnego }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .noSvnego }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noSvnego }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .wordOnlywithanotherneg }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noSvnego }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .noSvnego }
  , { walsCode := "fre", language := "French", iso := "fra", value := .wordOptdoubleneg }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .suffixNodoubleneg }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .noSvnego }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .noSvnego }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .noSvnego }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .noSvnego }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .noSvnego }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noSvnego }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .noSvnego }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .noSvnego }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noSvnego }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .wordOnlywithanotherneg }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .noSvnego }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .noSvnego }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .suffixOnlywithanotherneg }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noSvnego }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .noSvnego }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .suffixNodoubleneg }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noSvnego }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .noSvnego }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .wordOnlywithanotherneg }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noSvnego }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noSvnego }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .noSvnego }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noSvnego }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .noSvnego }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .noSvnego }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noSvnego }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .noSvnego }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noSvnego }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noSvnego }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .noSvnego }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noSvnego }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noSvnego }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noSvnego }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .wordNodoubleneg }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .wordOptdoubleneg }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .noSvnego }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .noSvnego }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .suffixOptdoubleneg }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noSvnego }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .noSvnego }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .noSvnego }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noSvnego }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noSvnego }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .noSvnego }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .noSvnego }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .suffixOnlywithanotherneg }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .noSvnego }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .noSvnego }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .noSvnego }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noSvnego }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .noSvnego }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .noSvnego }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .noSvnego }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .noSvnego }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .noSvnego }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .noSvnego }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .noSvnego }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .noSvnego }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .noSvnego }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .noSvnego }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .suffixNodoubleneg }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .noSvnego }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .noSvnego }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .wordOnlywithanotherneg }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noSvnego }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .noSvnego }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .noSvnego }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noSvnego }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noSvnego }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noSvnego }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noSvnego }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .noSvnego }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .noSvnego }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noSvnego }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .noSvnego }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .noSvnego }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .noSvnego }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .noSvnego }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noSvnego }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .suffixNodoubleneg }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .noSvnego }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .noSvnego }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .noSvnego }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .noSvnego }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noSvnego }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noSvnego }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noSvnego }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .noSvnego }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .noSvnego }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .noSvnego }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .suffixNodoubleneg }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .noSvnego }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .noSvnego }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .noSvnego }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .noSvnego }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noSvnego }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .wordOnlywithanotherneg }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .noSvnego }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .noSvnego }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noSvnego }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noSvnego }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noSvnego }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .noSvnego }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .noSvnego }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .noSvnego }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .noSvnego }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .wordOnlywithanotherneg }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .noSvnego }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .noSvnego }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .wordOptdoubleneg }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .noSvnego }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .noSvnego }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .noSvnego }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .noSvnego }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .noSvnego }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .noSvnego }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .noSvnego }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .noSvnego }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noSvnego }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .noSvnego }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .noSvnego }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noSvnego }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noSvnego }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .noSvnego }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noSvnego }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .noSvnego }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .noSvnego }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .noSvnego }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .noSvnego }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .suffixOnlywithanotherneg }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .noSvnego }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .noSvnego }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .noSvnego }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .suffixNodoubleneg }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .noSvnego }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noSvnego }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .noSvnego }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .wordNodoubleneg }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noSvnego }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .suffixNodoubleneg }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .noSvnego }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .noSvnego }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noSvnego }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .noSvnego }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .noSvnego }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .wordNodoubleneg }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noSvnego }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noSvnego }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .noSvnego }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .noSvnego }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .noSvnego }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .noSvnego }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .wordOptdoubleneg }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .noSvnego }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .noSvnego }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noSvnego }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .noSvnego }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .noSvnego }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .noSvnego }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .wordOnlywithanotherneg }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .noSvnego }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noSvnego }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .noSvnego }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .suffixNodoubleneg }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .noSvnego }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .noSvnego }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .noSvnego }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .noSvnego }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .noSvnego }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .noSvnego }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .noSvnego }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noSvnego }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noSvnego }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .noSvnego }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .noSvnego }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .noSvnego }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .noSvnego }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .noSvnego }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .noSvnego }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .noSvnego }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .suffixOnlywithanotherneg }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .noSvnego }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .noSvnego }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noSvnego }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noSvnego }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .noSvnego }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .noSvnego }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .suffixOnlywithanotherneg }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .noSvnego }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .noSvnego }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .suffixNodoubleneg }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noSvnego }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .noSvnego }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .noSvnego }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noSvnego }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .noSvnego }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .noSvnego }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .noSvnego }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .wordNodoubleneg }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .noSvnego }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .wordNodoubleneg }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .noSvnego }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .suffixOptdoubleneg }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .noSvnego }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noSvnego }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .noSvnego }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .suffixNodoubleneg }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .wordNodoubleneg }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .wordNodoubleneg }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .noSvnego }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .noSvnego }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noSvnego }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noSvnego }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .noSvnego }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .noSvnego }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .noSvnego }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .noSvnego }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .noSvnego }
  , { walsCode := "one", language := "One", iso := "aun", value := .noSvnego }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .noSvnego }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .noSvnego }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noSvnego }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noSvnego }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .noSvnego }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .noSvnego }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .noSvnego }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .noSvnego }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .noSvnego }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .suffixNodoubleneg }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .noSvnego }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .noSvnego }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noSvnego }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noSvnego }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .noSvnego }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .noSvnego }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .noSvnego }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .noSvnego }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noSvnego }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .noSvnego }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noSvnego }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .noSvnego }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .wordOnlywithanotherneg }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .noSvnego }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .noSvnego }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noSvnego }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .noSvnego }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .wordNodoubleneg }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .noSvnego }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noSvnego }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noSvnego }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .noSvnego }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .noSvnego }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .noSvnego }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .noSvnego }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .noSvnego }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .noSvnego }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .noSvnego }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .noSvnego }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .noSvnego }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .noSvnego }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .noSvnego }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .noSvnego }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .noSvnego }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .noSvnego }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .noSvnego }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .noSvnego }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .noSvnego }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .noSvnego }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .suffixOnlywithanotherneg }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .noSvnego }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noSvnego }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .noSvnego }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .noSvnego }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .noSvnego }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .suffixOnlywithanotherneg }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noSvnego }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noSvnego }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noSvnego }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .wordNodoubleneg }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noSvnego }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .noSvnego }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .noSvnego }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .noSvnego }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .noSvnego }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .suffixNodoubleneg }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .noSvnego }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .noSvnego }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .suffixNodoubleneg }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .noSvnego }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .wordOnlywithanotherneg }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .noSvnego }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .noSvnego }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .noSvnego }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .noSvnego }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .noSvnego }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .noSvnego }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noSvnego }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noSvnego }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noSvnego }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noSvnego }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .noSvnego }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noSvnego }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noSvnego }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .noSvnego }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noSvnego }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .noSvnego }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .suffixNodoubleneg }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .wordNodoubleneg }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .noSvnego }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .noSvnego }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noSvnego }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .noSvnego }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .noSvnego }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noSvnego }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noSvnego }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .noSvnego }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .noSvnego }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noSvnego }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .suffixOnlywithanotherneg }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .noSvnego }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .suffixOnlywithanotherneg }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .noSvnego }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .suffixOnlywithanotherneg }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noSvnego }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .suffixNodoubleneg }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .noSvnego }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .suffixNodoubleneg }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .noSvnego }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .noSvnego }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .noSvnego }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .noSvnego }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .noSvnego }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noSvnego }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .suffixOnlywithanotherneg }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .wordNodoubleneg }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .wordOnlywithanotherneg }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .suffixOnlywithanotherneg }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .suffixOnlywithanotherneg }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .suffixOnlywithanotherneg }
  ]

-- Count verification
theorem total_count : allData.length = 446 := by native_decide

theorem count_wordNodoubleneg :
    (allData.filter (·.value == .wordNodoubleneg)).length = 15 := by native_decide
theorem count_suffixNodoubleneg :
    (allData.filter (·.value == .suffixNodoubleneg)).length = 19 := by native_decide
theorem count_wordOptdoubleneg :
    (allData.filter (·.value == .wordOptdoubleneg)).length = 5 := by native_decide
theorem count_suffixOptdoubleneg :
    (allData.filter (·.value == .suffixOptdoubleneg)).length = 2 := by native_decide
theorem count_wordOnlywithanotherneg :
    (allData.filter (·.value == .wordOnlywithanotherneg)).length = 15 := by native_decide
theorem count_suffixOnlywithanotherneg :
    (allData.filter (·.value == .suffixOnlywithanotherneg)).length = 17 := by native_decide
theorem count_noSvnego :
    (allData.filter (·.value == .noSvnego)).length = 373 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144J
