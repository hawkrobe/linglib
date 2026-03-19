import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144K: SVONeg Order
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144K`.

Chapter 144, 446 languages.
-/

namespace Core.WALS.F144K

/-- WALS 144K values. -/
inductive SvonegOrder where
  | nodoubleneg  -- NoDoubleNeg (95 languages)
  | optdoubleneg  -- OptDoubleNeg (12 languages)
  | onlywithanotherneg  -- OnlyWithAnotherNeg (35 languages)
  | noSvoneg  -- No SVONeg (304 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144K dataset (446 languages). -/
def allData : List (Datapoint SvonegOrder) :=
  [ { walsCode := "xam", language := "/Xam", iso := "xam", value := .noSvoneg }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .noSvoneg }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noSvoneg }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .onlywithanotherneg }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .noSvoneg }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .noSvoneg }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .noSvoneg }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .onlywithanotherneg }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .noSvoneg }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .nodoubleneg }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noSvoneg }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noSvoneg }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .nodoubleneg }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .onlywithanotherneg }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .nodoubleneg }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .nodoubleneg }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .noSvoneg }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .nodoubleneg }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noSvoneg }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noSvoneg }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .noSvoneg }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .noSvoneg }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .noSvoneg }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noSvoneg }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .nodoubleneg }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .onlywithanotherneg }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noSvoneg }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .nodoubleneg }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .noSvoneg }
  , { walsCode := "au", language := "Au", iso := "avt", value := .nodoubleneg }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .noSvoneg }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .onlywithanotherneg }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .nodoubleneg }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .nodoubleneg }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .noSvoneg }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .noSvoneg }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .nodoubleneg }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .nodoubleneg }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .noSvoneg }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .noSvoneg }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .noSvoneg }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .noSvoneg }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .noSvoneg }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noSvoneg }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .noSvoneg }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noSvoneg }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .noSvoneg }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .noSvoneg }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .noSvoneg }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .nodoubleneg }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .noSvoneg }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .onlywithanotherneg }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .noSvoneg }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .nodoubleneg }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .nodoubleneg }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .onlywithanotherneg }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .onlywithanotherneg }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .optdoubleneg }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .noSvoneg }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .noSvoneg }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .noSvoneg }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .nodoubleneg }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .noSvoneg }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noSvoneg }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .onlywithanotherneg }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .nodoubleneg }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .noSvoneg }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .noSvoneg }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .noSvoneg }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noSvoneg }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noSvoneg }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .noSvoneg }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .nodoubleneg }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .nodoubleneg }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .noSvoneg }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .noSvoneg }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .onlywithanotherneg }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .noSvoneg }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .noSvoneg }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .noSvoneg }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .noSvoneg }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .noSvoneg }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .noSvoneg }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .noSvoneg }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noSvoneg }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .nodoubleneg }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .onlywithanotherneg }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noSvoneg }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .noSvoneg }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .nodoubleneg }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .noSvoneg }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .nodoubleneg }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .noSvoneg }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .onlywithanotherneg }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .nodoubleneg }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .noSvoneg }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noSvoneg }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .noSvoneg }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noSvoneg }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .noSvoneg }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .noSvoneg }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .onlywithanotherneg }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .noSvoneg }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noSvoneg }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .noSvoneg }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noSvoneg }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .noSvoneg }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .noSvoneg }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .optdoubleneg }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .nodoubleneg }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .optdoubleneg }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .nodoubleneg }
  , { walsCode := "ger", language := "German", iso := "deu", value := .nodoubleneg }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .nodoubleneg }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .noSvoneg }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noSvoneg }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noSvoneg }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .noSvoneg }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .nodoubleneg }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .noSvoneg }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .onlywithanotherneg }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .nodoubleneg }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .noSvoneg }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noSvoneg }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .noSvoneg }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .noSvoneg }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .nodoubleneg }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .onlywithanotherneg }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .noSvoneg }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noSvoneg }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .noSvoneg }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .noSvoneg }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noSvoneg }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .noSvoneg }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noSvoneg }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noSvoneg }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .noSvoneg }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noSvoneg }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noSvoneg }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noSvoneg }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noSvoneg }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .noSvoneg }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .nodoubleneg }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .noSvoneg }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .noSvoneg }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noSvoneg }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .nodoubleneg }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .noSvoneg }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .nodoubleneg }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noSvoneg }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .onlywithanotherneg }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .nodoubleneg }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .noSvoneg }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .nodoubleneg }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .nodoubleneg }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .nodoubleneg }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noSvoneg }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .noSvoneg }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .noSvoneg }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .noSvoneg }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .noSvoneg }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .noSvoneg }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .onlywithanotherneg }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .nodoubleneg }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .onlywithanotherneg }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .nodoubleneg }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .onlywithanotherneg }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noSvoneg }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .noSvoneg }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .noSvoneg }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .noSvoneg }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .nodoubleneg }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .nodoubleneg }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .nodoubleneg }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .nodoubleneg }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noSvoneg }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noSvoneg }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noSvoneg }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .noSvoneg }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .noSvoneg }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noSvoneg }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .noSvoneg }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .noSvoneg }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .noSvoneg }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .noSvoneg }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .onlywithanotherneg }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .noSvoneg }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .noSvoneg }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .noSvoneg }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .noSvoneg }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .noSvoneg }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noSvoneg }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noSvoneg }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noSvoneg }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .optdoubleneg }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .noSvoneg }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .noSvoneg }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noSvoneg }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .nodoubleneg }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .nodoubleneg }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .noSvoneg }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .nodoubleneg }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .nodoubleneg }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .noSvoneg }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .noSvoneg }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .noSvoneg }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noSvoneg }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noSvoneg }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noSvoneg }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .noSvoneg }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .noSvoneg }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .nodoubleneg }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .noSvoneg }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .noSvoneg }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .nodoubleneg }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .noSvoneg }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .onlywithanotherneg }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .onlywithanotherneg }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .nodoubleneg }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .noSvoneg }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .nodoubleneg }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .noSvoneg }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .nodoubleneg }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .onlywithanotherneg }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .noSvoneg }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .nodoubleneg }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .onlywithanotherneg }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .noSvoneg }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .nodoubleneg }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .optdoubleneg }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .onlywithanotherneg }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .nodoubleneg }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .noSvoneg }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .nodoubleneg }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .noSvoneg }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .noSvoneg }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .noSvoneg }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .noSvoneg }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .noSvoneg }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .nodoubleneg }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .noSvoneg }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .noSvoneg }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noSvoneg }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .nodoubleneg }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .noSvoneg }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noSvoneg }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noSvoneg }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .nodoubleneg }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .noSvoneg }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noSvoneg }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .nodoubleneg }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .onlywithanotherneg }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .nodoubleneg }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noSvoneg }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .nodoubleneg }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .nodoubleneg }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .noSvoneg }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .nodoubleneg }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .nodoubleneg }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .noSvoneg }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .nodoubleneg }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .nodoubleneg }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .nodoubleneg }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .nodoubleneg }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .noSvoneg }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .nodoubleneg }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .onlywithanotherneg }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .noSvoneg }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noSvoneg }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .noSvoneg }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .noSvoneg }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .onlywithanotherneg }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .nodoubleneg }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .noSvoneg }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .noSvoneg }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .nodoubleneg }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .noSvoneg }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .nodoubleneg }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .optdoubleneg }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noSvoneg }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .nodoubleneg }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .optdoubleneg }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .optdoubleneg }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .nodoubleneg }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .noSvoneg }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .noSvoneg }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .noSvoneg }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .noSvoneg }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .noSvoneg }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .noSvoneg }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noSvoneg }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noSvoneg }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .noSvoneg }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .noSvoneg }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .noSvoneg }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .noSvoneg }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .onlywithanotherneg }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .noSvoneg }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noSvoneg }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .noSvoneg }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .noSvoneg }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noSvoneg }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .nodoubleneg }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .noSvoneg }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .nodoubleneg }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noSvoneg }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .nodoubleneg }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .noSvoneg }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .noSvoneg }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .noSvoneg }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .noSvoneg }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noSvoneg }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .onlywithanotherneg }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .noSvoneg }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .noSvoneg }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .noSvoneg }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .noSvoneg }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .nodoubleneg }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noSvoneg }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .nodoubleneg }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .nodoubleneg }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .noSvoneg }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .noSvoneg }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .noSvoneg }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .nodoubleneg }
  , { walsCode := "one", language := "One", iso := "aun", value := .optdoubleneg }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .optdoubleneg }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .noSvoneg }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noSvoneg }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noSvoneg }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .noSvoneg }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .noSvoneg }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .noSvoneg }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .nodoubleneg }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .onlywithanotherneg }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noSvoneg }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .onlywithanotherneg }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .noSvoneg }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noSvoneg }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noSvoneg }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .noSvoneg }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .noSvoneg }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .noSvoneg }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .noSvoneg }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noSvoneg }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .noSvoneg }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noSvoneg }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .nodoubleneg }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .noSvoneg }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .noSvoneg }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .noSvoneg }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noSvoneg }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .noSvoneg }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .nodoubleneg }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .noSvoneg }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noSvoneg }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .nodoubleneg }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .noSvoneg }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .noSvoneg }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .noSvoneg }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .noSvoneg }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .onlywithanotherneg }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .noSvoneg }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .noSvoneg }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .noSvoneg }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .nodoubleneg }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .noSvoneg }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .noSvoneg }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .noSvoneg }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .nodoubleneg }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .noSvoneg }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .noSvoneg }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .noSvoneg }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .noSvoneg }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .noSvoneg }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .noSvoneg }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .nodoubleneg }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noSvoneg }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .noSvoneg }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .noSvoneg }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .noSvoneg }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .noSvoneg }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noSvoneg }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noSvoneg }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noSvoneg }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .noSvoneg }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .nodoubleneg }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .noSvoneg }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .noSvoneg }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .noSvoneg }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .noSvoneg }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .noSvoneg }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .noSvoneg }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .noSvoneg }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .noSvoneg }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .noSvoneg }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .noSvoneg }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .noSvoneg }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .noSvoneg }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .optdoubleneg }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .noSvoneg }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .noSvoneg }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .noSvoneg }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noSvoneg }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .optdoubleneg }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noSvoneg }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noSvoneg }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .nodoubleneg }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noSvoneg }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noSvoneg }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .noSvoneg }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noSvoneg }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .noSvoneg }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noSvoneg }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noSvoneg }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .noSvoneg }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .nodoubleneg }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noSvoneg }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .noSvoneg }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .nodoubleneg }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noSvoneg }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noSvoneg }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .onlywithanotherneg }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .noSvoneg }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noSvoneg }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .noSvoneg }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .noSvoneg }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .noSvoneg }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .nodoubleneg }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .noSvoneg }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .nodoubleneg }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noSvoneg }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .noSvoneg }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .noSvoneg }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .noSvoneg }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .noSvoneg }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .noSvoneg }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .noSvoneg }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .noSvoneg }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noSvoneg }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noSvoneg }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .noSvoneg }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .onlywithanotherneg }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .noSvoneg }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .noSvoneg }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noSvoneg }
  ]

-- Count verification
theorem total_count : allData.length = 446 := by native_decide

theorem count_nodoubleneg :
    (allData.filter (·.value == .nodoubleneg)).length = 95 := by native_decide
theorem count_optdoubleneg :
    (allData.filter (·.value == .optdoubleneg)).length = 12 := by native_decide
theorem count_onlywithanotherneg :
    (allData.filter (·.value == .onlywithanotherneg)).length = 35 := by native_decide
theorem count_noSvoneg :
    (allData.filter (·.value == .noSvoneg)).length = 304 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144K
