/-!
# WALS Feature 144P: NegSOV Order
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144P`.

Chapter 144, 408 languages.
-/

namespace Core.WALS.F144P

/-- WALS 144P values. -/
inductive NegsovOrder where
  | nodoubleneg  -- NoDoubleNeg (18 languages)
  | optdoubleneg  -- OptDoubleNeg (1 languages)
  | onlywithanotherneg  -- OnlyWithAnotherNeg (8 languages)
  | noNegsov  -- No NegSOV (381 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144P datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : NegsovOrder
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144P dataset (408 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "aba", language := "Abau", iso := "aau", value := .noNegsov }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noNegsov }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .noNegsov }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .noNegsov }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noNegsov }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .noNegsov }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noNegsov }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .noNegsov }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noNegsov }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noNegsov }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .noNegsov }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .noNegsov }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .noNegsov }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .noNegsov }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noNegsov }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .noNegsov }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noNegsov }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noNegsov }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noNegsov }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noNegsov }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .noNegsov }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .noNegsov }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .noNegsov }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .noNegsov }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noNegsov }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noNegsov }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noNegsov }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .noNegsov }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .noNegsov }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .onlywithanotherneg }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noNegsov }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .noNegsov }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .noNegsov }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .noNegsov }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noNegsov }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .noNegsov }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noNegsov }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noNegsov }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .noNegsov }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .noNegsov }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .noNegsov }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .noNegsov }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .noNegsov }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .noNegsov }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .noNegsov }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .noNegsov }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .noNegsov }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noNegsov }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noNegsov }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .noNegsov }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noNegsov }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .noNegsov }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .noNegsov }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noNegsov }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noNegsov }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .noNegsov }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .noNegsov }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .noNegsov }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .noNegsov }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .noNegsov }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .noNegsov }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .noNegsov }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .noNegsov }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .nodoubleneg }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .noNegsov }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noNegsov }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .noNegsov }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .noNegsov }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noNegsov }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .noNegsov }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .nodoubleneg }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .onlywithanotherneg }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .nodoubleneg }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noNegsov }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noNegsov }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .noNegsov }
  , { walsCode := "des", language := "Desano", iso := "des", value := .noNegsov }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .noNegsov }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .noNegsov }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noNegsov }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .noNegsov }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .noNegsov }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noNegsov }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .nodoubleneg }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noNegsov }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .noNegsov }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noNegsov }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .noNegsov }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noNegsov }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .noNegsov }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noNegsov }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .noNegsov }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noNegsov }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noNegsov }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .noNegsov }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .noNegsov }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .noNegsov }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .noNegsov }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noNegsov }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noNegsov }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noNegsov }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .noNegsov }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .noNegsov }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .noNegsov }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noNegsov }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noNegsov }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .noNegsov }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .noNegsov }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .noNegsov }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noNegsov }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noNegsov }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .onlywithanotherneg }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noNegsov }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .noNegsov }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .noNegsov }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noNegsov }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .noNegsov }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noNegsov }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .onlywithanotherneg }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .noNegsov }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noNegsov }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .noNegsov }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noNegsov }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .noNegsov }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .noNegsov }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .noNegsov }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .noNegsov }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noNegsov }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .nodoubleneg }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .noNegsov }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noNegsov }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .noNegsov }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .noNegsov }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noNegsov }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noNegsov }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .noNegsov }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .noNegsov }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .noNegsov }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .noNegsov }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .noNegsov }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .noNegsov }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .noNegsov }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .noNegsov }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .noNegsov }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .noNegsov }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noNegsov }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noNegsov }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .noNegsov }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .noNegsov }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .noNegsov }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .noNegsov }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .noNegsov }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .noNegsov }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .noNegsov }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .noNegsov }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noNegsov }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noNegsov }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .noNegsov }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .noNegsov }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noNegsov }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .noNegsov }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .noNegsov }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .noNegsov }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .noNegsov }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .onlywithanotherneg }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .noNegsov }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .noNegsov }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .onlywithanotherneg }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .noNegsov }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noNegsov }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .noNegsov }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .noNegsov }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noNegsov }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noNegsov }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .noNegsov }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .noNegsov }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .noNegsov }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .noNegsov }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noNegsov }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noNegsov }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .noNegsov }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .noNegsov }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .noNegsov }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noNegsov }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .noNegsov }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .noNegsov }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .noNegsov }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noNegsov }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .noNegsov }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .noNegsov }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .noNegsov }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .noNegsov }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .noNegsov }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noNegsov }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .noNegsov }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noNegsov }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noNegsov }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noNegsov }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noNegsov }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .noNegsov }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noNegsov }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .noNegsov }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .noNegsov }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noNegsov }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noNegsov }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .noNegsov }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .noNegsov }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noNegsov }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noNegsov }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .noNegsov }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .noNegsov }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noNegsov }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .noNegsov }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .noNegsov }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .noNegsov }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .noNegsov }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .noNegsov }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .noNegsov }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .noNegsov }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .noNegsov }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .noNegsov }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .noNegsov }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .noNegsov }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .optdoubleneg }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .noNegsov }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .nodoubleneg }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noNegsov }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .noNegsov }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .noNegsov }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .noNegsov }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .noNegsov }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .noNegsov }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .noNegsov }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .noNegsov }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .noNegsov }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .noNegsov }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .noNegsov }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .noNegsov }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .noNegsov }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .noNegsov }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noNegsov }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .noNegsov }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .nodoubleneg }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .noNegsov }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noNegsov }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noNegsov }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .noNegsov }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .noNegsov }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .noNegsov }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .noNegsov }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noNegsov }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noNegsov }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .noNegsov }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .noNegsov }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noNegsov }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noNegsov }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .nodoubleneg }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noNegsov }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .noNegsov }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .noNegsov }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .noNegsov }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .noNegsov }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .noNegsov }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .noNegsov }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .nodoubleneg }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noNegsov }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .noNegsov }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noNegsov }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .noNegsov }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .nodoubleneg }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .noNegsov }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .noNegsov }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .noNegsov }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .noNegsov }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .noNegsov }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .noNegsov }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noNegsov }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .noNegsov }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .nodoubleneg }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .noNegsov }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noNegsov }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .noNegsov }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .noNegsov }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noNegsov }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .nodoubleneg }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noNegsov }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .noNegsov }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .noNegsov }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .noNegsov }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .noNegsov }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .nodoubleneg }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noNegsov }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .noNegsov }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .noNegsov }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .noNegsov }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .nodoubleneg }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .noNegsov }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .noNegsov }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .noNegsov }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noNegsov }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .noNegsov }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .noNegsov }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noNegsov }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .noNegsov }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .noNegsov }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .noNegsov }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noNegsov }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .noNegsov }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .noNegsov }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .noNegsov }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .noNegsov }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .noNegsov }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noNegsov }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .noNegsov }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .noNegsov }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .noNegsov }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .noNegsov }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .noNegsov }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .noNegsov }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noNegsov }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .noNegsov }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noNegsov }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .noNegsov }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .noNegsov }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noNegsov }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .noNegsov }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .noNegsov }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .nodoubleneg }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .noNegsov }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .noNegsov }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .noNegsov }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .noNegsov }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .noNegsov }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .noNegsov }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .noNegsov }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .noNegsov }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noNegsov }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .noNegsov }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .noNegsov }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .noNegsov }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .noNegsov }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .noNegsov }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noNegsov }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .noNegsov }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .noNegsov }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .onlywithanotherneg }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .noNegsov }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noNegsov }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noNegsov }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .noNegsov }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .noNegsov }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noNegsov }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noNegsov }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .noNegsov }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .noNegsov }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .noNegsov }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .noNegsov }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .noNegsov }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .noNegsov }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .noNegsov }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noNegsov }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noNegsov }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .noNegsov }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noNegsov }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .noNegsov }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .noNegsov }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noNegsov }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .noNegsov }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .noNegsov }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .noNegsov }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .noNegsov }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noNegsov }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .noNegsov }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noNegsov }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noNegsov }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .noNegsov }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .noNegsov }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noNegsov }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .noNegsov }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .noNegsov }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .noNegsov }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .noNegsov }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .noNegsov }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .noNegsov }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noNegsov }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noNegsov }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .nodoubleneg }
  , { walsCode := "was", language := "Washo", iso := "was", value := .noNegsov }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .noNegsov }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .noNegsov }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .nodoubleneg }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .noNegsov }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .noNegsov }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .noNegsov }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .noNegsov }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .noNegsov }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .noNegsov }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noNegsov }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .noNegsov }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noNegsov }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noNegsov }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .noNegsov }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .nodoubleneg }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .noNegsov }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .noNegsov }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .onlywithanotherneg }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .noNegsov }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .noNegsov }
  ]

-- Count verification
theorem total_count : allData.length = 408 := by native_decide

theorem count_nodoubleneg :
    (allData.filter (·.value == .nodoubleneg)).length = 18 := by native_decide
theorem count_optdoubleneg :
    (allData.filter (·.value == .optdoubleneg)).length = 1 := by native_decide
theorem count_onlywithanotherneg :
    (allData.filter (·.value == .onlywithanotherneg)).length = 8 := by native_decide
theorem count_noNegsov :
    (allData.filter (·.value == .noNegsov)).length = 381 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144P
