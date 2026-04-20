import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144R: SONegV Order
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144R`.

Chapter 144, 411 languages.
-/

namespace Core.WALS.F144R

/-- WALS 144R values. -/
inductive SonegvOrder where
  /-- Word&NoDoubleNeg (76 languages). -/
  | wordNodoubleneg
  /-- Prefix&NoDoubleNeg (60 languages). -/
  | prefixNodoubleneg
  /-- Word&OptDoubleNeg (1 languages). -/
  | wordOptdoubleneg
  /-- Prefix&OptDoubleNeg (3 languages). -/
  | prefixOptdoubleneg
  /-- Word&OnlyWithAnotherNeg (11 languages). -/
  | wordOnlywithanotherneg
  /-- Prefix&OnlyWithAnotherNeg (21 languages). -/
  | prefixOnlywithanotherneg
  /-- Type 1 / Type 2 (1 languages). -/
  | type1Type2
  /-- No SONegV (238 languages). -/
  | noSonegv
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144R dataset (411 languages). -/
def allData : List (Datapoint SonegvOrder) :=
  [ { walsCode := "aba", language := "Abau", iso := "aau", value := .noSonegv }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .prefixNodoubleneg }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .noSonegv }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .noSonegv }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .wordNodoubleneg }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .wordNodoubleneg }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .wordNodoubleneg }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .noSonegv }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .wordOptdoubleneg }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .prefixOnlywithanotherneg }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .noSonegv }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .noSonegv }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .prefixOptdoubleneg }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .wordOnlywithanotherneg }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noSonegv }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .noSonegv }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noSonegv }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .type1Type2 }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .prefixNodoubleneg }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noSonegv }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noSonegv }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .prefixNodoubleneg }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .noSonegv }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .noSonegv }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .wordNodoubleneg }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .wordOnlywithanotherneg }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .prefixNodoubleneg }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .wordNodoubleneg }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .noSonegv }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .noSonegv }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .noSonegv }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noSonegv }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .prefixNodoubleneg }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .wordNodoubleneg }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .noSonegv }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .wordNodoubleneg }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .noSonegv }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noSonegv }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .prefixNodoubleneg }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .noSonegv }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .noSonegv }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .noSonegv }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .wordNodoubleneg }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .prefixOnlywithanotherneg }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .prefixNodoubleneg }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .noSonegv }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .noSonegv }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .noSonegv }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .prefixOnlywithanotherneg }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .prefixNodoubleneg }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .noSonegv }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .wordNodoubleneg }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .prefixOnlywithanotherneg }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .noSonegv }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noSonegv }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noSonegv }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .noSonegv }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .noSonegv }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .noSonegv }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .prefixNodoubleneg }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .wordNodoubleneg }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .prefixOnlywithanotherneg }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .prefixNodoubleneg }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .wordNodoubleneg }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .noSonegv }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .noSonegv }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .noSonegv }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noSonegv }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .noSonegv }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .noSonegv }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noSonegv }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .noSonegv }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .wordNodoubleneg }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .noSonegv }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .noSonegv }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .wordNodoubleneg }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noSonegv }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .prefixNodoubleneg }
  , { walsCode := "des", language := "Desano", iso := "des", value := .noSonegv }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .noSonegv }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .prefixNodoubleneg }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noSonegv }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .noSonegv }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .noSonegv }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noSonegv }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noSonegv }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .wordNodoubleneg }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .noSonegv }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noSonegv }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .wordOnlywithanotherneg }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .wordNodoubleneg }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .wordNodoubleneg }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noSonegv }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .noSonegv }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .wordOnlywithanotherneg }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .prefixOnlywithanotherneg }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .wordNodoubleneg }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .noSonegv }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .noSonegv }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .wordNodoubleneg }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noSonegv }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .wordNodoubleneg }
  , { walsCode := "ger", language := "German", iso := "deu", value := .wordNodoubleneg }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .noSonegv }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .noSonegv }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .noSonegv }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noSonegv }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noSonegv }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .wordNodoubleneg }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .wordNodoubleneg }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .prefixNodoubleneg }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .wordNodoubleneg }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noSonegv }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noSonegv }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .prefixNodoubleneg }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .wordNodoubleneg }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .noSonegv }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .wordNodoubleneg }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .wordNodoubleneg }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .prefixNodoubleneg }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .wordOnlywithanotherneg }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .prefixNodoubleneg }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noSonegv }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .noSonegv }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noSonegv }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .noSonegv }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .noSonegv }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .wordNodoubleneg }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .noSonegv }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noSonegv }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .noSonegv }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .noSonegv }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noSonegv }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .noSonegv }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .noSonegv }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noSonegv }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noSonegv }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .noSonegv }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .noSonegv }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .noSonegv }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .noSonegv }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .wordNodoubleneg }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .prefixNodoubleneg }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .prefixOnlywithanotherneg }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .noSonegv }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .noSonegv }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .noSonegv }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noSonegv }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noSonegv }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .noSonegv }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .noSonegv }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .noSonegv }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .noSonegv }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .noSonegv }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .noSonegv }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .noSonegv }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .noSonegv }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .wordNodoubleneg }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .prefixNodoubleneg }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .noSonegv }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .prefixOptdoubleneg }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noSonegv }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .prefixNodoubleneg }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .prefixNodoubleneg }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .prefixNodoubleneg }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .wordNodoubleneg }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .wordOnlywithanotherneg }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .noSonegv }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .wordNodoubleneg }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noSonegv }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .noSonegv }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noSonegv }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .wordOnlywithanotherneg }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .noSonegv }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noSonegv }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noSonegv }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .noSonegv }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .noSonegv }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .noSonegv }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .noSonegv }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .prefixOnlywithanotherneg }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .wordNodoubleneg }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .prefixOnlywithanotherneg }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .prefixOnlywithanotherneg }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .noSonegv }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noSonegv }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .noSonegv }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .noSonegv }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .noSonegv }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noSonegv }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .prefixNodoubleneg }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .prefixNodoubleneg }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .noSonegv }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .wordNodoubleneg }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .noSonegv }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noSonegv }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .noSonegv }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .prefixNodoubleneg }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .wordNodoubleneg }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noSonegv }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noSonegv }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .noSonegv }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noSonegv }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .prefixNodoubleneg }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .noSonegv }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .prefixOnlywithanotherneg }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noSonegv }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .wordNodoubleneg }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .prefixNodoubleneg }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noSonegv }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noSonegv }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .prefixNodoubleneg }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .wordNodoubleneg }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noSonegv }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .noSonegv }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .wordNodoubleneg }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .noSonegv }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .wordNodoubleneg }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .noSonegv }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .prefixOnlywithanotherneg }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .noSonegv }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .wordNodoubleneg }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .noSonegv }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .noSonegv }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .wordNodoubleneg }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noSonegv }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .noSonegv }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .noSonegv }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .prefixOnlywithanotherneg }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .wordNodoubleneg }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .noSonegv }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .noSonegv }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .noSonegv }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .noSonegv }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .noSonegv }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .noSonegv }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .noSonegv }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .noSonegv }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .noSonegv }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .noSonegv }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .noSonegv }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .noSonegv }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noSonegv }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .noSonegv }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .noSonegv }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .noSonegv }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .wordNodoubleneg }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .wordNodoubleneg }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .wordNodoubleneg }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .wordNodoubleneg }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .noSonegv }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .prefixNodoubleneg }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noSonegv }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noSonegv }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .prefixNodoubleneg }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .noSonegv }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .wordNodoubleneg }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noSonegv }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .wordNodoubleneg }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .wordNodoubleneg }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .wordNodoubleneg }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .noSonegv }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .prefixNodoubleneg }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .prefixNodoubleneg }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .noSonegv }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .wordNodoubleneg }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noSonegv }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noSonegv }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .noSonegv }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noSonegv }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .noSonegv }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .noSonegv }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .wordNodoubleneg }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .wordNodoubleneg }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .noSonegv }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .noSonegv }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .prefixNodoubleneg }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .noSonegv }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .prefixOnlywithanotherneg }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .noSonegv }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .noSonegv }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .wordNodoubleneg }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .prefixNodoubleneg }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .prefixNodoubleneg }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .noSonegv }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .prefixNodoubleneg }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .wordNodoubleneg }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noSonegv }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .noSonegv }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .prefixNodoubleneg }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .prefixNodoubleneg }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .noSonegv }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .noSonegv }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .wordNodoubleneg }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .wordNodoubleneg }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .noSonegv }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .prefixNodoubleneg }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .wordNodoubleneg }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noSonegv }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .noSonegv }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .noSonegv }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .noSonegv }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noSonegv }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .noSonegv }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .wordNodoubleneg }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noSonegv }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .prefixNodoubleneg }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .noSonegv }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .noSonegv }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .prefixNodoubleneg }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .prefixNodoubleneg }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .noSonegv }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .noSonegv }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .prefixNodoubleneg }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .wordNodoubleneg }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noSonegv }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .noSonegv }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .noSonegv }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .wordNodoubleneg }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .wordNodoubleneg }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .wordNodoubleneg }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .noSonegv }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noSonegv }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .prefixNodoubleneg }
  , { walsCode := "som", language := "Somali", iso := "som", value := .wordNodoubleneg }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .noSonegv }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .prefixNodoubleneg }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noSonegv }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .noSonegv }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .prefixOnlywithanotherneg }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .noSonegv }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .prefixNodoubleneg }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .wordNodoubleneg }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .noSonegv }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .wordNodoubleneg }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .noSonegv }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .noSonegv }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .noSonegv }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .prefixOnlywithanotherneg }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .wordNodoubleneg }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .noSonegv }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .noSonegv }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .prefixNodoubleneg }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .wordOnlywithanotherneg }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .prefixNodoubleneg }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .prefixNodoubleneg }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .prefixOnlywithanotherneg }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .prefixNodoubleneg }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .wordOnlywithanotherneg }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .wordOnlywithanotherneg }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .prefixNodoubleneg }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .wordNodoubleneg }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .noSonegv }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .prefixNodoubleneg }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noSonegv }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noSonegv }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .noSonegv }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .noSonegv }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .prefixOptdoubleneg }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .wordNodoubleneg }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .noSonegv }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .noSonegv }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .noSonegv }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noSonegv }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noSonegv }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .prefixOnlywithanotherneg }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noSonegv }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .noSonegv }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .wordOnlywithanotherneg }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noSonegv }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .prefixNodoubleneg }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .prefixNodoubleneg }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .wordNodoubleneg }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .noSonegv }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .wordNodoubleneg }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .wordNodoubleneg }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noSonegv }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .wordNodoubleneg }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .prefixNodoubleneg }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .noSonegv }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noSonegv }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .noSonegv }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .wordNodoubleneg }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .wordNodoubleneg }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .noSonegv }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .prefixNodoubleneg }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .noSonegv }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noSonegv }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noSonegv }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .noSonegv }
  , { walsCode := "was", language := "Washo", iso := "was", value := .noSonegv }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .wordNodoubleneg }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .prefixOnlywithanotherneg }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noSonegv }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .noSonegv }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .noSonegv }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .prefixNodoubleneg }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .noSonegv }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .noSonegv }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .prefixOnlywithanotherneg }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noSonegv }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .noSonegv }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .wordNodoubleneg }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .prefixNodoubleneg }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .prefixNodoubleneg }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .noSonegv }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .noSonegv }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .prefixNodoubleneg }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noSonegv }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .prefixNodoubleneg }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .prefixOnlywithanotherneg }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144R
