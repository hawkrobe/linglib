import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144Q: SNegOV Order
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144Q`.

Chapter 144, 408 languages.
-/

namespace Core.WALS.F144Q

/-- WALS 144Q values. -/
inductive SnegovOrder where
  | nodoubleneg  -- NoDoubleNeg (25 languages)
  | optdoubleneg  -- OptDoubleNeg (4 languages)
  | onlywithanotherneg  -- OnlyWithAnotherNeg (11 languages)
  | noSnegov  -- No SNegOV (368 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 144Q dataset (408 languages). -/
def allData : List (Datapoint SnegovOrder) :=
  [ { walsCode := "aba", language := "Abau", iso := "aau", value := .noSnegov }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noSnegov }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .noSnegov }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .onlywithanotherneg }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noSnegov }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .noSnegov }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noSnegov }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .noSnegov }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .optdoubleneg }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noSnegov }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .noSnegov }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .noSnegov }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .noSnegov }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .onlywithanotherneg }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noSnegov }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .noSnegov }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noSnegov }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noSnegov }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noSnegov }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noSnegov }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .noSnegov }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .noSnegov }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .noSnegov }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .noSnegov }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noSnegov }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noSnegov }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .nodoubleneg }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .noSnegov }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .noSnegov }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .onlywithanotherneg }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .nodoubleneg }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .noSnegov }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .noSnegov }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .nodoubleneg }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noSnegov }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .noSnegov }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noSnegov }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noSnegov }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .noSnegov }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .noSnegov }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .noSnegov }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .noSnegov }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .noSnegov }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .noSnegov }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .noSnegov }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .onlywithanotherneg }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .noSnegov }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noSnegov }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noSnegov }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .noSnegov }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noSnegov }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .noSnegov }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .noSnegov }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noSnegov }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noSnegov }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .noSnegov }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .noSnegov }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .noSnegov }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .noSnegov }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .noSnegov }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .noSnegov }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .noSnegov }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .noSnegov }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .noSnegov }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .noSnegov }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .noSnegov }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .noSnegov }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .noSnegov }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noSnegov }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .noSnegov }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .nodoubleneg }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .noSnegov }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .nodoubleneg }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noSnegov }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noSnegov }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .noSnegov }
  , { walsCode := "des", language := "Desano", iso := "des", value := .noSnegov }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .noSnegov }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .noSnegov }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noSnegov }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .noSnegov }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .noSnegov }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .nodoubleneg }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noSnegov }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .noSnegov }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .noSnegov }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noSnegov }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .noSnegov }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noSnegov }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .noSnegov }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noSnegov }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .noSnegov }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noSnegov }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noSnegov }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .noSnegov }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .noSnegov }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .noSnegov }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .noSnegov }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noSnegov }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noSnegov }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noSnegov }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .noSnegov }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .noSnegov }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .noSnegov }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nodoubleneg }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noSnegov }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .noSnegov }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .noSnegov }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .noSnegov }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noSnegov }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .onlywithanotherneg }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noSnegov }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noSnegov }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .noSnegov }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .noSnegov }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noSnegov }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .noSnegov }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noSnegov }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .onlywithanotherneg }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .noSnegov }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noSnegov }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .noSnegov }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noSnegov }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .noSnegov }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .noSnegov }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .noSnegov }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .noSnegov }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noSnegov }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .noSnegov }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .noSnegov }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noSnegov }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .noSnegov }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .noSnegov }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noSnegov }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noSnegov }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .noSnegov }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .noSnegov }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .noSnegov }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .noSnegov }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .nodoubleneg }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .noSnegov }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .noSnegov }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .noSnegov }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .noSnegov }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .noSnegov }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noSnegov }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noSnegov }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .noSnegov }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .noSnegov }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .noSnegov }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .noSnegov }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .noSnegov }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .noSnegov }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .noSnegov }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .noSnegov }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noSnegov }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noSnegov }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .noSnegov }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .noSnegov }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noSnegov }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .noSnegov }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .noSnegov }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .noSnegov }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .noSnegov }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .onlywithanotherneg }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .noSnegov }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .noSnegov }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noSnegov }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .noSnegov }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .onlywithanotherneg }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .onlywithanotherneg }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .nodoubleneg }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noSnegov }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noSnegov }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .noSnegov }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .noSnegov }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .noSnegov }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .noSnegov }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noSnegov }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noSnegov }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .noSnegov }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .noSnegov }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .noSnegov }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .nodoubleneg }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .noSnegov }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .noSnegov }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .noSnegov }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noSnegov }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .noSnegov }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .noSnegov }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .noSnegov }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .noSnegov }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .noSnegov }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noSnegov }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .optdoubleneg }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noSnegov }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noSnegov }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noSnegov }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noSnegov }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .noSnegov }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noSnegov }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .noSnegov }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .nodoubleneg }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noSnegov }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noSnegov }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .noSnegov }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .noSnegov }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noSnegov }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noSnegov }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .noSnegov }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .noSnegov }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noSnegov }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .noSnegov }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .noSnegov }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .noSnegov }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .noSnegov }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .noSnegov }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .noSnegov }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .nodoubleneg }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .noSnegov }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .nodoubleneg }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .nodoubleneg }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .noSnegov }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noSnegov }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .noSnegov }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .noSnegov }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noSnegov }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .noSnegov }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .noSnegov }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .noSnegov }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .optdoubleneg }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .nodoubleneg }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .noSnegov }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .noSnegov }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .noSnegov }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .noSnegov }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .noSnegov }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .noSnegov }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .noSnegov }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .noSnegov }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noSnegov }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .noSnegov }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .noSnegov }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .noSnegov }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noSnegov }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noSnegov }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .noSnegov }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .noSnegov }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .noSnegov }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .noSnegov }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noSnegov }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noSnegov }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .noSnegov }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .noSnegov }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noSnegov }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noSnegov }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .nodoubleneg }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noSnegov }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .noSnegov }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .noSnegov }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .noSnegov }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .noSnegov }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .noSnegov }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .noSnegov }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .nodoubleneg }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noSnegov }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .noSnegov }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noSnegov }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .noSnegov }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .noSnegov }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .noSnegov }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .noSnegov }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .noSnegov }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .noSnegov }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .noSnegov }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .noSnegov }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noSnegov }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .noSnegov }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .noSnegov }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .noSnegov }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noSnegov }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .noSnegov }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .noSnegov }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noSnegov }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .nodoubleneg }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noSnegov }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .noSnegov }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .noSnegov }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .noSnegov }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .noSnegov }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .nodoubleneg }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .nodoubleneg }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .noSnegov }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .noSnegov }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .noSnegov }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noSnegov }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .noSnegov }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .noSnegov }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .nodoubleneg }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noSnegov }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .noSnegov }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .noSnegov }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noSnegov }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .noSnegov }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .noSnegov }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .noSnegov }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noSnegov }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .noSnegov }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .noSnegov }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .noSnegov }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .noSnegov }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .noSnegov }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noSnegov }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .noSnegov }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .noSnegov }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .noSnegov }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .noSnegov }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .noSnegov }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .noSnegov }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noSnegov }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .noSnegov }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noSnegov }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .nodoubleneg }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .noSnegov }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .onlywithanotherneg }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .noSnegov }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .noSnegov }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .noSnegov }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .noSnegov }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .noSnegov }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .noSnegov }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .noSnegov }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .noSnegov }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .noSnegov }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .noSnegov }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .noSnegov }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noSnegov }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .noSnegov }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .noSnegov }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .noSnegov }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .noSnegov }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .noSnegov }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noSnegov }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .noSnegov }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .noSnegov }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .onlywithanotherneg }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .noSnegov }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noSnegov }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noSnegov }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .noSnegov }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .noSnegov }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noSnegov }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noSnegov }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .noSnegov }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .noSnegov }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .noSnegov }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .noSnegov }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .noSnegov }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .noSnegov }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .nodoubleneg }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noSnegov }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noSnegov }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .noSnegov }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noSnegov }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .noSnegov }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .noSnegov }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .optdoubleneg }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .noSnegov }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .noSnegov }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .noSnegov }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .noSnegov }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noSnegov }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .noSnegov }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noSnegov }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noSnegov }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .noSnegov }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .noSnegov }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noSnegov }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .nodoubleneg }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .noSnegov }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .noSnegov }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .noSnegov }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .noSnegov }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .noSnegov }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noSnegov }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noSnegov }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .noSnegov }
  , { walsCode := "was", language := "Washo", iso := "was", value := .noSnegov }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .noSnegov }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .noSnegov }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noSnegov }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .noSnegov }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .noSnegov }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .noSnegov }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .noSnegov }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .noSnegov }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .noSnegov }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .nodoubleneg }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .noSnegov }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noSnegov }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noSnegov }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .noSnegov }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .noSnegov }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .noSnegov }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .noSnegov }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noSnegov }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .noSnegov }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .noSnegov }
  ]

-- Count verification
theorem total_count : allData.length = 408 := by native_decide

theorem count_nodoubleneg :
    (allData.filter (·.value == .nodoubleneg)).length = 25 := by native_decide
theorem count_optdoubleneg :
    (allData.filter (·.value == .optdoubleneg)).length = 4 := by native_decide
theorem count_onlywithanotherneg :
    (allData.filter (·.value == .onlywithanotherneg)).length = 11 := by native_decide
theorem count_noSnegov :
    (allData.filter (·.value == .noSnegov)).length = 368 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144Q
