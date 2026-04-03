import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144S: SOVNeg Order
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144S`.

Chapter 144, 490 languages.
-/

namespace Core.WALS.F144S

/-- WALS 144S values. -/
inductive SovnegOrder where
  | wordNodoubleneg  -- Word&NoDoubleNeg (60 languages)
  | suffixNodoubleneg  -- Suffix&NoDoubleNeg (142 languages)
  | wordOptdoubleneg  -- Word&OptDoubleNeg (7 languages)
  | suffixOptdoubleneg  -- Suffix&OptDoubleNeg (8 languages)
  | wordOnlywithanotherneg  -- Word&OnlyWithAnotherNeg (10 languages)
  | suffixOnlywithanotherneg  -- Suffix&OnlyWithAnotherNeg (32 languages)
  | type1Type2  -- Type 1 / Type 2 (8 languages)
  | type1Type6  -- Type 1 / Type 6 (2 languages)
  | type5Type4  -- Type 5 / Type 4 (2 languages)
  | type5Type6  -- Type 5 / Type 6 (2 languages)
  | nosovneg  -- NoSOVNeg (217 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 144S dataset (490 languages). -/
def allData : List (Datapoint SovnegOrder) :=
  [ { walsCode := "aba", language := "Abau", iso := "aau", value := .wordNodoubleneg }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .suffixNodoubleneg }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .wordNodoubleneg }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .wordOptdoubleneg }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .nosovneg }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .wordNodoubleneg }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .nosovneg }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .nosovneg }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .nosovneg }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .suffixNodoubleneg }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .suffixOnlywithanotherneg }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .suffixNodoubleneg }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .suffixOptdoubleneg }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .suffixOnlywithanotherneg }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .wordNodoubleneg }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .suffixNodoubleneg }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .suffixOnlywithanotherneg }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .suffixOnlywithanotherneg }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .suffixNodoubleneg }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .suffixNodoubleneg }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .nosovneg }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .suffixNodoubleneg }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .nosovneg }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .nosovneg }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .suffixNodoubleneg }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .wordNodoubleneg }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .nosovneg }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .suffixNodoubleneg }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .wordNodoubleneg }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .nosovneg }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .type5Type6 }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .nosovneg }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .nosovneg }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .suffixNodoubleneg }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .suffixNodoubleneg }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .nosovneg }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .nosovneg }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .wordNodoubleneg }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .nosovneg }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .nosovneg }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .nosovneg }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .nosovneg }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .nosovneg }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .nosovneg }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .wordNodoubleneg }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .wordNodoubleneg }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .nosovneg }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .wordNodoubleneg }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .suffixNodoubleneg }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .suffixNodoubleneg }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .nosovneg }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .wordOptdoubleneg }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .nosovneg }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .suffixNodoubleneg }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .wordOptdoubleneg }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .nosovneg }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .nosovneg }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .nosovneg }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .suffixNodoubleneg }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .wordOnlywithanotherneg }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .nosovneg }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .wordNodoubleneg }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .nosovneg }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .suffixOnlywithanotherneg }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .suffixNodoubleneg }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .wordNodoubleneg }
  , { walsCode := "car", language := "Carib", iso := "car", value := .suffixNodoubleneg }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .suffixNodoubleneg }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .suffixNodoubleneg }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .suffixNodoubleneg }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .nosovneg }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .wordNodoubleneg }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .nosovneg }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .nosovneg }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .nosovneg }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .nosovneg }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .suffixNodoubleneg }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .nosovneg }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .wordNodoubleneg }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .suffixNodoubleneg }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .suffixNodoubleneg }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .suffixNodoubleneg }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .suffixNodoubleneg }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .suffixNodoubleneg }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .nosovneg }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .suffixOnlywithanotherneg }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .nosovneg }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .nosovneg }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .nosovneg }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .nosovneg }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .wordNodoubleneg }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .nosovneg }
  , { walsCode := "des", language := "Desano", iso := "des", value := .suffixNodoubleneg }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .suffixNodoubleneg }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .suffixOnlywithanotherneg }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .nosovneg }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .wordNodoubleneg }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .suffixNodoubleneg }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .suffixNodoubleneg }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .nosovneg }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .nosovneg }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .nosovneg }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .nosovneg }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .suffixNodoubleneg }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .wordNodoubleneg }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .type1Type6 }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .nosovneg }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .wordNodoubleneg }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .wordNodoubleneg }
  , { walsCode := "ene", language := "Enets", iso := "", value := .nosovneg }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .suffixNodoubleneg }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .wordNodoubleneg }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .nosovneg }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .suffixOnlywithanotherneg }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .suffixOnlywithanotherneg }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .suffixOnlywithanotherneg }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .nosovneg }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .suffixNodoubleneg }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .suffixNodoubleneg }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .nosovneg }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .suffixNodoubleneg }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .nosovneg }
  , { walsCode := "ger", language := "German", iso := "deu", value := .nosovneg }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .suffixNodoubleneg }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .suffixNodoubleneg }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .suffixNodoubleneg }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nosovneg }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .suffixNodoubleneg }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .suffixNodoubleneg }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .suffixOptdoubleneg }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .nosovneg }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .nosovneg }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .nosovneg }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .nosovneg }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .wordOnlywithanotherneg }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .suffixOnlywithanotherneg }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .nosovneg }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .nosovneg }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .suffixNodoubleneg }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .nosovneg }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .nosovneg }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .nosovneg }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .wordOptdoubleneg }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .nosovneg }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .suffixNodoubleneg }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .suffixNodoubleneg }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .suffixNodoubleneg }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .suffixNodoubleneg }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .wordNodoubleneg }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .nosovneg }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .type1Type2 }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .suffixNodoubleneg }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .nosovneg }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .suffixNodoubleneg }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .suffixNodoubleneg }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .suffixOnlywithanotherneg }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .wordNodoubleneg }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .suffixNodoubleneg }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .suffixNodoubleneg }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .nosovneg }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .suffixNodoubleneg }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .nosovneg }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .suffixNodoubleneg }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .suffixNodoubleneg }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .wordNodoubleneg }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .wordNodoubleneg }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .nosovneg }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .suffixNodoubleneg }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .suffixOptdoubleneg }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .wordNodoubleneg }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .nosovneg }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .suffixNodoubleneg }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .suffixNodoubleneg }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .nosovneg }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .suffixNodoubleneg }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .nosovneg }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .suffixNodoubleneg }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .type1Type2 }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .suffixNodoubleneg }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .type1Type2 }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .wordNodoubleneg }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .wordNodoubleneg }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .suffixOptdoubleneg }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .wordNodoubleneg }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .suffixNodoubleneg }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .nosovneg }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .nosovneg }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .suffixNodoubleneg }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .suffixOnlywithanotherneg }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .suffixNodoubleneg }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .nosovneg }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .nosovneg }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .nosovneg }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .nosovneg }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .wordOptdoubleneg }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .wordNodoubleneg }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .nosovneg }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .suffixOnlywithanotherneg }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .wordNodoubleneg }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .wordOnlywithanotherneg }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .suffixOnlywithanotherneg }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .nosovneg }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .suffixNodoubleneg }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .suffixNodoubleneg }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .suffixNodoubleneg }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .suffixNodoubleneg }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .suffixNodoubleneg }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .type1Type2 }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .suffixOptdoubleneg }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .nosovneg }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .suffixOnlywithanotherneg }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .suffixOnlywithanotherneg }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .suffixNodoubleneg }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .nosovneg }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .suffixNodoubleneg }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .nosovneg }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .suffixNodoubleneg }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .nosovneg }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .suffixNodoubleneg }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .suffixNodoubleneg }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .nosovneg }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .nosovneg }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .suffixNodoubleneg }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .nosovneg }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .suffixNodoubleneg }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .suffixNodoubleneg }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .suffixOptdoubleneg }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .wordOnlywithanotherneg }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .suffixNodoubleneg }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .nosovneg }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .wordNodoubleneg }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .wordNodoubleneg }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .nosovneg }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .wordNodoubleneg }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .type1Type2 }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .nosovneg }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .wordNodoubleneg }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .suffixOnlywithanotherneg }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .suffixNodoubleneg }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .nosovneg }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .nosovneg }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .type5Type4 }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .wordNodoubleneg }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .nosovneg }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .nosovneg }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .suffixNodoubleneg }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .suffixNodoubleneg }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .wordOnlywithanotherneg }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .nosovneg }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .nosovneg }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .suffixNodoubleneg }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .nosovneg }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .suffixNodoubleneg }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .suffixOnlywithanotherneg }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .nosovneg }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .nosovneg }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .nosovneg }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .nosovneg }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .nosovneg }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .wordOnlywithanotherneg }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .wordNodoubleneg }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .nosovneg }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .suffixOnlywithanotherneg }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .nosovneg }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .nosovneg }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .nosovneg }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .nosovneg }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .suffixNodoubleneg }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .suffixNodoubleneg }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .nosovneg }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .wordOnlywithanotherneg }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .nosovneg }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .wordNodoubleneg }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .suffixNodoubleneg }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .wordNodoubleneg }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .nosovneg }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .nosovneg }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .suffixNodoubleneg }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .suffixNodoubleneg }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .suffixNodoubleneg }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .suffixNodoubleneg }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .suffixNodoubleneg }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .wordNodoubleneg }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .nosovneg }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .suffixOnlywithanotherneg }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .type1Type2 }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .nosovneg }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .nosovneg }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .nosovneg }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .wordNodoubleneg }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .suffixNodoubleneg }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .nosovneg }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .nosovneg }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .nosovneg }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .nosovneg }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .wordNodoubleneg }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .nosovneg }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .wordNodoubleneg }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .wordNodoubleneg }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .suffixNodoubleneg }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .nosovneg }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .wordNodoubleneg }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .nosovneg }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .type1Type2 }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .nosovneg }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .nosovneg }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .nosovneg }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .suffixNodoubleneg }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .nosovneg }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .nosovneg }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .nosovneg }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .suffixNodoubleneg }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .nosovneg }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .nosovneg }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .nosovneg }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .type5Type4 }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .suffixNodoubleneg }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .suffixNodoubleneg }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .suffixNodoubleneg }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .nosovneg }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .nosovneg }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .nosovneg }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .nosovneg }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .nosovneg }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .nosovneg }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .suffixNodoubleneg }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .wordNodoubleneg }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .nosovneg }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .suffixNodoubleneg }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .suffixNodoubleneg }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .nosovneg }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .suffixOnlywithanotherneg }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .wordNodoubleneg }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .nosovneg }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .nosovneg }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .nosovneg }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .nosovneg }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .nosovneg }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .type1Type2 }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .nosovneg }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .nosovneg }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .suffixNodoubleneg }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .wordOnlywithanotherneg }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .suffixNodoubleneg }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .suffixOnlywithanotherneg }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .nosovneg }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .suffixNodoubleneg }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .nosovneg }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .suffixNodoubleneg }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .suffixNodoubleneg }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .wordOnlywithanotherneg }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .nosovneg }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .suffixNodoubleneg }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .nosovneg }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .suffixNodoubleneg }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .nosovneg }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .nosovneg }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .nosovneg }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .nosovneg }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .suffixNodoubleneg }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .nosovneg }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .suffixNodoubleneg }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .suffixOptdoubleneg }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .nosovneg }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .suffixNodoubleneg }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .suffixNodoubleneg }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .nosovneg }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .nosovneg }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .wordNodoubleneg }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .nosovneg }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .suffixNodoubleneg }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .nosovneg }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .wordNodoubleneg }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .suffixNodoubleneg }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .nosovneg }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .nosovneg }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .wordNodoubleneg }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .suffixNodoubleneg }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .nosovneg }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .nosovneg }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .nosovneg }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .suffixNodoubleneg }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .wordNodoubleneg }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .suffixNodoubleneg }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .nosovneg }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .nosovneg }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .nosovneg }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .wordNodoubleneg }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .wordNodoubleneg }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .nosovneg }
  , { walsCode := "som", language := "Somali", iso := "som", value := .nosovneg }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .nosovneg }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .nosovneg }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .nosovneg }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .wordOptdoubleneg }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .suffixNodoubleneg }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .type5Type6 }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .nosovneg }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .nosovneg }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .nosovneg }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .nosovneg }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .suffixNodoubleneg }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .nosovneg }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .suffixNodoubleneg }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .suffixNodoubleneg }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .nosovneg }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .nosovneg }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .suffixNodoubleneg }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .suffixOptdoubleneg }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .nosovneg }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .nosovneg }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .suffixNodoubleneg }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .wordNodoubleneg }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .nosovneg }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .suffixOnlywithanotherneg }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .nosovneg }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .wordNodoubleneg }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .nosovneg }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .suffixOnlywithanotherneg }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .nosovneg }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .wordOptdoubleneg }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .suffixOnlywithanotherneg }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .nosovneg }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .nosovneg }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .suffixNodoubleneg }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .nosovneg }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .suffixNodoubleneg }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .wordNodoubleneg }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .suffixNodoubleneg }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .wordNodoubleneg }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .type1Type6 }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .nosovneg }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .suffixNodoubleneg }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .suffixNodoubleneg }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .nosovneg }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .suffixNodoubleneg }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .suffixNodoubleneg }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .suffixOnlywithanotherneg }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .suffixNodoubleneg }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .suffixNodoubleneg }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .wordOnlywithanotherneg }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .suffixOnlywithanotherneg }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .suffixNodoubleneg }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .nosovneg }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .nosovneg }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .wordNodoubleneg }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .nosovneg }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .nosovneg }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .wordNodoubleneg }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .nosovneg }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .nosovneg }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .suffixNodoubleneg }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .suffixNodoubleneg }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .nosovneg }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .nosovneg }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .nosovneg }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .nosovneg }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .suffixNodoubleneg }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .nosovneg }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .wordNodoubleneg }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .suffixNodoubleneg }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .suffixNodoubleneg }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .nosovneg }
  , { walsCode := "was", language := "Washo", iso := "was", value := .suffixNodoubleneg }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .nosovneg }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .suffixOnlywithanotherneg }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .nosovneg }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .nosovneg }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .nosovneg }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .suffixNodoubleneg }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .wordNodoubleneg }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .nosovneg }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .suffixNodoubleneg }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .suffixNodoubleneg }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .suffixOnlywithanotherneg }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .nosovneg }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .suffixNodoubleneg }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .nosovneg }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .nosovneg }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .nosovneg }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .nosovneg }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .nosovneg }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .nosovneg }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .nosovneg }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .nosovneg }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .suffixNodoubleneg }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .nosovneg }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .suffixOnlywithanotherneg }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .nosovneg }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .suffixOnlywithanotherneg }
  ]

-- Count verification
theorem total_count : allData.length = 490 := by native_decide

theorem count_wordNodoubleneg :
    (allData.filter (·.value == .wordNodoubleneg)).length = 60 := by native_decide
theorem count_suffixNodoubleneg :
    (allData.filter (·.value == .suffixNodoubleneg)).length = 142 := by native_decide
theorem count_wordOptdoubleneg :
    (allData.filter (·.value == .wordOptdoubleneg)).length = 7 := by native_decide
theorem count_suffixOptdoubleneg :
    (allData.filter (·.value == .suffixOptdoubleneg)).length = 8 := by native_decide
theorem count_wordOnlywithanotherneg :
    (allData.filter (·.value == .wordOnlywithanotherneg)).length = 10 := by native_decide
theorem count_suffixOnlywithanotherneg :
    (allData.filter (·.value == .suffixOnlywithanotherneg)).length = 32 := by native_decide
theorem count_type1Type2 :
    (allData.filter (·.value == .type1Type2)).length = 8 := by native_decide
theorem count_type1Type6 :
    (allData.filter (·.value == .type1Type6)).length = 2 := by native_decide
theorem count_type5Type4 :
    (allData.filter (·.value == .type5Type4)).length = 2 := by native_decide
theorem count_type5Type6 :
    (allData.filter (·.value == .type5Type6)).length = 2 := by native_decide
theorem count_nosovneg :
    (allData.filter (·.value == .nosovneg)).length = 217 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144S
