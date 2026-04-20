import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144L: The Position of Negative Morphemes in SOV Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144L`.

Chapter 144, 573 languages.
-/

namespace Core.WALS.F144L

/-- WALS 144L values. -/
inductive PositionOfNegativeMorphemesInSovLanguages where
  /-- NegSOV (10 languages). -/
  | negsov
  /-- SNegOV (11 languages). -/
  | snegov
  /-- SONegV (64 languages). -/
  | sonegv
  /-- SOVNeg (48 languages). -/
  | sovneg
  /-- SO[Neg-V] (49 languages). -/
  | soNegV
  /-- SO[V-Neg] (128 languages). -/
  | soVNeg
  /-- SVO but SNegOV (3 languages). -/
  | svoButSnegov
  /-- SVO but SONegV (1 languages). -/
  | svoButSonegv
  /-- SVO but SOVNeg (1 languages). -/
  | svoButSovneg
  /-- SVO but SO[V-Neg] (1 languages). -/
  | svoButSoVNeg
  /-- SVO but SO[Neg-V] (1 languages). -/
  | svoButSoNegV
  /-- SVO/SOV but SNegOV (1 languages). -/
  | svoSovButSnegov
  /-- SVO/SOV but SOVNeg (1 languages). -/
  | svoSovButSovneg
  /-- Other NegV (57 languages). -/
  | otherNegv
  /-- More than one construction (54 languages). -/
  | moreThanOneConstruction
  /-- ObligDoubleNeg (45 languages). -/
  | obligdoubleneg
  /-- OptDoubleNeg (31 languages). -/
  | optdoubleneg
  /-- SV&OV&NegV (13 languages). -/
  | svOvNegv
  /-- SV&OV&VNeg (8 languages). -/
  | svOvVneg
  /-- SV&OV&[Neg-V] (14 languages). -/
  | svOvNegV
  /-- SV&OV&[V-Neg] (23 languages). -/
  | svOvVNeg
  /-- SV&OV&ImmedPreverbal (5 languages). -/
  | svOvImmedpreverbal
  /-- SV&OV&InitialNeg (4 languages). -/
  | svOvInitialneg
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint PositionOfNegativeMorphemesInSovLanguages) :=
  [ { walsCode := "aar", language := "Aari", iso := "aiw", value := .svOvVNeg }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .sovneg }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .moreThanOneConstruction }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .sovneg }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .optdoubleneg }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .sonegv }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .moreThanOneConstruction }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .sonegv }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .otherNegv }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .sonegv }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .soVNeg }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .obligdoubleneg }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .moreThanOneConstruction }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .svOvNegV }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .optdoubleneg }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .obligdoubleneg }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .obligdoubleneg }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .sovneg }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .soVNeg }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .optdoubleneg }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .obligdoubleneg }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .moreThanOneConstruction }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .soVNeg }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .otherNegv }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .obligdoubleneg }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .soVNeg }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .moreThanOneConstruction }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .moreThanOneConstruction }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .soVNeg }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .sovneg }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .soNegV }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .soVNeg }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .sovneg }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .sonegv }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .obligdoubleneg }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .soNegV }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .moreThanOneConstruction }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .soVNeg }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .soVNeg }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .otherNegv }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .obligdoubleneg }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .moreThanOneConstruction }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .snegov }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .otherNegv }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .soNegV }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .sonegv }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .snegov }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .svOvVNeg }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .sonegv }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .sovneg }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .sovneg }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .soNegV }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .optdoubleneg }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .sovneg }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .soVNeg }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .soVNeg }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .sonegv }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .optdoubleneg }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .svOvNegv }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .soNegV }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .soVNeg }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .moreThanOneConstruction }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .optdoubleneg }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .otherNegv }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .svOvInitialneg }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .otherNegv }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .otherNegv }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .soVNeg }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .obligdoubleneg }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .soNegV }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .sovneg }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .svOvNegV }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .sonegv }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .obligdoubleneg }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .soVNeg }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .sovneg }
  , { walsCode := "car", language := "Carib", iso := "car", value := .soVNeg }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .soVNeg }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .soVNeg }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .soVNeg }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .soNegV }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .moreThanOneConstruction }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .obligdoubleneg }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .soNegV }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .svOvNegV }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .otherNegv }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .sonegv }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .soVNeg }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .optdoubleneg }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .svOvVneg }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .svOvVneg }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .svOvVneg }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .negsov }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .sovneg }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .soVNeg }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .soVNeg }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .soVNeg }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .svOvNegv }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .soVNeg }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .soVNeg }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .moreThanOneConstruction }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .obligdoubleneg }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .moreThanOneConstruction }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .sonegv }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .otherNegv }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .otherNegv }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .sovneg }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .soNegV }
  , { walsCode := "des", language := "Desano", iso := "des", value := .soVNeg }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .soVNeg }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .obligdoubleneg }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .soNegV }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .sovneg }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .soVNeg }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .svOvVNeg }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .soVNeg }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .svoSovButSnegov }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .otherNegv }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .negsov }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .sonegv }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .svOvImmedpreverbal }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .soVNeg }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .svOvNegV }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .moreThanOneConstruction }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .sovneg }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .optdoubleneg }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .moreThanOneConstruction }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .svOvImmedpreverbal }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .moreThanOneConstruction }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .moreThanOneConstruction }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .svOvVNeg }
  , { walsCode := "ene", language := "Enets", iso := "", value := .otherNegv }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .soVNeg }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .sovneg }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .otherNegv }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .obligdoubleneg }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .obligdoubleneg }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .obligdoubleneg }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .sonegv }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .soVNeg }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .soVNeg }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .sonegv }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .soVNeg }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .svOvInitialneg }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .sonegv }
  , { walsCode := "ger", language := "German", iso := "deu", value := .moreThanOneConstruction }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .soVNeg }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .svOvVNeg }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .soVNeg }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .soVNeg }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .svOvImmedpreverbal }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .svoButSnegov }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .soVNeg }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .moreThanOneConstruction }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .optdoubleneg }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .sonegv }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .sonegv }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .soNegV }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .sonegv }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .obligdoubleneg }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .svOvNegV }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .obligdoubleneg }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .soNegV }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .svOvNegv }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .svOvVNeg }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .sonegv }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .soVNeg }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .sonegv }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .svOvVneg }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .sonegv }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .soNegV }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .optdoubleneg }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .soNegV }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .soVNeg }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .soVNeg }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .soVNeg }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .soVNeg }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .sovneg }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .svOvVneg }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .svOvVNeg }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .sonegv }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .moreThanOneConstruction }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .soVNeg }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .svOvNegv }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .optdoubleneg }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .negsov }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .soVNeg }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .soVNeg }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .obligdoubleneg }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .sovneg }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .soVNeg }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .soVNeg }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .otherNegv }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .soVNeg }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .otherNegv }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .soVNeg }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .soVNeg }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .sovneg }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .sovneg }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .moreThanOneConstruction }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .moreThanOneConstruction }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .moreThanOneConstruction }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .optdoubleneg }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .sovneg }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .otherNegv }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .soVNeg }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .soVNeg }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .otherNegv }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .soVNeg }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .otherNegv }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .soVNeg }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .moreThanOneConstruction }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .soVNeg }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .moreThanOneConstruction }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .sovneg }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .sovneg }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .optdoubleneg }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .sovneg }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .soVNeg }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .svOvNegv }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .sonegv }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .soNegV }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .soVNeg }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .optdoubleneg }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .soVNeg }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .soNegV }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .soNegV }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .soNegV }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .sonegv }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .svOvNegv }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .optdoubleneg }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .sovneg }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .sonegv }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .obligdoubleneg }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .sovneg }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .obligdoubleneg }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .obligdoubleneg }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .svoButSnegov }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .soVNeg }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .soVNeg }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .soVNeg }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .soVNeg }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .soVNeg }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .moreThanOneConstruction }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .optdoubleneg }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .svOvVNeg }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .sonegv }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .obligdoubleneg }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .obligdoubleneg }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .soVNeg }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .snegov }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .soVNeg }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .svOvImmedpreverbal }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .otherNegv }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .moreThanOneConstruction }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .soVNeg }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .otherNegv }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .soVNeg }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .soVNeg }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .soNegV }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .soNegV }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .soVNeg }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .sonegv }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .soVNeg }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .moreThanOneConstruction }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .optdoubleneg }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .optdoubleneg }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .svOvNegV }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .moreThanOneConstruction }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .sonegv }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .sovneg }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .sovneg }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .otherNegv }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .sovneg }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .svOvNegv }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .moreThanOneConstruction }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .svoButSoNegV }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .moreThanOneConstruction }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .obligdoubleneg }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .soVNeg }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .moreThanOneConstruction }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .obligdoubleneg }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .sonegv }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .soNegV }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .optdoubleneg }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .moreThanOneConstruction }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .soNegV }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .sonegv }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .soVNeg }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .soVNeg }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .obligdoubleneg }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .svOvImmedpreverbal }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .sonegv }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .otherNegv }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .svOvNegv }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .soVNeg }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .sonegv }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .svOvNegV }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .soVNeg }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .obligdoubleneg }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .snegov }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .sonegv }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .snegov }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .snegov }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .sonegv }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .optdoubleneg }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .sovneg }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .negsov }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .obligdoubleneg }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .otherNegv }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .otherNegv }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .otherNegv }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .sonegv }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .soVNeg }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .soVNeg }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .otherNegv }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .optdoubleneg }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .svoButSnegov }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .svoButSovneg }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .svoButSoVNeg }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .svOvVNeg }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .sovneg }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .svOvNegV }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .otherNegv }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .otherNegv }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .soVNeg }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .svOvVNeg }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .soVNeg }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .soVNeg }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .soVNeg }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .soVNeg }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .sovneg }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .otherNegv }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .obligdoubleneg }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .moreThanOneConstruction }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .otherNegv }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .negsov }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .otherNegv }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .moreThanOneConstruction }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .svOvVNeg }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .svOvVNeg }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .soVNeg }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .sonegv }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .sonegv }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .svoButSonegv }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .sonegv }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .sovneg }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .soNegV }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .svOvVneg }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .moreThanOneConstruction }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .svOvVNeg }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .sovneg }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .soVNeg }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .soNegV }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .sovneg }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .optdoubleneg }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .sonegv }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .moreThanOneConstruction }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .moreThanOneConstruction }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .svOvInitialneg }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .sonegv }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .sonegv }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .soVNeg }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .otherNegv }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .moreThanOneConstruction }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .soNegV }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .soVNeg }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .svOvNegv }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .sonegv }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .svOvVNeg }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .moreThanOneConstruction }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .svOvInitialneg }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .otherNegv }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .svOvVNeg }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .optdoubleneg }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .soVNeg }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .soVNeg }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .soVNeg }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .svoSovButSovneg }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .otherNegv }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .otherNegv }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .sonegv }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .svOvVNeg }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .otherNegv }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .sonegv }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .soVNeg }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .sovneg }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .soNegV }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .soVNeg }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .svOvNegV }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .moreThanOneConstruction }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .obligdoubleneg }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .obligdoubleneg }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .sovneg }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .otherNegv }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .negsov }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .sonegv }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .soNegV }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .soNegV }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .svOvVNeg }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .moreThanOneConstruction }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .soNegV }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .svOvVNeg }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .moreThanOneConstruction }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .soVNeg }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .obligdoubleneg }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .moreThanOneConstruction }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .soVNeg }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .obligdoubleneg }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .moreThanOneConstruction }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .moreThanOneConstruction }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .otherNegv }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .soVNeg }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .soVNeg }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .svOvVneg }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .obligdoubleneg }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .moreThanOneConstruction }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .moreThanOneConstruction }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .otherNegv }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .soVNeg }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .soNegV }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .otherNegv }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .sonegv }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .svOvNegV }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .negsov }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .soVNeg }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .otherNegv }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .soVNeg }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .optdoubleneg }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .snegov }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .soVNeg }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .soVNeg }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .otherNegv }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .sonegv }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .sovneg }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .otherNegv }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .moreThanOneConstruction }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .otherNegv }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .svOvVNeg }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .sovneg }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .soVNeg }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .soNegV }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .soNegV }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .sovneg }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .soVNeg }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .otherNegv }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .soNegV }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .sonegv }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .soVNeg }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .sovneg }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .soVNeg }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .sonegv }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .svOvVneg }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .sonegv }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .sonegv }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .svOvVNeg }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .sovneg }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .sovneg }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .soNegV }
  , { walsCode := "som", language := "Somali", iso := "som", value := .sonegv }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .snegov }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .soNegV }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .svOvNegv }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .otherNegv }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .optdoubleneg }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .soVNeg }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .obligdoubleneg }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .optdoubleneg }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .negsov }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .soNegV }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .otherNegv }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .sonegv }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .soVNeg }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .sonegv }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .soVNeg }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .obligdoubleneg }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .soVNeg }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .otherNegv }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .otherNegv }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .soVNeg }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .optdoubleneg }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .sonegv }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .otherNegv }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .soVNeg }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .svOvNegv }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .sovneg }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .soNegV }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .obligdoubleneg }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .soNegV }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .moreThanOneConstruction }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .svOvNegV }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .soNegV }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .obligdoubleneg }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .soNegV }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .optdoubleneg }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .obligdoubleneg }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .moreThanOneConstruction }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .sonegv }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .soVNeg }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .soNegV }
  ]

private def allData_1 : List (Datapoint PositionOfNegativeMorphemesInSovLanguages) :=
  [ { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .moreThanOneConstruction }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .moreThanOneConstruction }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .soVNeg }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .sovneg }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .optdoubleneg }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .sonegv }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .soVNeg }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .svOvVNeg }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .soVNeg }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .snegov }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .soVNeg }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .soVNeg }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .obligdoubleneg }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .soVNeg }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .soVNeg }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .obligdoubleneg }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .optdoubleneg }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .moreThanOneConstruction }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .soNegV }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .sonegv }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .sovneg }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .sonegv }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .sonegv }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .svOvNegv }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .sovneg }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .sonegv }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .soNegV }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .soVNeg }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .soVNeg }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .snegov }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .sonegv }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .otherNegv }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .sonegv }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .soVNeg }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .soNegV }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .sovneg }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .soVNeg }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .soVNeg }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .svOvVNeg }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .negsov }
  , { walsCode := "was", language := "Washo", iso := "was", value := .soVNeg }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .sonegv }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .svOvNegV }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .svOvVNeg }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .obligdoubleneg }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .otherNegv }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .moreThanOneConstruction }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .otherNegv }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .optdoubleneg }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .soVNeg }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .sovneg }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .soNegV }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .soVNeg }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .soVNeg }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .svOvNegV }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .obligdoubleneg }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .snegov }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .soVNeg }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .otherNegv }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .otherNegv }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .otherNegv }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .sonegv }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .svOvNegV }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .otherNegv }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .soNegV }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .soNegV }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .negsov }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .soVNeg }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .soNegV }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .obligdoubleneg }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .soNegV }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .obligdoubleneg }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .svOvNegv }
  ]

/-- Complete WALS 144L dataset (573 languages). -/
def allData : List (Datapoint PositionOfNegativeMorphemesInSovLanguages) := allData_0 ++ allData_1

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144L
