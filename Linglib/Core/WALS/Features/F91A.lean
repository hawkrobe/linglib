import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 91A: Order of Degree Word and Adjective
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 91A`.

Chapter 91, 481 languages.
-/

namespace Core.WALS.F91A

/-- WALS 91A values. -/
inductive OrderOfDegreeWordAndAdjective where
  | degreeWordAdjective  -- Degree word-Adjective (227 languages)
  | adjectiveDegreeWord  -- Adjective-Degree word (192 languages)
  | noDominantOrder  -- No dominant order (62 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 91A dataset (481 languages). -/
def allData : List (Datapoint OrderOfDegreeWordAndAdjective) :=
  [ { walsCode := "abi", language := "Abipón", iso := "axb", value := .degreeWordAdjective }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .degreeWordAdjective }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .adjectiveDegreeWord }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noDominantOrder }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .noDominantOrder }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .adjectiveDegreeWord }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .noDominantOrder }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .adjectiveDegreeWord }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .noDominantOrder }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .adjectiveDegreeWord }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .degreeWordAdjective }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .adjectiveDegreeWord }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .adjectiveDegreeWord }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .adjectiveDegreeWord }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .adjectiveDegreeWord }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .adjectiveDegreeWord }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .degreeWordAdjective }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .degreeWordAdjective }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .adjectiveDegreeWord }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .degreeWordAdjective }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .adjectiveDegreeWord }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .degreeWordAdjective }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .noDominantOrder }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .degreeWordAdjective }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .adjectiveDegreeWord }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .adjectiveDegreeWord }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noDominantOrder }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .degreeWordAdjective }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .degreeWordAdjective }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .adjectiveDegreeWord }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .adjectiveDegreeWord }
  , { walsCode := "au", language := "Au", iso := "avt", value := .adjectiveDegreeWord }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .degreeWordAdjective }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .degreeWordAdjective }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .degreeWordAdjective }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .adjectiveDegreeWord }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .degreeWordAdjective }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .degreeWordAdjective }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .adjectiveDegreeWord }
  , { walsCode := "bdw", language := "Baham", iso := "bdw", value := .adjectiveDegreeWord }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .noDominantOrder }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .degreeWordAdjective }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .adjectiveDegreeWord }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .adjectiveDegreeWord }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .adjectiveDegreeWord }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .degreeWordAdjective }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .degreeWordAdjective }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .degreeWordAdjective }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .degreeWordAdjective }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .adjectiveDegreeWord }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .adjectiveDegreeWord }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .adjectiveDegreeWord }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .degreeWordAdjective }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .adjectiveDegreeWord }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .adjectiveDegreeWord }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .noDominantOrder }
  , { walsCode := "boq", language := "Bokar", iso := "", value := .adjectiveDegreeWord }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .noDominantOrder }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noDominantOrder }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .adjectiveDegreeWord }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .degreeWordAdjective }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .degreeWordAdjective }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .degreeWordAdjective }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .adjectiveDegreeWord }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .degreeWordAdjective }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .degreeWordAdjective }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .adjectiveDegreeWord }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .degreeWordAdjective }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .adjectiveDegreeWord }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .degreeWordAdjective }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .adjectiveDegreeWord }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .degreeWordAdjective }
  , { walsCode := "car", language := "Carib", iso := "car", value := .adjectiveDegreeWord }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .noDominantOrder }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .degreeWordAdjective }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .noDominantOrder }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .adjectiveDegreeWord }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .adjectiveDegreeWord }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .degreeWordAdjective }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .adjectiveDegreeWord }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .degreeWordAdjective }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .degreeWordAdjective }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .adjectiveDegreeWord }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .adjectiveDegreeWord }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .noDominantOrder }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .degreeWordAdjective }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .degreeWordAdjective }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .noDominantOrder }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .adjectiveDegreeWord }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .adjectiveDegreeWord }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .degreeWordAdjective }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .degreeWordAdjective }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noDominantOrder }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .degreeWordAdjective }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .degreeWordAdjective }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .degreeWordAdjective }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .degreeWordAdjective }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .adjectiveDegreeWord }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noDominantOrder }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .degreeWordAdjective }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .adjectiveDegreeWord }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .adjectiveDegreeWord }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .degreeWordAdjective }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .degreeWordAdjective }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .adjectiveDegreeWord }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .adjectiveDegreeWord }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .noDominantOrder }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .degreeWordAdjective }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .adjectiveDegreeWord }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .adjectiveDegreeWord }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .adjectiveDegreeWord }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .degreeWordAdjective }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .adjectiveDegreeWord }
  , { walsCode := "eng", language := "English", iso := "eng", value := .degreeWordAdjective }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .adjectiveDegreeWord }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .degreeWordAdjective }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .degreeWordAdjective }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noDominantOrder }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .degreeWordAdjective }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .degreeWordAdjective }
  , { walsCode := "fre", language := "French", iso := "fra", value := .degreeWordAdjective }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .adjectiveDegreeWord }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .adjectiveDegreeWord }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .degreeWordAdjective }
  , { walsCode := "ger", language := "German", iso := "deu", value := .degreeWordAdjective }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .noDominantOrder }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .adjectiveDegreeWord }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .degreeWordAdjective }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .adjectiveDegreeWord }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .degreeWordAdjective }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .degreeWordAdjective }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .degreeWordAdjective }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .adjectiveDegreeWord }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .degreeWordAdjective }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .adjectiveDegreeWord }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .degreeWordAdjective }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .degreeWordAdjective }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .degreeWordAdjective }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .adjectiveDegreeWord }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .noDominantOrder }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .adjectiveDegreeWord }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .degreeWordAdjective }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .degreeWordAdjective }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .noDominantOrder }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .adjectiveDegreeWord }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .adjectiveDegreeWord }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .degreeWordAdjective }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .noDominantOrder }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .noDominantOrder }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .degreeWordAdjective }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .adjectiveDegreeWord }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .adjectiveDegreeWord }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .adjectiveDegreeWord }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .degreeWordAdjective }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .degreeWordAdjective }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .degreeWordAdjective }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .degreeWordAdjective }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .degreeWordAdjective }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .adjectiveDegreeWord }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .degreeWordAdjective }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .adjectiveDegreeWord }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .adjectiveDegreeWord }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noDominantOrder }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .degreeWordAdjective }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .degreeWordAdjective }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .noDominantOrder }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noDominantOrder }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .degreeWordAdjective }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .degreeWordAdjective }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .degreeWordAdjective }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .degreeWordAdjective }
  , { walsCode := "jad", language := "Jad", iso := "jda", value := .adjectiveDegreeWord }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .degreeWordAdjective }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .adjectiveDegreeWord }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .degreeWordAdjective }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .degreeWordAdjective }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .degreeWordAdjective }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .degreeWordAdjective }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .adjectiveDegreeWord }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .degreeWordAdjective }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .adjectiveDegreeWord }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .adjectiveDegreeWord }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .adjectiveDegreeWord }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .degreeWordAdjective }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .adjectiveDegreeWord }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .degreeWordAdjective }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .degreeWordAdjective }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .adjectiveDegreeWord }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .degreeWordAdjective }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .degreeWordAdjective }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .adjectiveDegreeWord }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .adjectiveDegreeWord }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .noDominantOrder }
  , { walsCode := "ktu", language := "Katu", iso := "", value := .noDominantOrder }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .adjectiveDegreeWord }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .adjectiveDegreeWord }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .degreeWordAdjective }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .degreeWordAdjective }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .degreeWordAdjective }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .degreeWordAdjective }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .degreeWordAdjective }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .adjectiveDegreeWord }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .adjectiveDegreeWord }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noDominantOrder }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .adjectiveDegreeWord }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .degreeWordAdjective }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .adjectiveDegreeWord }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .adjectiveDegreeWord }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noDominantOrder }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .degreeWordAdjective }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .adjectiveDegreeWord }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .adjectiveDegreeWord }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .degreeWordAdjective }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noDominantOrder }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .degreeWordAdjective }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .degreeWordAdjective }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .degreeWordAdjective }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .adjectiveDegreeWord }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .degreeWordAdjective }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .adjectiveDegreeWord }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noDominantOrder }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .degreeWordAdjective }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .degreeWordAdjective }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .degreeWordAdjective }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .degreeWordAdjective }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .noDominantOrder }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .adjectiveDegreeWord }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .adjectiveDegreeWord }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .noDominantOrder }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .adjectiveDegreeWord }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .adjectiveDegreeWord }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .degreeWordAdjective }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .adjectiveDegreeWord }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noDominantOrder }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .degreeWordAdjective }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .adjectiveDegreeWord }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .adjectiveDegreeWord }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .degreeWordAdjective }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .adjectiveDegreeWord }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .adjectiveDegreeWord }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .degreeWordAdjective }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .degreeWordAdjective }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .degreeWordAdjective }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .degreeWordAdjective }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .adjectiveDegreeWord }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .noDominantOrder }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .adjectiveDegreeWord }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .degreeWordAdjective }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .adjectiveDegreeWord }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .noDominantOrder }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .adjectiveDegreeWord }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .adjectiveDegreeWord }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .degreeWordAdjective }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .adjectiveDegreeWord }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .degreeWordAdjective }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .adjectiveDegreeWord }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .degreeWordAdjective }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .degreeWordAdjective }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .degreeWordAdjective }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .adjectiveDegreeWord }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .degreeWordAdjective }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .degreeWordAdjective }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .adjectiveDegreeWord }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .degreeWordAdjective }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .degreeWordAdjective }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .noDominantOrder }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .degreeWordAdjective }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .adjectiveDegreeWord }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .degreeWordAdjective }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .adjectiveDegreeWord }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .degreeWordAdjective }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .adjectiveDegreeWord }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .degreeWordAdjective }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .degreeWordAdjective }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .adjectiveDegreeWord }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .adjectiveDegreeWord }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .adjectiveDegreeWord }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .degreeWordAdjective }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .adjectiveDegreeWord }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .adjectiveDegreeWord }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .adjectiveDegreeWord }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .degreeWordAdjective }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .degreeWordAdjective }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .degreeWordAdjective }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noDominantOrder }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .adjectiveDegreeWord }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .adjectiveDegreeWord }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .adjectiveDegreeWord }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .adjectiveDegreeWord }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .degreeWordAdjective }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .adjectiveDegreeWord }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .degreeWordAdjective }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .adjectiveDegreeWord }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noDominantOrder }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .noDominantOrder }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .adjectiveDegreeWord }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .degreeWordAdjective }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .adjectiveDegreeWord }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .adjectiveDegreeWord }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .degreeWordAdjective }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .degreeWordAdjective }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .degreeWordAdjective }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .adjectiveDegreeWord }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .degreeWordAdjective }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .adjectiveDegreeWord }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .adjectiveDegreeWord }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .adjectiveDegreeWord }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .degreeWordAdjective }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .adjectiveDegreeWord }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noDominantOrder }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .adjectiveDegreeWord }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .degreeWordAdjective }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .degreeWordAdjective }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .degreeWordAdjective }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .adjectiveDegreeWord }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noDominantOrder }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .adjectiveDegreeWord }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .adjectiveDegreeWord }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .degreeWordAdjective }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .adjectiveDegreeWord }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .adjectiveDegreeWord }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .degreeWordAdjective }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .adjectiveDegreeWord }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .adjectiveDegreeWord }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .adjectiveDegreeWord }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .degreeWordAdjective }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .degreeWordAdjective }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .adjectiveDegreeWord }
  , { walsCode := "nus", language := "Nusu", iso := "nuf", value := .degreeWordAdjective }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .adjectiveDegreeWord }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .degreeWordAdjective }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .noDominantOrder }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .degreeWordAdjective }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .adjectiveDegreeWord }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .degreeWordAdjective }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .adjectiveDegreeWord }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .degreeWordAdjective }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .adjectiveDegreeWord }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .degreeWordAdjective }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .degreeWordAdjective }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .degreeWordAdjective }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .adjectiveDegreeWord }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .degreeWordAdjective }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .adjectiveDegreeWord }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .degreeWordAdjective }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .degreeWordAdjective }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .degreeWordAdjective }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .degreeWordAdjective }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .degreeWordAdjective }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .degreeWordAdjective }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .degreeWordAdjective }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .adjectiveDegreeWord }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .adjectiveDegreeWord }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noDominantOrder }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .adjectiveDegreeWord }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .degreeWordAdjective }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .degreeWordAdjective }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .degreeWordAdjective }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .degreeWordAdjective }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .degreeWordAdjective }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .noDominantOrder }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .degreeWordAdjective }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .degreeWordAdjective }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .degreeWordAdjective }
  , { walsCode := "rji", language := "Raji", iso := "rji", value := .noDominantOrder }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .adjectiveDegreeWord }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .degreeWordAdjective }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .degreeWordAdjective }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .noDominantOrder }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .degreeWordAdjective }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .adjectiveDegreeWord }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .degreeWordAdjective }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .degreeWordAdjective }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noDominantOrder }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .adjectiveDegreeWord }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .adjectiveDegreeWord }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noDominantOrder }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .degreeWordAdjective }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .adjectiveDegreeWord }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .adjectiveDegreeWord }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .degreeWordAdjective }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .noDominantOrder }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .adjectiveDegreeWord }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .adjectiveDegreeWord }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .adjectiveDegreeWord }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .noDominantOrder }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .adjectiveDegreeWord }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .degreeWordAdjective }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .degreeWordAdjective }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .degreeWordAdjective }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .degreeWordAdjective }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .adjectiveDegreeWord }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .adjectiveDegreeWord }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .degreeWordAdjective }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .noDominantOrder }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .adjectiveDegreeWord }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .adjectiveDegreeWord }
  , { walsCode := "som", language := "Somali", iso := "som", value := .degreeWordAdjective }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .adjectiveDegreeWord }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .degreeWordAdjective }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .degreeWordAdjective }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .degreeWordAdjective }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .adjectiveDegreeWord }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .adjectiveDegreeWord }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noDominantOrder }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .degreeWordAdjective }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noDominantOrder }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .adjectiveDegreeWord }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .adjectiveDegreeWord }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .degreeWordAdjective }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .degreeWordAdjective }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .degreeWordAdjective }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .degreeWordAdjective }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .adjectiveDegreeWord }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .degreeWordAdjective }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .adjectiveDegreeWord }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .degreeWordAdjective }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .degreeWordAdjective }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .degreeWordAdjective }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .degreeWordAdjective }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .degreeWordAdjective }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .adjectiveDegreeWord }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .adjectiveDegreeWord }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .adjectiveDegreeWord }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .degreeWordAdjective }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .adjectiveDegreeWord }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .adjectiveDegreeWord }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .adjectiveDegreeWord }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .adjectiveDegreeWord }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .adjectiveDegreeWord }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .degreeWordAdjective }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .degreeWordAdjective }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .degreeWordAdjective }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .degreeWordAdjective }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .degreeWordAdjective }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noDominantOrder }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .degreeWordAdjective }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .noDominantOrder }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .degreeWordAdjective }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .degreeWordAdjective }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .degreeWordAdjective }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .adjectiveDegreeWord }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .degreeWordAdjective }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .degreeWordAdjective }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noDominantOrder }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noDominantOrder }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .degreeWordAdjective }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .degreeWordAdjective }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .adjectiveDegreeWord }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .adjectiveDegreeWord }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .degreeWordAdjective }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .adjectiveDegreeWord }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .degreeWordAdjective }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .degreeWordAdjective }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .degreeWordAdjective }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .degreeWordAdjective }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .adjectiveDegreeWord }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .adjectiveDegreeWord }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .degreeWordAdjective }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .adjectiveDegreeWord }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noDominantOrder }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .adjectiveDegreeWord }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .degreeWordAdjective }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .noDominantOrder }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .degreeWordAdjective }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .adjectiveDegreeWord }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .adjectiveDegreeWord }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .adjectiveDegreeWord }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .adjectiveDegreeWord }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .adjectiveDegreeWord }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .degreeWordAdjective }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .degreeWordAdjective }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .degreeWordAdjective }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .adjectiveDegreeWord }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .adjectiveDegreeWord }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .degreeWordAdjective }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .degreeWordAdjective }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .degreeWordAdjective }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .degreeWordAdjective }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .degreeWordAdjective }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .noDominantOrder }
  ]

-- Count verification
theorem total_count : allData.length = 481 := by native_decide

theorem count_degreeWordAdjective :
    (allData.filter (·.value == .degreeWordAdjective)).length = 227 := by native_decide
theorem count_adjectiveDegreeWord :
    (allData.filter (·.value == .adjectiveDegreeWord)).length = 192 := by native_decide
theorem count_noDominantOrder :
    (allData.filter (·.value == .noDominantOrder)).length = 62 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F91A
