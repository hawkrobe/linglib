import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 93A: Position of Interrogative Phrases in Content Questions
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 93A`.

Chapter 93, 902 languages.
-/

namespace Core.WALS.F93A

/-- WALS 93A values. -/
inductive PositionOfInterrogativePhrasesInContentQuestions where
  | initialInterrogativePhrase  -- Initial interrogative phrase (264 languages)
  | notInitialInterrogativePhrase  -- Not initial interrogative phrase (615 languages)
  | mixed  -- Mixed (23 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint PositionOfInterrogativePhrasesInContentQuestions) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .notInitialInterrogativePhrase }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .notInitialInterrogativePhrase }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .notInitialInterrogativePhrase }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .initialInterrogativePhrase }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .notInitialInterrogativePhrase }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .notInitialInterrogativePhrase }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .notInitialInterrogativePhrase }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .mixed }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .initialInterrogativePhrase }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .notInitialInterrogativePhrase }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .notInitialInterrogativePhrase }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .notInitialInterrogativePhrase }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .notInitialInterrogativePhrase }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .notInitialInterrogativePhrase }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .notInitialInterrogativePhrase }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .initialInterrogativePhrase }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .initialInterrogativePhrase }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .notInitialInterrogativePhrase }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .notInitialInterrogativePhrase }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .notInitialInterrogativePhrase }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .notInitialInterrogativePhrase }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .notInitialInterrogativePhrase }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .notInitialInterrogativePhrase }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .notInitialInterrogativePhrase }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .notInitialInterrogativePhrase }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .notInitialInterrogativePhrase }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .notInitialInterrogativePhrase }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .notInitialInterrogativePhrase }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .notInitialInterrogativePhrase }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .notInitialInterrogativePhrase }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .notInitialInterrogativePhrase }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .notInitialInterrogativePhrase }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .notInitialInterrogativePhrase }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .notInitialInterrogativePhrase }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .notInitialInterrogativePhrase }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .notInitialInterrogativePhrase }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .initialInterrogativePhrase }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .initialInterrogativePhrase }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .notInitialInterrogativePhrase }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .notInitialInterrogativePhrase }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .notInitialInterrogativePhrase }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .notInitialInterrogativePhrase }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .initialInterrogativePhrase }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .notInitialInterrogativePhrase }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .notInitialInterrogativePhrase }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .notInitialInterrogativePhrase }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .notInitialInterrogativePhrase }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .notInitialInterrogativePhrase }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .notInitialInterrogativePhrase }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .notInitialInterrogativePhrase }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .notInitialInterrogativePhrase }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .notInitialInterrogativePhrase }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .notInitialInterrogativePhrase }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .notInitialInterrogativePhrase }
  , { walsCode := "au", language := "Au", iso := "avt", value := .notInitialInterrogativePhrase }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .notInitialInterrogativePhrase }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .notInitialInterrogativePhrase }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .notInitialInterrogativePhrase }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .notInitialInterrogativePhrase }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .notInitialInterrogativePhrase }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .notInitialInterrogativePhrase }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .notInitialInterrogativePhrase }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .initialInterrogativePhrase }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .initialInterrogativePhrase }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .notInitialInterrogativePhrase }
  , { walsCode := "bgs", language := "Baga Sitemu", iso := "bsp", value := .initialInterrogativePhrase }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .notInitialInterrogativePhrase }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .notInitialInterrogativePhrase }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .notInitialInterrogativePhrase }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .mixed }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .notInitialInterrogativePhrase }
  , { walsCode := "bkn", language := "Bakundu", iso := "bdu", value := .notInitialInterrogativePhrase }
  , { walsCode := "bgz", language := "Banggi", iso := "bdg", value := .initialInterrogativePhrase }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .notInitialInterrogativePhrase }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .notInitialInterrogativePhrase }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .initialInterrogativePhrase }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .notInitialInterrogativePhrase }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .notInitialInterrogativePhrase }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .initialInterrogativePhrase }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .notInitialInterrogativePhrase }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .initialInterrogativePhrase }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .notInitialInterrogativePhrase }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .initialInterrogativePhrase }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .notInitialInterrogativePhrase }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .notInitialInterrogativePhrase }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .notInitialInterrogativePhrase }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .initialInterrogativePhrase }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .initialInterrogativePhrase }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .initialInterrogativePhrase }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .initialInterrogativePhrase }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .notInitialInterrogativePhrase }
  , { walsCode := "bhu", language := "Bhumij", iso := "unr", value := .notInitialInterrogativePhrase }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .initialInterrogativePhrase }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .notInitialInterrogativePhrase }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .notInitialInterrogativePhrase }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .notInitialInterrogativePhrase }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .initialInterrogativePhrase }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .notInitialInterrogativePhrase }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .notInitialInterrogativePhrase }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .initialInterrogativePhrase }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .notInitialInterrogativePhrase }
  , { walsCode := "boq", language := "Bokar", iso := "", value := .notInitialInterrogativePhrase }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .notInitialInterrogativePhrase }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .initialInterrogativePhrase }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .notInitialInterrogativePhrase }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .initialInterrogativePhrase }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .notInitialInterrogativePhrase }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .notInitialInterrogativePhrase }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .initialInterrogativePhrase }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .notInitialInterrogativePhrase }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .notInitialInterrogativePhrase }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .notInitialInterrogativePhrase }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .initialInterrogativePhrase }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .initialInterrogativePhrase }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .notInitialInterrogativePhrase }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .notInitialInterrogativePhrase }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .notInitialInterrogativePhrase }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .notInitialInterrogativePhrase }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .notInitialInterrogativePhrase }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .notInitialInterrogativePhrase }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .notInitialInterrogativePhrase }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .initialInterrogativePhrase }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .notInitialInterrogativePhrase }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .notInitialInterrogativePhrase }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .initialInterrogativePhrase }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .initialInterrogativePhrase }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .notInitialInterrogativePhrase }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .initialInterrogativePhrase }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .initialInterrogativePhrase }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .notInitialInterrogativePhrase }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .notInitialInterrogativePhrase }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .mixed }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .notInitialInterrogativePhrase }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .notInitialInterrogativePhrase }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .initialInterrogativePhrase }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .initialInterrogativePhrase }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .notInitialInterrogativePhrase }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .notInitialInterrogativePhrase }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .initialInterrogativePhrase }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .notInitialInterrogativePhrase }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .notInitialInterrogativePhrase }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .notInitialInterrogativePhrase }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .notInitialInterrogativePhrase }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .initialInterrogativePhrase }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .initialInterrogativePhrase }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .initialInterrogativePhrase }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .initialInterrogativePhrase }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .initialInterrogativePhrase }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .notInitialInterrogativePhrase }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .initialInterrogativePhrase }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .initialInterrogativePhrase }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .initialInterrogativePhrase }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .initialInterrogativePhrase }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .notInitialInterrogativePhrase }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .notInitialInterrogativePhrase }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .initialInterrogativePhrase }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .initialInterrogativePhrase }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .notInitialInterrogativePhrase }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .initialInterrogativePhrase }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .notInitialInterrogativePhrase }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .notInitialInterrogativePhrase }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .notInitialInterrogativePhrase }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .initialInterrogativePhrase }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .notInitialInterrogativePhrase }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .notInitialInterrogativePhrase }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .notInitialInterrogativePhrase }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .initialInterrogativePhrase }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .notInitialInterrogativePhrase }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .notInitialInterrogativePhrase }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .initialInterrogativePhrase }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .notInitialInterrogativePhrase }
  , { walsCode := "des", language := "Desano", iso := "des", value := .initialInterrogativePhrase }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .notInitialInterrogativePhrase }
  , { walsCode := "dhb", language := "Dharumbal", iso := "xgm", value := .initialInterrogativePhrase }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .notInitialInterrogativePhrase }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .notInitialInterrogativePhrase }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .notInitialInterrogativePhrase }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .initialInterrogativePhrase }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .notInitialInterrogativePhrase }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .notInitialInterrogativePhrase }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .initialInterrogativePhrase }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .initialInterrogativePhrase }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .notInitialInterrogativePhrase }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .notInitialInterrogativePhrase }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .notInitialInterrogativePhrase }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .notInitialInterrogativePhrase }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .notInitialInterrogativePhrase }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .mixed }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .notInitialInterrogativePhrase }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .notInitialInterrogativePhrase }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .notInitialInterrogativePhrase }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .notInitialInterrogativePhrase }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .notInitialInterrogativePhrase }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .initialInterrogativePhrase }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .notInitialInterrogativePhrase }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .notInitialInterrogativePhrase }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .notInitialInterrogativePhrase }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .initialInterrogativePhrase }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .initialInterrogativePhrase }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .notInitialInterrogativePhrase }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .initialInterrogativePhrase }
  , { walsCode := "eng", language := "English", iso := "eng", value := .initialInterrogativePhrase }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .initialInterrogativePhrase }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .notInitialInterrogativePhrase }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .initialInterrogativePhrase }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .initialInterrogativePhrase }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .initialInterrogativePhrase }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .initialInterrogativePhrase }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .notInitialInterrogativePhrase }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .notInitialInterrogativePhrase }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .notInitialInterrogativePhrase }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .initialInterrogativePhrase }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .notInitialInterrogativePhrase }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .notInitialInterrogativePhrase }
  , { walsCode := "fre", language := "French", iso := "fra", value := .initialInterrogativePhrase }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .initialInterrogativePhrase }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .initialInterrogativePhrase }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .notInitialInterrogativePhrase }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .notInitialInterrogativePhrase }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .notInitialInterrogativePhrase }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .initialInterrogativePhrase }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .notInitialInterrogativePhrase }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .notInitialInterrogativePhrase }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .notInitialInterrogativePhrase }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .initialInterrogativePhrase }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .initialInterrogativePhrase }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .notInitialInterrogativePhrase }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .notInitialInterrogativePhrase }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .notInitialInterrogativePhrase }
  , { walsCode := "ger", language := "German", iso := "deu", value := .initialInterrogativePhrase }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .initialInterrogativePhrase }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .initialInterrogativePhrase }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .notInitialInterrogativePhrase }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .initialInterrogativePhrase }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .notInitialInterrogativePhrase }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .notInitialInterrogativePhrase }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .notInitialInterrogativePhrase }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .initialInterrogativePhrase }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .initialInterrogativePhrase }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .notInitialInterrogativePhrase }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .initialInterrogativePhrase }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .initialInterrogativePhrase }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .notInitialInterrogativePhrase }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .initialInterrogativePhrase }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .initialInterrogativePhrase }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .notInitialInterrogativePhrase }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .notInitialInterrogativePhrase }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .notInitialInterrogativePhrase }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .notInitialInterrogativePhrase }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .notInitialInterrogativePhrase }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .initialInterrogativePhrase }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .notInitialInterrogativePhrase }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .notInitialInterrogativePhrase }
  , { walsCode := "gdb", language := "Gutob", iso := "gbj", value := .notInitialInterrogativePhrase }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .notInitialInterrogativePhrase }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .notInitialInterrogativePhrase }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .notInitialInterrogativePhrase }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .mixed }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .notInitialInterrogativePhrase }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .notInitialInterrogativePhrase }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .notInitialInterrogativePhrase }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .mixed }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .notInitialInterrogativePhrase }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .notInitialInterrogativePhrase }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .initialInterrogativePhrase }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .initialInterrogativePhrase }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .notInitialInterrogativePhrase }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .notInitialInterrogativePhrase }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .initialInterrogativePhrase }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .notInitialInterrogativePhrase }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .notInitialInterrogativePhrase }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .notInitialInterrogativePhrase }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .notInitialInterrogativePhrase }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .notInitialInterrogativePhrase }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .notInitialInterrogativePhrase }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .initialInterrogativePhrase }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .initialInterrogativePhrase }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .notInitialInterrogativePhrase }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .initialInterrogativePhrase }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .notInitialInterrogativePhrase }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .notInitialInterrogativePhrase }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .initialInterrogativePhrase }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .notInitialInterrogativePhrase }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .notInitialInterrogativePhrase }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .initialInterrogativePhrase }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .notInitialInterrogativePhrase }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .mixed }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .notInitialInterrogativePhrase }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .initialInterrogativePhrase }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .notInitialInterrogativePhrase }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .notInitialInterrogativePhrase }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .notInitialInterrogativePhrase }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .initialInterrogativePhrase }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .notInitialInterrogativePhrase }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .initialInterrogativePhrase }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .initialInterrogativePhrase }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .notInitialInterrogativePhrase }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .mixed }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .notInitialInterrogativePhrase }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .initialInterrogativePhrase }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .notInitialInterrogativePhrase }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .notInitialInterrogativePhrase }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .initialInterrogativePhrase }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .notInitialInterrogativePhrase }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .initialInterrogativePhrase }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .notInitialInterrogativePhrase }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .notInitialInterrogativePhrase }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .notInitialInterrogativePhrase }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .notInitialInterrogativePhrase }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .initialInterrogativePhrase }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .notInitialInterrogativePhrase }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .notInitialInterrogativePhrase }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .notInitialInterrogativePhrase }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .notInitialInterrogativePhrase }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .notInitialInterrogativePhrase }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .notInitialInterrogativePhrase }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .notInitialInterrogativePhrase }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .notInitialInterrogativePhrase }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .notInitialInterrogativePhrase }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .notInitialInterrogativePhrase }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .notInitialInterrogativePhrase }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .initialInterrogativePhrase }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .initialInterrogativePhrase }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .notInitialInterrogativePhrase }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .notInitialInterrogativePhrase }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .notInitialInterrogativePhrase }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .initialInterrogativePhrase }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .notInitialInterrogativePhrase }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .initialInterrogativePhrase }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .notInitialInterrogativePhrase }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .notInitialInterrogativePhrase }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .notInitialInterrogativePhrase }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .notInitialInterrogativePhrase }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .notInitialInterrogativePhrase }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .initialInterrogativePhrase }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .initialInterrogativePhrase }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .initialInterrogativePhrase }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .notInitialInterrogativePhrase }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .notInitialInterrogativePhrase }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .notInitialInterrogativePhrase }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .notInitialInterrogativePhrase }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .notInitialInterrogativePhrase }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .notInitialInterrogativePhrase }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .notInitialInterrogativePhrase }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .notInitialInterrogativePhrase }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .initialInterrogativePhrase }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .notInitialInterrogativePhrase }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .notInitialInterrogativePhrase }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .notInitialInterrogativePhrase }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .notInitialInterrogativePhrase }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .initialInterrogativePhrase }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .initialInterrogativePhrase }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .notInitialInterrogativePhrase }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .initialInterrogativePhrase }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .notInitialInterrogativePhrase }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .notInitialInterrogativePhrase }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .notInitialInterrogativePhrase }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .notInitialInterrogativePhrase }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .notInitialInterrogativePhrase }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .notInitialInterrogativePhrase }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .notInitialInterrogativePhrase }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .notInitialInterrogativePhrase }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .notInitialInterrogativePhrase }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .notInitialInterrogativePhrase }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .notInitialInterrogativePhrase }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .notInitialInterrogativePhrase }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .notInitialInterrogativePhrase }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .notInitialInterrogativePhrase }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .notInitialInterrogativePhrase }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .initialInterrogativePhrase }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .notInitialInterrogativePhrase }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .notInitialInterrogativePhrase }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .notInitialInterrogativePhrase }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .initialInterrogativePhrase }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .notInitialInterrogativePhrase }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .notInitialInterrogativePhrase }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .initialInterrogativePhrase }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .notInitialInterrogativePhrase }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .initialInterrogativePhrase }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .initialInterrogativePhrase }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .notInitialInterrogativePhrase }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .notInitialInterrogativePhrase }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .notInitialInterrogativePhrase }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .notInitialInterrogativePhrase }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .notInitialInterrogativePhrase }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .notInitialInterrogativePhrase }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .notInitialInterrogativePhrase }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .initialInterrogativePhrase }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .notInitialInterrogativePhrase }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .initialInterrogativePhrase }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .notInitialInterrogativePhrase }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .initialInterrogativePhrase }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .mixed }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .initialInterrogativePhrase }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .notInitialInterrogativePhrase }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .notInitialInterrogativePhrase }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .mixed }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .initialInterrogativePhrase }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .notInitialInterrogativePhrase }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .notInitialInterrogativePhrase }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .notInitialInterrogativePhrase }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .notInitialInterrogativePhrase }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .notInitialInterrogativePhrase }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .notInitialInterrogativePhrase }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .notInitialInterrogativePhrase }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .notInitialInterrogativePhrase }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .notInitialInterrogativePhrase }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .initialInterrogativePhrase }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .notInitialInterrogativePhrase }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .notInitialInterrogativePhrase }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .notInitialInterrogativePhrase }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .notInitialInterrogativePhrase }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .notInitialInterrogativePhrase }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .notInitialInterrogativePhrase }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .notInitialInterrogativePhrase }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .initialInterrogativePhrase }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .notInitialInterrogativePhrase }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .notInitialInterrogativePhrase }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .notInitialInterrogativePhrase }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .notInitialInterrogativePhrase }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .notInitialInterrogativePhrase }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .notInitialInterrogativePhrase }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .notInitialInterrogativePhrase }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .notInitialInterrogativePhrase }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .notInitialInterrogativePhrase }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .notInitialInterrogativePhrase }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .notInitialInterrogativePhrase }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .notInitialInterrogativePhrase }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .notInitialInterrogativePhrase }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .notInitialInterrogativePhrase }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .initialInterrogativePhrase }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .notInitialInterrogativePhrase }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .notInitialInterrogativePhrase }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .notInitialInterrogativePhrase }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .notInitialInterrogativePhrase }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .notInitialInterrogativePhrase }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .notInitialInterrogativePhrase }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .notInitialInterrogativePhrase }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .notInitialInterrogativePhrase }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .notInitialInterrogativePhrase }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .notInitialInterrogativePhrase }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .notInitialInterrogativePhrase }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .notInitialInterrogativePhrase }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .initialInterrogativePhrase }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .notInitialInterrogativePhrase }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .notInitialInterrogativePhrase }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .notInitialInterrogativePhrase }
  , { walsCode := "loz", language := "Lozi", iso := "loz", value := .notInitialInterrogativePhrase }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .notInitialInterrogativePhrase }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .notInitialInterrogativePhrase }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .initialInterrogativePhrase }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .notInitialInterrogativePhrase }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .notInitialInterrogativePhrase }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .notInitialInterrogativePhrase }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .notInitialInterrogativePhrase }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .notInitialInterrogativePhrase }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .notInitialInterrogativePhrase }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .notInitialInterrogativePhrase }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .notInitialInterrogativePhrase }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .initialInterrogativePhrase }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .notInitialInterrogativePhrase }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .initialInterrogativePhrase }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .initialInterrogativePhrase }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .notInitialInterrogativePhrase }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .initialInterrogativePhrase }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .notInitialInterrogativePhrase }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .initialInterrogativePhrase }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .mixed }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .notInitialInterrogativePhrase }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .notInitialInterrogativePhrase }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .initialInterrogativePhrase }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .initialInterrogativePhrase }
  , { walsCode := "mmw", language := "Mambwe", iso := "mgr", value := .notInitialInterrogativePhrase }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .initialInterrogativePhrase }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .notInitialInterrogativePhrase }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .initialInterrogativePhrase }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .notInitialInterrogativePhrase }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .notInitialInterrogativePhrase }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .notInitialInterrogativePhrase }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .notInitialInterrogativePhrase }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .notInitialInterrogativePhrase }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .notInitialInterrogativePhrase }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .initialInterrogativePhrase }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .notInitialInterrogativePhrase }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .notInitialInterrogativePhrase }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .notInitialInterrogativePhrase }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .initialInterrogativePhrase }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .initialInterrogativePhrase }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .notInitialInterrogativePhrase }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .initialInterrogativePhrase }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .notInitialInterrogativePhrase }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .initialInterrogativePhrase }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .notInitialInterrogativePhrase }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .notInitialInterrogativePhrase }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .notInitialInterrogativePhrase }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .notInitialInterrogativePhrase }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .notInitialInterrogativePhrase }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .initialInterrogativePhrase }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .notInitialInterrogativePhrase }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .initialInterrogativePhrase }
  ]

private def allData_1 : List (Datapoint PositionOfInterrogativePhrasesInContentQuestions) :=
  [ { walsCode := "mba", language := "Mba", iso := "mfc", value := .notInitialInterrogativePhrase }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .notInitialInterrogativePhrase }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .notInitialInterrogativePhrase }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .notInitialInterrogativePhrase }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .notInitialInterrogativePhrase }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .initialInterrogativePhrase }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .notInitialInterrogativePhrase }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .initialInterrogativePhrase }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .initialInterrogativePhrase }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .initialInterrogativePhrase }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .notInitialInterrogativePhrase }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .notInitialInterrogativePhrase }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .notInitialInterrogativePhrase }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .notInitialInterrogativePhrase }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .notInitialInterrogativePhrase }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .notInitialInterrogativePhrase }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .notInitialInterrogativePhrase }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .notInitialInterrogativePhrase }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .notInitialInterrogativePhrase }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .initialInterrogativePhrase }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .initialInterrogativePhrase }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .initialInterrogativePhrase }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .initialInterrogativePhrase }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .initialInterrogativePhrase }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .initialInterrogativePhrase }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .mixed }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .notInitialInterrogativePhrase }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .initialInterrogativePhrase }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .initialInterrogativePhrase }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .notInitialInterrogativePhrase }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .notInitialInterrogativePhrase }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .initialInterrogativePhrase }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .notInitialInterrogativePhrase }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .notInitialInterrogativePhrase }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .notInitialInterrogativePhrase }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .notInitialInterrogativePhrase }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .initialInterrogativePhrase }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .notInitialInterrogativePhrase }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .initialInterrogativePhrase }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .notInitialInterrogativePhrase }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .notInitialInterrogativePhrase }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .initialInterrogativePhrase }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .notInitialInterrogativePhrase }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .notInitialInterrogativePhrase }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .notInitialInterrogativePhrase }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .initialInterrogativePhrase }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .notInitialInterrogativePhrase }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .notInitialInterrogativePhrase }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .notInitialInterrogativePhrase }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .initialInterrogativePhrase }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .notInitialInterrogativePhrase }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .notInitialInterrogativePhrase }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .initialInterrogativePhrase }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .notInitialInterrogativePhrase }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .notInitialInterrogativePhrase }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .notInitialInterrogativePhrase }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .notInitialInterrogativePhrase }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .notInitialInterrogativePhrase }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .initialInterrogativePhrase }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .initialInterrogativePhrase }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .initialInterrogativePhrase }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .initialInterrogativePhrase }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .initialInterrogativePhrase }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .notInitialInterrogativePhrase }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .notInitialInterrogativePhrase }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .notInitialInterrogativePhrase }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .notInitialInterrogativePhrase }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .notInitialInterrogativePhrase }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .notInitialInterrogativePhrase }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .notInitialInterrogativePhrase }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .notInitialInterrogativePhrase }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .notInitialInterrogativePhrase }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .notInitialInterrogativePhrase }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .notInitialInterrogativePhrase }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .notInitialInterrogativePhrase }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .notInitialInterrogativePhrase }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .initialInterrogativePhrase }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .initialInterrogativePhrase }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .notInitialInterrogativePhrase }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .notInitialInterrogativePhrase }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .notInitialInterrogativePhrase }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .initialInterrogativePhrase }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .notInitialInterrogativePhrase }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .notInitialInterrogativePhrase }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .initialInterrogativePhrase }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .initialInterrogativePhrase }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .notInitialInterrogativePhrase }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .notInitialInterrogativePhrase }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .notInitialInterrogativePhrase }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .notInitialInterrogativePhrase }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .notInitialInterrogativePhrase }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .initialInterrogativePhrase }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .notInitialInterrogativePhrase }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .notInitialInterrogativePhrase }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .notInitialInterrogativePhrase }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .mixed }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .initialInterrogativePhrase }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .notInitialInterrogativePhrase }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .notInitialInterrogativePhrase }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .notInitialInterrogativePhrase }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .notInitialInterrogativePhrase }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .initialInterrogativePhrase }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .mixed }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .initialInterrogativePhrase }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .notInitialInterrogativePhrase }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .notInitialInterrogativePhrase }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .notInitialInterrogativePhrase }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .notInitialInterrogativePhrase }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .notInitialInterrogativePhrase }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .notInitialInterrogativePhrase }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .notInitialInterrogativePhrase }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .notInitialInterrogativePhrase }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .notInitialInterrogativePhrase }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .initialInterrogativePhrase }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .notInitialInterrogativePhrase }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .notInitialInterrogativePhrase }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .notInitialInterrogativePhrase }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .notInitialInterrogativePhrase }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .initialInterrogativePhrase }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .notInitialInterrogativePhrase }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .notInitialInterrogativePhrase }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .notInitialInterrogativePhrase }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .notInitialInterrogativePhrase }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .notInitialInterrogativePhrase }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .initialInterrogativePhrase }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .notInitialInterrogativePhrase }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .initialInterrogativePhrase }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .notInitialInterrogativePhrase }
  , { walsCode := "one", language := "One", iso := "aun", value := .notInitialInterrogativePhrase }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .initialInterrogativePhrase }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .notInitialInterrogativePhrase }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .notInitialInterrogativePhrase }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .notInitialInterrogativePhrase }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .notInitialInterrogativePhrase }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .notInitialInterrogativePhrase }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .initialInterrogativePhrase }
  , { walsCode := "owi", language := "Owininga", iso := "owi", value := .notInitialInterrogativePhrase }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .notInitialInterrogativePhrase }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .initialInterrogativePhrase }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .notInitialInterrogativePhrase }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .initialInterrogativePhrase }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .initialInterrogativePhrase }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .notInitialInterrogativePhrase }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .notInitialInterrogativePhrase }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .initialInterrogativePhrase }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .initialInterrogativePhrase }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .initialInterrogativePhrase }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .initialInterrogativePhrase }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .notInitialInterrogativePhrase }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .notInitialInterrogativePhrase }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .notInitialInterrogativePhrase }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .notInitialInterrogativePhrase }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .initialInterrogativePhrase }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .initialInterrogativePhrase }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .notInitialInterrogativePhrase }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .notInitialInterrogativePhrase }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .notInitialInterrogativePhrase }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .initialInterrogativePhrase }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .notInitialInterrogativePhrase }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .initialInterrogativePhrase }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .initialInterrogativePhrase }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .mixed }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .notInitialInterrogativePhrase }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .notInitialInterrogativePhrase }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .initialInterrogativePhrase }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .notInitialInterrogativePhrase }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .notInitialInterrogativePhrase }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .notInitialInterrogativePhrase }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .notInitialInterrogativePhrase }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .notInitialInterrogativePhrase }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .notInitialInterrogativePhrase }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .initialInterrogativePhrase }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .notInitialInterrogativePhrase }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .notInitialInterrogativePhrase }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .initialInterrogativePhrase }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .initialInterrogativePhrase }
  , { walsCode := "rji", language := "Raji", iso := "rji", value := .notInitialInterrogativePhrase }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .notInitialInterrogativePhrase }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .notInitialInterrogativePhrase }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .notInitialInterrogativePhrase }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .notInitialInterrogativePhrase }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .notInitialInterrogativePhrase }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .mixed }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .initialInterrogativePhrase }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .initialInterrogativePhrase }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .initialInterrogativePhrase }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .notInitialInterrogativePhrase }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .notInitialInterrogativePhrase }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .notInitialInterrogativePhrase }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .notInitialInterrogativePhrase }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .notInitialInterrogativePhrase }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .initialInterrogativePhrase }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .notInitialInterrogativePhrase }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .notInitialInterrogativePhrase }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .notInitialInterrogativePhrase }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .notInitialInterrogativePhrase }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .notInitialInterrogativePhrase }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .notInitialInterrogativePhrase }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .notInitialInterrogativePhrase }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .notInitialInterrogativePhrase }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .notInitialInterrogativePhrase }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .notInitialInterrogativePhrase }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .notInitialInterrogativePhrase }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .initialInterrogativePhrase }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .notInitialInterrogativePhrase }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .notInitialInterrogativePhrase }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .notInitialInterrogativePhrase }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .notInitialInterrogativePhrase }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .notInitialInterrogativePhrase }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .notInitialInterrogativePhrase }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .notInitialInterrogativePhrase }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .initialInterrogativePhrase }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .notInitialInterrogativePhrase }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .notInitialInterrogativePhrase }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .initialInterrogativePhrase }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .notInitialInterrogativePhrase }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .notInitialInterrogativePhrase }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .notInitialInterrogativePhrase }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .notInitialInterrogativePhrase }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .notInitialInterrogativePhrase }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .initialInterrogativePhrase }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .notInitialInterrogativePhrase }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .notInitialInterrogativePhrase }
  , { walsCode := "ryu", language := "Shuri", iso := "ryu", value := .notInitialInterrogativePhrase }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .initialInterrogativePhrase }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .notInitialInterrogativePhrase }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .notInitialInterrogativePhrase }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .notInitialInterrogativePhrase }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .notInitialInterrogativePhrase }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .initialInterrogativePhrase }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .initialInterrogativePhrase }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .notInitialInterrogativePhrase }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .initialInterrogativePhrase }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .initialInterrogativePhrase }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .notInitialInterrogativePhrase }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .notInitialInterrogativePhrase }
  , { walsCode := "so", language := "So", iso := "teu", value := .initialInterrogativePhrase }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .notInitialInterrogativePhrase }
  , { walsCode := "som", language := "Somali", iso := "som", value := .notInitialInterrogativePhrase }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .notInitialInterrogativePhrase }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .notInitialInterrogativePhrase }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .notInitialInterrogativePhrase }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .notInitialInterrogativePhrase }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .initialInterrogativePhrase }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .notInitialInterrogativePhrase }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .notInitialInterrogativePhrase }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .notInitialInterrogativePhrase }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .notInitialInterrogativePhrase }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .notInitialInterrogativePhrase }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .notInitialInterrogativePhrase }
  , { walsCode := "slg", language := "Sulung", iso := "suv", value := .notInitialInterrogativePhrase }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .notInitialInterrogativePhrase }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .mixed }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .notInitialInterrogativePhrase }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .initialInterrogativePhrase }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .notInitialInterrogativePhrase }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .notInitialInterrogativePhrase }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .notInitialInterrogativePhrase }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .initialInterrogativePhrase }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .initialInterrogativePhrase }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .notInitialInterrogativePhrase }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .notInitialInterrogativePhrase }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .initialInterrogativePhrase }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .notInitialInterrogativePhrase }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .notInitialInterrogativePhrase }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .initialInterrogativePhrase }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .initialInterrogativePhrase }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .notInitialInterrogativePhrase }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .notInitialInterrogativePhrase }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .initialInterrogativePhrase }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .notInitialInterrogativePhrase }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .initialInterrogativePhrase }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .notInitialInterrogativePhrase }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .initialInterrogativePhrase }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .notInitialInterrogativePhrase }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .initialInterrogativePhrase }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .notInitialInterrogativePhrase }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .notInitialInterrogativePhrase }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .initialInterrogativePhrase }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .initialInterrogativePhrase }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .notInitialInterrogativePhrase }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .notInitialInterrogativePhrase }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .mixed }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .notInitialInterrogativePhrase }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .notInitialInterrogativePhrase }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .notInitialInterrogativePhrase }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .notInitialInterrogativePhrase }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .initialInterrogativePhrase }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .notInitialInterrogativePhrase }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .notInitialInterrogativePhrase }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .notInitialInterrogativePhrase }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .initialInterrogativePhrase }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .notInitialInterrogativePhrase }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .notInitialInterrogativePhrase }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .notInitialInterrogativePhrase }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .initialInterrogativePhrase }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .notInitialInterrogativePhrase }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .mixed }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .initialInterrogativePhrase }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .initialInterrogativePhrase }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .notInitialInterrogativePhrase }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .notInitialInterrogativePhrase }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .mixed }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .initialInterrogativePhrase }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .notInitialInterrogativePhrase }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .notInitialInterrogativePhrase }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .notInitialInterrogativePhrase }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .initialInterrogativePhrase }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .initialInterrogativePhrase }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .initialInterrogativePhrase }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .notInitialInterrogativePhrase }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .notInitialInterrogativePhrase }
  , { walsCode := "tsn", language := "Tsonga", iso := "tso", value := .notInitialInterrogativePhrase }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .notInitialInterrogativePhrase }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .initialInterrogativePhrase }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .mixed }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .notInitialInterrogativePhrase }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .notInitialInterrogativePhrase }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .notInitialInterrogativePhrase }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .notInitialInterrogativePhrase }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .notInitialInterrogativePhrase }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .initialInterrogativePhrase }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .notInitialInterrogativePhrase }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .mixed }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .initialInterrogativePhrase }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .notInitialInterrogativePhrase }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .notInitialInterrogativePhrase }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .notInitialInterrogativePhrase }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .notInitialInterrogativePhrase }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .notInitialInterrogativePhrase }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .initialInterrogativePhrase }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .notInitialInterrogativePhrase }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .notInitialInterrogativePhrase }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .notInitialInterrogativePhrase }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .initialInterrogativePhrase }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .notInitialInterrogativePhrase }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .notInitialInterrogativePhrase }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .notInitialInterrogativePhrase }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .notInitialInterrogativePhrase }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .notInitialInterrogativePhrase }
  , { walsCode := "wwa", language := "Waama", iso := "wwa", value := .notInitialInterrogativePhrase }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .notInitialInterrogativePhrase }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .notInitialInterrogativePhrase }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .notInitialInterrogativePhrase }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .notInitialInterrogativePhrase }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .notInitialInterrogativePhrase }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .initialInterrogativePhrase }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .notInitialInterrogativePhrase }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .initialInterrogativePhrase }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .notInitialInterrogativePhrase }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .initialInterrogativePhrase }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .initialInterrogativePhrase }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .initialInterrogativePhrase }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .notInitialInterrogativePhrase }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .initialInterrogativePhrase }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .notInitialInterrogativePhrase }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .notInitialInterrogativePhrase }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .initialInterrogativePhrase }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .notInitialInterrogativePhrase }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .initialInterrogativePhrase }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .initialInterrogativePhrase }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .notInitialInterrogativePhrase }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .initialInterrogativePhrase }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .notInitialInterrogativePhrase }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .initialInterrogativePhrase }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .notInitialInterrogativePhrase }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .initialInterrogativePhrase }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .notInitialInterrogativePhrase }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .notInitialInterrogativePhrase }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .notInitialInterrogativePhrase }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .notInitialInterrogativePhrase }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .initialInterrogativePhrase }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .notInitialInterrogativePhrase }
  , { walsCode := "yns", language := "Yansi", iso := "yns", value := .notInitialInterrogativePhrase }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .mixed }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .notInitialInterrogativePhrase }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .notInitialInterrogativePhrase }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .notInitialInterrogativePhrase }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .initialInterrogativePhrase }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .initialInterrogativePhrase }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .initialInterrogativePhrase }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .notInitialInterrogativePhrase }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .notInitialInterrogativePhrase }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .notInitialInterrogativePhrase }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .initialInterrogativePhrase }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .initialInterrogativePhrase }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .notInitialInterrogativePhrase }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .initialInterrogativePhrase }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .notInitialInterrogativePhrase }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .initialInterrogativePhrase }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .initialInterrogativePhrase }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .initialInterrogativePhrase }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .notInitialInterrogativePhrase }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .initialInterrogativePhrase }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .notInitialInterrogativePhrase }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .notInitialInterrogativePhrase }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .initialInterrogativePhrase }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .initialInterrogativePhrase }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .notInitialInterrogativePhrase }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .initialInterrogativePhrase }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .initialInterrogativePhrase }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .notInitialInterrogativePhrase }
  ]

/-- Complete WALS 93A dataset (902 languages). -/
def allData : List (Datapoint PositionOfInterrogativePhrasesInContentQuestions) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 902 := by native_decide

theorem count_initialInterrogativePhrase :
    (allData.filter (·.value == .initialInterrogativePhrase)).length = 264 := by native_decide
theorem count_notInitialInterrogativePhrase :
    (allData.filter (·.value == .notInitialInterrogativePhrase)).length = 615 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 23 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F93A
