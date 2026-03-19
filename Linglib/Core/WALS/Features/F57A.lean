/-!
# WALS Feature 57A: Position of Pronominal Possessive Affixes
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 57A`.

Chapter 57, 902 languages.
-/

namespace Core.WALS.F57A

/-- WALS 57A values. -/
inductive PositionOfPronominalPossessiveAffixes where
  | possessivePrefixes  -- Possessive prefixes (255 languages)
  | possessiveSuffixes  -- Possessive suffixes (355 languages)
  | prefixesAndSuffixes  -- Prefixes and suffixes (32 languages)
  | noPossessiveAffixes  -- No possessive affixes (260 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 57A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PositionOfPronominalPossessiveAffixes
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "aar", language := "Aari", iso := "aiw", value := .noPossessiveAffixes }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .prefixesAndSuffixes }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .possessivePrefixes }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .possessivePrefixes }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noPossessiveAffixes }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .possessivePrefixes }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .possessiveSuffixes }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .possessiveSuffixes }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .possessivePrefixes }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .possessivePrefixes }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .noPossessiveAffixes }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .possessivePrefixes }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .possessivePrefixes }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .possessivePrefixes }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .noPossessiveAffixes }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .possessiveSuffixes }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .possessivePrefixes }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .possessiveSuffixes }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .possessivePrefixes }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noPossessiveAffixes }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .possessiveSuffixes }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noPossessiveAffixes }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .possessiveSuffixes }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .prefixesAndSuffixes }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .prefixesAndSuffixes }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .possessiveSuffixes }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .possessivePrefixes }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .noPossessiveAffixes }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .possessiveSuffixes }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .possessiveSuffixes }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .prefixesAndSuffixes }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .possessiveSuffixes }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .possessiveSuffixes }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .possessiveSuffixes }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .possessivePrefixes }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .possessiveSuffixes }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .possessiveSuffixes }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .noPossessiveAffixes }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .possessiveSuffixes }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .noPossessiveAffixes }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .possessiveSuffixes }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .possessivePrefixes }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .possessivePrefixes }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .possessivePrefixes }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .possessivePrefixes }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .possessiveSuffixes }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .possessiveSuffixes }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .possessiveSuffixes }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .possessiveSuffixes }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .possessiveSuffixes }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .possessiveSuffixes }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noPossessiveAffixes }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noPossessiveAffixes }
  , { walsCode := "ari", language := "Aribwatsa", iso := "laz", value := .possessiveSuffixes }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .possessiveSuffixes }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .possessiveSuffixes }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .possessiveSuffixes }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .possessiveSuffixes }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .possessiveSuffixes }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noPossessiveAffixes }
  , { walsCode := "atm", language := "Atacameño", iso := "kuz", value := .possessivePrefixes }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .possessivePrefixes }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .possessivePrefixes }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noPossessiveAffixes }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noPossessiveAffixes }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .possessiveSuffixes }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .possessivePrefixes }
  , { walsCode := "ayr", language := "Ayoreo", iso := "ayo", value := .possessivePrefixes }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .possessiveSuffixes }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .possessiveSuffixes }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .possessiveSuffixes }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .possessiveSuffixes }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .noPossessiveAffixes }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .possessiveSuffixes }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .possessiveSuffixes }
  , { walsCode := "blg", language := "Balangao", iso := "blw", value := .possessiveSuffixes }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .possessiveSuffixes }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .possessiveSuffixes }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .possessiveSuffixes }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noPossessiveAffixes }
  , { walsCode := "mug", language := "Bargam", iso := "mlp", value := .possessivePrefixes }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .possessivePrefixes }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .possessivePrefixes }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .possessiveSuffixes }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noPossessiveAffixes }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .possessiveSuffixes }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .possessiveSuffixes }
  , { walsCode := "bau", language := "Bau", iso := "bbd", value := .possessiveSuffixes }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .possessivePrefixes }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noPossessiveAffixes }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .possessiveSuffixes }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .possessivePrefixes }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .possessiveSuffixes }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .possessiveSuffixes }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .possessiveSuffixes }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .possessiveSuffixes }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .possessiveSuffixes }
  , { walsCode := "bsi", language := "Berber (Siwa)", iso := "siz", value := .possessiveSuffixes }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .possessiveSuffixes }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .possessiveSuffixes }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .possessivePrefixes }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .noPossessiveAffixes }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .possessiveSuffixes }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .possessiveSuffixes }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .possessiveSuffixes }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .possessivePrefixes }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .possessivePrefixes }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .noPossessiveAffixes }
  , { walsCode := "big", language := "Binga", iso := "yul", value := .possessiveSuffixes }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .noPossessiveAffixes }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .possessivePrefixes }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .possessivePrefixes }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .possessivePrefixes }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .possessiveSuffixes }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .possessiveSuffixes }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .possessivePrefixes }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .possessiveSuffixes }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .possessiveSuffixes }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noPossessiveAffixes }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .possessiveSuffixes }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .possessivePrefixes }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noPossessiveAffixes }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .noPossessiveAffixes }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .possessivePrefixes }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .possessiveSuffixes }
  , { walsCode := "bmr", language := "Burum", iso := "bmu", value := .possessiveSuffixes }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .possessiveSuffixes }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .possessivePrefixes }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .noPossessiveAffixes }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .possessivePrefixes }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .possessivePrefixes }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .possessivePrefixes }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .possessivePrefixes }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .possessivePrefixes }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noPossessiveAffixes }
  , { walsCode := "car", language := "Carib", iso := "car", value := .possessivePrefixes }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .possessivePrefixes }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .noPossessiveAffixes }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .noPossessiveAffixes }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .prefixesAndSuffixes }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .possessiveSuffixes }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .possessiveSuffixes }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .possessiveSuffixes }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .possessiveSuffixes }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .possessivePrefixes }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .noPossessiveAffixes }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .noPossessiveAffixes }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .possessiveSuffixes }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .possessivePrefixes }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .prefixesAndSuffixes }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .noPossessiveAffixes }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .noPossessiveAffixes }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .possessivePrefixes }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .prefixesAndSuffixes }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .prefixesAndSuffixes }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .prefixesAndSuffixes }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .possessivePrefixes }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .noPossessiveAffixes }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .possessivePrefixes }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .possessivePrefixes }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .possessivePrefixes }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .possessivePrefixes }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .possessivePrefixes }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .possessiveSuffixes }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noPossessiveAffixes }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .possessivePrefixes }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noPossessiveAffixes }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .possessivePrefixes }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .possessiveSuffixes }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .possessivePrefixes }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .prefixesAndSuffixes }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noPossessiveAffixes }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .possessivePrefixes }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noPossessiveAffixes }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .possessivePrefixes }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .noPossessiveAffixes }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .possessivePrefixes }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .possessivePrefixes }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noPossessiveAffixes }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .possessivePrefixes }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .noPossessiveAffixes }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .possessiveSuffixes }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .possessiveSuffixes }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .noPossessiveAffixes }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .possessiveSuffixes }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .noPossessiveAffixes }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .possessivePrefixes }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .noPossessiveAffixes }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .noPossessiveAffixes }
  , { walsCode := "des", language := "Desano", iso := "des", value := .noPossessiveAffixes }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .possessiveSuffixes }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .possessivePrefixes }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .possessiveSuffixes }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .possessiveSuffixes }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noPossessiveAffixes }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .noPossessiveAffixes }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .possessiveSuffixes }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .possessiveSuffixes }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .possessiveSuffixes }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .possessiveSuffixes }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .possessivePrefixes }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .noPossessiveAffixes }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noPossessiveAffixes }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .possessiveSuffixes }
  , { walsCode := "ene", language := "Enets", iso := "", value := .possessiveSuffixes }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noPossessiveAffixes }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .possessiveSuffixes }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noPossessiveAffixes }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noPossessiveAffixes }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .noPossessiveAffixes }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .possessiveSuffixes }
  , { walsCode := "ess", language := "Esselen", iso := "esq", value := .possessivePrefixes }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .possessivePrefixes }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .possessiveSuffixes }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .possessiveSuffixes }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .possessiveSuffixes }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .noPossessiveAffixes }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .possessiveSuffixes }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .possessiveSuffixes }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noPossessiveAffixes }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .possessiveSuffixes }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .possessivePrefixes }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noPossessiveAffixes }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .possessiveSuffixes }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .possessiveSuffixes }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .possessivePrefixes }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .prefixesAndSuffixes }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .noPossessiveAffixes }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noPossessiveAffixes }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noPossessiveAffixes }
  , { walsCode := "grs", language := "Garus", iso := "gyb", value := .possessiveSuffixes }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .possessivePrefixes }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .possessivePrefixes }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .possessiveSuffixes }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .possessiveSuffixes }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .possessiveSuffixes }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noPossessiveAffixes }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noPossessiveAffixes }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .possessiveSuffixes }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .possessivePrefixes }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .possessiveSuffixes }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .possessiveSuffixes }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .noPossessiveAffixes }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .possessiveSuffixes }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .possessivePrefixes }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noPossessiveAffixes }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noPossessiveAffixes }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .possessiveSuffixes }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .possessivePrefixes }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .possessivePrefixes }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .possessivePrefixes }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .possessiveSuffixes }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .possessiveSuffixes }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .possessiveSuffixes }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .possessivePrefixes }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .noPossessiveAffixes }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noPossessiveAffixes }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .possessivePrefixes }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .possessiveSuffixes }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noPossessiveAffixes }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .possessiveSuffixes }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .possessiveSuffixes }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .possessivePrefixes }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .possessiveSuffixes }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .prefixesAndSuffixes }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .possessivePrefixes }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .possessiveSuffixes }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noPossessiveAffixes }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .noPossessiveAffixes }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .possessiveSuffixes }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .possessiveSuffixes }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .noPossessiveAffixes }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .possessivePrefixes }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .possessiveSuffixes }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .prefixesAndSuffixes }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .prefixesAndSuffixes }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .possessivePrefixes }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .possessivePrefixes }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .possessivePrefixes }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .prefixesAndSuffixes }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .possessiveSuffixes }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noPossessiveAffixes }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .noPossessiveAffixes }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .possessivePrefixes }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .noPossessiveAffixes }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .possessiveSuffixes }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noPossessiveAffixes }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noPossessiveAffixes }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .noPossessiveAffixes }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noPossessiveAffixes }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .possessivePrefixes }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .possessivePrefixes }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .possessivePrefixes }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .possessiveSuffixes }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noPossessiveAffixes }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .possessivePrefixes }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noPossessiveAffixes }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .possessiveSuffixes }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noPossessiveAffixes }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .noPossessiveAffixes }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .possessivePrefixes }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .noPossessiveAffixes }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .possessiveSuffixes }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .possessivePrefixes }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noPossessiveAffixes }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noPossessiveAffixes }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .possessivePrefixes }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .possessivePrefixes }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .possessivePrefixes }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .possessiveSuffixes }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .noPossessiveAffixes }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .possessivePrefixes }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .possessiveSuffixes }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .possessivePrefixes }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .noPossessiveAffixes }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noPossessiveAffixes }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .possessiveSuffixes }
  , { walsCode := "jrw", language := "Jarawa (in Andamans)", iso := "anq", value := .possessivePrefixes }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .possessiveSuffixes }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .noPossessiveAffixes }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .noPossessiveAffixes }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noPossessiveAffixes }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .possessivePrefixes }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .possessiveSuffixes }
  , { walsCode := "kai", language := "Kaian", iso := "kct", value := .noPossessiveAffixes }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .noPossessiveAffixes }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .possessiveSuffixes }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .possessiveSuffixes }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .possessivePrefixes }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .noPossessiveAffixes }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .possessiveSuffixes }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .possessiveSuffixes }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .possessivePrefixes }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .noPossessiveAffixes }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .noPossessiveAffixes }
  , { walsCode := "kbu", language := "Kanembu", iso := "kbl", value := .possessiveSuffixes }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noPossessiveAffixes }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .possessiveSuffixes }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .possessiveSuffixes }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .possessiveSuffixes }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .possessivePrefixes }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .possessiveSuffixes }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .possessivePrefixes }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .possessivePrefixes }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .possessivePrefixes }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .possessivePrefixes }
  , { walsCode := "ktm", language := "Kathlamet", iso := "", value := .possessivePrefixes }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .possessiveSuffixes }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .possessiveSuffixes }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .possessiveSuffixes }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .possessivePrefixes }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noPossessiveAffixes }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .possessivePrefixes }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .prefixesAndSuffixes }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .possessiveSuffixes }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .possessiveSuffixes }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .possessivePrefixes }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .possessivePrefixes }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noPossessiveAffixes }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .possessiveSuffixes }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .possessivePrefixes }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .possessiveSuffixes }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .possessivePrefixes }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .possessiveSuffixes }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .noPossessiveAffixes }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noPossessiveAffixes }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .noPossessiveAffixes }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noPossessiveAffixes }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noPossessiveAffixes }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .noPossessiveAffixes }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .possessiveSuffixes }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .possessivePrefixes }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .possessiveSuffixes }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .possessivePrefixes }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .possessivePrefixes }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .possessiveSuffixes }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .possessiveSuffixes }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .noPossessiveAffixes }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .possessivePrefixes }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .possessivePrefixes }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .possessivePrefixes }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .noPossessiveAffixes }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .possessiveSuffixes }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .possessivePrefixes }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .possessiveSuffixes }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .possessivePrefixes }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .noPossessiveAffixes }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .possessiveSuffixes }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noPossessiveAffixes }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .possessivePrefixes }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .noPossessiveAffixes }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noPossessiveAffixes }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .possessivePrefixes }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .noPossessiveAffixes }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .possessiveSuffixes }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noPossessiveAffixes }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noPossessiveAffixes }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .possessivePrefixes }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .possessiveSuffixes }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noPossessiveAffixes }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .noPossessiveAffixes }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noPossessiveAffixes }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .possessivePrefixes }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .possessiveSuffixes }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .possessiveSuffixes }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .noPossessiveAffixes }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .possessiveSuffixes }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .possessiveSuffixes }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .noPossessiveAffixes }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .possessiveSuffixes }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .possessiveSuffixes }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noPossessiveAffixes }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .noPossessiveAffixes }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .noPossessiveAffixes }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .possessiveSuffixes }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .noPossessiveAffixes }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .possessiveSuffixes }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .possessiveSuffixes }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .possessiveSuffixes }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noPossessiveAffixes }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .possessivePrefixes }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .noPossessiveAffixes }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .possessiveSuffixes }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .possessiveSuffixes }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .noPossessiveAffixes }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noPossessiveAffixes }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .possessiveSuffixes }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noPossessiveAffixes }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .possessivePrefixes }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .possessivePrefixes }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .possessiveSuffixes }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .possessiveSuffixes }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .possessivePrefixes }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .possessivePrefixes }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noPossessiveAffixes }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .possessiveSuffixes }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noPossessiveAffixes }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .possessiveSuffixes }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .prefixesAndSuffixes }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .possessivePrefixes }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .possessiveSuffixes }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .possessiveSuffixes }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .possessiveSuffixes }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .possessiveSuffixes }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .possessivePrefixes }
  , { walsCode := "lul", language := "Lule", iso := "ule", value := .possessiveSuffixes }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .possessiveSuffixes }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .possessiveSuffixes }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .possessiveSuffixes }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .possessiveSuffixes }
  , { walsCode := "jlu", language := "Luwo", iso := "lwo", value := .possessiveSuffixes }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .possessiveSuffixes }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noPossessiveAffixes }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .possessivePrefixes }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .possessiveSuffixes }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .possessivePrefixes }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .possessivePrefixes }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .possessivePrefixes }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .possessiveSuffixes }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noPossessiveAffixes }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .noPossessiveAffixes }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .possessiveSuffixes }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noPossessiveAffixes }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .prefixesAndSuffixes }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .possessiveSuffixes }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .possessivePrefixes }
  , { walsCode := "mmi", language := "Mambai", iso := "mcs", value := .possessiveSuffixes }
  , { walsCode := "mmw", language := "Mambwe", iso := "mgr", value := .possessiveSuffixes }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .possessivePrefixes }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .possessiveSuffixes }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .possessivePrefixes }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noPossessiveAffixes }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .possessiveSuffixes }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .possessiveSuffixes }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .possessiveSuffixes }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .noPossessiveAffixes }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .possessiveSuffixes }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noPossessiveAffixes }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noPossessiveAffixes }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .possessiveSuffixes }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .possessiveSuffixes }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .possessiveSuffixes }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .possessiveSuffixes }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .possessivePrefixes }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .possessivePrefixes }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .possessiveSuffixes }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .possessiveSuffixes }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .possessivePrefixes }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .noPossessiveAffixes }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .noPossessiveAffixes }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .possessivePrefixes }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .possessivePrefixes }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .possessivePrefixes }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .noPossessiveAffixes }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .possessiveSuffixes }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .possessiveSuffixes }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .possessivePrefixes }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .possessiveSuffixes }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .possessiveSuffixes }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .noPossessiveAffixes }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "mee", language := "Me'en", iso := "mym", value := .possessiveSuffixes }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .possessivePrefixes }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .possessivePrefixes }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .possessiveSuffixes }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .possessivePrefixes }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .possessiveSuffixes }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .possessivePrefixes }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .noPossessiveAffixes }
  , { walsCode := "mig", language := "Migama", iso := "mmy", value := .possessiveSuffixes }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .possessivePrefixes }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .possessivePrefixes }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noPossessiveAffixes }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .possessiveSuffixes }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .possessiveSuffixes }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .possessiveSuffixes }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .possessivePrefixes }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noPossessiveAffixes }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .possessiveSuffixes }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .possessiveSuffixes }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .possessiveSuffixes }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noPossessiveAffixes }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .noPossessiveAffixes }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .possessivePrefixes }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .possessivePrefixes }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .possessiveSuffixes }
  , { walsCode := "mko", language := "Mokilko", iso := "moz", value := .possessiveSuffixes }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .noPossessiveAffixes }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .noPossessiveAffixes }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .possessiveSuffixes }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .possessivePrefixes }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .possessiveSuffixes }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .possessiveSuffixes }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .possessiveSuffixes }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .possessiveSuffixes }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .possessiveSuffixes }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .possessiveSuffixes }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .possessivePrefixes }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .possessivePrefixes }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .noPossessiveAffixes }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .possessivePrefixes }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noPossessiveAffixes }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .possessiveSuffixes }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .possessiveSuffixes }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .possessiveSuffixes }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .possessiveSuffixes }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .possessivePrefixes }
  , { walsCode := "mnz", language := "Munzombo", iso := "moj", value := .noPossessiveAffixes }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .noPossessiveAffixes }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .possessiveSuffixes }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .possessiveSuffixes }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .possessiveSuffixes }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .possessiveSuffixes }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .possessiveSuffixes }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .possessivePrefixes }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .possessiveSuffixes }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .possessiveSuffixes }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .noPossessiveAffixes }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .possessivePrefixes }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .possessivePrefixes }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .possessivePrefixes }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .possessivePrefixes }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .possessivePrefixes }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .noPossessiveAffixes }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .possessiveSuffixes }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .possessivePrefixes }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .possessivePrefixes }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .noPossessiveAffixes }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .noPossessiveAffixes }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .possessiveSuffixes }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .noPossessiveAffixes }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .possessiveSuffixes }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .possessivePrefixes }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .possessivePrefixes }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .possessivePrefixes }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .noPossessiveAffixes }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .prefixesAndSuffixes }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .possessiveSuffixes }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .noPossessiveAffixes }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .noPossessiveAffixes }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noPossessiveAffixes }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .possessiveSuffixes }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .possessiveSuffixes }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .possessiveSuffixes }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .possessivePrefixes }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .noPossessiveAffixes }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .noPossessiveAffixes }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .possessivePrefixes }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .possessiveSuffixes }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .possessiveSuffixes }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .possessiveSuffixes }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .possessiveSuffixes }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .possessiveSuffixes }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .noPossessiveAffixes }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .possessiveSuffixes }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noPossessiveAffixes }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .possessiveSuffixes }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .noPossessiveAffixes }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .possessiveSuffixes }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .possessiveSuffixes }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noPossessiveAffixes }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .possessivePrefixes }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .possessiveSuffixes }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .noPossessiveAffixes }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .possessivePrefixes }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .noPossessiveAffixes }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .possessiveSuffixes }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .noPossessiveAffixes }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .possessiveSuffixes }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .noPossessiveAffixes }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .prefixesAndSuffixes }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .possessivePrefixes }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .possessiveSuffixes }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noPossessiveAffixes }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .noPossessiveAffixes }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .noPossessiveAffixes }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .possessivePrefixes }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .possessiveSuffixes }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .possessivePrefixes }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .noPossessiveAffixes }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .possessivePrefixes }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .noPossessiveAffixes }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .possessiveSuffixes }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .prefixesAndSuffixes }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .prefixesAndSuffixes }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .possessivePrefixes }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .possessiveSuffixes }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .possessiveSuffixes }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .possessiveSuffixes }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noPossessiveAffixes }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .noPossessiveAffixes }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .noPossessiveAffixes }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .possessiveSuffixes }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .possessiveSuffixes }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .possessiveSuffixes }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .noPossessiveAffixes }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .possessiveSuffixes }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .possessivePrefixes }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .possessiveSuffixes }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noPossessiveAffixes }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .prefixesAndSuffixes }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .prefixesAndSuffixes }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .noPossessiveAffixes }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .possessivePrefixes }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .possessiveSuffixes }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noPossessiveAffixes }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .possessivePrefixes }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .possessivePrefixes }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .possessivePrefixes }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .possessivePrefixes }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .possessivePrefixes }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .possessiveSuffixes }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .possessiveSuffixes }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .noPossessiveAffixes }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .possessiveSuffixes }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .possessivePrefixes }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .possessivePrefixes }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .possessiveSuffixes }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .possessiveSuffixes }
  , { walsCode := "puq", language := "Puquina", iso := "puq", value := .noPossessiveAffixes }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .noPossessiveAffixes }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .possessiveSuffixes }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .possessiveSuffixes }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .noPossessiveAffixes }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .possessiveSuffixes }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noPossessiveAffixes }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .possessiveSuffixes }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .possessiveSuffixes }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .possessivePrefixes }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .noPossessiveAffixes }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .possessiveSuffixes }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .possessiveSuffixes }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .noPossessiveAffixes }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .noPossessiveAffixes }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .possessivePrefixes }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .possessivePrefixes }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .possessiveSuffixes }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noPossessiveAffixes }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .possessiveSuffixes }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .possessiveSuffixes }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .noPossessiveAffixes }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .possessivePrefixes }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .noPossessiveAffixes }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noPossessiveAffixes }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .noPossessiveAffixes }
  , { walsCode := "saa", language := "Sa'a", iso := "apb", value := .possessiveSuffixes }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .possessiveSuffixes }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noPossessiveAffixes }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .possessiveSuffixes }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .possessiveSuffixes }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .prefixesAndSuffixes }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .possessiveSuffixes }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noPossessiveAffixes }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .noPossessiveAffixes }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noPossessiveAffixes }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .possessiveSuffixes }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .possessiveSuffixes }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noPossessiveAffixes }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .possessivePrefixes }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .noPossessiveAffixes }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .possessiveSuffixes }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .possessiveSuffixes }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .possessiveSuffixes }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .possessivePrefixes }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .possessivePrefixes }
  , { walsCode := "sen", language := "Sena", iso := "seh", value := .possessiveSuffixes }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noPossessiveAffixes }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .noPossessiveAffixes }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .possessivePrefixes }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .possessiveSuffixes }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .possessiveSuffixes }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .possessiveSuffixes }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noPossessiveAffixes }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .possessiveSuffixes }
  , { walsCode := "smp", language := "Shompen", iso := "sii", value := .noPossessiveAffixes }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .prefixesAndSuffixes }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .possessiveSuffixes }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .noPossessiveAffixes }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .possessiveSuffixes }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .possessiveSuffixes }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .possessivePrefixes }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .possessivePrefixes }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .noPossessiveAffixes }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .possessiveSuffixes }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .possessiveSuffixes }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .possessivePrefixes }
  , { walsCode := "so", language := "So", iso := "teu", value := .possessiveSuffixes }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .possessiveSuffixes }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .possessiveSuffixes }
  , { walsCode := "som", language := "Somali", iso := "som", value := .possessiveSuffixes }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .possessiveSuffixes }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .possessivePrefixes }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noPossessiveAffixes }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .prefixesAndSuffixes }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noPossessiveAffixes }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .possessivePrefixes }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noPossessiveAffixes }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .possessiveSuffixes }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .noPossessiveAffixes }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .possessiveSuffixes }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noPossessiveAffixes }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .possessivePrefixes }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .noPossessiveAffixes }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .possessiveSuffixes }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .possessiveSuffixes }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .noPossessiveAffixes }
  , { walsCode := "tmg", language := "Tamagario", iso := "tcg", value := .noPossessiveAffixes }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .possessiveSuffixes }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .possessivePrefixes }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .possessiveSuffixes }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .possessivePrefixes }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .noPossessiveAffixes }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .possessivePrefixes }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .possessiveSuffixes }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .possessiveSuffixes }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .possessivePrefixes }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .possessiveSuffixes }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .noPossessiveAffixes }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .noPossessiveAffixes }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .possessiveSuffixes }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .possessivePrefixes }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .possessivePrefixes }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .possessivePrefixes }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .possessivePrefixes }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .possessiveSuffixes }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .noPossessiveAffixes }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .prefixesAndSuffixes }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .noPossessiveAffixes }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .noPossessiveAffixes }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .noPossessiveAffixes }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noPossessiveAffixes }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .possessivePrefixes }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .possessivePrefixes }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .possessiveSuffixes }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .possessiveSuffixes }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .possessiveSuffixes }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .possessivePrefixes }
  , { walsCode := "tia", language := "Tima", iso := "tms", value := .possessiveSuffixes }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .possessiveSuffixes }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .possessiveSuffixes }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .possessivePrefixes }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .possessiveSuffixes }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .possessivePrefixes }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noPossessiveAffixes }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .possessiveSuffixes }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .possessivePrefixes }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .possessivePrefixes }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .possessivePrefixes }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .possessiveSuffixes }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .possessiveSuffixes }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .possessiveSuffixes }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .noPossessiveAffixes }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .possessivePrefixes }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .possessivePrefixes }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .possessivePrefixes }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .noPossessiveAffixes }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .prefixesAndSuffixes }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .noPossessiveAffixes }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .noPossessiveAffixes }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .possessiveSuffixes }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .possessiveSuffixes }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .possessiveSuffixes }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .possessivePrefixes }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noPossessiveAffixes }
  , { walsCode := "tum", language := "Tumleo", iso := "tmq", value := .possessiveSuffixes }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .noPossessiveAffixes }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .possessivePrefixes }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .possessiveSuffixes }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .possessivePrefixes }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .possessivePrefixes }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .possessiveSuffixes }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .possessivePrefixes }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .possessivePrefixes }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noPossessiveAffixes }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .possessivePrefixes }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .noPossessiveAffixes }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .possessiveSuffixes }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .noPossessiveAffixes }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .possessiveSuffixes }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .possessivePrefixes }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .prefixesAndSuffixes }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .noPossessiveAffixes }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noPossessiveAffixes }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .noPossessiveAffixes }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .possessivePrefixes }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .prefixesAndSuffixes }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .possessiveSuffixes }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .possessiveSuffixes }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .possessiveSuffixes }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .noPossessiveAffixes }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noPossessiveAffixes }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .possessiveSuffixes }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .possessiveSuffixes }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .noPossessiveAffixes }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .noPossessiveAffixes }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .possessivePrefixes }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noPossessiveAffixes }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .possessivePrefixes }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .possessivePrefixes }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .possessivePrefixes }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .possessiveSuffixes }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .possessivePrefixes }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .possessiveSuffixes }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .possessivePrefixes }
  , { walsCode := "was", language := "Washo", iso := "was", value := .possessivePrefixes }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .possessivePrefixes }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .possessiveSuffixes }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .possessiveSuffixes }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .possessivePrefixes }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .possessiveSuffixes }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .possessiveSuffixes }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .possessivePrefixes }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .possessivePrefixes }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .possessivePrefixes }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noPossessiveAffixes }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noPossessiveAffixes }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .noPossessiveAffixes }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .possessivePrefixes }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .noPossessiveAffixes }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .possessiveSuffixes }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .possessiveSuffixes }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .possessiveSuffixes }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .noPossessiveAffixes }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .possessivePrefixes }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .possessivePrefixes }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .possessivePrefixes }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .possessivePrefixes }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .noPossessiveAffixes }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .possessiveSuffixes }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .prefixesAndSuffixes }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .possessivePrefixes }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .noPossessiveAffixes }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .possessiveSuffixes }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .possessiveSuffixes }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .possessivePrefixes }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noPossessiveAffixes }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .noPossessiveAffixes }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .noPossessiveAffixes }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .possessivePrefixes }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noPossessiveAffixes }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .possessiveSuffixes }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .noPossessiveAffixes }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noPossessiveAffixes }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .possessivePrefixes }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .possessiveSuffixes }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noPossessiveAffixes }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .possessiveSuffixes }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .possessiveSuffixes }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .possessivePrefixes }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .noPossessiveAffixes }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .possessiveSuffixes }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .possessivePrefixes }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .possessiveSuffixes }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .possessiveSuffixes }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .possessiveSuffixes }
  , { walsCode := "zen", language := "Zenaga", iso := "zen", value := .possessiveSuffixes }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .noPossessiveAffixes }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .possessivePrefixes }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .possessivePrefixes }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noPossessiveAffixes }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .possessivePrefixes }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .possessivePrefixes }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .noPossessiveAffixes }
  ]

/-- Complete WALS 57A dataset (902 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 902 := by native_decide

theorem count_possessivePrefixes :
    (allData.filter (·.value == .possessivePrefixes)).length = 255 := by native_decide
theorem count_possessiveSuffixes :
    (allData.filter (·.value == .possessiveSuffixes)).length = 355 := by native_decide
theorem count_prefixesAndSuffixes :
    (allData.filter (·.value == .prefixesAndSuffixes)).length = 32 := by native_decide
theorem count_noPossessiveAffixes :
    (allData.filter (·.value == .noPossessiveAffixes)).length = 260 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F57A
