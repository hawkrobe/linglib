/-!
# WALS Feature 69A: Position of Tense-Aspect Affixes
@cite{dahl-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 69A`.

Chapter 69, 1131 languages.
-/

namespace Core.WALS.F69A

/-- WALS 69A values. -/
inductive TenseAspectAffixPosition where
  | tenseAspectPrefixes  -- Tense-aspect prefixes (153 languages)
  | tenseAspectSuffixes  -- Tense-aspect suffixes (667 languages)
  | tenseAspectTone  -- Tense-aspect tone (13 languages)
  | mixedType  -- Mixed type (146 languages)
  | noTenseAspectInflection  -- No tense-aspect inflection (152 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 69A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : TenseAspectAffixPosition
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .tenseAspectSuffixes }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .tenseAspectSuffixes }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .tenseAspectSuffixes }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .tenseAspectSuffixes }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .tenseAspectSuffixes }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noTenseAspectInflection }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noTenseAspectInflection }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .tenseAspectSuffixes }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .tenseAspectPrefixes }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .tenseAspectSuffixes }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .tenseAspectSuffixes }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .tenseAspectSuffixes }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .noTenseAspectInflection }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .tenseAspectPrefixes }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .tenseAspectSuffixes }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .tenseAspectSuffixes }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .tenseAspectSuffixes }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .mixedType }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .tenseAspectSuffixes }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .tenseAspectPrefixes }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .tenseAspectPrefixes }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .noTenseAspectInflection }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .tenseAspectPrefixes }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .tenseAspectSuffixes }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .tenseAspectSuffixes }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .tenseAspectSuffixes }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .tenseAspectSuffixes }
  , { walsCode := "alc", language := "Allentiac", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noTenseAspectInflection }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .tenseAspectSuffixes }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .tenseAspectSuffixes }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .tenseAspectSuffixes }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .noTenseAspectInflection }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .tenseAspectSuffixes }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .tenseAspectSuffixes }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .mixedType }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .tenseAspectPrefixes }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .tenseAspectSuffixes }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .noTenseAspectInflection }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .tenseAspectSuffixes }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .noTenseAspectInflection }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .mixedType }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .tenseAspectSuffixes }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .tenseAspectSuffixes }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .mixedType }
  , { walsCode := "ayi", language := "Anyi", iso := "any", value := .tenseAspectPrefixes }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .mixedType }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .tenseAspectSuffixes }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .tenseAspectPrefixes }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .tenseAspectSuffixes }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .tenseAspectSuffixes }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .tenseAspectSuffixes }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .tenseAspectSuffixes }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .mixedType }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .mixedType }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .mixedType }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .mixedType }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .mixedType }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .tenseAspectSuffixes }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .tenseAspectPrefixes }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .tenseAspectSuffixes }
  , { walsCode := "ari", language := "Aribwatsa", iso := "laz", value := .tenseAspectPrefixes }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .tenseAspectSuffixes }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .tenseAspectSuffixes }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .noTenseAspectInflection }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .tenseAspectSuffixes }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .tenseAspectSuffixes }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .tenseAspectSuffixes }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .tenseAspectSuffixes }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .tenseAspectSuffixes }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .mixedType }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .tenseAspectSuffixes }
  , { walsCode := "ats", language := "Atsugewi", iso := "atw", value := .mixedType }
  , { walsCode := "au", language := "Au", iso := "avt", value := .noTenseAspectInflection }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .tenseAspectSuffixes }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .tenseAspectSuffixes }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .tenseAspectSuffixes }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .tenseAspectSuffixes }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .tenseAspectSuffixes }
  , { walsCode := "awy", language := "Awyi", iso := "auw", value := .mixedType }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .tenseAspectSuffixes }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .tenseAspectSuffixes }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .mixedType }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .tenseAspectSuffixes }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .tenseAspectSuffixes }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .mixedType }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .tenseAspectPrefixes }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .noTenseAspectInflection }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .tenseAspectPrefixes }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .tenseAspectSuffixes }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .tenseAspectSuffixes }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .tenseAspectSuffixes }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .tenseAspectPrefixes }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .tenseAspectSuffixes }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .tenseAspectTone }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .tenseAspectSuffixes }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .tenseAspectPrefixes }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .tenseAspectSuffixes }
  , { walsCode := "mug", language := "Bargam", iso := "mlp", value := .mixedType }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .tenseAspectPrefixes }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .tenseAspectSuffixes }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .tenseAspectSuffixes }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .tenseAspectSuffixes }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .mixedType }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .tenseAspectSuffixes }
  , { walsCode := "bau", language := "Bau", iso := "bbd", value := .tenseAspectSuffixes }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .tenseAspectSuffixes }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .tenseAspectSuffixes }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noTenseAspectInflection }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .tenseAspectSuffixes }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .tenseAspectSuffixes }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .tenseAspectSuffixes }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .mixedType }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .tenseAspectPrefixes }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .mixedType }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .mixedType }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .tenseAspectPrefixes }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .mixedType }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .tenseAspectSuffixes }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .mixedType }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .tenseAspectSuffixes }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .tenseAspectSuffixes }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .noTenseAspectInflection }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .mixedType }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .mixedType }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .tenseAspectSuffixes }
  , { walsCode := "bnr", language := "Bilinarra", iso := "nbj", value := .tenseAspectSuffixes }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .tenseAspectSuffixes }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .tenseAspectSuffixes }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .tenseAspectSuffixes }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .tenseAspectSuffixes }
  , { walsCode := "big", language := "Binga", iso := "yul", value := .tenseAspectPrefixes }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .mixedType }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .tenseAspectSuffixes }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .tenseAspectPrefixes }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .tenseAspectPrefixes }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .mixedType }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .tenseAspectSuffixes }
  , { walsCode := "boi", language := "Boiken", iso := "bzf", value := .tenseAspectSuffixes }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .tenseAspectPrefixes }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .tenseAspectPrefixes }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .tenseAspectSuffixes }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .tenseAspectSuffixes }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .tenseAspectSuffixes }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .tenseAspectSuffixes }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .tenseAspectSuffixes }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .mixedType }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .tenseAspectPrefixes }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .tenseAspectSuffixes }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .tenseAspectSuffixes }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .tenseAspectSuffixes }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .noTenseAspectInflection }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .tenseAspectSuffixes }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .tenseAspectSuffixes }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .tenseAspectSuffixes }
  , { walsCode := "bmr", language := "Burum", iso := "bmu", value := .tenseAspectSuffixes }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .tenseAspectSuffixes }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .tenseAspectSuffixes }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .tenseAspectPrefixes }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .tenseAspectSuffixes }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .tenseAspectSuffixes }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .tenseAspectPrefixes }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .tenseAspectSuffixes }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noTenseAspectInflection }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .tenseAspectSuffixes }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .tenseAspectSuffixes }
  , { walsCode := "car", language := "Carib", iso := "car", value := .tenseAspectSuffixes }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .tenseAspectSuffixes }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .tenseAspectSuffixes }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .tenseAspectSuffixes }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .mixedType }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .tenseAspectPrefixes }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .mixedType }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .tenseAspectSuffixes }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .tenseAspectSuffixes }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .tenseAspectSuffixes }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .tenseAspectSuffixes }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .tenseAspectPrefixes }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .mixedType }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .tenseAspectSuffixes }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .tenseAspectSuffixes }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .tenseAspectSuffixes }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .tenseAspectPrefixes }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .tenseAspectSuffixes }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .noTenseAspectInflection }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .noTenseAspectInflection }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .mixedType }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .mixedType }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .tenseAspectPrefixes }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .mixedType }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .mixedType }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .tenseAspectSuffixes }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .tenseAspectPrefixes }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .tenseAspectPrefixes }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .tenseAspectSuffixes }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .tenseAspectSuffixes }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .tenseAspectSuffixes }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .tenseAspectSuffixes }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .tenseAspectSuffixes }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noTenseAspectInflection }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .tenseAspectPrefixes }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .mixedType }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .tenseAspectSuffixes }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .tenseAspectSuffixes }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .tenseAspectSuffixes }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .tenseAspectSuffixes }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .noTenseAspectInflection }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .tenseAspectPrefixes }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .tenseAspectSuffixes }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .tenseAspectSuffixes }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .noTenseAspectInflection }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .tenseAspectSuffixes }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .tenseAspectPrefixes }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .tenseAspectSuffixes }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .tenseAspectSuffixes }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .tenseAspectSuffixes }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .mixedType }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .noTenseAspectInflection }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .tenseAspectSuffixes }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .mixedType }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .tenseAspectSuffixes }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .tenseAspectSuffixes }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .tenseAspectSuffixes }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .tenseAspectSuffixes }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .tenseAspectSuffixes }
  , { walsCode := "des", language := "Desano", iso := "des", value := .tenseAspectSuffixes }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .tenseAspectSuffixes }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .tenseAspectSuffixes }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .tenseAspectSuffixes }
  , { walsCode := "dhb", language := "Dharumbal", iso := "xgm", value := .tenseAspectSuffixes }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .tenseAspectSuffixes }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .mixedType }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .tenseAspectSuffixes }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .tenseAspectSuffixes }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .tenseAspectSuffixes }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noTenseAspectInflection }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .mixedType }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .tenseAspectSuffixes }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .tenseAspectSuffixes }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .tenseAspectSuffixes }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .tenseAspectSuffixes }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .tenseAspectSuffixes }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .tenseAspectSuffixes }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .tenseAspectSuffixes }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .tenseAspectSuffixes }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .tenseAspectSuffixes }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .tenseAspectSuffixes }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .tenseAspectSuffixes }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .tenseAspectSuffixes }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .mixedType }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .tenseAspectTone }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noTenseAspectInflection }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .tenseAspectSuffixes }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .tenseAspectSuffixes }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .tenseAspectSuffixes }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .tenseAspectSuffixes }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .tenseAspectSuffixes }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .tenseAspectSuffixes }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .noTenseAspectInflection }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .tenseAspectSuffixes }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .tenseAspectSuffixes }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .tenseAspectSuffixes }
  , { walsCode := "ene", language := "Enets", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .tenseAspectTone }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .mixedType }
  , { walsCode := "eng", language := "English", iso := "eng", value := .tenseAspectSuffixes }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .tenseAspectSuffixes }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .tenseAspectSuffixes }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .tenseAspectSuffixes }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .tenseAspectSuffixes }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .tenseAspectSuffixes }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .tenseAspectPrefixes }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .tenseAspectSuffixes }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noTenseAspectInflection }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .tenseAspectSuffixes }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .tenseAspectSuffixes }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .noTenseAspectInflection }
  , { walsCode := "for", language := "Fore", iso := "for", value := .tenseAspectSuffixes }
  , { walsCode := "fre", language := "French", iso := "fra", value := .tenseAspectSuffixes }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .tenseAspectSuffixes }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .tenseAspectSuffixes }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .noTenseAspectInflection }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .tenseAspectSuffixes }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .tenseAspectSuffixes }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .tenseAspectSuffixes }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .mixedType }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .tenseAspectSuffixes }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .tenseAspectSuffixes }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .tenseAspectSuffixes }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .tenseAspectSuffixes }
  , { walsCode := "grs", language := "Garus", iso := "gyb", value := .tenseAspectSuffixes }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .tenseAspectSuffixes }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .mixedType }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .tenseAspectSuffixes }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .tenseAspectSuffixes }
  , { walsCode := "ger", language := "German", iso := "deu", value := .tenseAspectSuffixes }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .tenseAspectSuffixes }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .tenseAspectSuffixes }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .tenseAspectSuffixes }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .noTenseAspectInflection }
  , { walsCode := "gog", language := "Gogodala", iso := "ggw", value := .tenseAspectSuffixes }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .tenseAspectTone }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .tenseAspectSuffixes }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .tenseAspectSuffixes }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .tenseAspectPrefixes }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .tenseAspectSuffixes }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .tenseAspectSuffixes }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .tenseAspectSuffixes }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .tenseAspectSuffixes }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noTenseAspectInflection }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .tenseAspectSuffixes }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .tenseAspectSuffixes }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .tenseAspectSuffixes }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .tenseAspectSuffixes }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .tenseAspectSuffixes }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .tenseAspectPrefixes }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .tenseAspectSuffixes }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .mixedType }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .mixedType }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .tenseAspectSuffixes }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .tenseAspectSuffixes }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .tenseAspectSuffixes }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .tenseAspectPrefixes }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .tenseAspectSuffixes }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .tenseAspectSuffixes }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .tenseAspectSuffixes }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .mixedType }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .tenseAspectSuffixes }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noTenseAspectInflection }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noTenseAspectInflection }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .tenseAspectPrefixes }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .tenseAspectSuffixes }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .mixedType }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .tenseAspectSuffixes }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .tenseAspectSuffixes }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .noTenseAspectInflection }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noTenseAspectInflection }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .tenseAspectSuffixes }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .tenseAspectSuffixes }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .tenseAspectSuffixes }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .tenseAspectSuffixes }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noTenseAspectInflection }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .mixedType }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .tenseAspectSuffixes }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .tenseAspectSuffixes }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .tenseAspectSuffixes }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .tenseAspectPrefixes }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .tenseAspectSuffixes }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .tenseAspectSuffixes }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .tenseAspectSuffixes }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .mixedType }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .noTenseAspectInflection }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noTenseAspectInflection }
  , { walsCode := "iat", language := "Iatmul", iso := "ian", value := .tenseAspectSuffixes }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noTenseAspectInflection }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .tenseAspectSuffixes }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .tenseAspectPrefixes }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .tenseAspectPrefixes }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .tenseAspectSuffixes }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .tenseAspectSuffixes }
  , { walsCode := "iha", language := "Iha", iso := "ihp", value := .tenseAspectSuffixes }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .tenseAspectSuffixes }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .tenseAspectSuffixes }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .tenseAspectSuffixes }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .tenseAspectPrefixes }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .tenseAspectSuffixes }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .tenseAspectSuffixes }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .tenseAspectSuffixes }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .tenseAspectSuffixes }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .tenseAspectSuffixes }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .tenseAspectSuffixes }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .tenseAspectSuffixes }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .tenseAspectSuffixes }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noTenseAspectInflection }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .tenseAspectPrefixes }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .mixedType }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .tenseAspectSuffixes }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .tenseAspectSuffixes }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .mixedType }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .tenseAspectSuffixes }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .tenseAspectPrefixes }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .mixedType }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .tenseAspectPrefixes }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .mixedType }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .tenseAspectPrefixes }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .mixedType }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .tenseAspectSuffixes }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .mixedType }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .tenseAspectSuffixes }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .tenseAspectSuffixes }
  , { walsCode := "jwr", language := "Jarawara", iso := "jaa", value := .tenseAspectSuffixes }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .tenseAspectSuffixes }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .noTenseAspectInflection }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .noTenseAspectInflection }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .tenseAspectSuffixes }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .noTenseAspectInflection }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .noTenseAspectInflection }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noTenseAspectInflection }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .mixedType }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .tenseAspectSuffixes }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .tenseAspectPrefixes }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .mixedType }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .noTenseAspectInflection }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .tenseAspectSuffixes }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .mixedType }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .tenseAspectSuffixes }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .tenseAspectSuffixes }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .tenseAspectSuffixes }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .noTenseAspectInflection }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .tenseAspectSuffixes }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .tenseAspectPrefixes }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .noTenseAspectInflection }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .tenseAspectSuffixes }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .mixedType }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .mixedType }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .tenseAspectSuffixes }
  , { walsCode := "kbu", language := "Kanembu", iso := "kbl", value := .tenseAspectSuffixes }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .tenseAspectSuffixes }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .tenseAspectSuffixes }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .tenseAspectSuffixes }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .mixedType }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .tenseAspectSuffixes }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .tenseAspectSuffixes }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .tenseAspectSuffixes }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .tenseAspectSuffixes }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .tenseAspectSuffixes }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .noTenseAspectInflection }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .noTenseAspectInflection }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .tenseAspectSuffixes }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .tenseAspectSuffixes }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .noTenseAspectInflection }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .tenseAspectPrefixes }
  , { walsCode := "ktm", language := "Kathlamet", iso := "", value := .mixedType }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .tenseAspectSuffixes }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .tenseAspectSuffixes }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .tenseAspectSuffixes }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noTenseAspectInflection }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .tenseAspectSuffixes }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .tenseAspectPrefixes }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .tenseAspectSuffixes }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .tenseAspectSuffixes }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .tenseAspectSuffixes }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .tenseAspectPrefixes }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .tenseAspectSuffixes }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .tenseAspectSuffixes }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .tenseAspectSuffixes }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .tenseAspectSuffixes }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .tenseAspectSuffixes }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .tenseAspectSuffixes }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .noTenseAspectInflection }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noTenseAspectInflection }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .tenseAspectSuffixes }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noTenseAspectInflection }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noTenseAspectInflection }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .mixedType }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .tenseAspectPrefixes }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .tenseAspectPrefixes }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .noTenseAspectInflection }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .tenseAspectSuffixes }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .tenseAspectPrefixes }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .tenseAspectSuffixes }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .tenseAspectSuffixes }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .tenseAspectSuffixes }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .tenseAspectPrefixes }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .noTenseAspectInflection }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .tenseAspectTone }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .tenseAspectSuffixes }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .tenseAspectSuffixes }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .tenseAspectSuffixes }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .tenseAspectSuffixes }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .tenseAspectSuffixes }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .tenseAspectSuffixes }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .tenseAspectSuffixes }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .tenseAspectSuffixes }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .tenseAspectSuffixes }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .noTenseAspectInflection }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .tenseAspectSuffixes }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .noTenseAspectInflection }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .mixedType }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .tenseAspectSuffixes }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .tenseAspectSuffixes }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .noTenseAspectInflection }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .tenseAspectSuffixes }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .tenseAspectSuffixes }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .tenseAspectSuffixes }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .tenseAspectSuffixes }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .mixedType }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noTenseAspectInflection }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .tenseAspectSuffixes }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noTenseAspectInflection }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noTenseAspectInflection }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .tenseAspectSuffixes }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .mixedType }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .mixedType }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .tenseAspectSuffixes }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .tenseAspectSuffixes }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .tenseAspectSuffixes }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .tenseAspectSuffixes }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .tenseAspectSuffixes }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .tenseAspectSuffixes }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .mixedType }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .mixedType }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .tenseAspectSuffixes }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noTenseAspectInflection }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .tenseAspectSuffixes }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .tenseAspectSuffixes }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .tenseAspectSuffixes }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .tenseAspectSuffixes }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .tenseAspectPrefixes }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .tenseAspectSuffixes }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .tenseAspectSuffixes }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .tenseAspectSuffixes }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .tenseAspectSuffixes }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .tenseAspectSuffixes }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .mixedType }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .tenseAspectSuffixes }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .tenseAspectSuffixes }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .tenseAspectPrefixes }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noTenseAspectInflection }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .tenseAspectSuffixes }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .noTenseAspectInflection }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noTenseAspectInflection }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .mixedType }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .tenseAspectSuffixes }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .noTenseAspectInflection }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .tenseAspectTone }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noTenseAspectInflection }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .mixedType }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .mixedType }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .tenseAspectSuffixes }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .mixedType }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .tenseAspectSuffixes }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .mixedType }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .tenseAspectPrefixes }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .tenseAspectPrefixes }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .tenseAspectSuffixes }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .tenseAspectSuffixes }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .tenseAspectSuffixes }
  , { walsCode := "les", language := "Lese", iso := "les", value := .tenseAspectPrefixes }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .tenseAspectPrefixes }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .tenseAspectSuffixes }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .tenseAspectSuffixes }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .tenseAspectSuffixes }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .mixedType }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .tenseAspectTone }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .tenseAspectSuffixes }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .tenseAspectSuffixes }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .mixedType }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .noTenseAspectInflection }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .noTenseAspectInflection }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .tenseAspectSuffixes }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .noTenseAspectInflection }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .tenseAspectPrefixes }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .tenseAspectPrefixes }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .tenseAspectSuffixes }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .mixedType }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .tenseAspectSuffixes }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .tenseAspectPrefixes }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .tenseAspectPrefixes }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .tenseAspectPrefixes }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .tenseAspectPrefixes }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .tenseAspectTone }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .mixedType }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .tenseAspectSuffixes }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .tenseAspectSuffixes }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .tenseAspectSuffixes }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .tenseAspectSuffixes }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .noTenseAspectInflection }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .tenseAspectSuffixes }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .tenseAspectSuffixes }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .tenseAspectSuffixes }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .tenseAspectSuffixes }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .tenseAspectPrefixes }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .tenseAspectSuffixes }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .noTenseAspectInflection }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .tenseAspectPrefixes }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .tenseAspectPrefixes }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .tenseAspectPrefixes }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noTenseAspectInflection }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .tenseAspectPrefixes }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .mixedType }
  , { walsCode := "mmi", language := "Mambai", iso := "mcs", value := .tenseAspectSuffixes }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .noTenseAspectInflection }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .tenseAspectSuffixes }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .tenseAspectSuffixes }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .tenseAspectSuffixes }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .tenseAspectSuffixes }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .tenseAspectSuffixes }
  , { walsCode := "mem", language := "Manem", iso := "jet", value := .tenseAspectSuffixes }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .mixedType }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .tenseAspectSuffixes }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .noTenseAspectInflection }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .tenseAspectSuffixes }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .tenseAspectPrefixes }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .tenseAspectSuffixes }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noTenseAspectInflection }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .tenseAspectSuffixes }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .tenseAspectSuffixes }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noTenseAspectInflection }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .tenseAspectSuffixes }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .tenseAspectSuffixes }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .mixedType }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .tenseAspectSuffixes }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .tenseAspectSuffixes }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .tenseAspectPrefixes }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .tenseAspectSuffixes }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .tenseAspectSuffixes }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .tenseAspectSuffixes }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .tenseAspectTone }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .mixedType }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .tenseAspectSuffixes }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .tenseAspectSuffixes }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .noTenseAspectInflection }
  , { walsCode := "mtk", language := "Matukar", iso := "mjk", value := .tenseAspectSuffixes }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .tenseAspectPrefixes }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .noTenseAspectInflection }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .tenseAspectSuffixes }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noTenseAspectInflection }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .tenseAspectTone }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .tenseAspectPrefixes }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .tenseAspectPrefixes }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .noTenseAspectInflection }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .tenseAspectSuffixes }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .mixedType }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .tenseAspectSuffixes }
  , { walsCode := "mhk", language := "Mehek", iso := "nux", value := .tenseAspectSuffixes }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .mixedType }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .tenseAspectSuffixes }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .noTenseAspectInflection }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .tenseAspectSuffixes }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .tenseAspectPrefixes }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .mixedType }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .mixedType }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .tenseAspectSuffixes }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .noTenseAspectInflection }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .tenseAspectSuffixes }
  , { walsCode := "mkr", language := "Mikarew", iso := "msy", value := .tenseAspectSuffixes }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .mixedType }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .tenseAspectSuffixes }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noTenseAspectInflection }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .tenseAspectSuffixes }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .tenseAspectSuffixes }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .tenseAspectSuffixes }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .tenseAspectSuffixes }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .tenseAspectPrefixes }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .tenseAspectPrefixes }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .mixedType }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .tenseAspectPrefixes }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .noTenseAspectInflection }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noTenseAspectInflection }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .mixedType }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .tenseAspectSuffixes }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .tenseAspectSuffixes }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .mixedType }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .mixedType }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .tenseAspectSuffixes }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .tenseAspectSuffixes }
  , { walsCode := "mqf", language := "Momuna", iso := "mqf", value := .tenseAspectSuffixes }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .noTenseAspectInflection }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .mixedType }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .tenseAspectSuffixes }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .tenseAspectSuffixes }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .tenseAspectSuffixes }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .tenseAspectSuffixes }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .tenseAspectSuffixes }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .tenseAspectPrefixes }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .tenseAspectSuffixes }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .tenseAspectSuffixes }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .noTenseAspectInflection }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .tenseAspectSuffixes }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .noTenseAspectInflection }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .tenseAspectPrefixes }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .tenseAspectSuffixes }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .tenseAspectSuffixes }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .tenseAspectTone }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .tenseAspectPrefixes }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .tenseAspectSuffixes }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .tenseAspectPrefixes }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .noTenseAspectInflection }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .mixedType }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .mixedType }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .tenseAspectSuffixes }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .tenseAspectPrefixes }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .tenseAspectSuffixes }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .tenseAspectPrefixes }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .tenseAspectPrefixes }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .tenseAspectSuffixes }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .tenseAspectSuffixes }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .tenseAspectSuffixes }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .tenseAspectSuffixes }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .tenseAspectSuffixes }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .tenseAspectSuffixes }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .tenseAspectSuffixes }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .tenseAspectSuffixes }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .tenseAspectSuffixes }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .mixedType }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noTenseAspectInflection }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .tenseAspectSuffixes }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .mixedType }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .noTenseAspectInflection }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .mixedType }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .tenseAspectSuffixes }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .tenseAspectSuffixes }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .tenseAspectSuffixes }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .tenseAspectPrefixes }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .mixedType }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .mixedType }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .mixedType }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .tenseAspectSuffixes }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .tenseAspectPrefixes }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .tenseAspectSuffixes }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noTenseAspectInflection }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .tenseAspectSuffixes }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .mixedType }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .tenseAspectSuffixes }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .tenseAspectSuffixes }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .tenseAspectSuffixes }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .tenseAspectSuffixes }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .tenseAspectSuffixes }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .tenseAspectSuffixes }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noTenseAspectInflection }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .tenseAspectSuffixes }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .tenseAspectSuffixes }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .tenseAspectSuffixes }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .noTenseAspectInflection }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .tenseAspectSuffixes }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .tenseAspectSuffixes }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .tenseAspectSuffixes }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .tenseAspectSuffixes }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .tenseAspectSuffixes }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .tenseAspectSuffixes }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .mixedType }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .tenseAspectSuffixes }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .tenseAspectSuffixes }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .tenseAspectPrefixes }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .tenseAspectSuffixes }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .tenseAspectSuffixes }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .noTenseAspectInflection }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .tenseAspectSuffixes }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .tenseAspectPrefixes }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .tenseAspectPrefixes }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .tenseAspectSuffixes }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .tenseAspectSuffixes }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .tenseAspectSuffixes }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .tenseAspectSuffixes }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .noTenseAspectInflection }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .tenseAspectSuffixes }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .noTenseAspectInflection }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noTenseAspectInflection }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .tenseAspectSuffixes }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noTenseAspectInflection }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .mixedType }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .tenseAspectSuffixes }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .tenseAspectSuffixes }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .mixedType }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .tenseAspectPrefixes }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .tenseAspectSuffixes }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .tenseAspectPrefixes }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .tenseAspectPrefixes }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .tenseAspectPrefixes }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .tenseAspectSuffixes }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .tenseAspectSuffixes }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .tenseAspectSuffixes }
  , { walsCode := "one", language := "One", iso := "aun", value := .tenseAspectSuffixes }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .mixedType }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .tenseAspectSuffixes }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .tenseAspectSuffixes }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .tenseAspectTone }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .tenseAspectSuffixes }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .tenseAspectSuffixes }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .tenseAspectSuffixes }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .tenseAspectSuffixes }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .tenseAspectSuffixes }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .tenseAspectSuffixes }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .tenseAspectSuffixes }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .tenseAspectPrefixes }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .tenseAspectPrefixes }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .tenseAspectSuffixes }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .tenseAspectSuffixes }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .tenseAspectPrefixes }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .tenseAspectSuffixes }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .mixedType }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .tenseAspectPrefixes }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .tenseAspectSuffixes }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .tenseAspectPrefixes }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .tenseAspectSuffixes }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .tenseAspectSuffixes }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .tenseAspectPrefixes }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .tenseAspectSuffixes }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .tenseAspectSuffixes }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .noTenseAspectInflection }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .tenseAspectSuffixes }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .tenseAspectSuffixes }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .tenseAspectSuffixes }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .mixedType }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .mixedType }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .tenseAspectSuffixes }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .tenseAspectSuffixes }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .tenseAspectSuffixes }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .tenseAspectSuffixes }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .tenseAspectSuffixes }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .tenseAspectSuffixes }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .tenseAspectSuffixes }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .tenseAspectSuffixes }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .mixedType }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .noTenseAspectInflection }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .mixedType }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .tenseAspectSuffixes }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .tenseAspectSuffixes }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .tenseAspectSuffixes }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .tenseAspectSuffixes }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .tenseAspectSuffixes }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .noTenseAspectInflection }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .tenseAspectSuffixes }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .noTenseAspectInflection }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .tenseAspectSuffixes }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .tenseAspectSuffixes }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .tenseAspectSuffixes }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .tenseAspectPrefixes }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .tenseAspectSuffixes }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .mixedType }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .tenseAspectSuffixes }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .tenseAspectSuffixes }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .tenseAspectSuffixes }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .tenseAspectSuffixes }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noTenseAspectInflection }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .tenseAspectSuffixes }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .tenseAspectSuffixes }
  , { walsCode := "rmb", language := "Rembarnga", iso := "rmb", value := .tenseAspectSuffixes }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .tenseAspectSuffixes }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .tenseAspectSuffixes }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .tenseAspectSuffixes }
  , { walsCode := "ria", language := "Riantana", iso := "ran", value := .noTenseAspectInflection }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .mixedType }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .tenseAspectSuffixes }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .tenseAspectSuffixes }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .tenseAspectSuffixes }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .tenseAspectSuffixes }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .tenseAspectPrefixes }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .tenseAspectSuffixes }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .tenseAspectSuffixes }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .tenseAspectPrefixes }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .tenseAspectPrefixes }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .mixedType }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .mixedType }
  , { walsCode := "saa", language := "Sa'a", iso := "apb", value := .noTenseAspectInflection }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .tenseAspectSuffixes }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noTenseAspectInflection }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .mixedType }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .tenseAspectSuffixes }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noTenseAspectInflection }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .tenseAspectSuffixes }
  , { walsCode := "nmd", language := "Samo", iso := "smq", value := .tenseAspectSuffixes }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .tenseAspectPrefixes }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .tenseAspectSuffixes }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noTenseAspectInflection }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .tenseAspectSuffixes }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .tenseAspectSuffixes }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noTenseAspectInflection }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .mixedType }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .tenseAspectSuffixes }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .mixedType }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .tenseAspectSuffixes }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .tenseAspectSuffixes }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .tenseAspectSuffixes }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .tenseAspectSuffixes }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .tenseAspectSuffixes }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .tenseAspectSuffixes }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .tenseAspectSuffixes }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .tenseAspectSuffixes }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .noTenseAspectInflection }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .tenseAspectPrefixes }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .tenseAspectPrefixes }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .tenseAspectSuffixes }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .mixedType }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .mixedType }
  , { walsCode := "shd", language := "Sherdukpen", iso := "sdp", value := .tenseAspectSuffixes }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .tenseAspectSuffixes }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .tenseAspectPrefixes }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .tenseAspectSuffixes }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .tenseAspectSuffixes }
  , { walsCode := "shy", language := "Shira Yughur", iso := "yuy", value := .tenseAspectSuffixes }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .tenseAspectSuffixes }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .tenseAspectPrefixes }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .tenseAspectSuffixes }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .noTenseAspectInflection }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .tenseAspectSuffixes }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .tenseAspectSuffixes }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .tenseAspectSuffixes }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .noTenseAspectInflection }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .tenseAspectPrefixes }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .tenseAspectSuffixes }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .noTenseAspectInflection }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .tenseAspectSuffixes }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .tenseAspectPrefixes }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .tenseAspectSuffixes }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .tenseAspectSuffixes }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .noTenseAspectInflection }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .tenseAspectSuffixes }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .tenseAspectTone }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .tenseAspectPrefixes }
  , { walsCode := "so", language := "So", iso := "teu", value := .tenseAspectPrefixes }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .mixedType }
  , { walsCode := "som", language := "Somali", iso := "som", value := .tenseAspectSuffixes }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .mixedType }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .tenseAspectPrefixes }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .tenseAspectSuffixes }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .noTenseAspectInflection }
  , { walsCode := "sub", language := "Subiya", iso := "sbs", value := .tenseAspectPrefixes }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .tenseAspectSuffixes }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .tenseAspectSuffixes }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .tenseAspectPrefixes }
  , { walsCode := "slg", language := "Sulung", iso := "suv", value := .tenseAspectSuffixes }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noTenseAspectInflection }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .tenseAspectSuffixes }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .mixedType }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .tenseAspectSuffixes }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .tenseAspectPrefixes }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .tenseAspectSuffixes }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .tenseAspectSuffixes }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .tenseAspectPrefixes }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .tenseAspectSuffixes }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .tenseAspectSuffixes }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .tenseAspectSuffixes }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .tenseAspectPrefixes }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .noTenseAspectInflection }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .tenseAspectSuffixes }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .mixedType }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .tenseAspectSuffixes }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .tenseAspectSuffixes }
  , { walsCode := "tmg", language := "Tamagario", iso := "tcg", value := .tenseAspectSuffixes }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .tenseAspectSuffixes }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .tenseAspectSuffixes }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .tenseAspectPrefixes }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .tenseAspectSuffixes }
  , { walsCode := "tbx", language := "Tangbe", iso := "skj", value := .tenseAspectSuffixes }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .tenseAspectSuffixes }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .tenseAspectSuffixes }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .tenseAspectSuffixes }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .tenseAspectSuffixes }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .tenseAspectPrefixes }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .tenseAspectSuffixes }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .tenseAspectSuffixes }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .tenseAspectPrefixes }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .tenseAspectPrefixes }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .tenseAspectSuffixes }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .tenseAspectPrefixes }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .tenseAspectPrefixes }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .mixedType }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .tenseAspectPrefixes }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .tenseAspectSuffixes }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .noTenseAspectInflection }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .mixedType }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .mixedType }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .tenseAspectSuffixes }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .tenseAspectSuffixes }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .noTenseAspectInflection }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .tenseAspectSuffixes }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .mixedType }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .noTenseAspectInflection }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noTenseAspectInflection }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .tenseAspectSuffixes }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .tenseAspectSuffixes }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .tenseAspectSuffixes }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .mixedType }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noTenseAspectInflection }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noTenseAspectInflection }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .tenseAspectSuffixes }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .tenseAspectSuffixes }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .mixedType }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noTenseAspectInflection }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .tenseAspectSuffixes }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .tenseAspectSuffixes }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .tenseAspectPrefixes }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .tenseAspectPrefixes }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .mixedType }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .tenseAspectSuffixes }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .mixedType }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noTenseAspectInflection }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .tenseAspectPrefixes }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .tenseAspectPrefixes }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .noTenseAspectInflection }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .tenseAspectSuffixes }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .tenseAspectSuffixes }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .mixedType }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .mixedType }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .tenseAspectPrefixes }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .tenseAspectSuffixes }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .tenseAspectSuffixes }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .tenseAspectSuffixes }
  ]

private def allData_2 : List Datapoint :=
  [ { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noTenseAspectInflection }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .tenseAspectSuffixes }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .tenseAspectPrefixes }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .tenseAspectSuffixes }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .tenseAspectPrefixes }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .tenseAspectPrefixes }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .tenseAspectSuffixes }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .tenseAspectSuffixes }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .tenseAspectPrefixes }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .tenseAspectSuffixes }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .mixedType }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .tenseAspectSuffixes }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .tenseAspectSuffixes }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noTenseAspectInflection }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .tenseAspectSuffixes }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .mixedType }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .mixedType }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .tenseAspectSuffixes }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .tenseAspectSuffixes }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .tenseAspectSuffixes }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .tenseAspectSuffixes }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .tenseAspectSuffixes }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .tenseAspectPrefixes }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noTenseAspectInflection }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .tenseAspectSuffixes }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noTenseAspectInflection }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .tenseAspectSuffixes }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noTenseAspectInflection }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .noTenseAspectInflection }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .tenseAspectSuffixes }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noTenseAspectInflection }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .tenseAspectSuffixes }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .tenseAspectSuffixes }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .tenseAspectSuffixes }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .tenseAspectSuffixes }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .mixedType }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .tenseAspectPrefixes }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noTenseAspectInflection }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .mixedType }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .tenseAspectSuffixes }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .tenseAspectSuffixes }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .noTenseAspectInflection }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .tenseAspectSuffixes }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .tenseAspectSuffixes }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .tenseAspectSuffixes }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .tenseAspectSuffixes }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .tenseAspectSuffixes }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .tenseAspectPrefixes }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .tenseAspectSuffixes }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noTenseAspectInflection }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .noTenseAspectInflection }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .tenseAspectSuffixes }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .tenseAspectSuffixes }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .tenseAspectSuffixes }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .mixedType }
  , { walsCode := "was", language := "Washo", iso := "was", value := .tenseAspectSuffixes }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .tenseAspectSuffixes }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .tenseAspectSuffixes }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .tenseAspectSuffixes }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .tenseAspectSuffixes }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .tenseAspectSuffixes }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .tenseAspectSuffixes }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .tenseAspectSuffixes }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noTenseAspectInflection }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .mixedType }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .tenseAspectSuffixes }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .tenseAspectSuffixes }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .tenseAspectSuffixes }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .tenseAspectSuffixes }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .tenseAspectSuffixes }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noTenseAspectInflection }
  , { walsCode := "wog", language := "Wogamusin", iso := "wog", value := .tenseAspectSuffixes }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .tenseAspectSuffixes }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .noTenseAspectInflection }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .noTenseAspectInflection }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .mixedType }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .noTenseAspectInflection }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .mixedType }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .noTenseAspectInflection }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .mixedType }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .tenseAspectSuffixes }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .tenseAspectSuffixes }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .tenseAspectSuffixes }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .tenseAspectSuffixes }
  , { walsCode := "yns", language := "Yansi", iso := "yns", value := .tenseAspectPrefixes }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .tenseAspectPrefixes }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .noTenseAspectInflection }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .tenseAspectPrefixes }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .tenseAspectSuffixes }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .tenseAspectSuffixes }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .tenseAspectSuffixes }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .noTenseAspectInflection }
  , { walsCode := "yyg", language := "Yaygir", iso := "xya", value := .tenseAspectSuffixes }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .mixedType }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .tenseAspectSuffixes }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .tenseAspectPrefixes }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .tenseAspectSuffixes }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .tenseAspectSuffixes }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .tenseAspectSuffixes }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .tenseAspectSuffixes }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .tenseAspectSuffixes }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noTenseAspectInflection }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .tenseAspectSuffixes }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .tenseAspectSuffixes }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .tenseAspectSuffixes }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .tenseAspectSuffixes }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .noTenseAspectInflection }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .mixedType }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .tenseAspectSuffixes }
  , { walsCode := "yrm", language := "Yurimangí", iso := "", value := .tenseAspectSuffixes }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noTenseAspectInflection }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .tenseAspectSuffixes }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .tenseAspectPrefixes }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .tenseAspectSuffixes }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .tenseAspectPrefixes }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .tenseAspectPrefixes }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .tenseAspectPrefixes }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .tenseAspectPrefixes }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .tenseAspectSuffixes }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .noTenseAspectInflection }
  , { walsCode := "zim", language := "Zimakani", iso := "zik", value := .tenseAspectPrefixes }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .tenseAspectSuffixes }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .tenseAspectSuffixes }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .tenseAspectSuffixes }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .tenseAspectPrefixes }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .tenseAspectSuffixes }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .tenseAspectSuffixes }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .tenseAspectSuffixes }
  ]

/-- Complete WALS 69A dataset (1131 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1131 := by native_decide

theorem count_tenseAspectPrefixes :
    (allData.filter (·.value == .tenseAspectPrefixes)).length = 153 := by native_decide
theorem count_tenseAspectSuffixes :
    (allData.filter (·.value == .tenseAspectSuffixes)).length = 667 := by native_decide
theorem count_tenseAspectTone :
    (allData.filter (·.value == .tenseAspectTone)).length = 13 := by native_decide
theorem count_mixedType :
    (allData.filter (·.value == .mixedType)).length = 146 := by native_decide
theorem count_noTenseAspectInflection :
    (allData.filter (·.value == .noTenseAspectInflection)).length = 152 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F69A
