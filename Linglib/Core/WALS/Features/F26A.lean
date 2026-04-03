import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 26A: Prefixing vs. Suffixing in Inflectional Morphology
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 26A`.

Chapter 26, 969 languages.
-/

namespace Core.WALS.F26A

/-- WALS 26A values. -/
inductive PrefixSuffixPreference where
  | littleAffixation  -- Little affixation (141 languages)
  | stronglySuffixing  -- Strongly suffixing (406 languages)
  | weaklySuffixing  -- Weakly suffixing (123 languages)
  | equalPrefixingAndSuffixing  -- Equal prefixing and suffixing (147 languages)
  | weaklyPrefixing  -- Weakly prefixing (94 languages)
  | strongPrefixing  -- Strong prefixing (58 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint PrefixSuffixPreference) :=
  [ { walsCode := "aar", language := "Aari", iso := "aiw", value := .stronglySuffixing }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .stronglySuffixing }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .equalPrefixingAndSuffixing }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .equalPrefixingAndSuffixing }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .littleAffixation }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .littleAffixation }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .equalPrefixingAndSuffixing }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .equalPrefixingAndSuffixing }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .stronglySuffixing }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .equalPrefixingAndSuffixing }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .littleAffixation }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .weaklyPrefixing }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .stronglySuffixing }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .weaklySuffixing }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .stronglySuffixing }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .equalPrefixingAndSuffixing }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .strongPrefixing }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .littleAffixation }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .stronglySuffixing }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .stronglySuffixing }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .stronglySuffixing }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .stronglySuffixing }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .equalPrefixingAndSuffixing }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .stronglySuffixing }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .stronglySuffixing }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .stronglySuffixing }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .littleAffixation }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .weaklyPrefixing }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .stronglySuffixing }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .weaklySuffixing }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .weaklyPrefixing }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .weaklySuffixing }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .equalPrefixingAndSuffixing }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .littleAffixation }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .littleAffixation }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .stronglySuffixing }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .stronglySuffixing }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .equalPrefixingAndSuffixing }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .littleAffixation }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .weaklySuffixing }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .equalPrefixingAndSuffixing }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .equalPrefixingAndSuffixing }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .stronglySuffixing }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .equalPrefixingAndSuffixing }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .stronglySuffixing }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .weaklySuffixing }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .weaklySuffixing }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .stronglySuffixing }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .weaklySuffixing }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .weaklySuffixing }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .stronglySuffixing }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .weaklyPrefixing }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .stronglySuffixing }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .stronglySuffixing }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .stronglySuffixing }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .littleAffixation }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .stronglySuffixing }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .stronglySuffixing }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .stronglySuffixing }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .stronglySuffixing }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .littleAffixation }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .stronglySuffixing }
  , { walsCode := "au", language := "Au", iso := "avt", value := .weaklyPrefixing }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .stronglySuffixing }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .stronglySuffixing }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .stronglySuffixing }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .weaklySuffixing }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .stronglySuffixing }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .stronglySuffixing }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .stronglySuffixing }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .equalPrefixingAndSuffixing }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .weaklySuffixing }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .weaklyPrefixing }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .littleAffixation }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .littleAffixation }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .littleAffixation }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .littleAffixation }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .stronglySuffixing }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .stronglySuffixing }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .stronglySuffixing }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .weaklyPrefixing }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .stronglySuffixing }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .weaklyPrefixing }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .stronglySuffixing }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .weaklyPrefixing }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .weaklyPrefixing }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .weaklySuffixing }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .weaklySuffixing }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .stronglySuffixing }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .equalPrefixingAndSuffixing }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .stronglySuffixing }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .weaklySuffixing }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .littleAffixation }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .weaklySuffixing }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .weaklySuffixing }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .stronglySuffixing }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .stronglySuffixing }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .weaklyPrefixing }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .equalPrefixingAndSuffixing }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .weaklyPrefixing }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .weaklySuffixing }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .weaklySuffixing }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .weaklySuffixing }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .stronglySuffixing }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .stronglySuffixing }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .weaklyPrefixing }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .littleAffixation }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .stronglySuffixing }
  , { walsCode := "bnr", language := "Bilinarra", iso := "nbj", value := .stronglySuffixing }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .equalPrefixingAndSuffixing }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .weaklySuffixing }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .stronglySuffixing }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .weaklyPrefixing }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .stronglySuffixing }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .strongPrefixing }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .weaklyPrefixing }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .stronglySuffixing }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .weaklyPrefixing }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .equalPrefixingAndSuffixing }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .weaklySuffixing }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .stronglySuffixing }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .weaklySuffixing }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .stronglySuffixing }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .strongPrefixing }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .equalPrefixingAndSuffixing }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .stronglySuffixing }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .stronglySuffixing }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .stronglySuffixing }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .littleAffixation }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .weaklyPrefixing }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .stronglySuffixing }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .stronglySuffixing }
  , { walsCode := "bmr", language := "Burum", iso := "bmu", value := .stronglySuffixing }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .stronglySuffixing }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .weaklySuffixing }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .strongPrefixing }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .stronglySuffixing }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .equalPrefixingAndSuffixing }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .stronglySuffixing }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .weaklyPrefixing }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .equalPrefixingAndSuffixing }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .littleAffixation }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .littleAffixation }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .stronglySuffixing }
  , { walsCode := "car", language := "Carib", iso := "car", value := .equalPrefixingAndSuffixing }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .equalPrefixingAndSuffixing }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .stronglySuffixing }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .stronglySuffixing }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .weaklyPrefixing }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .equalPrefixingAndSuffixing }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .littleAffixation }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .stronglySuffixing }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .stronglySuffixing }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .weaklyPrefixing }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .weaklySuffixing }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .littleAffixation }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .strongPrefixing }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .strongPrefixing }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .littleAffixation }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .equalPrefixingAndSuffixing }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .weaklyPrefixing }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .stronglySuffixing }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .strongPrefixing }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .stronglySuffixing }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .equalPrefixingAndSuffixing }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .weaklySuffixing }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .weaklySuffixing }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .stronglySuffixing }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .littleAffixation }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .weaklySuffixing }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .equalPrefixingAndSuffixing }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .stronglySuffixing }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .stronglySuffixing }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .equalPrefixingAndSuffixing }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .stronglySuffixing }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .stronglySuffixing }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .weaklySuffixing }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .weaklyPrefixing }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .stronglySuffixing }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .equalPrefixingAndSuffixing }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .stronglySuffixing }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .equalPrefixingAndSuffixing }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .weaklySuffixing }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .littleAffixation }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .stronglySuffixing }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .weaklySuffixing }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .stronglySuffixing }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .stronglySuffixing }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .stronglySuffixing }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .weaklySuffixing }
  , { walsCode := "des", language := "Desano", iso := "des", value := .stronglySuffixing }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .stronglySuffixing }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .stronglySuffixing }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .stronglySuffixing }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .stronglySuffixing }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .weaklyPrefixing }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .stronglySuffixing }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .stronglySuffixing }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .stronglySuffixing }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .littleAffixation }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .equalPrefixingAndSuffixing }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .stronglySuffixing }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .stronglySuffixing }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .stronglySuffixing }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .stronglySuffixing }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .stronglySuffixing }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .stronglySuffixing }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .stronglySuffixing }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .stronglySuffixing }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .stronglySuffixing }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .stronglySuffixing }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .weaklySuffixing }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .stronglySuffixing }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .stronglySuffixing }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .littleAffixation }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .littleAffixation }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .littleAffixation }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .stronglySuffixing }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .stronglySuffixing }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .weaklyPrefixing }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .stronglySuffixing }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .stronglySuffixing }
  , { walsCode := "ene", language := "Enets", iso := "", value := .stronglySuffixing }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .littleAffixation }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .weaklyPrefixing }
  , { walsCode := "eng", language := "English", iso := "eng", value := .stronglySuffixing }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .stronglySuffixing }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .littleAffixation }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .stronglySuffixing }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .weaklySuffixing }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .stronglySuffixing }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .stronglySuffixing }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .strongPrefixing }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .stronglySuffixing }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .littleAffixation }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .stronglySuffixing }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .stronglySuffixing }
  , { walsCode := "for", language := "Fore", iso := "for", value := .stronglySuffixing }
  , { walsCode := "fre", language := "French", iso := "fra", value := .stronglySuffixing }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .weaklySuffixing }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .equalPrefixingAndSuffixing }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .weaklySuffixing }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .littleAffixation }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .weaklySuffixing }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .equalPrefixingAndSuffixing }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .weaklySuffixing }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .weaklySuffixing }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .stronglySuffixing }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .stronglySuffixing }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .stronglySuffixing }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .stronglySuffixing }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .equalPrefixingAndSuffixing }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .stronglySuffixing }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .weaklySuffixing }
  , { walsCode := "ger", language := "German", iso := "deu", value := .stronglySuffixing }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .stronglySuffixing }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .weaklySuffixing }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .littleAffixation }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .littleAffixation }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .stronglySuffixing }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .stronglySuffixing }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .weaklyPrefixing }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .stronglySuffixing }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .stronglySuffixing }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .stronglySuffixing }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .strongPrefixing }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .stronglySuffixing }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .stronglySuffixing }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .littleAffixation }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .equalPrefixingAndSuffixing }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .weaklySuffixing }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .weaklyPrefixing }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .stronglySuffixing }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .weaklySuffixing }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .stronglySuffixing }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .weaklyPrefixing }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .weaklySuffixing }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .stronglySuffixing }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .stronglySuffixing }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .equalPrefixingAndSuffixing }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .strongPrefixing }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .littleAffixation }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .littleAffixation }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .stronglySuffixing }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .weaklySuffixing }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .stronglySuffixing }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .equalPrefixingAndSuffixing }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .littleAffixation }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .littleAffixation }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .stronglySuffixing }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .littleAffixation }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .stronglySuffixing }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .weaklySuffixing }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .weaklySuffixing }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .littleAffixation }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .equalPrefixingAndSuffixing }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .equalPrefixingAndSuffixing }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .stronglySuffixing }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .stronglySuffixing }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .strongPrefixing }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .stronglySuffixing }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .stronglySuffixing }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .stronglySuffixing }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .weaklyPrefixing }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .littleAffixation }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .littleAffixation }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .littleAffixation }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .stronglySuffixing }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .weaklyPrefixing }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .weaklySuffixing }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .stronglySuffixing }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .weaklySuffixing }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .stronglySuffixing }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .weaklySuffixing }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .stronglySuffixing }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .stronglySuffixing }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .equalPrefixingAndSuffixing }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .stronglySuffixing }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .stronglySuffixing }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .strongPrefixing }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .stronglySuffixing }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .stronglySuffixing }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .equalPrefixingAndSuffixing }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .equalPrefixingAndSuffixing }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .strongPrefixing }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .stronglySuffixing }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .stronglySuffixing }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .stronglySuffixing }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .stronglySuffixing }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .littleAffixation }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .stronglySuffixing }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .littleAffixation }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .littleAffixation }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .littleAffixation }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .stronglySuffixing }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .weaklyPrefixing }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .stronglySuffixing }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .weaklyPrefixing }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .stronglySuffixing }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .strongPrefixing }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .weaklySuffixing }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .weaklyPrefixing }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .stronglySuffixing }
  , { walsCode := "kbu", language := "Kanembu", iso := "kbl", value := .stronglySuffixing }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .stronglySuffixing }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .stronglySuffixing }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .stronglySuffixing }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .stronglySuffixing }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .stronglySuffixing }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .stronglySuffixing }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .weaklyPrefixing }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .littleAffixation }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .weaklyPrefixing }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .littleAffixation }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .weaklyPrefixing }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .stronglySuffixing }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .littleAffixation }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .stronglySuffixing }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .strongPrefixing }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .stronglySuffixing }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .stronglySuffixing }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .stronglySuffixing }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .weaklyPrefixing }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .weaklyPrefixing }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .stronglySuffixing }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .stronglySuffixing }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .stronglySuffixing }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .stronglySuffixing }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .weaklySuffixing }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .stronglySuffixing }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .littleAffixation }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .littleAffixation }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .stronglySuffixing }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .littleAffixation }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .littleAffixation }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .strongPrefixing }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .weaklyPrefixing }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .littleAffixation }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .stronglySuffixing }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .stronglySuffixing }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .littleAffixation }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .weaklySuffixing }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .stronglySuffixing }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .weaklySuffixing }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .stronglySuffixing }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .stronglySuffixing }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .stronglySuffixing }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .stronglySuffixing }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .littleAffixation }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .stronglySuffixing }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .stronglySuffixing }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .littleAffixation }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .stronglySuffixing }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .weaklySuffixing }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .strongPrefixing }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .weaklySuffixing }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .stronglySuffixing }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .stronglySuffixing }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .stronglySuffixing }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .stronglySuffixing }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .weaklySuffixing }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .stronglySuffixing }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .weaklySuffixing }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .littleAffixation }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .stronglySuffixing }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .littleAffixation }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .littleAffixation }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .weaklyPrefixing }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .stronglySuffixing }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .stronglySuffixing }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .stronglySuffixing }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .weaklySuffixing }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .weaklySuffixing }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .equalPrefixingAndSuffixing }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .weaklySuffixing }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .weaklySuffixing }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .littleAffixation }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .stronglySuffixing }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .strongPrefixing }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .stronglySuffixing }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .stronglySuffixing }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .stronglySuffixing }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .stronglySuffixing }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .stronglySuffixing }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .stronglySuffixing }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .stronglySuffixing }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .equalPrefixingAndSuffixing }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .littleAffixation }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .littleAffixation }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .weaklyPrefixing }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .littleAffixation }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .weaklyPrefixing }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .stronglySuffixing }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .stronglySuffixing }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .littleAffixation }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .equalPrefixingAndSuffixing }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .littleAffixation }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .weaklyPrefixing }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .weaklySuffixing }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .weaklySuffixing }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .weaklySuffixing }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .stronglySuffixing }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .strongPrefixing }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .weaklyPrefixing }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .equalPrefixingAndSuffixing }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .littleAffixation }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .weaklyPrefixing }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .stronglySuffixing }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .stronglySuffixing }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .stronglySuffixing }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .littleAffixation }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .stronglySuffixing }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .equalPrefixingAndSuffixing }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .littleAffixation }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .weaklyPrefixing }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .weaklySuffixing }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .littleAffixation }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .strongPrefixing }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .weaklyPrefixing }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .stronglySuffixing }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .weaklyPrefixing }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .equalPrefixingAndSuffixing }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .weaklyPrefixing }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .strongPrefixing }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .littleAffixation }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .weaklyPrefixing }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .weaklySuffixing }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .stronglySuffixing }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .stronglySuffixing }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .littleAffixation }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .stronglySuffixing }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .equalPrefixingAndSuffixing }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .weaklyPrefixing }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .stronglySuffixing }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .stronglySuffixing }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .littleAffixation }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .littleAffixation }
  ]

private def allData_1 : List (Datapoint PrefixSuffixPreference) :=
  [ { walsCode := "mal", language := "Malagasy", iso := "plt", value := .littleAffixation }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .stronglySuffixing }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .weaklyPrefixing }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .littleAffixation }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .weaklyPrefixing }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .weaklySuffixing }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .stronglySuffixing }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .weaklySuffixing }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .stronglySuffixing }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .littleAffixation }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .stronglySuffixing }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .littleAffixation }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .strongPrefixing }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .stronglySuffixing }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .littleAffixation }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .stronglySuffixing }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .weaklyPrefixing }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .littleAffixation }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .stronglySuffixing }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .stronglySuffixing }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .weaklySuffixing }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .stronglySuffixing }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .stronglySuffixing }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .littleAffixation }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .equalPrefixingAndSuffixing }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .stronglySuffixing }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .stronglySuffixing }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .strongPrefixing }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .littleAffixation }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .weaklyPrefixing }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .strongPrefixing }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .weaklySuffixing }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .weaklyPrefixing }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .stronglySuffixing }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .stronglySuffixing }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .weaklySuffixing }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .littleAffixation }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .stronglySuffixing }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .weaklySuffixing }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .littleAffixation }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .stronglySuffixing }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .weaklyPrefixing }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .stronglySuffixing }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .littleAffixation }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .weaklySuffixing }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .stronglySuffixing }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .littleAffixation }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .stronglySuffixing }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .stronglySuffixing }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .stronglySuffixing }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .strongPrefixing }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .littleAffixation }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .weaklyPrefixing }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .stronglySuffixing }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .littleAffixation }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .weaklySuffixing }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .stronglySuffixing }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .weaklyPrefixing }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .weaklySuffixing }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .weaklySuffixing }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .littleAffixation }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .stronglySuffixing }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .stronglySuffixing }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .stronglySuffixing }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .stronglySuffixing }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .weaklyPrefixing }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .weaklySuffixing }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .stronglySuffixing }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .stronglySuffixing }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .weaklyPrefixing }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .weaklySuffixing }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .weaklySuffixing }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .littleAffixation }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .equalPrefixingAndSuffixing }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .stronglySuffixing }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .strongPrefixing }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .littleAffixation }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .weaklySuffixing }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .weaklySuffixing }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .stronglySuffixing }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .stronglySuffixing }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .littleAffixation }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .stronglySuffixing }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .stronglySuffixing }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .stronglySuffixing }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .littleAffixation }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .stronglySuffixing }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .equalPrefixingAndSuffixing }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .weaklyPrefixing }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .equalPrefixingAndSuffixing }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .stronglySuffixing }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .weaklySuffixing }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .stronglySuffixing }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .stronglySuffixing }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .equalPrefixingAndSuffixing }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .equalPrefixingAndSuffixing }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .weaklySuffixing }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .stronglySuffixing }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .stronglySuffixing }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .strongPrefixing }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .strongPrefixing }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .stronglySuffixing }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .littleAffixation }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .stronglySuffixing }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .stronglySuffixing }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .stronglySuffixing }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .equalPrefixingAndSuffixing }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .weaklySuffixing }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .stronglySuffixing }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .littleAffixation }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .stronglySuffixing }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .weaklySuffixing }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .weaklySuffixing }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .weaklySuffixing }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .stronglySuffixing }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .stronglySuffixing }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .stronglySuffixing }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .stronglySuffixing }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .strongPrefixing }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .stronglySuffixing }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .strongPrefixing }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .stronglySuffixing }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .stronglySuffixing }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .littleAffixation }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .littleAffixation }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .weaklySuffixing }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .strongPrefixing }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .strongPrefixing }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .stronglySuffixing }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .stronglySuffixing }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .equalPrefixingAndSuffixing }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .stronglySuffixing }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .stronglySuffixing }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .weaklyPrefixing }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .stronglySuffixing }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .stronglySuffixing }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .littleAffixation }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .equalPrefixingAndSuffixing }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .littleAffixation }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .strongPrefixing }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .stronglySuffixing }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .stronglySuffixing }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .weaklyPrefixing }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .weaklyPrefixing }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .equalPrefixingAndSuffixing }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .strongPrefixing }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .strongPrefixing }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .strongPrefixing }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .weaklySuffixing }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .weaklyPrefixing }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .weaklySuffixing }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .stronglySuffixing }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .stronglySuffixing }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .stronglySuffixing }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .littleAffixation }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .stronglySuffixing }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .weaklyPrefixing }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .weaklyPrefixing }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .stronglySuffixing }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .stronglySuffixing }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .weaklyPrefixing }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .stronglySuffixing }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .equalPrefixingAndSuffixing }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .weaklyPrefixing }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .stronglySuffixing }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .weaklyPrefixing }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .stronglySuffixing }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .strongPrefixing }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .stronglySuffixing }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .stronglySuffixing }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .equalPrefixingAndSuffixing }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .equalPrefixingAndSuffixing }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .stronglySuffixing }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .equalPrefixingAndSuffixing }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .equalPrefixingAndSuffixing }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .weaklySuffixing }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .weaklySuffixing }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .weaklyPrefixing }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .weaklySuffixing }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .equalPrefixingAndSuffixing }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .stronglySuffixing }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .weaklySuffixing }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .stronglySuffixing }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .weaklySuffixing }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .littleAffixation }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .weaklySuffixing }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .stronglySuffixing }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .stronglySuffixing }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .stronglySuffixing }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .equalPrefixingAndSuffixing }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .stronglySuffixing }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .littleAffixation }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .stronglySuffixing }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .stronglySuffixing }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .stronglySuffixing }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .stronglySuffixing }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .weaklySuffixing }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .stronglySuffixing }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .weaklySuffixing }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .stronglySuffixing }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .stronglySuffixing }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .weaklySuffixing }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .equalPrefixingAndSuffixing }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .littleAffixation }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .weaklyPrefixing }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .littleAffixation }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .stronglySuffixing }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .equalPrefixingAndSuffixing }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .stronglySuffixing }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .stronglySuffixing }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .stronglySuffixing }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .littleAffixation }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .equalPrefixingAndSuffixing }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .stronglySuffixing }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .stronglySuffixing }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .equalPrefixingAndSuffixing }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .strongPrefixing }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .stronglySuffixing }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .weaklySuffixing }
  , { walsCode := "saa", language := "Sa'a", iso := "apb", value := .littleAffixation }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .stronglySuffixing }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .strongPrefixing }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .weaklyPrefixing }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .weaklySuffixing }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .equalPrefixingAndSuffixing }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .stronglySuffixing }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .littleAffixation }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .stronglySuffixing }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .strongPrefixing }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .stronglySuffixing }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .stronglySuffixing }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .littleAffixation }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .weaklyPrefixing }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .stronglySuffixing }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .stronglySuffixing }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .stronglySuffixing }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .littleAffixation }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .stronglySuffixing }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .stronglySuffixing }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .weaklySuffixing }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .weaklySuffixing }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .stronglySuffixing }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .stronglySuffixing }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .strongPrefixing }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .strongPrefixing }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .weaklySuffixing }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .equalPrefixingAndSuffixing }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .stronglySuffixing }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .stronglySuffixing }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .stronglySuffixing }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .strongPrefixing }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .stronglySuffixing }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .equalPrefixingAndSuffixing }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .stronglySuffixing }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .stronglySuffixing }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .littleAffixation }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .weaklyPrefixing }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .equalPrefixingAndSuffixing }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .stronglySuffixing }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .strongPrefixing }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .weaklyPrefixing }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .stronglySuffixing }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .littleAffixation }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .stronglySuffixing }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .strongPrefixing }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .stronglySuffixing }
  , { walsCode := "so", language := "So", iso := "teu", value := .weaklySuffixing }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .equalPrefixingAndSuffixing }
  , { walsCode := "som", language := "Somali", iso := "som", value := .stronglySuffixing }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .littleAffixation }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .weaklyPrefixing }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .stronglySuffixing }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .stronglySuffixing }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .littleAffixation }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .stronglySuffixing }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .stronglySuffixing }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .strongPrefixing }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .littleAffixation }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .weaklySuffixing }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .weaklyPrefixing }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .stronglySuffixing }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .littleAffixation }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .stronglySuffixing }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .littleAffixation }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .littleAffixation }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .stronglySuffixing }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .weaklySuffixing }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .weaklySuffixing }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .weaklySuffixing }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .stronglySuffixing }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .stronglySuffixing }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .strongPrefixing }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .equalPrefixingAndSuffixing }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .stronglySuffixing }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .weaklySuffixing }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .weaklyPrefixing }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .stronglySuffixing }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .weaklySuffixing }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .weaklyPrefixing }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .weaklyPrefixing }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .stronglySuffixing }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .weaklyPrefixing }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .strongPrefixing }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .weaklySuffixing }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .stronglySuffixing }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .littleAffixation }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .weaklyPrefixing }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .stronglySuffixing }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .stronglySuffixing }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .strongPrefixing }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .littleAffixation }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .littleAffixation }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .stronglySuffixing }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .stronglySuffixing }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .strongPrefixing }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .littleAffixation }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .weaklySuffixing }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .weaklyPrefixing }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .littleAffixation }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .littleAffixation }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .equalPrefixingAndSuffixing }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .stronglySuffixing }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .strongPrefixing }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .littleAffixation }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .weaklyPrefixing }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .strongPrefixing }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .littleAffixation }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .weaklySuffixing }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .stronglySuffixing }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .weaklySuffixing }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .stronglySuffixing }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .weaklySuffixing }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .stronglySuffixing }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .weaklyPrefixing }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .stronglySuffixing }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .stronglySuffixing }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .weaklyPrefixing }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .weaklySuffixing }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .stronglySuffixing }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .strongPrefixing }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .stronglySuffixing }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .weaklyPrefixing }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .stronglySuffixing }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .equalPrefixingAndSuffixing }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .strongPrefixing }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .stronglySuffixing }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .equalPrefixingAndSuffixing }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .stronglySuffixing }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .stronglySuffixing }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .stronglySuffixing }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .strongPrefixing }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .littleAffixation }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .stronglySuffixing }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .littleAffixation }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .stronglySuffixing }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .littleAffixation }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .stronglySuffixing }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .littleAffixation }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .stronglySuffixing }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .weaklyPrefixing }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .weaklySuffixing }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .stronglySuffixing }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .stronglySuffixing }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .stronglySuffixing }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .littleAffixation }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .littleAffixation }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .equalPrefixingAndSuffixing }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .stronglySuffixing }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .stronglySuffixing }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .weaklyPrefixing }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .stronglySuffixing }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .stronglySuffixing }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .stronglySuffixing }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .stronglySuffixing }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .weaklySuffixing }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .equalPrefixingAndSuffixing }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .weaklySuffixing }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .littleAffixation }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .stronglySuffixing }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .equalPrefixingAndSuffixing }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .stronglySuffixing }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .stronglySuffixing }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .weaklyPrefixing }
  , { walsCode := "was", language := "Washo", iso := "was", value := .weaklySuffixing }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .stronglySuffixing }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .stronglySuffixing }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .stronglySuffixing }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .weaklySuffixing }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .stronglySuffixing }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .stronglySuffixing }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .strongPrefixing }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .weaklyPrefixing }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .equalPrefixingAndSuffixing }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .stronglySuffixing }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .stronglySuffixing }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .stronglySuffixing }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .stronglySuffixing }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .stronglySuffixing }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .littleAffixation }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .equalPrefixingAndSuffixing }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .littleAffixation }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .littleAffixation }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .weaklyPrefixing }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .strongPrefixing }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .littleAffixation }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .equalPrefixingAndSuffixing }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .stronglySuffixing }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .stronglySuffixing }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .stronglySuffixing }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .littleAffixation }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .stronglySuffixing }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .stronglySuffixing }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .stronglySuffixing }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .stronglySuffixing }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .equalPrefixingAndSuffixing }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .stronglySuffixing }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .stronglySuffixing }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .stronglySuffixing }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .littleAffixation }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .stronglySuffixing }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .stronglySuffixing }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .stronglySuffixing }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .equalPrefixingAndSuffixing }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .stronglySuffixing }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .weaklySuffixing }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .stronglySuffixing }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .equalPrefixingAndSuffixing }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .weaklySuffixing }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .equalPrefixingAndSuffixing }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .equalPrefixingAndSuffixing }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .equalPrefixingAndSuffixing }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .stronglySuffixing }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .littleAffixation }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .equalPrefixingAndSuffixing }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .strongPrefixing }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .equalPrefixingAndSuffixing }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .stronglySuffixing }
  ]

/-- Complete WALS 26A dataset (969 languages). -/
def allData : List (Datapoint PrefixSuffixPreference) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 969 := by native_decide

theorem count_littleAffixation :
    (allData.filter (·.value == .littleAffixation)).length = 141 := by native_decide
theorem count_stronglySuffixing :
    (allData.filter (·.value == .stronglySuffixing)).length = 406 := by native_decide
theorem count_weaklySuffixing :
    (allData.filter (·.value == .weaklySuffixing)).length = 123 := by native_decide
theorem count_equalPrefixingAndSuffixing :
    (allData.filter (·.value == .equalPrefixingAndSuffixing)).length = 147 := by native_decide
theorem count_weaklyPrefixing :
    (allData.filter (·.value == .weaklyPrefixing)).length = 94 := by native_decide
theorem count_strongPrefixing :
    (allData.filter (·.value == .strongPrefixing)).length = 58 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F26A
