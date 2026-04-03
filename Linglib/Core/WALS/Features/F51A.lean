import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 51A: Position of Case Affixes
@cite{iggesen-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 51A`.

Chapter 51, 1031 languages.
-/

namespace Core.WALS.F51A

/-- WALS 51A values. -/
inductive CaseAffixPosition where
  | caseSuffixes  -- Case suffixes (452 languages)
  | casePrefixes  -- Case prefixes (38 languages)
  | caseTone  -- Case tone (5 languages)
  | caseStemChange  -- Case stem change (1 languages)
  | mixedMorphologicalCase  -- Mixed morphological case (9 languages)
  | postpositionalClitics  -- Postpositional clitics (123 languages)
  | prepositionalClitics  -- Prepositional clitics (17 languages)
  | inpositionalClitics  -- Inpositional clitics (7 languages)
  | noCaseAffixesOrAdpositionalClitics  -- No case affixes or adpositional clitics (379 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint CaseAffixPosition) :=
  [ { walsCode := "aar", language := "Aari", iso := "aiw", value := .caseSuffixes }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .caseSuffixes }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .caseSuffixes }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .caseSuffixes }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .caseSuffixes }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .caseSuffixes }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .caseSuffixes }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .postpositionalClitics }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .caseSuffixes }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .caseSuffixes }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .caseSuffixes }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .caseSuffixes }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .caseSuffixes }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .postpositionalClitics }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .caseSuffixes }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .caseSuffixes }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .caseSuffixes }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .inpositionalClitics }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .postpositionalClitics }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .caseSuffixes }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .postpositionalClitics }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .caseSuffixes }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .prepositionalClitics }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .caseSuffixes }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .prepositionalClitics }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .caseSuffixes }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .caseSuffixes }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .caseSuffixes }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .caseSuffixes }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .postpositionalClitics }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .caseSuffixes }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .caseSuffixes }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .caseSuffixes }
  , { walsCode := "ats", language := "Atsugewi", iso := "atw", value := .caseSuffixes }
  , { walsCode := "au", language := "Au", iso := "avt", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .caseSuffixes }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .caseSuffixes }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .postpositionalClitics }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .postpositionalClitics }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .postpositionalClitics }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .caseSuffixes }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .caseSuffixes }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .caseSuffixes }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .postpositionalClitics }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .caseSuffixes }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .postpositionalClitics }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .caseSuffixes }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .caseSuffixes }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .caseSuffixes }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .caseSuffixes }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .caseSuffixes }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .postpositionalClitics }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .caseSuffixes }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .postpositionalClitics }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .caseSuffixes }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .caseSuffixes }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .caseSuffixes }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .caseSuffixes }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .casePrefixes }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .casePrefixes }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .casePrefixes }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .postpositionalClitics }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .caseSuffixes }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .caseSuffixes }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .caseSuffixes }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bnr", language := "Bilinarra", iso := "nbj", value := .caseSuffixes }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .caseSuffixes }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .postpositionalClitics }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .caseSuffixes }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .caseSuffixes }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .caseSuffixes }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .caseSuffixes }
  , { walsCode := "boi", language := "Boiken", iso := "bzf", value := .caseSuffixes }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .caseSuffixes }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .caseSuffixes }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .prepositionalClitics }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .caseSuffixes }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .caseSuffixes }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .inpositionalClitics }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .casePrefixes }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .caseSuffixes }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .caseSuffixes }
  , { walsCode := "bmr", language := "Burum", iso := "bmu", value := .caseSuffixes }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .caseSuffixes }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .caseSuffixes }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .caseSuffixes }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .caseSuffixes }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .caseSuffixes }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .caseSuffixes }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .caseSuffixes }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .caseSuffixes }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .postpositionalClitics }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .caseSuffixes }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .prepositionalClitics }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .caseSuffixes }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .postpositionalClitics }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .postpositionalClitics }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .caseSuffixes }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .caseSuffixes }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .caseSuffixes }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .postpositionalClitics }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .prepositionalClitics }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .caseSuffixes }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .caseSuffixes }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .postpositionalClitics }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .caseSuffixes }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .casePrefixes }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .caseSuffixes }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .caseSuffixes }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .caseSuffixes }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .caseSuffixes }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .caseSuffixes }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .postpositionalClitics }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .prepositionalClitics }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .caseSuffixes }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .caseSuffixes }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cua", language := "Cua", iso := "cua", value := .casePrefixes }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .caseSuffixes }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .caseSuffixes }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .caseSuffixes }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .caseSuffixes }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .caseSuffixes }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .caseSuffixes }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .caseSuffixes }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .caseSuffixes }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "day", language := "Day", iso := "dai", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "des", language := "Desano", iso := "des", value := .postpositionalClitics }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .mixedMorphologicalCase }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .caseSuffixes }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .caseSuffixes }
  , { walsCode := "dhb", language := "Dharumbal", iso := "xgm", value := .caseSuffixes }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .caseSuffixes }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .postpositionalClitics }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .postpositionalClitics }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .postpositionalClitics }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .postpositionalClitics }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .caseSuffixes }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .caseSuffixes }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .caseSuffixes }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .caseSuffixes }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .caseSuffixes }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .caseSuffixes }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .caseSuffixes }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .postpositionalClitics }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .caseSuffixes }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .caseSuffixes }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .postpositionalClitics }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .postpositionalClitics }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .postpositionalClitics }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .caseSuffixes }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .postpositionalClitics }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .casePrefixes }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .postpositionalClitics }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .caseSuffixes }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .postpositionalClitics }
  , { walsCode := "ene", language := "Enets", iso := "", value := .caseSuffixes }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .casePrefixes }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .postpositionalClitics }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .caseSuffixes }
  , { walsCode := "ess", language := "Esselen", iso := "esq", value := .caseSuffixes }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .caseSuffixes }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .caseSuffixes }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .caseSuffixes }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .caseSuffixes }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .postpositionalClitics }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .caseSuffixes }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .postpositionalClitics }
  , { walsCode := "for", language := "Fore", iso := "for", value := .postpositionalClitics }
  , { walsCode := "fre", language := "French", iso := "fra", value := .prepositionalClitics }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .prepositionalClitics }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .postpositionalClitics }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .caseSuffixes }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .caseSuffixes }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .mixedMorphologicalCase }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .caseSuffixes }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .caseSuffixes }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .caseSuffixes }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .casePrefixes }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .postpositionalClitics }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .caseSuffixes }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .caseSuffixes }
  , { walsCode := "ger", language := "German", iso := "deu", value := .caseSuffixes }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .caseSuffixes }
  , { walsCode := "gil", language := "Gilaki", iso := "glk", value := .caseSuffixes }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .postpositionalClitics }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .caseSuffixes }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .caseSuffixes }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gog", language := "Gogodala", iso := "ggw", value := .caseSuffixes }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .caseSuffixes }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .inpositionalClitics }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .caseSuffixes }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .caseSuffixes }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .caseSuffixes }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .caseSuffixes }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .caseSuffixes }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .caseSuffixes }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .postpositionalClitics }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .caseSuffixes }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .casePrefixes }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .caseSuffixes }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .caseSuffixes }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .postpositionalClitics }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .postpositionalClitics }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .prepositionalClitics }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .caseSuffixes }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .postpositionalClitics }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .caseSuffixes }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .caseSuffixes }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .caseSuffixes }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .caseSuffixes }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .caseSuffixes }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .caseSuffixes }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .caseSuffixes }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .casePrefixes }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .caseSuffixes }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .caseSuffixes }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .postpositionalClitics }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .caseSuffixes }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .caseSuffixes }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .caseSuffixes }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .caseSuffixes }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .postpositionalClitics }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .postpositionalClitics }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .postpositionalClitics }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .caseSuffixes }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .postpositionalClitics }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .caseSuffixes }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .mixedMorphologicalCase }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .caseSuffixes }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .caseSuffixes }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .caseTone }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .postpositionalClitics }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .caseSuffixes }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .caseSuffixes }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .caseSuffixes }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .caseSuffixes }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .caseSuffixes }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .casePrefixes }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .caseSuffixes }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .caseSuffixes }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .postpositionalClitics }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .caseSuffixes }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .caseSuffixes }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .caseSuffixes }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .postpositionalClitics }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .casePrefixes }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kbu", language := "Kanembu", iso := "kbl", value := .caseSuffixes }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .caseSuffixes }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .caseSuffixes }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .postpositionalClitics }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .caseSuffixes }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .caseSuffixes }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .caseSuffixes }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .postpositionalClitics }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .caseSuffixes }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .caseSuffixes }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .caseSuffixes }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .caseSuffixes }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .caseSuffixes }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .caseSuffixes }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .postpositionalClitics }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .caseSuffixes }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .postpositionalClitics }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .caseSuffixes }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .caseSuffixes }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .caseSuffixes }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .caseSuffixes }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .postpositionalClitics }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .caseSuffixes }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .postpositionalClitics }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .caseSuffixes }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .caseSuffixes }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .caseSuffixes }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .prepositionalClitics }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .caseSuffixes }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .caseSuffixes }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .caseSuffixes }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .caseSuffixes }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .caseSuffixes }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .postpositionalClitics }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .caseSuffixes }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .caseSuffixes }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .caseSuffixes }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .caseSuffixes }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .caseSuffixes }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .caseSuffixes }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .caseSuffixes }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .caseSuffixes }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .caseSuffixes }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .caseSuffixes }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .caseSuffixes }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .caseSuffixes }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .caseSuffixes }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .caseSuffixes }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .caseSuffixes }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .casePrefixes }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .postpositionalClitics }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .caseSuffixes }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .caseSuffixes }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .caseSuffixes }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .postpositionalClitics }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .caseSuffixes }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .inpositionalClitics }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .caseSuffixes }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .caseSuffixes }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .postpositionalClitics }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .postpositionalClitics }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .postpositionalClitics }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .postpositionalClitics }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .caseSuffixes }
  , { walsCode := "laf", language := "Lafofa", iso := "laf", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .caseSuffixes }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .caseSuffixes }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .caseSuffixes }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .caseSuffixes }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .caseSuffixes }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .caseSuffixes }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .caseSuffixes }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .caseSuffixes }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .caseSuffixes }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .noCaseAffixesOrAdpositionalClitics }
  ]

private def allData_1 : List (Datapoint CaseAffixPosition) :=
  [ { walsCode := "lis", language := "Lisu", iso := "lis", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .caseSuffixes }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .postpositionalClitics }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .casePrefixes }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .prepositionalClitics }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .caseSuffixes }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .casePrefixes }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .caseTone }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .caseTone }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .caseSuffixes }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .caseSuffixes }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .caseSuffixes }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mgh", language := "Magahi", iso := "mag", value := .caseSuffixes }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .caseSuffixes }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .caseSuffixes }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .postpositionalClitics }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .caseSuffixes }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .caseSuffixes }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .prepositionalClitics }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .caseSuffixes }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .postpositionalClitics }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .caseSuffixes }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .caseSuffixes }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .mixedMorphologicalCase }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .postpositionalClitics }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .caseSuffixes }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .caseSuffixes }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .caseSuffixes }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .casePrefixes }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .caseSuffixes }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .caseSuffixes }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .caseSuffixes }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .postpositionalClitics }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .caseSuffixes }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .caseSuffixes }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .caseSuffixes }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .casePrefixes }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .caseSuffixes }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .caseSuffixes }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .caseSuffixes }
  , { walsCode := "mhk", language := "Mehek", iso := "nux", value := .caseSuffixes }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .postpositionalClitics }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .caseSuffixes }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .postpositionalClitics }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .caseSuffixes }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .postpositionalClitics }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .caseSuffixes }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .caseSuffixes }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .caseSuffixes }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mhl", language := "Miri (Hill):", iso := "mrg", value := .caseSuffixes }
  , { walsCode := "mir", language := "Miriwung", iso := "mep", value := .caseSuffixes }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .postpositionalClitics }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .postpositionalClitics }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .caseSuffixes }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .caseSuffixes }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .caseSuffixes }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .postpositionalClitics }
  , { walsCode := "mqf", language := "Momuna", iso := "mqf", value := .caseSuffixes }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .caseSuffixes }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .caseSuffixes }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .caseSuffixes }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .caseSuffixes }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .mixedMorphologicalCase }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .prepositionalClitics }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .caseSuffixes }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .caseSuffixes }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .caseSuffixes }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .caseSuffixes }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .caseSuffixes }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .caseSuffixes }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .casePrefixes }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .postpositionalClitics }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .caseSuffixes }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .caseSuffixes }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .caseSuffixes }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .caseTone }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .postpositionalClitics }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .postpositionalClitics }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .caseSuffixes }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .postpositionalClitics }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .casePrefixes }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .caseSuffixes }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .casePrefixes }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .caseSuffixes }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .prepositionalClitics }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .caseSuffixes }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .caseSuffixes }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .caseSuffixes }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .caseSuffixes }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .caseSuffixes }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .caseSuffixes }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .caseSuffixes }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .caseSuffixes }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .postpositionalClitics }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .caseSuffixes }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .caseSuffixes }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .postpositionalClitics }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .caseSuffixes }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .caseSuffixes }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .caseSuffixes }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .caseSuffixes }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .casePrefixes }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .caseSuffixes }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .caseSuffixes }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .caseSuffixes }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .caseSuffixes }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .casePrefixes }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .caseSuffixes }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .postpositionalClitics }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .caseStemChange }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .caseSuffixes }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .caseSuffixes }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .caseSuffixes }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .caseSuffixes }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .inpositionalClitics }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .casePrefixes }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .caseSuffixes }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .caseSuffixes }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .postpositionalClitics }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "one", language := "One", iso := "aun", value := .caseSuffixes }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .caseSuffixes }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .caseSuffixes }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .caseSuffixes }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .caseSuffixes }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .caseSuffixes }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .caseSuffixes }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .caseSuffixes }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .postpositionalClitics }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .caseSuffixes }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .caseSuffixes }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .caseSuffixes }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .caseSuffixes }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .caseSuffixes }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .caseSuffixes }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .caseSuffixes }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .caseSuffixes }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .caseSuffixes }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .postpositionalClitics }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .caseSuffixes }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .caseSuffixes }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .caseSuffixes }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .caseSuffixes }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .caseSuffixes }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .postpositionalClitics }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .caseSuffixes }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .caseSuffixes }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .caseSuffixes }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .caseSuffixes }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .caseSuffixes }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .caseSuffixes }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .casePrefixes }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "puq", language := "Puquina", iso := "puq", value := .caseSuffixes }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .caseSuffixes }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .caseSuffixes }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .postpositionalClitics }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .caseSuffixes }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .postpositionalClitics }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .postpositionalClitics }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .caseSuffixes }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .caseSuffixes }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "rmb", language := "Rembarnga", iso := "rmb", value := .caseSuffixes }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .caseSuffixes }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .postpositionalClitics }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .postpositionalClitics }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .caseSuffixes }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .caseSuffixes }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .caseSuffixes }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .caseSuffixes }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .caseSuffixes }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .caseSuffixes }
  , { walsCode := "saa", language := "Sa'a", iso := "apb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .caseSuffixes }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .prepositionalClitics }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .postpositionalClitics }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .caseSuffixes }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .caseSuffixes }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .postpositionalClitics }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .postpositionalClitics }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .caseSuffixes }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .postpositionalClitics }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .caseSuffixes }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .caseSuffixes }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .postpositionalClitics }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .caseSuffixes }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .caseSuffixes }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .caseSuffixes }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .caseTone }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .caseSuffixes }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .postpositionalClitics }
  , { walsCode := "shy", language := "Shira Yughur", iso := "yuy", value := .caseSuffixes }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .caseSuffixes }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .caseSuffixes }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .casePrefixes }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .caseSuffixes }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .mixedMorphologicalCase }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .postpositionalClitics }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .postpositionalClitics }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .caseSuffixes }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .caseSuffixes }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .postpositionalClitics }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .mixedMorphologicalCase }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .postpositionalClitics }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .caseSuffixes }
  , { walsCode := "so", language := "So", iso := "teu", value := .caseSuffixes }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .caseSuffixes }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .prepositionalClitics }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .caseSuffixes }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .caseSuffixes }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .mixedMorphologicalCase }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .caseSuffixes }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .casePrefixes }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .casePrefixes }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .caseSuffixes }
  , { walsCode := "tmg", language := "Tamagario", iso := "tcg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .postpositionalClitics }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .casePrefixes }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .caseSuffixes }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tbx", language := "Tangbe", iso := "skj", value := .postpositionalClitics }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .caseSuffixes }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .caseSuffixes }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .caseSuffixes }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .caseSuffixes }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .postpositionalClitics }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .casePrefixes }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .caseSuffixes }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .postpositionalClitics }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .caseSuffixes }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .caseSuffixes }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .casePrefixes }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .caseSuffixes }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .casePrefixes }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .casePrefixes }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .caseSuffixes }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .casePrefixes }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .caseSuffixes }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .caseSuffixes }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .postpositionalClitics }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .caseSuffixes }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .prepositionalClitics }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .postpositionalClitics }
  , { walsCode := "tia", language := "Tima", iso := "tms", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .caseSuffixes }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .caseSuffixes }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .caseSuffixes }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .caseSuffixes }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .postpositionalClitics }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .caseSuffixes }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .casePrefixes }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .postpositionalClitics }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .caseSuffixes }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .postpositionalClitics }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .caseSuffixes }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .postpositionalClitics }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .caseSuffixes }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .postpositionalClitics }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .caseSuffixes }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .caseSuffixes }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .mixedMorphologicalCase }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .caseSuffixes }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .caseSuffixes }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .caseSuffixes }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .postpositionalClitics }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .caseSuffixes }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .postpositionalClitics }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .caseSuffixes }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .caseSuffixes }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .caseSuffixes }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .postpositionalClitics }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .caseSuffixes }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .caseSuffixes }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .caseSuffixes }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .caseSuffixes }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .caseSuffixes }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .caseSuffixes }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .caseSuffixes }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .caseSuffixes }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .caseSuffixes }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .caseSuffixes }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .postpositionalClitics }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .postpositionalClitics }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .caseSuffixes }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .caseSuffixes }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .postpositionalClitics }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .caseSuffixes }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .caseSuffixes }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .caseSuffixes }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .caseSuffixes }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .caseSuffixes }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .caseSuffixes }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .inpositionalClitics }
  , { walsCode := "was", language := "Washo", iso := "was", value := .caseSuffixes }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .caseSuffixes }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .postpositionalClitics }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .caseSuffixes }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .caseSuffixes }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .caseSuffixes }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .caseSuffixes }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .caseSuffixes }
  , { walsCode := "wn", language := "Wik Ngathana", iso := "wig", value := .caseSuffixes }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .caseSuffixes }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .caseSuffixes }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .postpositionalClitics }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .caseSuffixes }
  , { walsCode := "wog", language := "Wogamusin", iso := "wog", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .caseSuffixes }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .caseSuffixes }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .casePrefixes }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .postpositionalClitics }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .caseSuffixes }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .caseSuffixes }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .caseSuffixes }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .postpositionalClitics }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .caseSuffixes }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .caseSuffixes }
  ]

private def allData_2 : List (Datapoint CaseAffixPosition) :=
  [ { walsCode := "yar", language := "Yareba", iso := "yrb", value := .caseSuffixes }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .caseSuffixes }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .inpositionalClitics }
  , { walsCode := "yyg", language := "Yaygir", iso := "xya", value := .caseSuffixes }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .caseSuffixes }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .caseSuffixes }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .caseSuffixes }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .caseSuffixes }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .caseSuffixes }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .caseSuffixes }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .caseSuffixes }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .caseSuffixes }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .caseSuffixes }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .caseSuffixes }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .caseSuffixes }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .caseSuffixes }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .caseSuffixes }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .caseSuffixes }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .casePrefixes }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .caseSuffixes }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .noCaseAffixesOrAdpositionalClitics }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .caseSuffixes }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .caseSuffixes }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .casePrefixes }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .caseSuffixes }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .postpositionalClitics }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .caseSuffixes }
  ]

/-- Complete WALS 51A dataset (1031 languages). -/
def allData : List (Datapoint CaseAffixPosition) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1031 := by native_decide

theorem count_caseSuffixes :
    (allData.filter (·.value == .caseSuffixes)).length = 452 := by native_decide
theorem count_casePrefixes :
    (allData.filter (·.value == .casePrefixes)).length = 38 := by native_decide
theorem count_caseTone :
    (allData.filter (·.value == .caseTone)).length = 5 := by native_decide
theorem count_caseStemChange :
    (allData.filter (·.value == .caseStemChange)).length = 1 := by native_decide
theorem count_mixedMorphologicalCase :
    (allData.filter (·.value == .mixedMorphologicalCase)).length = 9 := by native_decide
theorem count_postpositionalClitics :
    (allData.filter (·.value == .postpositionalClitics)).length = 123 := by native_decide
theorem count_prepositionalClitics :
    (allData.filter (·.value == .prepositionalClitics)).length = 17 := by native_decide
theorem count_inpositionalClitics :
    (allData.filter (·.value == .inpositionalClitics)).length = 7 := by native_decide
theorem count_noCaseAffixesOrAdpositionalClitics :
    (allData.filter (·.value == .noCaseAffixesOrAdpositionalClitics)).length = 379 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F51A
