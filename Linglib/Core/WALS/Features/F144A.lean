import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144A: Position of Negative Word With Respect to Subject, Object, and Verb
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144A`.

Chapter 144, 1190 languages.
-/

namespace Core.WALS.F144A

/-- WALS 144A values. -/
inductive PositionOfNegativeWordWithRespectToSubjectObjectAndVerb where
  /-- NegSVO (10 languages). -/
  | negsvo
  /-- SNegVO (112 languages). -/
  | snegvo
  /-- SVNegO (2 languages). -/
  | svnego
  /-- SVONeg (81 languages). -/
  | svoneg
  /-- NegSOV (11 languages). -/
  | negsov
  /-- SNegOV (15 languages). -/
  | snegov
  /-- SONegV (65 languages). -/
  | sonegv
  /-- SOVNeg (49 languages). -/
  | sovneg
  /-- NegVSO (58 languages). -/
  | negvso
  /-- VSNegO (1 languages). -/
  | vsnego
  /-- VSONeg (1 languages). -/
  | vsoneg
  /-- NegVOS (18 languages). -/
  | negvos
  /-- ONegVS (3 languages). -/
  | onegvs
  /-- OVNegS (1 languages). -/
  | ovnegs
  /-- OSVNeg (1 languages). -/
  | osvneg
  /-- More than one position (91 languages). -/
  | moreThanOnePosition
  /-- OptSingleNeg (1 languages). -/
  | optsingleneg
  /-- ObligDoubleNeg (101 languages). -/
  | obligdoubleneg
  /-- OptDoubleNeg (67 languages). -/
  | optdoubleneg
  /-- MorphNeg (333 languages). -/
  | morphneg
  /-- Other (169 languages). -/
  | other
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint PositionOfNegativeWordWithRespectToSubjectObjectAndVerb) :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .other }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .other }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .snegvo }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .morphneg }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .sovneg }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .other }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .morphneg }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .sovneg }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .obligdoubleneg }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .snegvo }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .moreThanOnePosition }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .other }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .optdoubleneg }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .morphneg }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .optdoubleneg }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .moreThanOnePosition }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .negvso }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .negvso }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .sonegv }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .svoneg }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .moreThanOnePosition }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .morphneg }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .sonegv }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .other }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .sonegv }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .snegvo }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .other }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .svoneg }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .morphneg }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .obligdoubleneg }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .obligdoubleneg }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .svoneg }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .moreThanOnePosition }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .morphneg }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .optdoubleneg }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .obligdoubleneg }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .obligdoubleneg }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .negvos }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .sovneg }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .svoneg }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .morphneg }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .other }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .svnego }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .other }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .svoneg }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .optdoubleneg }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .obligdoubleneg }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .morphneg }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .morphneg }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .moreThanOnePosition }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .other }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .optdoubleneg }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .snegvo }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .morphneg }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .snegvo }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .negvso }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .obligdoubleneg }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .moreThanOnePosition }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .obligdoubleneg }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .svoneg }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .optdoubleneg }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .morphneg }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .moreThanOnePosition }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .moreThanOnePosition }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .svoneg }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .snegvo }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .morphneg }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .sovneg }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .morphneg }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .obligdoubleneg }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .other }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .morphneg }
  , { walsCode := "au", language := "Au", iso := "avt", value := .moreThanOnePosition }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .sovneg }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .sonegv }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .obligdoubleneg }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .morphneg }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .moreThanOnePosition }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .morphneg }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .morphneg }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .morphneg }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .obligdoubleneg }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .other }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .other }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .obligdoubleneg }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .svoneg }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .svoneg }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .snegvo }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .other }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .svoneg }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .svoneg }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .morphneg }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .morphneg }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .snegvo }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .moreThanOnePosition }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .snegov }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .snegvo }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .other }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .obligdoubleneg }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .morphneg }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .sonegv }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .optdoubleneg }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .snegvo }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .snegov }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .snegvo }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .other }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .morphneg }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .sonegv }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .moreThanOnePosition }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .negvos }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .negvos }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .sovneg }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .sovneg }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .morphneg }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .optdoubleneg }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .negvso }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .sovneg }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .moreThanOnePosition }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .negvso }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .snegvo }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .morphneg }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .morphneg }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .morphneg }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .sonegv }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .svoneg }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .obligdoubleneg }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .morphneg }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .optdoubleneg }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .other }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .optdoubleneg }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .snegvo }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .other }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .moreThanOnePosition }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .svoneg }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .morphneg }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .morphneg }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .obligdoubleneg }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .moreThanOnePosition }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .optdoubleneg }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .optdoubleneg }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .optdoubleneg }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .other }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .snegvo }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .obligdoubleneg }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .other }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .svoneg }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .other }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .other }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .snegvo }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .obligdoubleneg }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .svoneg }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .other }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .other }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .other }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .morphneg }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .obligdoubleneg }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .morphneg }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .morphneg }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .sovneg }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .morphneg }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .morphneg }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .sonegv }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .obligdoubleneg }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .obligdoubleneg }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .morphneg }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .sovneg }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .snegvo }
  , { walsCode := "car", language := "Carib", iso := "car", value := .morphneg }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .morphneg }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .morphneg }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .optdoubleneg }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .morphneg }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .morphneg }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .morphneg }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .morphneg }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .moreThanOnePosition }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .svoneg }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .obligdoubleneg }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .negvso }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .morphneg }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .morphneg }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .negvso }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .negvso }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .other }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .sonegv }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .morphneg }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .morphneg }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .optdoubleneg }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .other }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .other }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .other }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .morphneg }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .negvos }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .morphneg }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .negvso }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .negvos }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .negsov }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .sovneg }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .morphneg }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .morphneg }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .morphneg }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .other }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .snegvo }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .optdoubleneg }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .optdoubleneg }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .other }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .morphneg }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .morphneg }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .morphneg }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .negsvo }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .moreThanOnePosition }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .optdoubleneg }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .negvso }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .other }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .other }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .morphneg }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .obligdoubleneg }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .moreThanOnePosition }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .morphneg }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .negvos }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .sonegv }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .snegvo }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .snegvo }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .other }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .other }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .sovneg }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .moreThanOnePosition }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .morphneg }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .obligdoubleneg }
  , { walsCode := "des", language := "Desano", iso := "des", value := .morphneg }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .morphneg }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .obligdoubleneg }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .morphneg }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .negvso }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .sovneg }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .morphneg }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .morphneg }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .morphneg }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .snegov }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .morphneg }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .other }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .negsov }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .other }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .sonegv }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .other }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .other }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .moreThanOnePosition }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .morphneg }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .obligdoubleneg }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .moreThanOnePosition }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .snegvo }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .svoneg }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .morphneg }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .optdoubleneg }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .morphneg }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .sovneg }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .obligdoubleneg }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .moreThanOnePosition }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .other }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .snegvo }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .obligdoubleneg }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .svoneg }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .moreThanOnePosition }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .moreThanOnePosition }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .morphneg }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .morphneg }
  , { walsCode := "ene", language := "Enets", iso := "", value := .other }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .morphneg }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .other }
  , { walsCode := "eng", language := "English", iso := "eng", value := .snegvo }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .morphneg }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .morphneg }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .sovneg }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .snegvo }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .other }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .obligdoubleneg }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .obligdoubleneg }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .obligdoubleneg }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .optdoubleneg }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .moreThanOnePosition }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .snegvo }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .snegvo }
  , { walsCode := "fre", language := "French", iso := "fra", value := .optdoubleneg }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .morphneg }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .obligdoubleneg }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .snegvo }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .optdoubleneg }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .sonegv }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .negvso }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .morphneg }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .morphneg }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .sonegv }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .morphneg }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .negvso }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .other }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .svoneg }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .optdoubleneg }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .negvos }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .svoneg }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .sonegv }
  , { walsCode := "ger", language := "German", iso := "deu", value := .moreThanOnePosition }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .morphneg }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .negvso }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .morphneg }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .svoneg }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .snegvo }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .morphneg }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .morphneg }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .other }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .snegov }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .moreThanOnePosition }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .morphneg }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .morphneg }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .obligdoubleneg }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .other }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .negsvo }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .moreThanOnePosition }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .optdoubleneg }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .sonegv }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .svoneg }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .sonegv }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .other }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .obligdoubleneg }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .other }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .morphneg }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .sonegv }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .obligdoubleneg }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .svoneg }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .morphneg }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .morphneg }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .morphneg }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .obligdoubleneg }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .snegvo }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .obligdoubleneg }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .negvso }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .morphneg }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .other }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .morphneg }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .svoneg }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .optdoubleneg }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .negvso }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .morphneg }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .sonegv }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .obligdoubleneg }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .snegvo }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .morphneg }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .negvso }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .morphneg }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .negvso }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .sonegv }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .morphneg }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .snegvo }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .other }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .snegvo }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .negvso }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .morphneg }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .sonegv }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .morphneg }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .optdoubleneg }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .snegvo }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .other }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .morphneg }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .morphneg }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .morphneg }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .morphneg }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .snegvo }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .morphneg }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .morphneg }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .other }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .sovneg }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .snegvo }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .other }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .other }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .moreThanOnePosition }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .morphneg }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .sonegv }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .optdoubleneg }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .other }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .obligdoubleneg }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .svoneg }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .other }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .moreThanOnePosition }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .negvso }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .morphneg }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .morphneg }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .other }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .other }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .snegvo }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .svoneg }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .negsov }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .negsvo }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .morphneg }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .morphneg }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .svoneg }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .negvso }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .snegvo }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .obligdoubleneg }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .sovneg }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .obligdoubleneg }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .svoneg }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .obligdoubleneg }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .svoneg }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .negvso }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .morphneg }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .morphneg }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .other }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .morphneg }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .other }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .svoneg }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .svoneg }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .snegvo }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .morphneg }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .morphneg }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .obligdoubleneg }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .morphneg }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .negvso }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .morphneg }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .other }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .sovneg }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .sovneg }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .moreThanOnePosition }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .negvso }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .moreThanOnePosition }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .morphneg }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .optdoubleneg }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .sovneg }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .other }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .morphneg }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .morphneg }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .morphneg }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .other }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .snegvo }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .obligdoubleneg }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .other }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .morphneg }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .other }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .morphneg }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .svoneg }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .moreThanOnePosition }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .morphneg }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .obligdoubleneg }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .svoneg }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .obligdoubleneg }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .moreThanOnePosition }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .moreThanOnePosition }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .sovneg }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .morphneg }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .snegvo }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .other }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .sovneg }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .obligdoubleneg }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .other }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .optdoubleneg }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .svoneg }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .sovneg }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .svoneg }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .morphneg }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .svoneg }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .svoneg }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .other }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .sonegv }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .morphneg }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .morphneg }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .optdoubleneg }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .morphneg }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .morphneg }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .morphneg }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .morphneg }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .sonegv }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .other }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .snegvo }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .snegvo }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .other }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .other }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .morphneg }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .other }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .optdoubleneg }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .morphneg }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .sovneg }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .morphneg }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .sonegv }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .morphneg }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .obligdoubleneg }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .morphneg }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .sovneg }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .negvos }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .snegvo }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .obligdoubleneg }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .obligdoubleneg }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .other }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .snegov }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .negvso }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .morphneg }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .morphneg }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .moreThanOnePosition }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .morphneg }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .morphneg }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .morphneg }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .negvso }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .moreThanOnePosition }
  ]

private def allData_1 : List (Datapoint PositionOfNegativeWordWithRespectToSubjectObjectAndVerb) :=
  [ { walsCode := "kmb", language := "Kombai", iso := "", value := .optdoubleneg }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .snegvo }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .snegvo }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .snegvo }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .moreThanOnePosition }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .morphneg }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .snegvo }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .other }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .sonegv }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .snegvo }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .obligdoubleneg }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .obligdoubleneg }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .snegvo }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .morphneg }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .snegvo }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .snegov }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .morphneg }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .optdoubleneg }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .obligdoubleneg }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .other }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .other }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .morphneg }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .morphneg }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .other }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .morphneg }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .morphneg }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .morphneg }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .negvso }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .morphneg }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .morphneg }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .moreThanOnePosition }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .sonegv }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .morphneg }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .snegvo }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .other }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .morphneg }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .optdoubleneg }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .optdoubleneg }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .osvneg }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .morphneg }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .negvso }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .svoneg }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .svoneg }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .other }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .morphneg }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .svoneg }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .sonegv }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .sovneg }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .sovneg }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .other }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .svoneg }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .optdoubleneg }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .sovneg }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .obligdoubleneg }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .morphneg }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .morphneg }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .snegvo }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .snegvo }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .other }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .morphneg }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .moreThanOnePosition }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .morphneg }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .morphneg }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .morphneg }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .svoneg }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .morphneg }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .obligdoubleneg }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .moreThanOnePosition }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .obligdoubleneg }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .morphneg }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .optdoubleneg }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .morphneg }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .moreThanOnePosition }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .obligdoubleneg }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .obligdoubleneg }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .svoneg }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .sonegv }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .morphneg }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .moreThanOnePosition }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .other }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .morphneg }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .negvos }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .svoneg }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .morphneg }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .obligdoubleneg }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .morphneg }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .moreThanOnePosition }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .other }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .obligdoubleneg }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .moreThanOnePosition }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .svoneg }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .obligdoubleneg }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .obligdoubleneg }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .moreThanOnePosition }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .moreThanOnePosition }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .optdoubleneg }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .snegvo }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .other }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .moreThanOnePosition }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .svoneg }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .snegvo }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .morphneg }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .sonegv }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .morphneg }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .morphneg }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .obligdoubleneg }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .other }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .negsvo }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .morphneg }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .negvso }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .sonegv }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .other }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .morphneg }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .morphneg }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .negvos }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .other }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .morphneg }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .svoneg }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .morphneg }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .negvso }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .negvso }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .morphneg }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .sonegv }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .morphneg }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .morphneg }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .obligdoubleneg }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .snegvo }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .snegov }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .svoneg }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .onegvs }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .moreThanOnePosition }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .sonegv }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .snegov }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .snegov }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .negvso }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .sonegv }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .negsvo }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .morphneg }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .optdoubleneg }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .sovneg }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .negsov }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .svoneg }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .obligdoubleneg }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .other }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .other }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .negsvo }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .other }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .snegvo }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .sonegv }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .svoneg }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .obligdoubleneg }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .morphneg }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .morphneg }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .other }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .moreThanOnePosition }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .optdoubleneg }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .snegvo }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .svoneg }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .svoneg }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .morphneg }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .other }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .snegvo }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .svoneg }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .svoneg }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .optdoubleneg }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .snegov }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .svoneg }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .sovneg }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .svoneg }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .morphneg }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .moreThanOnePosition }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .morphneg }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .sovneg }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .morphneg }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .other }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .other }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .svoneg }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .morphneg }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .other }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .morphneg }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .morphneg }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .morphneg }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .svoneg }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .morphneg }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .morphneg }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .negvso }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .negvso }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .negvso }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .negvso }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .obligdoubleneg }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .sovneg }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .morphneg }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .other }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .snegvo }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .obligdoubleneg }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .snegvo }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .moreThanOnePosition }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .moreThanOnePosition }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .other }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .negsov }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .obligdoubleneg }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .svoneg }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .other }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .other }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .snegvo }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .moreThanOnePosition }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .moreThanOnePosition }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .moreThanOnePosition }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .morphneg }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .moreThanOnePosition }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .svoneg }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .obligdoubleneg }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .morphneg }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .morphneg }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .optdoubleneg }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .snegvo }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .svoneg }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .sonegv }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .optdoubleneg }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .optdoubleneg }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .negvso }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .sonegv }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .sonegv }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .other }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .svoneg }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .other }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .negvso }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .snegvo }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .snegvo }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .morphneg }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .obligdoubleneg }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .sonegv }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .other }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .moreThanOnePosition }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .sovneg }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .morphneg }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .other }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .moreThanOnePosition }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .negvso }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .snegvo }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .other }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .morphneg }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .snegvo }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .snegvo }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .sovneg }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .morphneg }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .morphneg }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .morphneg }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .sovneg }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .optdoubleneg }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .sonegv }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .moreThanOnePosition }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .moreThanOnePosition }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .snegvo }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .morphneg }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .other }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .other }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .obligdoubleneg }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .morphneg }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .snegvo }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .snegvo }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .sonegv }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .snegvo }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .sonegv }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .morphneg }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .other }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .morphneg }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .morphneg }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .other }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .morphneg }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .other }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .other }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .svoneg }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .sonegv }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .morphneg }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .negsvo }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .svoneg }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .moreThanOnePosition }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .other }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .svoneg }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .moreThanOnePosition }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .snegvo }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .other }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .negvos }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .negvos }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .morphneg }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .negvso }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .negvso }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .negvso }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .optdoubleneg }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .optdoubleneg }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .morphneg }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .morphneg }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .morphneg }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .obligdoubleneg }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .morphneg }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .moreThanOnePosition }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .moreThanOnePosition }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .morphneg }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .svoneg }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .morphneg }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .morphneg }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .negsov }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .snegvo }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .other }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .other }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .svoneg }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .other }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .sonegv }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .morphneg }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .svoneg }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .other }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .morphneg }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .morphneg }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .morphneg }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .other }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .moreThanOnePosition }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .sonegv }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .svoneg }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .morphneg }
  , { walsCode := "one", language := "One", iso := "aun", value := .optdoubleneg }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .other }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .sovneg }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .morphneg }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .morphneg }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .morphneg }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .moreThanOnePosition }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .obligdoubleneg }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .obligdoubleneg }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .sovneg }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .other }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .negvos }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .obligdoubleneg }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .optdoubleneg }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .negsvo }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .morphneg }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .negsov }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .moreThanOnePosition }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .snegvo }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .snegvo }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .negvso }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .morphneg }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .sonegv }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .morphneg }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .morphneg }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .svoneg }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .morphneg }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .morphneg }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .optdoubleneg }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .moreThanOnePosition }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .moreThanOnePosition }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .obligdoubleneg }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .morphneg }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .morphneg }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .morphneg }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .moreThanOnePosition }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .other }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .morphneg }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .obligdoubleneg }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .other }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .vsoneg }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .other }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .snegvo }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .optdoubleneg }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .snegvo }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .morphneg }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .obligdoubleneg }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .snegvo }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .morphneg }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .snegvo }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .moreThanOnePosition }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .snegvo }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .morphneg }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .other }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .morphneg }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .other }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .morphneg }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .other }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .other }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .obligdoubleneg }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .moreThanOnePosition }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .negvso }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .obligdoubleneg }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .moreThanOnePosition }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .other }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .morphneg }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .optdoubleneg }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .morphneg }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .other }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .sonegv }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .morphneg }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .negsov }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .morphneg }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .other }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .morphneg }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .optdoubleneg }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .snegvo }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .other }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .svoneg }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .obligdoubleneg }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .negvso }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .moreThanOnePosition }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .other }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .morphneg }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .optdoubleneg }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .morphneg }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .morphneg }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .snegvo }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .other }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .moreThanOnePosition }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .morphneg }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .snegov }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .obligdoubleneg }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .morphneg }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .moreThanOnePosition }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .morphneg }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .svoneg }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .morphneg }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .other }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .sonegv }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .sovneg }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .snegvo }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .other }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .snegvo }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .morphneg }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .other }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .snegvo }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .negvos }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .ovnegs }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .morphneg }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .sovneg }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .moreThanOnePosition }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .morphneg }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .obligdoubleneg }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .morphneg }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .other }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .morphneg }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .other }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .sovneg }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .morphneg }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .morphneg }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .svoneg }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .other }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .morphneg }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .snegvo }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .sonegv }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .morphneg }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .sovneg }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .morphneg }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .moreThanOnePosition }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .morphneg }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .snegvo }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .sonegv }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .other }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .sonegv }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .sonegv }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .svoneg }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .morphneg }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .negvso }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .sovneg }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .snegvo }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .snegvo }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .sovneg }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .snegvo }
  , { walsCode := "so", language := "So", iso := "teu", value := .negvso }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .snegvo }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .morphneg }
  , { walsCode := "som", language := "Somali", iso := "som", value := .sonegv }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .snegov }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .other }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .morphneg }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .obligdoubleneg }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .svoneg }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .other }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .snegvo }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .negvso }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .snegvo }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .snegvo }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .other }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .other }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .morphneg }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .morphneg }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .snegvo }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .optdoubleneg }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .morphneg }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .moreThanOnePosition }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .svoneg }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .morphneg }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .obligdoubleneg }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .morphneg }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .other }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .negvso }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .negvso }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .snegvo }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .negsov }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .morphneg }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .other }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .sonegv }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .morphneg }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .morphneg }
  ]

private def allData_2 : List (Datapoint PositionOfNegativeWordWithRespectToSubjectObjectAndVerb) :=
  [ { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .snegvo }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .sonegv }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .optdoubleneg }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .morphneg }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .obligdoubleneg }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .morphneg }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .morphneg }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .other }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .other }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .morphneg }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .optdoubleneg }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .other }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .sonegv }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .other }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .negvso }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .morphneg }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .optdoubleneg }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .snegvo }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .morphneg }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .negsvo }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .other }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .obligdoubleneg }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .moreThanOnePosition }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .other }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .negvso }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .optdoubleneg }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .sovneg }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .negsvo }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .morphneg }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .snegvo }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .snegvo }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .morphneg }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .moreThanOnePosition }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .obligdoubleneg }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .morphneg }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .moreThanOnePosition }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .morphneg }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .morphneg }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .optdoubleneg }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .snegvo }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .obligdoubleneg }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .morphneg }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .optdoubleneg }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .negvso }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .moreThanOnePosition }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .morphneg }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .obligdoubleneg }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .svoneg }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .morphneg }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .snegvo }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .morphneg }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .sonegv }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .morphneg }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .optdoubleneg }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .morphneg }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .morphneg }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .other }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .other }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .morphneg }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .moreThanOnePosition }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .morphneg }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .negvso }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .moreThanOnePosition }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .morphneg }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .sovneg }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .optdoubleneg }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .obligdoubleneg }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .sonegv }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .morphneg }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .morphneg }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .negvos }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .morphneg }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .morphneg }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .snegov }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .morphneg }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .svoneg }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .morphneg }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .morphneg }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .other }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .obligdoubleneg }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .onegvs }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .morphneg }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .morphneg }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .obligdoubleneg }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .negvos }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .moreThanOnePosition }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .optdoubleneg }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .morphneg }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .morphneg }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .sonegv }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .sovneg }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .snegvo }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .svoneg }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .snegvo }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .sonegv }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .onegvs }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .snegvo }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .morphneg }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .optdoubleneg }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .sonegv }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .other }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .sovneg }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .sonegv }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .morphneg }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .morphneg }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .morphneg }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .snegov }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .morphneg }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .snegvo }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .morphneg }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .sonegv }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .other }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .sonegv }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .snegvo }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .other }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .morphneg }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .morphneg }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .sovneg }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .morphneg }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .morphneg }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .morphneg }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .other }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .obligdoubleneg }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .svoneg }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .negvos }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .negsov }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .morphneg }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .other }
  , { walsCode := "was", language := "Washo", iso := "was", value := .morphneg }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .sonegv }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .morphneg }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .morphneg }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .obligdoubleneg }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .other }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .negvso }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .vsnego }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .negvos }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .svoneg }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .moreThanOnePosition }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .moreThanOnePosition }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .other }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .optdoubleneg }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .morphneg }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .snegvo }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .moreThanOnePosition }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .sovneg }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .optsingleneg }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .morphneg }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .snegvo }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .morphneg }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .other }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .morphneg }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .morphneg }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .morphneg }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .morphneg }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .negvso }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .obligdoubleneg }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .snegov }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .morphneg }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .other }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .other }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .other }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .sonegv }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .morphneg }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .snegvo }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .snegvo }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .other }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .snegvo }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .other }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .morphneg }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .morphneg }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .obligdoubleneg }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .svnego }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .other }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .negsov }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .obligdoubleneg }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .obligdoubleneg }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .negvso }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .morphneg }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .negvso }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .morphneg }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .morphneg }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .optdoubleneg }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .moreThanOnePosition }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .other }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .morphneg }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .obligdoubleneg }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .morphneg }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .obligdoubleneg }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .other }
  ]

/-- Complete WALS 144A dataset (1190 languages). -/
def allData : List (Datapoint PositionOfNegativeWordWithRespectToSubjectObjectAndVerb) := allData_0 ++ allData_1 ++ allData_2

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144A
