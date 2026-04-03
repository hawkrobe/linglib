import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 112A: Negative Morphemes
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 112A`.

Chapter 112, 1157 languages.
-/

namespace Core.WALS.F112A

/-- WALS 112A values. -/
inductive NegativeMorphemeType where
  | negativeAffix  -- Negative affix (395 languages)
  | negativeParticle  -- Negative particle (502 languages)
  | negativeAuxiliaryVerb  -- Negative auxiliary verb (47 languages)
  | negativeWordUnclearIfVerbOrParticle  -- Negative word, unclear if verb or particle (73 languages)
  | variationBetweenNegativeWordAndAffix  -- Variation between negative word and affix (21 languages)
  | doubleNegation  -- Double negation (119 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint NegativeMorphemeType) :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .negativeParticle }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .negativeParticle }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .negativeAffix }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .negativeParticle }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .negativeAffix }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .negativeAuxiliaryVerb }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .doubleNegation }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .negativeAffix }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .negativeAuxiliaryVerb }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .negativeParticle }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .negativeParticle }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .negativeAffix }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .negativeParticle }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .negativeAffix }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .negativeParticle }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .negativeAuxiliaryVerb }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .negativeParticle }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .negativeParticle }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .negativeParticle }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .negativeAffix }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .negativeParticle }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .negativeParticle }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .negativeParticle }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .negativeParticle }
  , { walsCode := "alc", language := "Allentiac", iso := "", value := .negativeParticle }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .negativeParticle }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .negativeAffix }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .negativeAffix }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .doubleNegation }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .doubleNegation }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .negativeParticle }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .negativeParticle }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .negativeAffix }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .negativeParticle }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .doubleNegation }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .doubleNegation }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .doubleNegation }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .negativeParticle }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .negativeAffix }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .negativeParticle }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .negativeParticle }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .negativeParticle }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .negativeAffix }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .doubleNegation }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .negativeAffix }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .negativeAffix }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .negativeParticle }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .negativeParticle }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .negativeParticle }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .negativeParticle }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .negativeAffix }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .negativeParticle }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .doubleNegation }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .negativeParticle }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .doubleNegation }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .negativeParticle }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .negativeParticle }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .negativeAffix }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .negativeAuxiliaryVerb }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .negativeParticle }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .negativeAffix }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .negativeAffix }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .negativeParticle }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .negativeAffix }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .doubleNegation }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .negativeAffix }
  , { walsCode := "au", language := "Au", iso := "avt", value := .negativeParticle }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .negativeAuxiliaryVerb }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .negativeParticle }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .doubleNegation }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .negativeAffix }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .negativeParticle }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .negativeAffix }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .negativeAffix }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .negativeAffix }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .doubleNegation }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .negativeParticle }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .doubleNegation }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .negativeParticle }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .negativeParticle }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .negativeParticle }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .negativeParticle }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .negativeAffix }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .negativeAffix }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .negativeParticle }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .negativeParticle }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .doubleNegation }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .negativeAffix }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .negativeParticle }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .negativeAffix }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .negativeAffix }
  , { walsCode := "mug", language := "Bargam", iso := "mlp", value := .negativeAffix }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .negativeParticle }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .negativeAffix }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .negativeParticle }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .negativeParticle }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .negativeParticle }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .negativeParticle }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .negativeAffix }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .negativeAffix }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .negativeParticle }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .negativeParticle }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .negativeParticle }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .negativeParticle }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .negativeParticle }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .negativeAffix }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .negativeAffix }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .negativeAffix }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .negativeParticle }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .doubleNegation }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .negativeAffix }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .negativeAffix }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .negativeParticle }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .negativeParticle }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .negativeParticle }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .negativeParticle }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .negativeParticle }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .negativeAffix }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .negativeAffix }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .negativeAffix }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .doubleNegation }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .doubleNegation }
  , { walsCode := "boi", language := "Boiken", iso := "bzf", value := .doubleNegation }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .negativeAffix }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .negativeParticle }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .negativeAuxiliaryVerb }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .negativeAffix }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .negativeAffix }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .negativeAffix }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .doubleNegation }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .negativeParticle }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .negativeParticle }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .negativeAffix }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .negativeParticle }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .negativeParticle }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .negativeParticle }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .doubleNegation }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .negativeParticle }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .negativeParticle }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .negativeAffix }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .doubleNegation }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .negativeAffix }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .negativeAffix }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .negativeAffix }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .negativeAffix }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .negativeParticle }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .doubleNegation }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .doubleNegation }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .negativeParticle }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .negativeAffix }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .negativeAffix }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .negativeAffix }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .negativeParticle }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .negativeParticle }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .negativeAffix }
  , { walsCode := "car", language := "Carib", iso := "car", value := .negativeAffix }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .negativeAffix }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .negativeAffix }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .negativeParticle }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .negativeAffix }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .negativeAffix }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .negativeAffix }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .negativeAffix }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .negativeParticle }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .doubleNegation }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .negativeParticle }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .negativeAffix }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .negativeAffix }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .negativeParticle }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .negativeParticle }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .negativeParticle }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .negativeAffix }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .negativeAffix }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .negativeAffix }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .negativeAffix }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .negativeParticle }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .negativeAffix }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .negativeParticle }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .negativeAffix }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .negativeParticle }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .negativeParticle }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .negativeParticle }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .negativeAffix }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .negativeAffix }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .negativeAffix }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .negativeAffix }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .negativeParticle }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .negativeParticle }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .negativeParticle }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .negativeAffix }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .negativeAffix }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .negativeAffix }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .negativeAffix }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .negativeParticle }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .negativeParticle }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .negativeAffix }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .negativeParticle }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .negativeParticle }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .negativeParticle }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .negativeAffix }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .doubleNegation }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .negativeParticle }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .negativeAffix }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .negativeParticle }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .negativeParticle }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .negativeParticle }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .negativeParticle }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .negativeParticle }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .negativeParticle }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .negativeAffix }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .doubleNegation }
  , { walsCode := "des", language := "Desano", iso := "des", value := .negativeAffix }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .negativeAffix }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .doubleNegation }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .negativeParticle }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .negativeParticle }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .negativeAffix }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .negativeAffix }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .negativeAuxiliaryVerb }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .negativeAuxiliaryVerb }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .negativeAffix }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .negativeAffix }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .negativeAffix }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .negativeAuxiliaryVerb }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .negativeAffix }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .negativeParticle }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .negativeParticle }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .negativeParticle }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .negativeParticle }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .negativeParticle }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .negativeParticle }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .negativeParticle }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .negativeAffix }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .doubleNegation }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .negativeParticle }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .negativeParticle }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .negativeAffix }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .negativeAffix }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .negativeParticle }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .negativeParticle }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .negativeParticle }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .doubleNegation }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .negativeAffix }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .negativeParticle }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .negativeParticle }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .negativeParticle }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .doubleNegation }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .negativeAffix }
  , { walsCode := "ene", language := "Enets", iso := "", value := .negativeAuxiliaryVerb }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .negativeParticle }
  , { walsCode := "eng", language := "English", iso := "eng", value := .negativeParticle }
  , { walsCode := "eny", language := "Enya", iso := "gey", value := .negativeAffix }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .negativeAffix }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .negativeAffix }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .negativeParticle }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .negativeParticle }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .negativeParticle }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .doubleNegation }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .doubleNegation }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .doubleNegation }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .negativeParticle }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .negativeAuxiliaryVerb }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "fre", language := "French", iso := "fra", value := .negativeParticle }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .negativeAffix }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .negativeAffix }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .doubleNegation }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .negativeAuxiliaryVerb }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .negativeParticle }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .negativeParticle }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .negativeParticle }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .negativeParticle }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .negativeAffix }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .negativeAffix }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .negativeParticle }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .negativeAffix }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .negativeParticle }
  , { walsCode := "grs", language := "Garus", iso := "gyb", value := .negativeParticle }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .negativeParticle }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .negativeParticle }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .negativeParticle }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .negativeParticle }
  , { walsCode := "ger", language := "German", iso := "deu", value := .negativeParticle }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .negativeAffix }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .negativeAffix }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .negativeParticle }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .negativeAffix }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .negativeAffix }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .negativeParticle }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .negativeAuxiliaryVerb }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .negativeParticle }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .negativeAffix }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .negativeAffix }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .doubleNegation }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .negativeParticle }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .negativeParticle }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .negativeParticle }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .negativeParticle }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .negativeParticle }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .doubleNegation }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .negativeParticle }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .negativeParticle }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .negativeAffix }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .negativeParticle }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .doubleNegation }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .negativeAffix }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .negativeAffix }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .negativeAffix }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .doubleNegation }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .doubleNegation }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .negativeAuxiliaryVerb }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .negativeAffix }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .negativeAffix }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .negativeParticle }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .negativeParticle }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .negativeParticle }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .negativeAffix }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .negativeParticle }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .doubleNegation }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .negativeParticle }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .negativeAffix }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .negativeAffix }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .negativeParticle }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .negativeParticle }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .negativeAffix }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .negativeAffix }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .negativeAffix }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .negativeAuxiliaryVerb }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .negativeParticle }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .negativeAffix }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .negativeAffix }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .negativeAffix }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .negativeAffix }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .negativeParticle }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .negativeAffix }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .negativeAffix }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .negativeParticle }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .negativeParticle }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .negativeParticle }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .doubleNegation }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .negativeAffix }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .doubleNegation }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .negativeParticle }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .negativeAuxiliaryVerb }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .negativeParticle }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .negativeAffix }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .negativeAffix }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .negativeParticle }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .negativeAffix }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .negativeParticle }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .negativeAffix }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .negativeParticle }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .negativeAffix }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .negativeAffix }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .negativeParticle }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .negativeParticle }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .negativeParticle }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .doubleNegation }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .negativeParticle }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .doubleNegation }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .negativeParticle }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .doubleNegation }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .negativeParticle }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .negativeParticle }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .negativeAffix }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .negativeAffix }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .negativeParticle }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .negativeAffix }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .negativeAffix }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .negativeParticle }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .negativeAffix }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .negativeAffix }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .doubleNegation }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .negativeAffix }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .negativeParticle }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .negativeAffix }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .negativeParticle }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .negativeAffix }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .negativeParticle }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .negativeParticle }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .negativeParticle }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .negativeParticle }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .negativeAffix }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .negativeAffix }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .negativeParticle }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .negativeAffix }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .negativeAffix }
  , { walsCode := "kmi", language := "Kami", iso := "kcu", value := .negativeAffix }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .negativeAffix }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .negativeParticle }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .doubleNegation }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .negativeAffix }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .negativeParticle }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .negativeAffix }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .negativeParticle }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .negativeParticle }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .negativeAffix }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .doubleNegation }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .doubleNegation }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .doubleNegation }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .negativeParticle }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .negativeAffix }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .negativeAuxiliaryVerb }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .negativeParticle }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .doubleNegation }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .negativeParticle }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .negativeAffix }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .negativeAffix }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .negativeParticle }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .negativeAffix }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .negativeParticle }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .negativeParticle }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .negativeParticle }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .negativeAffix }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .negativeAffix }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .negativeAffix }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .negativeAffix }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .negativeAffix }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .negativeAffix }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .negativeAffix }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .negativeParticle }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .negativeParticle }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .negativeAffix }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .negativeParticle }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .negativeParticle }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .negativeAffix }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .negativeAffix }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .negativeParticle }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .negativeAffix }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .doubleNegation }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .negativeAffix }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .doubleNegation }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .doubleNegation }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .negativeParticle }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .negativeParticle }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .negativeAffix }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .negativeAffix }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .negativeAuxiliaryVerb }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .negativeAffix }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .negativeParticle }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .negativeAffix }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .negativeAffix }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .negativeAuxiliaryVerb }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .negativeAffix }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .negativeAuxiliaryVerb }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .negativeAuxiliaryVerb }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .negativeAuxiliaryVerb }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .negativeAuxiliaryVerb }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .doubleNegation }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .negativeAffix }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .negativeParticle }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .negativeParticle }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .negativeParticle }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .doubleNegation }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .doubleNegation }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .negativeParticle }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .negativeAffix }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .negativeParticle }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .negativeAffix }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .negativeParticle }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .doubleNegation }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .negativeParticle }
  ]

private def allData_1 : List (Datapoint NegativeMorphemeType) :=
  [ { walsCode := "klg", language := "Kulung", iso := "kle", value := .negativeAffix }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .negativeAffix }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .negativeParticle }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .negativeAffix }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .negativeAffix }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .negativeAffix }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .negativeParticle }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .negativeAffix }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .negativeAffix }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .negativeParticle }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .negativeParticle }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .negativeAffix }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .negativeParticle }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .negativeParticle }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .negativeAffix }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .negativeAffix }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .negativeParticle }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .negativeAffix }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .negativeAuxiliaryVerb }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .negativeParticle }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .negativeParticle }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .negativeParticle }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .negativeAffix }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .negativeParticle }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .negativeParticle }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .negativeParticle }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .negativeParticle }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .doubleNegation }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .negativeAffix }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .negativeAffix }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .negativeParticle }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .negativeParticle }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .negativeAffix }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .negativeAffix }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .negativeAffix }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .negativeAffix }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .negativeAffix }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .negativeParticle }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .negativeAffix }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .doubleNegation }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .negativeParticle }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .doubleNegation }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .doubleNegation }
  , { walsCode := "les", language := "Lese", iso := "les", value := .negativeAffix }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .negativeAffix }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .negativeAffix }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .doubleNegation }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .doubleNegation }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .negativeParticle }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .negativeAffix }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .negativeParticle }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .negativeParticle }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .negativeAffix }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .negativeParticle }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .negativeAffix }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .doubleNegation }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .negativeAffix }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .negativeAffix }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .negativeParticle }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .doubleNegation }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .negativeParticle }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .negativeParticle }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .doubleNegation }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .doubleNegation }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .negativeParticle }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .negativeParticle }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .negativeAffix }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .negativeParticle }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .negativeParticle }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .negativeParticle }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .negativeParticle }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .negativeParticle }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .negativeAffix }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .negativeParticle }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .negativeAffix }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .negativeAffix }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .doubleNegation }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .negativeAuxiliaryVerb }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .doubleNegation }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .negativeParticle }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .negativeAffix }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .negativeAffix }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .negativeParticle }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .negativeParticle }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .negativeAffix }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .negativeParticle }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .negativeAffix }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .negativeParticle }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .negativeParticle }
  , { walsCode := "mmw", language := "Mambwe", iso := "mgr", value := .negativeAffix }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .negativeAffix }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .negativeParticle }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .negativeAffix }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .negativeAffix }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .doubleNegation }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .negativeParticle }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .negativeParticle }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .negativeParticle }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .negativeParticle }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .negativeAuxiliaryVerb }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .negativeParticle }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .negativeAffix }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .negativeParticle }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .negativeParticle }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .negativeParticle }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .negativeParticle }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .negativeAuxiliaryVerb }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .doubleNegation }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .negativeParticle }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .negativeParticle }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .negativeParticle }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .negativeParticle }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .doubleNegation }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .negativeAffix }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .negativeAffix }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .negativeParticle }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .negativeParticle }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .negativeParticle }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .negativeParticle }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .negativeAffix }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .negativeParticle }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .negativeParticle }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .negativeParticle }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .negativeParticle }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .doubleNegation }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .negativeParticle }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .negativeAffix }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .negativeParticle }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .negativeAffix }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .negativeAffix }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .negativeParticle }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .doubleNegation }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .negativeParticle }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .negativeParticle }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .negativeAffix }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .negativeAffix }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .negativeAffix }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .negativeAffix }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .negativeParticle }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "mhl", language := "Miri (Hill):", iso := "mrg", value := .negativeAffix }
  , { walsCode := "mir", language := "Miriwung", iso := "mep", value := .negativeParticle }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .negativeAffix }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .negativeAffix }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .negativeParticle }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .negativeParticle }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .negativeParticle }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .negativeParticle }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .negativeParticle }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .negativeParticle }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .doubleNegation }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .negativeParticle }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .negativeAffix }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .negativeParticle }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .negativeParticle }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .negativeParticle }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .doubleNegation }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .negativeParticle }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .negativeParticle }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .negativeParticle }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .doubleNegation }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .negativeParticle }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .negativeParticle }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .negativeAuxiliaryVerb }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .negativeParticle }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .negativeParticle }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .negativeParticle }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .negativeAffix }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .negativeParticle }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .negativeParticle }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .doubleNegation }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .negativeAffix }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .negativeAffix }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .negativeParticle }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .negativeParticle }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .negativeParticle }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .negativeParticle }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .negativeParticle }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .negativeParticle }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .negativeParticle }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .negativeParticle }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .negativeParticle }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .negativeParticle }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .negativeParticle }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .negativeAffix }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .doubleNegation }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .negativeParticle }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .negativeParticle }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .negativeAuxiliaryVerb }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .negativeAffix }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .negativeParticle }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .negativeParticle }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .negativeAuxiliaryVerb }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .negativeParticle }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .negativeParticle }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .negativeParticle }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .negativeAffix }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .negativeAuxiliaryVerb }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .negativeParticle }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .negativeParticle }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .negativeAffix }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .negativeAffix }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .negativeAffix }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .negativeAffix }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .negativeParticle }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .negativeAffix }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .negativeParticle }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .negativeParticle }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .doubleNegation }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .negativeParticle }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .negativeParticle }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .doubleNegation }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .negativeAffix }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .negativeParticle }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .negativeAuxiliaryVerb }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .negativeParticle }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .negativeAffix }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .negativeParticle }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .negativeAffix }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .negativeAffix }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .negativeParticle }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .negativeAffix }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .negativeParticle }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .negativeAffix }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .negativeParticle }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .negativeAuxiliaryVerb }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .negativeAffix }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .negativeParticle }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .negativeParticle }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .negativeParticle }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .negativeParticle }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .negativeParticle }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .negativeParticle }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .negativeParticle }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .negativeAffix }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .negativeAuxiliaryVerb }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .negativeAffix }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .negativeParticle }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .negativeAffix }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .negativeAffix }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .negativeAffix }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .doubleNegation }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .negativeAffix }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .negativeParticle }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .negativeParticle }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .negativeAffix }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .negativeParticle }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .negativeAffix }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .negativeAffix }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .negativeParticle }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .negativeParticle }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .negativeAffix }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .negativeParticle }
  , { walsCode := "nyh", language := "Nyiha", iso := "nih", value := .negativeAffix }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .negativeParticle }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .negativeAffix }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .negativeParticle }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .negativeParticle }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .negativeParticle }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .negativeAffix }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .negativeAffix }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .negativeAffix }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .negativeParticle }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .negativeParticle }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .negativeParticle }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .negativeAffix }
  , { walsCode := "one", language := "One", iso := "aun", value := .negativeParticle }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .negativeParticle }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .negativeParticle }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .negativeAffix }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .negativeAffix }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .negativeAffix }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .doubleNegation }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .doubleNegation }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .negativeParticle }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .negativeParticle }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .negativeParticle }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .doubleNegation }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .negativeParticle }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .negativeParticle }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .negativeAffix }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .negativeParticle }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .negativeParticle }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .negativeParticle }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .negativeAffix }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .negativeParticle }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .negativeAffix }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .negativeAffix }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .doubleNegation }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .negativeAffix }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .negativeAffix }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .negativeParticle }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .negativeParticle }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .negativeAffix }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .negativeAffix }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .doubleNegation }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .negativeAffix }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .negativeAffix }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .negativeAffix }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .negativeParticle }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .negativeParticle }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .negativeAffix }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .doubleNegation }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .negativeParticle }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .negativeParticle }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .negativeParticle }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .negativeAuxiliaryVerb }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .negativeParticle }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .negativeAffix }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .doubleNegation }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .negativeAffix }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .negativeAffix }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .negativeParticle }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .negativeParticle }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .negativeAffix }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .negativeAffix }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .negativeParticle }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .negativeAffix }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .negativeParticle }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .negativeAffix }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .doubleNegation }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .negativeParticle }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .negativeAuxiliaryVerb }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .doubleNegation }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .negativeParticle }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .negativeAffix }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .negativeAffix }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .negativeParticle }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .negativeAffix }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .negativeParticle }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .negativeAffix }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .negativeParticle }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .negativeAffix }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .negativeAffix }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .negativeParticle }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .negativeParticle }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .doubleNegation }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .negativeParticle }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .negativeAuxiliaryVerb }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .negativeParticle }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .negativeAffix }
  , { walsCode := "rnd", language := "Rundi", iso := "run", value := .negativeAffix }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .negativeAffix }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .negativeAffix }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .negativeAffix }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .negativeParticle }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .negativeAuxiliaryVerb }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .negativeParticle }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .negativeAffix }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .negativeParticle }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .doubleNegation }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .negativeAffix }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .negativeParticle }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .negativeAffix }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .negativeParticle }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .negativeAffix }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .negativeParticle }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .negativeAuxiliaryVerb }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .negativeParticle }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .negativeParticle }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .negativeAffix }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .negativeAuxiliaryVerb }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .negativeAffix }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .negativeParticle }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .negativeParticle }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .negativeAffix }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .doubleNegation }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .negativeAffix }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .negativeParticle }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .negativeAffix }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .negativeParticle }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .negativeAffix }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .negativeAffix }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .negativeParticle }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .negativeParticle }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .negativeAffix }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .negativeParticle }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .negativeParticle }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .negativeAffix }
  , { walsCode := "shy", language := "Shira Yughur", iso := "yuy", value := .negativeParticle }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .negativeAffix }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .negativeParticle }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .negativeAffix }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .negativeParticle }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .negativeParticle }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .negativeParticle }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .negativeParticle }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .negativeAffix }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .negativeParticle }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .negativeAuxiliaryVerb }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .negativeParticle }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .negativeParticle }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .negativeParticle }
  , { walsCode := "so", language := "So", iso := "teu", value := .negativeParticle }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .negativeParticle }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .negativeAffix }
  , { walsCode := "som", language := "Somali", iso := "som", value := .negativeParticle }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .negativeParticle }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .negativeAffix }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .negativeAffix }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .doubleNegation }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .negativeParticle }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .negativeParticle }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .negativeParticle }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .negativeAuxiliaryVerb }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "sub", language := "Subiya", iso := "sbs", value := .doubleNegation }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .doubleNegation }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .negativeAffix }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .negativeAffix }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .negativeParticle }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .negativeAffix }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .doubleNegation }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .negativeParticle }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .negativeAffix }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .negativeParticle }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .negativeAffix }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .doubleNegation }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .negativeAffix }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .negativeParticle }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .negativeParticle }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .negativeParticle }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .negativeAuxiliaryVerb }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .negativeParticle }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .negativeAffix }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .negativeParticle }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .negativeParticle }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .negativeAffix }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .negativeAffix }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .negativeParticle }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .negativeParticle }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .negativeAffix }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .doubleNegation }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .negativeAffix }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .negativeAffix }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .negativeParticle }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .negativeAffix }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .negativeAffix }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .negativeAffix }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .negativeParticle }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .negativeParticle }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .negativeParticle }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .negativeParticle }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .negativeAffix }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .negativeParticle }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .negativeParticle }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .negativeAffix }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .negativeParticle }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .negativeParticle }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .doubleNegation }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .negativeParticle }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .negativeParticle }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .negativeParticle }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .negativeParticle }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .negativeParticle }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .negativeParticle }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .negativeAffix }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .negativeParticle }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .negativeAuxiliaryVerb }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .negativeAffix }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .negativeParticle }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .doubleNegation }
  ]

private def allData_2 : List (Datapoint NegativeMorphemeType) :=
  [ { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .negativeAffix }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .negativeParticle }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .negativeAffix }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .negativeAffix }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .negativeParticle }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .doubleNegation }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .negativeAffix }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .negativeParticle }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .negativeParticle }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .negativeAffix }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .doubleNegation }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .negativeAffix }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .negativeParticle }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .negativeAffix }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .negativeParticle }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .negativeAffix }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .negativeParticle }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .negativeAffix }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .negativeAffix }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .negativeParticle }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .negativeAffix }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .negativeAffix }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .negativeParticle }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .negativeAffix }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .negativeAuxiliaryVerb }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .doubleNegation }
  , { walsCode := "tsn", language := "Tsonga", iso := "tso", value := .negativeParticle }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .negativeParticle }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .negativeParticle }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .negativeAffix }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .negativeAffix }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .negativeAffix }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .negativeAffix }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .negativeParticle }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .negativeAffix }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .negativeAffix }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .negativeAffix }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .negativeParticle }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .doubleNegation }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .negativeAffix }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .negativeAffix }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .doubleNegation }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .negativeParticle }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .negativeParticle }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .negativeParticle }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .negativeAffix }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .negativeAffix }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .negativeAuxiliaryVerb }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .negativeParticle }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .negativeParticle }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .negativeParticle }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .negativeParticle }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .negativeAffix }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .negativeParticle }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .negativeParticle }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .negativeParticle }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .negativeAffix }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .doubleNegation }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .negativeAffix }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .negativeAffix }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .negativeAffix }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .doubleNegation }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .negativeParticle }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .negativeAffix }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .negativeParticle }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .negativeParticle }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .negativeParticle }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .negativeParticle }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .negativeAffix }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .negativeAffix }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .negativeAffix }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .negativeAffix }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .negativeAffix }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .negativeParticle }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .negativeParticle }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .doubleNegation }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .negativeParticle }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .negativeAffix }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .negativeParticle }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .negativeParticle }
  , { walsCode := "was", language := "Washo", iso := "was", value := .negativeAffix }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .negativeParticle }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .negativeAffix }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .variationBetweenNegativeWordAndAffix }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .negativeAffix }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .doubleNegation }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .negativeParticle }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .negativeParticle }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .negativeParticle }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .negativeParticle }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .negativeParticle }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .negativeParticle }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .negativeParticle }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .doubleNegation }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .negativeParticle }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .negativeParticle }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .negativeAffix }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .negativeAffix }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .negativeParticle }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .negativeParticle }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .negativeParticle }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .negativeParticle }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .negativeAffix }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .negativeAffix }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .negativeParticle }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .negativeAffix }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .negativeAffix }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .negativeAffix }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .negativeAffix }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .negativeParticle }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .doubleNegation }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .negativeParticle }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .negativeAffix }
  , { walsCode := "yrr", language := "Yaruro", iso := "yae", value := .negativeAffix }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .negativeParticle }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .negativeParticle }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .negativeParticle }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .negativeParticle }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .negativeAffix }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .negativeParticle }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .negativeParticle }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .negativeParticle }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .negativeAffix }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .negativeAffix }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .doubleNegation }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .negativeAffix }
  , { walsCode := "yrm", language := "Yurimangí", iso := "", value := .negativeAffix }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .negativeParticle }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .negativeParticle }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .doubleNegation }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .doubleNegation }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .negativeParticle }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .negativeAffix }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .negativeParticle }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .negativeAffix }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .negativeAffix }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .negativeWordUnclearIfVerbOrParticle }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .negativeParticle }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .negativeAuxiliaryVerb }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .negativeAffix }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .doubleNegation }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .negativeAffix }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .doubleNegation }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .negativeParticle }
  ]

/-- Complete WALS 112A dataset (1157 languages). -/
def allData : List (Datapoint NegativeMorphemeType) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1157 := by native_decide

theorem count_negativeAffix :
    (allData.filter (·.value == .negativeAffix)).length = 395 := by native_decide
theorem count_negativeParticle :
    (allData.filter (·.value == .negativeParticle)).length = 502 := by native_decide
theorem count_negativeAuxiliaryVerb :
    (allData.filter (·.value == .negativeAuxiliaryVerb)).length = 47 := by native_decide
theorem count_negativeWordUnclearIfVerbOrParticle :
    (allData.filter (·.value == .negativeWordUnclearIfVerbOrParticle)).length = 73 := by native_decide
theorem count_variationBetweenNegativeWordAndAffix :
    (allData.filter (·.value == .variationBetweenNegativeWordAndAffix)).length = 21 := by native_decide
theorem count_doubleNegation :
    (allData.filter (·.value == .doubleNegation)).length = 119 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F112A
