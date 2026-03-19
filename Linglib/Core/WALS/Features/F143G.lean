import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 143G: Minor morphological means of signaling negation
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 143G`.

Chapter 143, 1325 languages.
-/

namespace Core.WALS.F143G

/-- WALS 143G values. -/
inductive MinorMorphologicalMeansOfSignalingNegation where
  | negtone  -- NegTone (7 languages)
  | neginfix  -- NegInfix (2 languages)
  | negstemchange  -- NegStemChange (1 languages)
  | none  -- None (1315 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint MinorMorphologicalMeansOfSignalingNegation) :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .none }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .none }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .none }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .none }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .none }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .none }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .none }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .none }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .none }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .none }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .none }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .none }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .none }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .none }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .none }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .none }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .none }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .none }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .none }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .none }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .none }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .none }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .none }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .none }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .none }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .none }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .none }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .none }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .none }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .none }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .none }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .none }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .none }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .none }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .none }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .none }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .none }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .none }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .none }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .none }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .none }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .none }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .none }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .none }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .none }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .none }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .none }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .none }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .none }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .none }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .none }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .none }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .none }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .none }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .none }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .none }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .none }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .none }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .none }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .none }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .none }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .none }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .none }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .none }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .none }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .none }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .none }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .none }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .none }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .none }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .none }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .none }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .none }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .none }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .none }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .none }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .none }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .none }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .none }
  , { walsCode := "au", language := "Au", iso := "avt", value := .none }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .none }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .none }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .none }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .none }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .none }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .none }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .none }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .none }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .none }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .none }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .none }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .none }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .none }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .none }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .none }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .none }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .none }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .none }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .none }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .none }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .none }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .none }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .none }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .none }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .none }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .none }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .negtone }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .none }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .none }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .none }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .none }
  , { walsCode := "mug", language := "Bargam", iso := "mlp", value := .none }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .none }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .none }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .none }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .none }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .none }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .none }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .none }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .none }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .none }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .none }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .none }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .none }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .none }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .none }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .none }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .none }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .none }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .none }
  , { walsCode := "bmz", language := "Berber (Mzab)", iso := "mzb", value := .none }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .none }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .none }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .none }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .none }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .none }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .none }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .none }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .none }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .none }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .none }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .none }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .none }
  , { walsCode := "big", language := "Binga", iso := "yul", value := .none }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .none }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .none }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .none }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .none }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .none }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .none }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .none }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .none }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .none }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .none }
  , { walsCode := "boi", language := "Boiken", iso := "bzf", value := .none }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .none }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .none }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .none }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .none }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .none }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .none }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .none }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .none }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .none }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .none }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .none }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .none }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .none }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .none }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .none }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .none }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .none }
  , { walsCode := "buw", language := "Bulu", iso := "bum", value := .none }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .none }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .none }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .none }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .none }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .none }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .none }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .none }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .none }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .none }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .none }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .none }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .none }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .none }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .none }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .none }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .none }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .none }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .none }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .none }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .none }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .none }
  , { walsCode := "car", language := "Carib", iso := "car", value := .none }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .none }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .none }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .none }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .none }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .none }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .none }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .none }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .none }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .none }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .none }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .none }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .none }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .none }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .none }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .none }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .none }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .none }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .none }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .none }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .none }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .none }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .none }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .none }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .none }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .none }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .none }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .none }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .none }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .none }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .none }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .none }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .none }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .none }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .none }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .none }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .none }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .none }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .none }
  , { walsCode := "crt", language := "Chorote", iso := "", value := .none }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .none }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .none }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .none }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .none }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .none }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .none }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .none }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .none }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .none }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .none }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .none }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .none }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .none }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .none }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .none }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .none }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .none }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .none }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .none }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .none }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .none }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .none }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .none }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .none }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .none }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .none }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .none }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .negtone }
  , { walsCode := "des", language := "Desano", iso := "des", value := .none }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .none }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .none }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .none }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .none }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .none }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .none }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .none }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .none }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .none }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .none }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .none }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .none }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .none }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .none }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .none }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .none }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .none }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .none }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .none }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .none }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .none }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .none }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .negtone }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .none }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .none }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .none }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .none }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .none }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .none }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .none }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .none }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .none }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .none }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .none }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .none }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .none }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .none }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .none }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .none }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .none }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .none }
  , { walsCode := "ene", language := "Enets", iso := "", value := .none }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .negtone }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .none }
  , { walsCode := "eng", language := "English", iso := "eng", value := .none }
  , { walsCode := "eny", language := "Enya", iso := "gey", value := .none }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .none }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .none }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .none }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .none }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .none }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .none }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .none }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .none }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .negtone }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .none }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .none }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .none }
  , { walsCode := "fre", language := "French", iso := "fra", value := .none }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .none }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .none }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .none }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .none }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .none }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .none }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .none }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .none }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .none }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .none }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .none }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .none }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .none }
  , { walsCode := "grs", language := "Garus", iso := "gyb", value := .none }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .none }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .none }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .none }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .none }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .none }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .none }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .none }
  , { walsCode := "ger", language := "German", iso := "deu", value := .none }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .none }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .none }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .none }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .none }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .none }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .none }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .none }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .none }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .none }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .none }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .none }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .none }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .none }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .none }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .none }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .none }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .none }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .none }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .none }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .none }
  , { walsCode := "gir", language := "Gula Iro", iso := "glj", value := .none }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .none }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .none }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .none }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .none }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .none }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .none }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .none }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .none }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .none }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .none }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .none }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .none }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .none }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .none }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .none }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .none }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .none }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .none }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .none }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .none }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .none }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .none }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .none }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .none }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .none }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .none }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .none }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .none }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .none }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .none }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .none }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .none }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .none }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .none }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .none }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .none }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .none }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .none }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .none }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .none }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .none }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .none }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .none }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .none }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .none }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .none }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .none }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .none }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .none }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .none }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .none }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .none }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .none }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .none }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .none }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .none }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .none }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .none }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .none }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .none }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .none }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .none }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .none }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .none }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .none }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .none }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .none }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .none }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .none }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .none }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .none }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .none }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .none }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .none }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .none }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .none }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .none }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .none }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .none }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .none }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .none }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .none }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .none }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .none }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .none }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .none }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .none }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .none }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .none }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .none }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .none }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .none }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .none }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .none }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .none }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .none }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .none }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .none }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .none }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .none }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .none }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .none }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .none }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .none }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .none }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .none }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .none }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .none }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .none }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .none }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .none }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .none }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .none }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .none }
  , { walsCode := "kmi", language := "Kami", iso := "kcu", value := .none }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .none }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .none }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .none }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .none }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .none }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .none }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .none }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .none }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .none }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .none }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .none }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .none }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .none }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .none }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .none }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .none }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .none }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .none }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .none }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .none }
  ]

private def allData_1 : List (Datapoint MinorMorphologicalMeansOfSignalingNegation) :=
  [ { walsCode := "ksn", language := "Kasong", iso := "cog", value := .none }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .none }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .none }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .none }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .none }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .none }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .none }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .none }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .none }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .none }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .none }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .none }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .none }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .none }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .none }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .none }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .none }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .none }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .none }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .none }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .none }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .none }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .none }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .none }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .none }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .none }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .none }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .none }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .none }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .none }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .none }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .none }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .none }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .none }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .none }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .none }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .none }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .none }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .none }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .none }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .none }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .none }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .negtone }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .none }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .none }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .none }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .none }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .none }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .none }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .none }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .none }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .none }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .none }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .none }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .none }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .none }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .none }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .none }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .none }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .none }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .none }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .none }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .none }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .none }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .none }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .none }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .none }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .none }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .none }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .none }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .none }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .none }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .none }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .none }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .none }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .none }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .none }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .none }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .none }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .none }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .none }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .none }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .none }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .none }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .none }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .none }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .none }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .none }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .none }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .none }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .none }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .none }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .none }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .none }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .none }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .none }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .none }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .none }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .none }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .none }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .none }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .none }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .none }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .none }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .none }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .none }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .none }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .none }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .none }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .none }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .none }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .none }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .none }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .none }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .none }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .none }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .none }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .none }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .none }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .none }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .none }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .none }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .none }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .none }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .none }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .none }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .none }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .none }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .none }
  , { walsCode := "les", language := "Lese", iso := "les", value := .none }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .none }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .none }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .none }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .none }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .none }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .none }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .none }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .none }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .none }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .none }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .none }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .none }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .none }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .none }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .none }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .none }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .none }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .none }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .none }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .none }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .none }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .none }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .none }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .none }
  , { walsCode := "jlu", language := "Luwo", iso := "lwo", value := .none }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .none }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .none }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .none }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .none }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .none }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .none }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .none }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .none }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .none }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .none }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .none }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .none }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .none }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .none }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .none }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .none }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .none }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .none }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .none }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .none }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .none }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .none }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .none }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .none }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .none }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .none }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .none }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .none }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .none }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .none }
  , { walsCode := "mmw", language := "Mambwe", iso := "mgr", value := .none }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .none }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .none }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .none }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .none }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .none }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .none }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .none }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .none }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .none }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .none }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .none }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .none }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .none }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .none }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .none }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .none }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .none }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .none }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .none }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .none }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .none }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .none }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .none }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .none }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .none }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .none }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .none }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .none }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .none }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .none }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .none }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .none }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .none }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .none }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .none }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .none }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .none }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .none }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .none }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .none }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .none }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .none }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .none }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .none }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .none }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .none }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .none }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .none }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .none }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .none }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .none }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .none }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .none }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .none }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .none }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .none }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .none }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .none }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .none }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .none }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .none }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .none }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .none }
  , { walsCode := "mig", language := "Migama", iso := "mmy", value := .none }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .none }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .none }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .none }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .none }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .none }
  , { walsCode := "mhl", language := "Miri (Hill):", iso := "mrg", value := .none }
  , { walsCode := "mir", language := "Miriwung", iso := "mep", value := .none }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .none }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .none }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .none }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .none }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .none }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .none }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .none }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .none }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .none }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .none }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .none }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .none }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .none }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .none }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .none }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .none }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .none }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .none }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .none }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .none }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .none }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .none }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .none }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .none }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .none }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .none }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .none }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .none }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .none }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .none }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .none }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .none }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .none }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .none }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .none }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .none }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .none }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .none }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .none }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .none }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .none }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .none }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .none }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .none }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .none }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .none }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .none }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .none }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .none }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .none }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .none }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .none }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .none }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .none }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .none }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .none }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .none }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .none }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .none }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .none }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .none }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .none }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .none }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .none }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .none }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .none }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .none }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .none }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .none }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .none }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .none }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .none }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .none }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .none }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .none }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .none }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .none }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .none }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .none }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .none }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .none }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .none }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .none }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .none }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .none }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .none }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .none }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .none }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .none }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .none }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .none }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .none }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .none }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .neginfix }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .none }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .none }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .none }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .none }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .none }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .none }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .none }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .none }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .none }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .none }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .none }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .none }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .none }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .none }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .none }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .none }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .none }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .none }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .none }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .none }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .none }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .none }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .none }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .none }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .none }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .none }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .none }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .none }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .none }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .none }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .none }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .none }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .none }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .none }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .none }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .none }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .none }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .none }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .none }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .none }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .none }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .none }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .none }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .none }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .none }
  , { walsCode := "nyr", language := "Nyangumarda", iso := "nna", value := .none }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .none }
  , { walsCode := "nyh", language := "Nyiha", iso := "nih", value := .none }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .none }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .none }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .none }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .none }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .none }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .none }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .none }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .none }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .none }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .none }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .none }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .none }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .none }
  , { walsCode := "one", language := "One", iso := "aun", value := .none }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .none }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .none }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .none }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .none }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .none }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .none }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .none }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .negtone }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .none }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .none }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .none }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .none }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .none }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .none }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .none }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .none }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .none }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .none }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .none }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .none }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .none }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .none }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .none }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .none }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .none }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .none }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .none }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .none }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .none }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .none }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .none }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .none }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .none }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .none }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .none }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .none }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .none }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .none }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .none }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .none }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .none }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .none }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .none }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .none }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .none }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .none }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .none }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .none }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .none }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .none }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .none }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .none }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .none }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .none }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .none }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .none }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .none }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .none }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .none }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .none }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .none }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .none }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .none }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .none }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .none }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .none }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .none }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .none }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .none }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .none }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .none }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .none }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .none }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .none }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .none }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .none }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .none }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .none }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .none }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .none }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .none }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .none }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .none }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .none }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .none }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .none }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .none }
  ]

private def allData_2 : List (Datapoint MinorMorphologicalMeansOfSignalingNegation) :=
  [ { walsCode := "rov", language := "Roviana", iso := "rug", value := .none }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .none }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .none }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .none }
  , { walsCode := "rnd", language := "Rundi", iso := "run", value := .none }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .none }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .none }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .none }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .none }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .none }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .none }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .none }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .none }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .none }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .none }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .none }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .none }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .none }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .none }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .none }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .none }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .none }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .none }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .none }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .none }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .none }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .none }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .none }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .none }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .none }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .none }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .none }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .none }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .none }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .none }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .none }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .none }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .none }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .none }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .none }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .none }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .none }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .none }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .none }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .none }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .none }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .none }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .none }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .none }
  , { walsCode := "shy", language := "Shira Yughur", iso := "yuy", value := .none }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .none }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .none }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .none }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .none }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .none }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .none }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .none }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .none }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .none }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .none }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .none }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .none }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .none }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .none }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .none }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .none }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .none }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .none }
  , { walsCode := "so", language := "So", iso := "teu", value := .none }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .none }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .none }
  , { walsCode := "som", language := "Somali", iso := "som", value := .none }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .none }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .none }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .none }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .none }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .none }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .none }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .none }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .none }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .none }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .none }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .none }
  , { walsCode := "sub", language := "Subiya", iso := "sbs", value := .none }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .none }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .none }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .none }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .none }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .none }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .none }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .none }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .none }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .none }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .none }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .none }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .none }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .none }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .neginfix }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .none }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .none }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .none }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .none }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .none }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .none }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .none }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .none }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .none }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .none }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .none }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .none }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .none }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .negstemchange }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .none }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .none }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .none }
  , { walsCode := "tbx", language := "Tangbe", iso := "skj", value := .none }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .none }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .none }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .none }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .none }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .none }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .none }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .none }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .none }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .none }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .none }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .none }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .none }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .none }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .none }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .none }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .none }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .none }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .none }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .none }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .none }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .none }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .none }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .none }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .none }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .none }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .none }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .none }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .none }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .none }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .none }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .none }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .none }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .none }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .none }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .none }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .none }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .none }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .none }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .none }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .none }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .none }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .none }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .none }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .none }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .none }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .none }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .none }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .none }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .none }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .none }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .none }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .none }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .none }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .none }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .none }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .none }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .none }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .none }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .none }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .none }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .none }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .none }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .none }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .none }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .none }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .none }
  , { walsCode := "tgo", language := "Tsogo", iso := "tsv", value := .none }
  , { walsCode := "tsn", language := "Tsonga", iso := "tso", value := .none }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .none }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .none }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .none }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .none }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .none }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .none }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .none }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .none }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .none }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .none }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .none }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .none }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .none }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .none }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .none }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .none }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .none }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .none }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .none }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .none }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .none }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .none }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .none }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .none }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .none }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .none }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .none }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .none }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .none }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .none }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .none }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .none }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .none }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .none }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .none }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .none }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .none }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .none }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .none }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .none }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .none }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .none }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .none }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .none }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .none }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .none }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .none }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .none }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .none }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .none }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .none }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .none }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .none }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .none }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .none }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .none }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .none }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .none }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .none }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .none }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .none }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .none }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .none }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .none }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .none }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .none }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .none }
  , { walsCode := "was", language := "Washo", iso := "was", value := .none }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .none }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .none }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .none }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .none }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .none }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .none }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .none }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .none }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .none }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .none }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .none }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .none }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .none }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .none }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .none }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .none }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .none }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .none }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .none }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .none }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .none }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .none }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .none }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .none }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .none }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .none }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .none }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .none }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .none }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .none }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .none }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .none }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .none }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .none }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .none }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .none }
  , { walsCode := "yrr", language := "Yaruro", iso := "yae", value := .none }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .none }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .none }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .none }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .none }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .none }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .none }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .none }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .none }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .none }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .none }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .none }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .none }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .none }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .none }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .none }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .none }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .none }
  , { walsCode := "yrm", language := "Yurimangí", iso := "", value := .none }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .none }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .none }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .none }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .none }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .none }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .none }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .none }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .none }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .none }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .none }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .none }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .none }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .none }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .none }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .none }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .none }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .none }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .none }
  ]

/-- Complete WALS 143G dataset (1325 languages). -/
def allData : List (Datapoint MinorMorphologicalMeansOfSignalingNegation) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1325 := by native_decide

theorem count_negtone :
    (allData.filter (·.value == .negtone)).length = 7 := by native_decide
theorem count_neginfix :
    (allData.filter (·.value == .neginfix)).length = 2 := by native_decide
theorem count_negstemchange :
    (allData.filter (·.value == .negstemchange)).length = 1 := by native_decide
theorem count_none :
    (allData.filter (·.value == .none)).length = 1315 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F143G
