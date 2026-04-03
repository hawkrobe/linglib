import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 143F: Postverbal Negative Morphemes
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 143F`.

Chapter 143, 1325 languages.
-/

namespace Core.WALS.F143F

/-- WALS 143F values. -/
inductive PostverbalNegativeMorphemes where
  | vneg  -- VNeg (288 languages)
  | vNeg  -- [V-Neg] (307 languages)
  | vnegVNeg  -- VNeg&[V-Neg] (18 languages)
  | none  -- None (712 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint PostverbalNegativeMorphemes) :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .vneg }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .none }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .none }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .vNeg }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .vneg }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .none }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .vNeg }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .vneg }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .vneg }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .none }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .none }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .vneg }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .vNeg }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .none }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .vNeg }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .vneg }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .vNeg }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .vneg }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .vneg }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .none }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .none }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .none }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .vneg }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .vneg }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .none }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .none }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .none }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .none }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .none }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .none }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .none }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .vneg }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .vNeg }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .vNeg }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .vNeg }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .vneg }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .vneg }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .vNeg }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .none }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .vNeg }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .vNeg }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .vneg }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .vNeg }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .none }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .vneg }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .vneg }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .vNeg }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .none }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .vneg }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .none }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .vneg }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .vNeg }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .vNeg }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .vNeg }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .vNeg }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .none }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .none }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .vNeg }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .none }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .none }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .none }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .none }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .vNeg }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .none }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .vNeg }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .vneg }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .vneg }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .vNeg }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .none }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .none }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .vneg }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .none }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .vNeg }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .vNeg }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .vneg }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .none }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .vNeg }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .none }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .vNeg }
  , { walsCode := "au", language := "Au", iso := "avt", value := .vneg }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .vneg }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .none }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .vnegVNeg }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .none }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .none }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .vNeg }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .vNeg }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .none }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .vneg }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .none }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .none }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .none }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .vneg }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .vneg }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .none }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .none }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .none }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .vneg }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .vneg }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .none }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .none }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .none }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .vneg }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .none }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .none }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .none }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .none }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .none }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .none }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .vneg }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .vNeg }
  , { walsCode := "mug", language := "Bargam", iso := "mlp", value := .none }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .none }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .none }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .none }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .vneg }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .vNeg }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .none }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .none }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .none }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .none }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .vneg }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .vneg }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .none }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .vNeg }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .none }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .none }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .vneg }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .none }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .none }
  , { walsCode := "bmz", language := "Berber (Mzab)", iso := "mzb", value := .none }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .none }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .vNeg }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .none }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .vNeg }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .none }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .vneg }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .vneg }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .none }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .vNeg }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .vneg }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .none }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .vneg }
  , { walsCode := "big", language := "Binga", iso := "yul", value := .vneg }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .none }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .none }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .vneg }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .vneg }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .none }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .none }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .vNeg }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .vneg }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .vneg }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .vneg }
  , { walsCode := "boi", language := "Boiken", iso := "bzf", value := .vNeg }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .vneg }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .vneg }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .vneg }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .none }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .vNeg }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .vNeg }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .vNeg }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .none }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .vneg }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .none }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .vneg }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .none }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .none }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .none }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .none }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .none }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .vneg }
  , { walsCode := "buw", language := "Bulu", iso := "bum", value := .none }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .vneg }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .none }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .none }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .none }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .vNeg }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .vneg }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .vNeg }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .none }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .vneg }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .none }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .none }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .none }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .vneg }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .vNeg }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .none }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .none }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .vNeg }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .vNeg }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .vneg }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .none }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .vNeg }
  , { walsCode := "car", language := "Carib", iso := "car", value := .vNeg }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .vNeg }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .vNeg }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .vneg }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .vNeg }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .none }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .none }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .none }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .vneg }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .vneg }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .none }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .none }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .none }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .none }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .none }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .none }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .none }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .none }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .vNeg }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .vNeg }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .none }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .none }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .vNeg }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .vneg }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .vneg }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .vneg }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .none }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .none }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .none }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .none }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .none }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .none }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .vneg }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .vNeg }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .vNeg }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .vNeg }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .vNeg }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .none }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .none }
  , { walsCode := "crt", language := "Chorote", iso := "", value := .none }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .vneg }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .vneg }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .none }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .none }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .vNeg }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .vNeg }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .vNeg }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .none }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .none }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .none }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .vneg }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .none }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .none }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .none }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .vNeg }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .vNeg }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .none }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .none }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .none }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .none }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .none }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .none }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .none }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .none }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .vneg }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .vneg }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .none }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .none }
  , { walsCode := "des", language := "Desano", iso := "des", value := .vNeg }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .vNeg }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .vNeg }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .none }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .none }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .none }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .none }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .vneg }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .vNeg }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .vNeg }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .vNeg }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .none }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .vNeg }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .none }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .none }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .none }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .none }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .none }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .none }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .none }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .vNeg }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .vneg }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .vNeg }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .vnegVNeg }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .none }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .none }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .vneg }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .none }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .vneg }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .vNeg }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .vneg }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .vnegVNeg }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .vneg }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .none }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .none }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .vneg }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .vNeg }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .vneg }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .vneg }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .vneg }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .vNeg }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .vNeg }
  , { walsCode := "ene", language := "Enets", iso := "", value := .none }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .none }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .none }
  , { walsCode := "eng", language := "English", iso := "eng", value := .none }
  , { walsCode := "eny", language := "Enya", iso := "gey", value := .none }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .vNeg }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .none }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .vneg }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .none }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .none }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .vNeg }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .vNeg }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .vneg }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .vneg }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .none }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .none }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .none }
  , { walsCode := "fre", language := "French", iso := "fra", value := .vneg }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .vNeg }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .vNeg }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .vNeg }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .none }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .vneg }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .none }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .none }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .none }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .vNeg }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .vNeg }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .none }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .vNeg }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .none }
  , { walsCode := "grs", language := "Garus", iso := "gyb", value := .none }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .none }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .none }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .vneg }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .vneg }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .none }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .vneg }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .none }
  , { walsCode := "ger", language := "German", iso := "deu", value := .vneg }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .vNeg }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .vneg }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .none }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .vNeg }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .vneg }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .none }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .vNeg }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .vNeg }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .none }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .none }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .none }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .vNeg }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .none }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .vneg }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .none }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .none }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .vNeg }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .vNeg }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .none }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .vneg }
  , { walsCode := "gir", language := "Gula Iro", iso := "glj", value := .none }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .none }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .vneg }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .vNeg }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .none }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .none }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .none }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .vneg }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .vneg }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .none }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .vNeg }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .none }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .vNeg }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .none }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .vneg }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .none }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .none }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .none }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .vNeg }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .vneg }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .vneg }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .none }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .none }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .none }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .vneg }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .none }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .none }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .none }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .vNeg }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .none }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .none }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .vNeg }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .none }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .vneg }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .none }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .none }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .none }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .none }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .none }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .vneg }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .none }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .none }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .none }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .vNeg }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .vNeg }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .none }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .none }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .vNeg }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .vNeg }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .none }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .vneg }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .none }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .vneg }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .none }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .vneg }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .vneg }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .vNeg }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .none }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .vneg }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .none }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .vneg }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .vneg }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .none }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .vnegVNeg }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .none }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .vNeg }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .none }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .none }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .vNeg }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .none }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .vneg }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .vNeg }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .none }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .none }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .vNeg }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .vNeg }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .vneg }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .none }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .none }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .vNeg }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .vneg }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .vneg }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .vneg }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .vNeg }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .vneg }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .none }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .vNeg }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .vNeg }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .none }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .vNeg }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .none }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .vNeg }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .none }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .vneg }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .vneg }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .none }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .vNeg }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .none }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .vneg }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .vNeg }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .none }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .none }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .none }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .none }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .vneg }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .vneg }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .none }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .none }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .vneg }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .vNeg }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .vNeg }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .vneg }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .none }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .none }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .vNeg }
  , { walsCode := "kmi", language := "Kami", iso := "kcu", value := .none }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .vNeg }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .none }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .none }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .vneg }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .none }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .vNeg }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .none }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .vNeg }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .vneg }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .vnegVNeg }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .none }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .vNeg }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .vneg }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .vneg }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .vneg }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .none }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .vnegVNeg }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .vNeg }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .vneg }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .vNeg }
  ]

private def allData_1 : List (Datapoint PostverbalNegativeMorphemes) :=
  [ { walsCode := "ksn", language := "Kasong", iso := "cog", value := .none }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .none }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .vneg }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .vneg }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .vneg }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .none }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .vNeg }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .vneg }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .vneg }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .vNeg }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .vneg }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .vNeg }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .vneg }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .vneg }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .none }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .none }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .none }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .vNeg }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .vNeg }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .vNeg }
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
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .vneg }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .none }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .vneg }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .none }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .none }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .none }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .vNeg }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .vNeg }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .vneg }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .none }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .none }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .vneg }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .vNeg }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .none }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .none }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .none }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .vNeg }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .vNeg }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .vNeg }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .vNeg }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .none }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .vNeg }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .vNeg }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .none }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .vnegVNeg }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .vNeg }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .none }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .none }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .none }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .none }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .vnegVNeg }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .vNeg }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .none }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .vneg }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .none }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .none }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .vNeg }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .vNeg }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .none }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .vNeg }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .none }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .none }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .vNeg }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .vneg }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .vneg }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .none }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .none }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .vNeg }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .vNeg }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .none }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .vNeg }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .vNeg }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .none }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .none }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .none }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .vNeg }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .none }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .none }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .vNeg }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .none }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .none }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .vNeg }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .none }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .vNeg }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .vnegVNeg }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .vneg }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .none }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .none }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .vneg }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .vneg }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .none }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .vNeg }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .vneg }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .none }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .vneg }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .vneg }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .none }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .vneg }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .vneg }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .vneg }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .vneg }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .none }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .none }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .none }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .none }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .none }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .none }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .vnegVNeg }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .none }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .none }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .none }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .vNeg }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .vneg }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .none }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .vneg }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .vneg }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .vNeg }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .vNeg }
  , { walsCode := "les", language := "Lese", iso := "les", value := .none }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .none }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .vneg }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .vNeg }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .vNeg }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .vNeg }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .vneg }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .vneg }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .none }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .none }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .vneg }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .vneg }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .none }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .none }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .vneg }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .none }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .vneg }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .none }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .none }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .vneg }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .none }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .vneg }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .none }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .vneg }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .vneg }
  , { walsCode := "jlu", language := "Luwo", iso := "lwo", value := .none }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .vneg }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .vneg }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .none }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .vnegVNeg }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .none }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .none }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .vneg }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .vneg }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .none }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .none }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .none }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .none }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .vNeg }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .vNeg }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .vneg }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .none }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .none }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .vNeg }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .none }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .none }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .none }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .none }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .none }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .none }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .none }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .vNeg }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .vneg }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .vNeg }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .none }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .none }
  , { walsCode := "mmw", language := "Mambwe", iso := "mgr", value := .none }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .none }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .none }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .none }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .vNeg }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .vNeg }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .none }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .none }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .vneg }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .none }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .vneg }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .none }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .none }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .none }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .none }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .none }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .none }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .vNeg }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .none }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .vneg }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .vneg }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .none }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .vneg }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .none }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .vNeg }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .none }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .none }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .none }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .none }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .none }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .none }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .vneg }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .vneg }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .vNeg }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .vNeg }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .none }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .vneg }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .vneg }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .none }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .vneg }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .vneg }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .vNeg }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .vneg }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .none }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .vneg }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .vneg }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .vneg }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .none }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .vneg }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .vNeg }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .vneg }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .vneg }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .vNeg }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .vneg }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .vNeg }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .vneg }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .none }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .none }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .vNeg }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .none }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .none }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .vneg }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .vNeg }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .none }
  , { walsCode := "mig", language := "Migama", iso := "mmy", value := .vneg }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .vNeg }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .vNeg }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .vNeg }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .vneg }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .vneg }
  , { walsCode := "mhl", language := "Miri (Hill):", iso := "mrg", value := .vNeg }
  , { walsCode := "mir", language := "Miriwung", iso := "mep", value := .none }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .vNeg }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .vNeg }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .none }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .none }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .none }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .none }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .none }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .none }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .none }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .vneg }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .vneg }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .none }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .none }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .none }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .none }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .vNeg }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .none }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .vNeg }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .vnegVNeg }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .none }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .none }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .vneg }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .vneg }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .none }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .none }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .none }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .vneg }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .none }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .vneg }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .vNeg }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .none }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .none }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .vneg }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .vneg }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .vNeg }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .vNeg }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .vneg }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .none }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .vneg }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .none }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .vneg }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .vneg }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .none }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .none }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .none }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .none }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .vneg }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .vneg }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .none }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .none }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .none }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .none }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .vNeg }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .none }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .none }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .none }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .vneg }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .none }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .vneg }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .vneg }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .none }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .none }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .none }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .none }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .vNeg }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .none }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .none }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .none }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .vneg }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .vNeg }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .none }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .none }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .none }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .vneg }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .vneg }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .vNeg }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .none }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .vnegVNeg }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .none }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .none }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .none }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .vNeg }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .none }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .none }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .vneg }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .vNeg }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .none }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .none }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .none }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .none }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .none }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .vNeg }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .none }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .none }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .none }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .none }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .vNeg }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .none }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .none }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .vNeg }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .vneg }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .none }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .vNeg }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .none }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .none }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .vneg }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .none }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .none }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .vneg }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .vneg }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .none }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .none }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .none }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .none }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .none }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .vNeg }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .none }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .none }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .none }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .vnegVNeg }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .vNeg }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .none }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .none }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .vNeg }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .vneg }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .vNeg }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .vneg }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .vneg }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .none }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .vneg }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .vNeg }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .vNeg }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .none }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .none }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .none }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .none }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .vneg }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .none }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .none }
  , { walsCode := "nyr", language := "Nyangumarda", iso := "nna", value := .none }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .none }
  , { walsCode := "nyh", language := "Nyiha", iso := "nih", value := .none }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .none }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .vNeg }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .none }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .vneg }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .none }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .none }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .none }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .none }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .none }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .none }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .none }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .vneg }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .vNeg }
  , { walsCode := "one", language := "One", iso := "aun", value := .vneg }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .none }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .vneg }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .none }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .none }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .vNeg }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .none }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .vNeg }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .none }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .vNeg }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .vneg }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .none }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .none }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .vneg }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .vneg }
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
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .vNeg }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .vneg }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .none }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .vNeg }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .vneg }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .vNeg }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .vnegVNeg }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .none }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .vNeg }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .vneg }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .none }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .vNeg }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .none }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .none }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .none }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .vNeg }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .vneg }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .vnegVNeg }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .none }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .vneg }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .vneg }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .none }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .vNeg }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .none }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .vNeg }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .vNeg }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .vNeg }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .none }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .none }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .none }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .none }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .none }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .vNeg }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .none }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .vNeg }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .none }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .vNeg }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .none }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .vneg }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .none }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .vneg }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .none }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .none }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .vneg }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .vNeg }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .none }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .vNeg }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .none }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .none }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .none }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .none }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .none }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .none }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .vNeg }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .none }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .none }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .vNeg }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .vneg }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .none }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .vneg }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .vneg }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .vneg }
  ]

private def allData_2 : List (Datapoint PostverbalNegativeMorphemes) :=
  [ { walsCode := "rov", language := "Roviana", iso := "rug", value := .none }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .none }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .none }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .vNeg }
  , { walsCode := "rnd", language := "Rundi", iso := "run", value := .none }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .vNeg }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .none }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .none }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .none }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .none }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .vneg }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .none }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .none }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .none }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .vNeg }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .none }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .vNeg }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .vneg }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .none }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .none }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .none }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .vneg }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .none }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .none }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .none }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .vNeg }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .none }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .vneg }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .none }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .none }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .vneg }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .vNeg }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .vneg }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .none }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .vNeg }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .vneg }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .none }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .none }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .none }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .none }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .vneg }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .none }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .vNeg }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .vneg }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .none }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .none }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .none }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .none }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .vNeg }
  , { walsCode := "shy", language := "Shira Yughur", iso := "yuy", value := .vneg }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .vneg }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .none }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .none }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .vNeg }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .none }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .none }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .vneg }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .none }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .none }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .vneg }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .vNeg }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .none }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .vneg }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .none }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .none }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .vNeg }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .vneg }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .none }
  , { walsCode := "so", language := "So", iso := "teu", value := .none }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .none }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .none }
  , { walsCode := "som", language := "Somali", iso := "som", value := .none }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .none }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .none }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .none }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .none }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .vNeg }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .vneg }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .none }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .none }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .none }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .none }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .none }
  , { walsCode := "sub", language := "Subiya", iso := "sbs", value := .vNeg }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .none }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .none }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .vNeg }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .none }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .none }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .vNeg }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .vneg }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .none }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .vNeg }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .vneg }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .vNeg }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .vneg }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .vNeg }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .vnegVNeg }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .none }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .vneg }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .none }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .none }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .none }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .none }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .none }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .none }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .none }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .none }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .vNeg }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .none }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .none }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .none }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .vNeg }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .vNeg }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .vNeg }
  , { walsCode := "tbx", language := "Tangbe", iso := "skj", value := .none }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .vNeg }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .none }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .none }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .vNeg }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .vNeg }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .none }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .none }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .none }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .none }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .none }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .none }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .vNeg }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .vNeg }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .none }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .vNeg }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .none }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .none }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .vneg }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .none }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .none }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .none }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .vneg }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .vneg }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .none }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .none }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .none }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .none }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .none }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .none }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .vNeg }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .none }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .vneg }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .none }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .none }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .vneg }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .none }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .vNeg }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .none }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .vneg }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .none }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .none }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .vNeg }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .vNeg }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .vneg }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .none }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .none }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .none }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .none }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .none }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .vNeg }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .vNeg }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .none }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .none }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .none }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .none }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .none }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .none }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .none }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .vNeg }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .none }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .none }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .vneg }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .vNeg }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .vneg }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .vnegVNeg }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .none }
  , { walsCode := "tgo", language := "Tsogo", iso := "tsv", value := .none }
  , { walsCode := "tsn", language := "Tsonga", iso := "tso", value := .none }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .none }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .none }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .vNeg }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .vNeg }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .none }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .none }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .vNeg }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .none }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .vNeg }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .vneg }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .none }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .vNeg }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .none }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .vNeg }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .none }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .vNeg }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .vNeg }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .vneg }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .none }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .none }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .vNeg }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .vNeg }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .none }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .none }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .vneg }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .none }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .vneg }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .none }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .none }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .none }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .none }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .vNeg }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .vneg }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .none }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .none }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .vneg }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .none }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .none }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .vNeg }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .vNeg }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .vNeg }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .none }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .none }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .none }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .vNeg }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .none }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .none }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .vNeg }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .none }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .none }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .none }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .none }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .vNeg }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .none }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .vneg }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .vNeg }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .vNeg }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .vNeg }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .none }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .vNeg }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .vneg }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .none }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .none }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .none }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .vNeg }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .none }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .none }
  , { walsCode := "was", language := "Washo", iso := "was", value := .vNeg }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .none }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .none }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .vNeg }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .vNeg }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .vNeg }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .none }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .none }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .vneg }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .none }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .vneg }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .none }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .vNeg }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .none }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .none }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .vNeg }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .vNeg }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .vNeg }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .vNeg }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .none }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .vNeg }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .vneg }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .none }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .none }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .vneg }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .none }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .none }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .none }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .none }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .vNeg }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .vNeg }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .none }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .none }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .none }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .vNeg }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .none }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .vNeg }
  , { walsCode := "yrr", language := "Yaruro", iso := "yae", value := .vNeg }
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
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .vNeg }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .vneg }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .vNeg }
  , { walsCode := "yrm", language := "Yurimangí", iso := "", value := .vNeg }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .none }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .none }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .vneg }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .vNeg }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .none }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .none }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .none }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .none }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .vNeg }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .none }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .vNeg }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .none }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .none }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .vNeg }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .vNeg }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .none }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .vNeg }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .none }
  ]

/-- Complete WALS 143F dataset (1325 languages). -/
def allData : List (Datapoint PostverbalNegativeMorphemes) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1325 := by native_decide

theorem count_vneg :
    (allData.filter (·.value == .vneg)).length = 288 := by native_decide
theorem count_vNeg :
    (allData.filter (·.value == .vNeg)).length = 307 := by native_decide
theorem count_vnegVNeg :
    (allData.filter (·.value == .vnegVNeg)).length = 18 := by native_decide
theorem count_none :
    (allData.filter (·.value == .none)).length = 712 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F143F
