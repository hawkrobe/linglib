import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 143E: Preverbal Negative Morphemes
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 143E`.

Chapter 143, 1325 languages.
-/

namespace Core.WALS.F143E

/-- WALS 143E values. -/
inductive PreverbalNegativeMorphemes where
  | negv  -- NegV (682 languages)
  | negV  -- [Neg-V] (230 languages)
  | negvNegV  -- NegV&[Neg-V] (23 languages)
  | none  -- None (390 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint PreverbalNegativeMorphemes) :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .none }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .negv }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .negv }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .none }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .none }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .negv }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .negV }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .none }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .negv }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .negv }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .negv }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .negv }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .none }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .negv }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .negv }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .negv }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .none }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .negV }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .negv }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .negv }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .negv }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .negv }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .none }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .negv }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .negV }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .negv }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .negv }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .negv }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .negv }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .negv }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .negv }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .none }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .none }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .none }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .negv }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .negv }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .none }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .negv }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .negV }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .negv }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .negV }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .negv }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .negv }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .negv }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .none }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .none }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .none }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .negvNegV }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .none }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .negv }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .none }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .negV }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .negv }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .none }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .none }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .negv }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .negv }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .negvNegV }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .negv }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .negV }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .negv }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .negv }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .negV }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .negv }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .negV }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .none }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .negv }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .none }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .negvNegV }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .negvNegV }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .none }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .negv }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .none }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .none }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .none }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .negV }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .negV }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .negv }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .none }
  , { walsCode := "au", language := "Au", iso := "avt", value := .negv }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .none }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .negv }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .negv }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .negV }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .negv }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .none }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .none }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .negV }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .negv }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .negv }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .negv }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .negv }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .none }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .none }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .negv }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .negv }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .negv }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .none }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .none }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .negV }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .negV }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .negv }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .negv }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .negv }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .negv }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .negv }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .none }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .negV }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .negv }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .negV }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .none }
  , { walsCode := "mug", language := "Bargam", iso := "mlp", value := .negV }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .negv }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .negv }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .negv }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .none }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .none }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .negv }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .negv }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .negv }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .negv }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .none }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .none }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .negV }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .negV }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .negv }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .negv }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .none }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .negv }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .negv }
  , { walsCode := "bmz", language := "Berber (Mzab)", iso := "mzb", value := .negv }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .negv }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .none }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .negV }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .none }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .negv }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .none }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .negv }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .negV }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .none }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .negV }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .negv }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .negv }
  , { walsCode := "big", language := "Binga", iso := "yul", value := .none }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .negv }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .negv }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .negv }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .none }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .negV }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .negV }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .none }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .negv }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .negv }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .negv }
  , { walsCode := "boi", language := "Boiken", iso := "bzf", value := .negv }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .negv }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .negV }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .negv }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .negv }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .none }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .none }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .none }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .negv }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .negv }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .negv }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .none }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .negv }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .negV }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .negv }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .negv }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .negv }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .negv }
  , { walsCode := "buw", language := "Bulu", iso := "bum", value := .negv }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .none }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .negv }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .negv }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .negv }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .none }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .negV }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .none }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .negV }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .none }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .negV }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .negV }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .negv }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .negv }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .negV }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .negv }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .negV }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .none }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .none }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .none }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .negv }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .none }
  , { walsCode := "car", language := "Carib", iso := "car", value := .none }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .none }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .none }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .negv }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .none }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .negV }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .negV }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .negV }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .negv }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .none }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .negvNegV }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .negv }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .negV }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .negV }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .negv }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .negv }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .negv }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .negv }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .negv }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .none }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .negv }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .negV }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .negV }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .none }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .none }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .none }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .negV }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .negv }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .negV }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .negv }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .negv }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .negv }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .none }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .none }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .none }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .none }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .none }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .negv }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .negv }
  , { walsCode := "crt", language := "Chorote", iso := "", value := .negv }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .negv }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .negv }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .negv }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .negV }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .none }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .none }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .none }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .negv }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .negv }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .negv }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .negvNegV }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .negv }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .negv }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .negv }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .none }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .negv }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .negv }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .negV }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .negv }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .negv }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .negv }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .negv }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .negv }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .negv }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .none }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .negv }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .negV }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .negV }
  , { walsCode := "des", language := "Desano", iso := "des", value := .none }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .none }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .negv }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .negv }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .negV }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .negV }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .negv }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .none }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .none }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .none }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .none }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .negv }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .none }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .negv }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .negv }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .negv }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .negv }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .negv }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .negv }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .negv }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .negvNegV }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .none }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .none }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .negv }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .negv }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .negv }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .none }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .negV }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .negv }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .negV }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .none }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .negV }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .negv }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .negv }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .negv }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .negv }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .none }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .none }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .negv }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .negv }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .negV }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .none }
  , { walsCode := "ene", language := "Enets", iso := "", value := .negv }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .none }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .negv }
  , { walsCode := "eng", language := "English", iso := "eng", value := .negv }
  , { walsCode := "eny", language := "Enya", iso := "gey", value := .negV }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .none }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .negV }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .none }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .negv }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .negv }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .negv }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .negv }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .negv }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .negv }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .negv }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .negv }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .negv }
  , { walsCode := "fre", language := "French", iso := "fra", value := .negv }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .none }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .none }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .negV }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .negv }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .negv }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .negv }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .negv }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .negv }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .none }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .none }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .negv }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .none }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .negv }
  , { walsCode := "grs", language := "Garus", iso := "gyb", value := .negv }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .negv }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .negv }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .none }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .negv }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .negv }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .none }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .negv }
  , { walsCode := "ger", language := "German", iso := "deu", value := .negv }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .none }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .none }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .negv }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .none }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .none }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .negv }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .none }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .none }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .negv }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .negv }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .negv }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .none }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .negV }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .negv }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .negv }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .negv }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .negv }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .negv }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .negv }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .none }
  , { walsCode := "gir", language := "Gula Iro", iso := "glj", value := .negv }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .negv }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .none }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .negvNegV }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .negv }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .negV }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .negv }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .negv }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .none }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .negV }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .none }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .negV }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .negv }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .negv }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .negv }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .negv }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .negV }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .negv }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .none }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .none }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .negv }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .negv }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .negV }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .negv }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .none }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .negv }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .negV }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .negv }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .none }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .negv }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .negv }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .none }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .negv }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .none }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .negv }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .negv }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .negV }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .negv }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .negV }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .negv }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .negv }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .negv }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .negV }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .none }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .none }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .negV }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .negv }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .none }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .none }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .negv }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .none }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .negv }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .none }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .negv }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .negv }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .negv }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .none }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .negv }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .negV }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .negv }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .negv }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .none }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .negv }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .none }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .negv }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .none }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .negV }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .negv }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .negv }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .negv }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .none }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .none }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .negv }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .negv }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .none }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .none }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .none }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .negv }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .negv }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .negv }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .none }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .negV }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .none }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .negv }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .none }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .negv }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .none }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .none }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .negv }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .none }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .negv }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .none }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .negv }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .none }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .none }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .negv }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .none }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .negV }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .negv }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .none }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .negv }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .negV }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .negv }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .negV }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .none }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .none }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .negv }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .negv }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .negv }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .negV }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .negV }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .none }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .negv }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .negV }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .none }
  , { walsCode := "kmi", language := "Kami", iso := "kcu", value := .negV }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .none }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .negv }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .negv }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .negv }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .negv }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .none }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .negv }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .none }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .none }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .none }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .negv }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .none }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .negV }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .none }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .negv }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .negvNegV }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .none }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .negv }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .none }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .none }
  ]

private def allData_1 : List (Datapoint PreverbalNegativeMorphemes) :=
  [ { walsCode := "ksn", language := "Kasong", iso := "cog", value := .negv }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .negv }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .none }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .negv }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .none }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .negv }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .negV }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .none }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .none }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .none }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .none }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .none }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .none }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .none }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .negv }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .negv }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .negV }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .none }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .negV }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .none }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .negV }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .negV }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .negV }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .negv }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .negv }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .negv }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .negv }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .negv }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .negv }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .negV }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .negv }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .negv }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .negV }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .none }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .negV }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .negv }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .negV }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .negv }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .none }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .none }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .negv }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .negv }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .negv }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .negv }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .negv }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .negv }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .negv }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .none }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .none }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .negv }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .none }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .negv }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .none }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .none }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .negv }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .none }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .negV }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .negv }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .negv }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .negv }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .negv }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .negvNegV }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .none }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .negv }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .none }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .negv }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .negv }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .negV }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .negV }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .negv }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .none }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .negv }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .negv }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .none }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .negv }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .negv }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .negv }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .negv }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .negV }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .none }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .negv }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .none }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .none }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .negV }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .negv }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .negV }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .none }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .negv }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .negv }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .none }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .negv }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .negv }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .none }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .negv }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .negv }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .negv }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .none }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .negV }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .negv }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .none }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .none }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .negv }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .negV }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .none }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .negv }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .none }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .none }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .negv }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .none }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .none }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .none }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .negv }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .negV }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .negV }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .negv }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .negv }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .negv }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .negV }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .none }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .negV }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .negV }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .negV }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .none }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .none }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .negV }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .negV }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .negv }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .negV }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .negV }
  , { walsCode := "les", language := "Lese", iso := "les", value := .negV }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .negV }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .none }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .none }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .negv }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .negV }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .negV }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .none }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .negv }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .negV }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .none }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .none }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .negV }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .negv }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .none }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .negV }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .negv }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .negV }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .negV }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .none }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .negv }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .negV }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .negv }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .none }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .negvNegV }
  , { walsCode := "jlu", language := "Luwo", iso := "lwo", value := .negv }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .negV }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .none }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .negvNegV }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .none }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .negv }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .negv }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .none }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .none }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .negv }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .negv }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .negV }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .negv }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .none }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .none }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .negv }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .negv }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .negv }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .negV }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .negv }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .negv }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .negv }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .negV }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .negV }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .negv }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .negv }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .none }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .none }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .none }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .negv }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .negv }
  , { walsCode := "mmw", language := "Mambwe", iso := "mgr", value := .negV }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .negV }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .negv }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .negV }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .none }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .negV }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .negv }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .negv }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .none }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .negv }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .negv }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .negv }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .negv }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .negv }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .negv }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .negv }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .negv }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .none }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .negvNegV }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .negv }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .none }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .negv }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .none }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .negv }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .negV }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .negv }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .negv }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .negv }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .negv }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .negv }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .negv }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .none }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .negv }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .none }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .none }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .negv }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .none }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .negv }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .negv }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .none }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .none }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .none }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .none }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .negv }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .none }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .none }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .negv }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .negv }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .none }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .negV }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .none }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .none }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .none }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .none }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .none }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .none }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .negV }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .negv }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .negv }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .negv }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .negv }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .none }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .none }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .negv }
  , { walsCode := "mig", language := "Migama", iso := "mmy", value := .none }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .none }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .none }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .none }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .none }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .negv }
  , { walsCode := "mhl", language := "Miri (Hill):", iso := "mrg", value := .none }
  , { walsCode := "mir", language := "Miriwung", iso := "mep", value := .negv }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .none }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .none }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .negv }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .negvNegV }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .negv }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .negv }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .negv }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .negv }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .negv }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .negv }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .none }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .negV }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .negv }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .negvNegV }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .negv }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .negv }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .negv }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .negv }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .none }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .negv }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .negv }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .negv }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .none }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .negv }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .negv }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .negv }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .none }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .negv }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .negv }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .none }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .negv }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .negv }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .none }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .negv }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .none }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .none }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .negv }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .negv }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .none }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .negv }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .negv }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .negv }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .negv }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .negv }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .negv }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .negv }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .none }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .none }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .negv }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .negv }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .negv }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .negV }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .negv }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .negv }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .negv }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .negvNegV }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .none }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .negV }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .none }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .negv }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .negv }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .negv }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .negv }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .negv }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .none }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .negv }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .negv }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .negv }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .none }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .none }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .negV }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .negV }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .negV }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .none }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .none }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .negV }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .negv }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .none }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .negv }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .negv }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .negv }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .negV }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .negv }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .negv }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .negV }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .none }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .negv }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .negv }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .negv }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .negv }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .negv }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .none }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .negv }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .negV }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .negV }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .negv }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .none }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .negv }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .negv }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .none }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .none }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .negv }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .none }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .negv }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .negv }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .none }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .negv }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .negv }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .none }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .negV }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .negv }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .negv }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .negv }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .negv }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .negv }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .none }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .negv }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .negv }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .negv }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .none }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .negv }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .negV }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .negV }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .none }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .negv }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .none }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .negv }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .negV }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .negV }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .none }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .none }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .none }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .negv }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .negv }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .negv }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .negv }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .none }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .negv }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .negV }
  , { walsCode := "nyr", language := "Nyangumarda", iso := "nna", value := .negv }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .negv }
  , { walsCode := "nyh", language := "Nyiha", iso := "nih", value := .negV }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .negv }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .none }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .negv }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .none }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .negv }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .negV }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .negV }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .negV }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .negv }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .negv }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .negv }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .none }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .none }
  , { walsCode := "one", language := "One", iso := "aun", value := .negv }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .negvNegV }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .none }
  , { walsCode := "ono", language := "Ono", iso := "ons", value := .negv }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .negV }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .none }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .negV }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .negv }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .negV }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .negv }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .none }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .negv }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .negv }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .negv }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .negv }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .negv }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .negV }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .negv }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .negv }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .negv }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .negv }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .negv }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .negV }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .negv }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .negV }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .negV }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .negv }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .none }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .negV }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .none }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .negv }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .negv }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .none }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .negV }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .none }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .negv }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .negV }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .none }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .negV }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .negv }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .negv }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .none }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .negv }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .none }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .negv }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .none }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .none }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .negv }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .negvNegV }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .negv }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .none }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .negv }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .none }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .negv }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .negV }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .negv }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .negvNegV }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .negv }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .negV }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .negv }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .none }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .negv }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .none }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .negv }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .none }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .negV }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .negv }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .negv }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .negv }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .negv }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .negv }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .negv }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .none }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .negv }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .negV }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .negv }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .negv }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .negV }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .negv }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .none }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .negv }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .negV }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .none }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .negv }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .negv }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .none }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .none }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .negv }
  ]

private def allData_2 : List (Datapoint PreverbalNegativeMorphemes) :=
  [ { walsCode := "rov", language := "Roviana", iso := "rug", value := .negv }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .negv }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .negv }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .none }
  , { walsCode := "rnd", language := "Rundi", iso := "run", value := .negV }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .negv }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .negV }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .negV }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .negv }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .negv }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .none }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .negV }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .negv }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .negvNegV }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .none }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .negv }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .none }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .none }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .negV }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .negv }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .negv }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .none }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .negv }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .negv }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .negv }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .negV }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .negv }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .none }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .negv }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .negv }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .none }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .none }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .none }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .negv }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .none }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .negV }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .negV }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .negv }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .negV }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .negv }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .none }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .negV }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .none }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .none }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .negv }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .negV }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .negv }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .negv }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .none }
  , { walsCode := "shy", language := "Shira Yughur", iso := "yuy", value := .none }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .none }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .negV }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .negv }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .none }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .negv }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .negv }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .none }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .negv }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .negv }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .none }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .none }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .negv }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .none }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .negv }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .negv }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .negv }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .none }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .negv }
  , { walsCode := "so", language := "So", iso := "teu", value := .negv }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .negv }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .negV }
  , { walsCode := "som", language := "Somali", iso := "som", value := .negv }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .negv }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .negv }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .negV }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .negV }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .negv }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .none }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .negv }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .negv }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .negv }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .negv }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .negv }
  , { walsCode := "sub", language := "Subiya", iso := "sbs", value := .negV }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .negv }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .negv }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .negV }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .negV }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .negv }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .none }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .negv }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .negV }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .negV }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .negv }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .none }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .none }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .none }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .negV }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .negV }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .negv }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .negv }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .negv }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .negv }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .negv }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .negV }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .negv }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .negv }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .negV }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .none }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .negv }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .negv }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .negv }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .none }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .negv }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .none }
  , { walsCode := "tbx", language := "Tangbe", iso := "skj", value := .negv }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .none }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .negv }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .negv }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .none }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .negV }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .negvNegV }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .negV }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .negv }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .negv }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .negv }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .negv }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .none }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .negv }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .negv }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .none }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .negv }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .negv }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .negv }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .negv }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .negv }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .negv }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .negv }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .none }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .negv }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .negV }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .negv }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .negv }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .negV }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .negv }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .negv }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .negV }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .negv }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .negV }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .negV }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .negv }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .negv }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .negV }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .negV }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .negv }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .negv }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .negv }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .none }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .negvNegV }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .none }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .negV }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .negv }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .negV }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .negv }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .negV }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .negv }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .none }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .negV }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .negv }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .negv }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .negv }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .negv }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .negV }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .negv }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .none }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .negv }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .negv }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .none }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .none }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .none }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .negV }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .negv }
  , { walsCode := "tgo", language := "Tsogo", iso := "tsv", value := .negv }
  , { walsCode := "tsn", language := "Tsonga", iso := "tso", value := .negv }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .negv }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .negv }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .none }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .none }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .negv }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .negV }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .none }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .negv }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .none }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .none }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .negV }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .none }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .negv }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .negV }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .negv }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .none }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .none }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .negv }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .negv }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .negv }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .negv }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .negV }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .negV }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .negv }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .none }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .negv }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .none }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .negv }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .negv }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .negv }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .negv }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .none }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .negv }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .negv }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .negv }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .none }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .negv }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .negV }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .negV }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .none }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .none }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .negv }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .negV }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .negv }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .negV }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .negv }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .negv }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .none }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .negv }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .negv }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .negv }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .negv }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .none }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .negV }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .none }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .none }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .none }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .none }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .negv }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .negv }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .none }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .negv }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .negv }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .negv }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .negV }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .negv }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .negv }
  , { walsCode := "was", language := "Washo", iso := "was", value := .none }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .negv }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .negV }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .negv }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .none }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .negV }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .negv }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .negv }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .none }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .negv }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .none }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .negv }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .negv }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .negv }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .negv }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .negv }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .negv }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .negv }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .none }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .negv }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .negv }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .none }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .negv }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .negv }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .none }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .negV }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .negv }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .negV }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .negv }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .none }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .none }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .negV }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .negV }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .negv }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .negV }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .negv }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .none }
  , { walsCode := "yrr", language := "Yaruro", iso := "yae", value := .none }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .negv }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .negv }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .negv }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .negv }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .negv }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .negv }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .negV }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .negv }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .negv }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .negv }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .negv }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .negv }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .negV }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .negV }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .negv }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .none }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .none }
  , { walsCode := "yrm", language := "Yurimangí", iso := "", value := .none }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .negv }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .negv }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .none }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .negv }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .negv }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .negV }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .negv }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .negv }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .none }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .negV }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .negv }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .negvNegV }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .negv }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .negV }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .negv }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .negV }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .negV }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .negv }
  ]

/-- Complete WALS 143E dataset (1325 languages). -/
def allData : List (Datapoint PreverbalNegativeMorphemes) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1325 := by native_decide

theorem count_negv :
    (allData.filter (·.value == .negv)).length = 682 := by native_decide
theorem count_negV :
    (allData.filter (·.value == .negV)).length = 230 := by native_decide
theorem count_negvNegV :
    (allData.filter (·.value == .negvNegV)).length = 23 := by native_decide
theorem count_none :
    (allData.filter (·.value == .none)).length = 390 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F143E
