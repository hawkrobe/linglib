/-!
# WALS Feature 97A: Relationship between the Order of Object and Verb and the Order of Adjective and Noun
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 97A`.

Chapter 97, 1316 languages.
-/

namespace Core.WALS.F97A

/-- WALS 97A values. -/
inductive RelationshipBetweenTheOrderOfObjectAndVerbAndTheOrderOfAdjectiveAndNoun where
  | ovAndAdjn  -- OV and AdjN (216 languages)
  | ovAndNadj  -- OV and NAdj (332 languages)
  | voAndAdjn  -- VO and AdjN (114 languages)
  | voAndNadj  -- VO and NAdj (456 languages)
  | other  -- Other (198 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 97A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : RelationshipBetweenTheOrderOfObjectAndVerbAndTheOrderOfAdjectiveAndNoun
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .voAndNadj }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .other }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .voAndNadj }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .voAndNadj }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .ovAndNadj }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .other }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .ovAndNadj }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .ovAndNadj }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .voAndNadj }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .other }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .voAndNadj }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .other }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .voAndNadj }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .other }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .ovAndNadj }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .voAndNadj }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .ovAndNadj }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .other }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .voAndNadj }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .ovAndNadj }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .ovAndAdjn }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .voAndNadj }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .voAndAdjn }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .voAndAdjn }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .ovAndAdjn }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .voAndAdjn }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .other }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .voAndNadj }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .ovAndNadj }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .ovAndAdjn }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .other }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .voAndNadj }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .voAndAdjn }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .voAndNadj }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .ovAndNadj }
  , { walsCode := "amm", language := "Ama", iso := "amm", value := .other }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .ovAndNadj }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .ovAndNadj }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .voAndNadj }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .voAndNadj }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .voAndNadj }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .ovAndAdjn }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .other }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .ovAndNadj }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .ovAndAdjn }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .voAndAdjn }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .voAndNadj }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .ovAndNadj }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .voAndNadj }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .ovAndNadj }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .voAndNadj }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .ovAndNadj }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .ovAndNadj }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .ovAndNadj }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .voAndNadj }
  , { walsCode := "ayi", language := "Anyi", iso := "any", value := .voAndNadj }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .other }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .voAndNadj }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .ovAndNadj }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .ovAndNadj }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .ovAndNadj }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .ovAndNadj }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .other }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .ovAndNadj }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .voAndNadj }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .voAndNadj }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .voAndNadj }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .voAndNadj }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .voAndNadj }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .voAndNadj }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .voAndNadj }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .ovAndNadj }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .voAndNadj }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .voAndAdjn }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .ovAndNadj }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .ovAndAdjn }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .other }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .ovAndAdjn }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .voAndNadj }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .voAndNadj }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .ovAndNadj }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .ovAndNadj }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .ovAndAdjn }
  , { walsCode := "atm", language := "Atacameño", iso := "kuz", value := .ovAndNadj }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .other }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .ovAndAdjn }
  , { walsCode := "au", language := "Au", iso := "avt", value := .voAndNadj }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .ovAndAdjn }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .other }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .ovAndAdjn }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .ovAndAdjn }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .ovAndNadj }
  , { walsCode := "awy", language := "Awyi", iso := "auw", value := .ovAndNadj }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .voAndNadj }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .ovAndAdjn }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .voAndNadj }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .ovAndAdjn }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .voAndNadj }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .voAndNadj }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .other }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .ovAndNadj }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .voAndNadj }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .voAndNadj }
  , { walsCode := "bdw", language := "Baham", iso := "bdw", value := .ovAndNadj }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .voAndAdjn }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .voAndNadj }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .voAndNadj }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .voAndAdjn }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .voAndAdjn }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .voAndNadj }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .voAndNadj }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .voAndNadj }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .ovAndAdjn }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .ovAndNadj }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .ovAndAdjn }
  , { walsCode := "bgm", language := "Bangime", iso := "dba", value := .ovAndNadj }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .voAndNadj }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .voAndNadj }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .voAndNadj }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .ovAndNadj }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .ovAndNadj }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .voAndAdjn }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .other }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .voAndNadj }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .ovAndNadj }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .ovAndNadj }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .voAndNadj }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .ovAndNadj }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .voAndNadj }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .ovAndAdjn }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .ovAndNadj }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .voAndNadj }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .voAndNadj }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .voAndNadj }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .ovAndNadj }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .other }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .ovAndAdjn }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .voAndAdjn }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .other }
  , { walsCode := "blu", language := "Bena-Lulua", iso := "lua", value := .voAndNadj }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .voAndNadj }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .voAndNadj }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .voAndNadj }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .voAndNadj }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .ovAndNadj }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .voAndNadj }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .ovAndAdjn }
  , { walsCode := "bhu", language := "Bhumij", iso := "unr", value := .ovAndAdjn }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .voAndNadj }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .voAndNadj }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .other }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .voAndNadj }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .ovAndNadj }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .ovAndNadj }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .voAndAdjn }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .ovAndNadj }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .voAndNadj }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .other }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .voAndAdjn }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .voAndNadj }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .ovAndNadj }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .voAndAdjn }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .ovAndAdjn }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .ovAndNadj }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .other }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .ovAndNadj }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .other }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .other }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .voAndNadj }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .voAndNadj }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .ovAndNadj }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .ovAndAdjn }
  , { walsCode := "bub", language := "Bubi", iso := "bvb", value := .voAndNadj }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .voAndNadj }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .voAndNadj }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .other }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .ovAndNadj }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .voAndAdjn }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .voAndNadj }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .ovAndNadj }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .voAndNadj }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .other }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .other }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .ovAndAdjn }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .ovAndNadj }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .voAndNadj }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .voAndNadj }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .ovAndAdjn }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .ovAndNadj }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .voAndNadj }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .ovAndAdjn }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .ovAndAdjn }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .voAndAdjn }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .voAndNadj }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .other }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .ovAndNadj }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .voAndAdjn }
  , { walsCode := "car", language := "Carib", iso := "car", value := .ovAndAdjn }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .ovAndNadj }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .ovAndNadj }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .voAndNadj }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .ovAndNadj }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .other }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .ovAndAdjn }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .voAndAdjn }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .voAndNadj }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .ovAndAdjn }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .other }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .voAndNadj }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .voAndNadj }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .ovAndNadj }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .voAndAdjn }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .other }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .ovAndAdjn }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .voAndNadj }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .voAndNadj }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .ovAndAdjn }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .ovAndAdjn }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .other }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .ovAndAdjn }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .ovAndAdjn }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .voAndNadj }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .ovAndNadj }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .ovAndNadj }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .other }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .ovAndNadj }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .voAndNadj }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .voAndNadj }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .voAndNadj }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .voAndNadj }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .voAndAdjn }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .ovAndAdjn }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .ovAndNadj }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .other }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .ovAndAdjn }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .voAndAdjn }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .voAndAdjn }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .voAndNadj }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .ovAndAdjn }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .ovAndAdjn }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .ovAndNadj }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .voAndNadj }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .ovAndAdjn }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .other }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .voAndNadj }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .voAndNadj }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .voAndNadj }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .ovAndNadj }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .ovAndAdjn }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .ovAndNadj }
  , { walsCode := "cuc", language := "Cuica", iso := "", value := .other }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .ovAndNadj }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .voAndAdjn }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .voAndNadj }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .other }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .ovAndNadj }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .voAndNadj }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .voAndNadj }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .ovAndAdjn }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .other }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .ovAndNadj }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .voAndAdjn }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .ovAndAdjn }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .ovAndAdjn }
  , { walsCode := "day", language := "Day", iso := "dai", value := .voAndNadj }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .other }
  , { walsCode := "des", language := "Desano", iso := "des", value := .ovAndAdjn }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .ovAndAdjn }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .ovAndNadj }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .other }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .ovAndAdjn }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .voAndNadj }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .other }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .ovAndNadj }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .ovAndNadj }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .ovAndNadj }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .other }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .voAndNadj }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .ovAndNadj }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .other }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .other }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .other }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .ovAndNadj }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .other }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .other }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .ovAndAdjn }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .voAndAdjn }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .voAndNadj }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .other }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .ovAndNadj }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .voAndNadj }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .voAndNadj }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .voAndNadj }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .voAndNadj }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .other }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .voAndNadj }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .ovAndAdjn }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .ovAndNadj }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .ovAndNadj }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .other }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .ovAndNadj }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .ovAndNadj }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .ovAndNadj }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .voAndNadj }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .voAndNadj }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .ovAndAdjn }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .ovAndNadj }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .other }
  , { walsCode := "ene", language := "Enets", iso := "", value := .ovAndAdjn }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .voAndNadj }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .voAndNadj }
  , { walsCode := "eng", language := "English", iso := "eng", value := .voAndAdjn }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .ovAndNadj }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .voAndNadj }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .ovAndNadj }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .other }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .voAndAdjn }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .ovAndAdjn }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .ovAndAdjn }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .voAndNadj }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .voAndNadj }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .ovAndNadj }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .voAndNadj }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .voAndAdjn }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .ovAndNadj }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .other }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .voAndNadj }
  , { walsCode := "for", language := "Fore", iso := "for", value := .ovAndAdjn }
  , { walsCode := "fre", language := "French", iso := "fra", value := .voAndNadj }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .other }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .voAndNadj }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .voAndNadj }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .ovAndNadj }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .ovAndNadj }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .voAndNadj }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .voAndNadj }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .voAndNadj }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .ovAndAdjn }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .voAndNadj }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .other }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .ovAndAdjn }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .ovAndAdjn }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .ovAndNadj }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .voAndNadj }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .voAndNadj }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .ovAndNadj }
  , { walsCode := "gbk", language := "Gbaya (Northwest)", iso := "gya", value := .voAndAdjn }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .voAndAdjn }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .voAndNadj }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .voAndNadj }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .ovAndAdjn }
  , { walsCode := "ger", language := "German", iso := "deu", value := .other }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .other }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .other }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .other }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .voAndNadj }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .ovAndAdjn }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .voAndNadj }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .voAndAdjn }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .ovAndNadj }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .ovAndAdjn }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .ovAndNadj }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .ovAndNadj }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .voAndNadj }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .voAndAdjn }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .ovAndNadj }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .voAndNadj }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .voAndNadj }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .other }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .voAndNadj }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .voAndAdjn }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .ovAndNadj }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .ovAndNadj }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .ovAndAdjn }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .voAndNadj }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .ovAndNadj }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .other }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .other }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .voAndAdjn }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .voAndNadj }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .other }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .other }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .other }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .ovAndAdjn }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .ovAndNadj }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .other }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .ovAndNadj }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .voAndNadj }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .ovAndNadj }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .voAndNadj }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .voAndAdjn }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .ovAndNadj }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .ovAndAdjn }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .other }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .ovAndNadj }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .voAndNadj }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .voAndAdjn }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .voAndNadj }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .voAndNadj }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .ovAndAdjn }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .voAndNadj }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .voAndNadj }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .voAndNadj }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .voAndAdjn }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .voAndNadj }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .ovAndNadj }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .other }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .ovAndAdjn }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .ovAndNadj }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .voAndNadj }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .ovAndNadj }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .voAndNadj }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .ovAndAdjn }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .voAndNadj }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .voAndNadj }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .ovAndAdjn }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .ovAndAdjn }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .ovAndNadj }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .voAndAdjn }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .voAndAdjn }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .ovAndAdjn }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .ovAndAdjn }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .voAndNadj }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .voAndAdjn }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .ovAndAdjn }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .ovAndNadj }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .other }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .ovAndNadj }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .voAndAdjn }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .voAndNadj }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .voAndAdjn }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .other }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .ovAndAdjn }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .ovAndNadj }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .voAndNadj }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .voAndAdjn }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .voAndNadj }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .voAndNadj }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .voAndNadj }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .ovAndAdjn }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .voAndNadj }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .ovAndNadj }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .voAndNadj }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .voAndAdjn }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .ovAndNadj }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .other }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .voAndNadj }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .voAndNadj }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .ovAndNadj }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .voAndNadj }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .ovAndNadj }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .ovAndNadj }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .voAndNadj }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .voAndNadj }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .voAndNadj }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .other }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .other }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .voAndAdjn }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .voAndNadj }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .voAndNadj }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .other }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .ovAndNadj }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .voAndNadj }
  , { walsCode := "jad", language := "Jad", iso := "jda", value := .ovAndNadj }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .voAndAdjn }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .other }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .ovAndNadj }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .ovAndAdjn }
  , { walsCode := "jrw", language := "Jarawa (in Andamans)", iso := "anq", value := .ovAndNadj }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .other }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .ovAndNadj }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .ovAndNadj }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .ovAndAdjn }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .ovAndAdjn }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .other }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .voAndNadj }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .voAndNadj }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .voAndNadj }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .ovAndAdjn }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .voAndNadj }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .voAndNadj }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .other }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .voAndNadj }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .voAndNadj }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .ovAndNadj }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .ovAndNadj }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .ovAndNadj }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .ovAndNadj }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .ovAndNadj }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .ovAndAdjn }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .ovAndNadj }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .ovAndNadj }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .ovAndNadj }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .ovAndAdjn }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .voAndNadj }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .voAndNadj }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .ovAndNadj }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .other }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .other }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .other }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "knd", language := "Kannada", iso := "kan", value := .ovAndAdjn }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .ovAndNadj }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .ovAndNadj }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .other }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .voAndNadj }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .ovAndAdjn }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .other }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .ovAndNadj }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .ovAndAdjn }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .other }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .voAndNadj }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .voAndNadj }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .voAndNadj }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .voAndNadj }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .other }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .other }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .ovAndNadj }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .voAndAdjn }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .voAndNadj }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .voAndNadj }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .voAndNadj }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .voAndNadj }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .other }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .ovAndNadj }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .voAndNadj }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .other }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .voAndNadj }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .ovAndAdjn }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .voAndNadj }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .ovAndAdjn }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .voAndNadj }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .ovAndAdjn }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .ovAndAdjn }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .ovAndAdjn }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .ovAndAdjn }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .ovAndAdjn }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .ovAndNadj }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .ovAndNadj }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .ovAndAdjn }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .voAndNadj }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .voAndNadj }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .voAndNadj }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .ovAndAdjn }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .voAndNadj }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .voAndNadj }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .ovAndNadj }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .voAndNadj }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .ovAndAdjn }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .voAndNadj }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .voAndNadj }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .ovAndNadj }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .voAndNadj }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .voAndNadj }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .other }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .ovAndAdjn }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .other }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .other }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .voAndAdjn }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .ovAndNadj }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .ovAndNadj }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .voAndNadj }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .ovAndNadj }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .ovAndNadj }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .ovAndNadj }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .voAndNadj }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .ovAndAdjn }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .ovAndAdjn }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .ovAndNadj }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .voAndNadj }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .ovAndAdjn }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .voAndAdjn }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .voAndNadj }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .voAndNadj }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .ovAndAdjn }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .ovAndAdjn }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .voAndNadj }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .ovAndAdjn }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .voAndNadj }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .ovAndAdjn }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .ovAndAdjn }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .voAndNadj }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .ovAndAdjn }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .voAndNadj }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .ovAndNadj }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .ovAndNadj }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .ovAndNadj }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .ovAndNadj }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .voAndAdjn }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .voAndNadj }
  , { walsCode := "krz", language := "Kryz", iso := "kry", value := .ovAndAdjn }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .ovAndNadj }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .ovAndNadj }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .ovAndAdjn }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .ovAndNadj }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .ovAndAdjn }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .ovAndNadj }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .ovAndNadj }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .voAndNadj }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .ovAndNadj }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .other }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .ovAndNadj }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .ovAndNadj }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .ovAndAdjn }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .voAndNadj }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .voAndAdjn }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .voAndNadj }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .ovAndNadj }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .ovAndNadj }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .ovAndAdjn }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .other }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .ovAndAdjn }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .ovAndNadj }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .ovAndNadj }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .voAndNadj }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .voAndNadj }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .voAndAdjn }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .ovAndNadj }
  , { walsCode := "laf", language := "Lafofa", iso := "laf", value := .other }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .voAndNadj }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .other }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .other }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .ovAndAdjn }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .ovAndNadj }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .ovAndNadj }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .voAndNadj }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .voAndNadj }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .ovAndAdjn }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .other }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .voAndNadj }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .voAndNadj }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .voAndNadj }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .voAndNadj }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .ovAndNadj }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .voAndAdjn }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .ovAndNadj }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .voAndNadj }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .voAndNadj }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .other }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .voAndNadj }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .voAndNadj }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .voAndNadj }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .other }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .ovAndNadj }
  , { walsCode := "les", language := "Lese", iso := "les", value := .other }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .voAndNadj }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .voAndNadj }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .ovAndAdjn }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .voAndAdjn }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .ovAndAdjn }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .other }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .voAndAdjn }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .voAndNadj }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .ovAndNadj }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .voAndAdjn }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .other }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .voAndAdjn }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .voAndNadj }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .voAndNadj }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .voAndNadj }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .ovAndNadj }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .voAndNadj }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .voAndNadj }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .other }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .other }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .voAndNadj }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .other }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .voAndNadj }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .voAndNadj }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .voAndNadj }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .voAndAdjn }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .voAndNadj }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .other }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .voAndNadj }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .ovAndNadj }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .voAndAdjn }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .other }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .ovAndNadj }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .voAndNadj }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .voAndAdjn }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .voAndNadj }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .ovAndAdjn }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .voAndNadj }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .ovAndNadj }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .ovAndAdjn }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .voAndAdjn }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .voAndNadj }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .other }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .ovAndNadj }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .voAndNadj }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .voAndNadj }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .voAndNadj }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .ovAndNadj }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .ovAndAdjn }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .voAndNadj }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .voAndNadj }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .ovAndAdjn }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .other }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .other }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .voAndNadj }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .voAndNadj }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .voAndNadj }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .ovAndNadj }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .other }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .ovAndAdjn }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .ovAndNadj }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .voAndAdjn }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .ovAndNadj }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .voAndNadj }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .ovAndNadj }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .voAndNadj }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .voAndNadj }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .ovAndAdjn }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .ovAndNadj }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .ovAndNadj }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .voAndAdjn }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .ovAndAdjn }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .voAndNadj }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .voAndAdjn }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .other }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .ovAndNadj }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .ovAndAdjn }
  , { walsCode := "mrc", language := "Marchha", iso := "rnp", value := .ovAndAdjn }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .voAndNadj }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .ovAndAdjn }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .ovAndNadj }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .ovAndNadj }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .voAndNadj }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .ovAndNadj }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .voAndNadj }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .ovAndNadj }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .voAndNadj }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .voAndNadj }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .ovAndNadj }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .other }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .ovAndNadj }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .ovAndNadj }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .ovAndNadj }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .voAndNadj }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .ovAndNadj }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .voAndAdjn }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .voAndNadj }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .voAndAdjn }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .voAndNadj }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .other }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .voAndNadj }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .voAndNadj }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .voAndNadj }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .voAndNadj }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .voAndNadj }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .voAndAdjn }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .voAndNadj }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .voAndNadj }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .voAndNadj }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .voAndNadj }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .voAndNadj }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .other }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .ovAndNadj }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .ovAndNadj }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .ovAndNadj }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .other }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .ovAndNadj }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .ovAndAdjn }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .voAndNadj }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .ovAndNadj }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .voAndNadj }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .ovAndNadj }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .ovAndNadj }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .other }
  , { walsCode := "mil", language := "Milang", iso := "", value := .ovAndAdjn }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .voAndNadj }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .other }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .ovAndNadj }
  , { walsCode := "mir", language := "Miriwung", iso := "mep", value := .other }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .ovAndAdjn }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .ovAndNadj }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .other }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .other }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .voAndNadj }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .voAndNadj }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .voAndNadj }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .voAndNadj }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .voAndNadj }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .voAndNadj }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .ovAndNadj }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .voAndNadj }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .other }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .voAndNadj }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .other }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .voAndNadj }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .voAndNadj }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .voAndNadj }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .voAndNadj }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .other }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .ovAndNadj }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .voAndNadj }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .voAndNadj }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .voAndAdjn }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .voAndNadj }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .other }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .other }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .ovAndNadj }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .ovAndNadj }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .voAndNadj }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .voAndNadj }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .voAndNadj }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .ovAndNadj }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .voAndNadj }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .voAndNadj }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .voAndNadj }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .ovAndAdjn }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .voAndNadj }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .voAndNadj }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .voAndNadj }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .ovAndNadj }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .voAndNadj }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .other }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .voAndNadj }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .voAndNadj }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .voAndAdjn }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .voAndAdjn }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .voAndNadj }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .voAndNadj }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .ovAndNadj }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .voAndNadj }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .ovAndNadj }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .ovAndNadj }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .ovAndNadj }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .other }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .voAndNadj }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .voAndNadj }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .other }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .voAndNadj }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .other }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .voAndNadj }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .voAndNadj }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .ovAndAdjn }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .ovAndNadj }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .voAndNadj }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .voAndNadj }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .ovAndNadj }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .ovAndNadj }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .ovAndNadj }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .other }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .ovAndNadj }
  , { walsCode := "nau", language := "Nauruan", iso := "nau", value := .voAndNadj }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .ovAndNadj }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .voAndNadj }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .voAndNadj }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .ovAndNadj }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .voAndNadj }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .voAndNadj }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .voAndNadj }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .voAndAdjn }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .voAndNadj }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .ovAndNadj }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .ovAndAdjn }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .ovAndNadj }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .ovAndAdjn }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .ovAndAdjn }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .ovAndAdjn }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .ovAndAdjn }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .other }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .other }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .ovAndNadj }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .voAndNadj }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .ovAndNadj }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .other }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .ovAndNadj }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .voAndNadj }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .ovAndNadj }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .ovAndAdjn }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .ovAndNadj }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .other }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .other }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .voAndNadj }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .other }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .other }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .voAndNadj }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .voAndNadj }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .voAndNadj }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .ovAndNadj }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .other }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .voAndNadj }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .voAndAdjn }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .ovAndAdjn }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .voAndAdjn }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .voAndNadj }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .voAndNadj }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .ovAndAdjn }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .other }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .voAndNadj }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .voAndNadj }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .ovAndNadj }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .ovAndAdjn }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .voAndNadj }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .voAndNadj }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .voAndAdjn }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .voAndNadj }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .voAndNadj }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .voAndNadj }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .ovAndNadj }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .ovAndNadj }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .other }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .voAndNadj }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .other }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .ovAndNadj }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .voAndNadj }
  , { walsCode := "nus", language := "Nusu", iso := "nuf", value := .ovAndNadj }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .other }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .ovAndNadj }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .voAndNadj }
  , { walsCode := "nyr", language := "Nyangumarda", iso := "nna", value := .other }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .ovAndNadj }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .ovAndAdjn }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .voAndAdjn }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .voAndAdjn }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .other }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .voAndAdjn }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .voAndAdjn }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .other }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .voAndNadj }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .ovAndNadj }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .ovAndAdjn }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .ovAndNadj }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .ovAndNadj }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .ovAndNadj }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .ovAndNadj }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .ovAndNadj }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .ovAndNadj }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .ovAndNadj }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .ovAndAdjn }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .voAndAdjn }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .voAndNadj }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .voAndAdjn }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .voAndAdjn }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .voAndNadj }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .ovAndAdjn }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .voAndNadj }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .voAndAdjn }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .voAndNadj }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .voAndNadj }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .voAndNadj }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .other }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .other }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .voAndNadj }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .ovAndAdjn }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .other }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .voAndNadj }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .ovAndAdjn }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .voAndNadj }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .ovAndAdjn }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .voAndNadj }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .other }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .ovAndAdjn }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .voAndNadj }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .ovAndNadj }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .ovAndNadj }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .voAndNadj }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .ovAndAdjn }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .voAndAdjn }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .ovAndNadj }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .ovAndNadj }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .ovAndNadj }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .other }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .other }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .voAndNadj }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .other }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .voAndNadj }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .voAndAdjn }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .voAndNadj }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .voAndNadj }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .ovAndAdjn }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .voAndNadj }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .ovAndNadj }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .ovAndAdjn }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .voAndNadj }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .ovAndNadj }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .ovAndNadj }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .ovAndAdjn }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .ovAndAdjn }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .ovAndAdjn }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .voAndAdjn }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .voAndNadj }
  , { walsCode := "rji", language := "Raji", iso := "rji", value := .other }
  , { walsCode := "ral", language := "Ralte", iso := "ral", value := .ovAndNadj }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .ovAndNadj }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .ovAndAdjn }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .ovAndNadj }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .voAndNadj }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .ovAndNadj }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .ovAndNadj }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .ovAndNadj }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .ovAndAdjn }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .ovAndAdjn }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .ovAndAdjn }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .other }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .voAndAdjn }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .voAndNadj }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .voAndNadj }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .voAndNadj }
  ]

private def allData_2 : List Datapoint :=
  [ { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .voAndNadj }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .voAndNadj }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .other }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .ovAndNadj }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .ovAndNadj }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .voAndNadj }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .voAndNadj }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .voAndAdjn }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .ovAndAdjn }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .voAndAdjn }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .voAndNadj }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .voAndNadj }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .ovAndNadj }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .other }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .ovAndNadj }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .voAndNadj }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .voAndNadj }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .ovAndNadj }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .voAndAdjn }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .voAndNadj }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .ovAndAdjn }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .ovAndAdjn }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .ovAndNadj }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .voAndNadj }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .ovAndNadj }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .voAndNadj }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .ovAndAdjn }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .ovAndAdjn }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .ovAndAdjn }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .voAndNadj }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .voAndNadj }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .other }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .ovAndAdjn }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .ovAndAdjn }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .ovAndNadj }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .ovAndNadj }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .voAndNadj }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .ovAndNadj }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .other }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .ovAndNadj }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .voAndAdjn }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .other }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .voAndNadj }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .ovAndAdjn }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .voAndNadj }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .voAndNadj }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .ovAndNadj }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .voAndNadj }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .ovAndAdjn }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .other }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .ovAndNadj }
  , { walsCode := "smp", language := "Shompen", iso := "sii", value := .voAndAdjn }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .voAndNadj }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .ovAndAdjn }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .ovAndNadj }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .voAndAdjn }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .ovAndAdjn }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .ovAndNadj }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .ovAndNadj }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .voAndNadj }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .ovAndNadj }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .ovAndAdjn }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .voAndNadj }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .ovAndAdjn }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .voAndAdjn }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .ovAndNadj }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .ovAndNadj }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .voAndNadj }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .voAndAdjn }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .ovAndNadj }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .ovAndNadj }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .voAndAdjn }
  , { walsCode := "so", language := "So", iso := "teu", value := .voAndNadj }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .voAndNadj }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .ovAndAdjn }
  , { walsCode := "som", language := "Somali", iso := "som", value := .ovAndNadj }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .ovAndNadj }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .other }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .ovAndAdjn }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .voAndNadj }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .voAndNadj }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .voAndNadj }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .ovAndNadj }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .voAndAdjn }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .voAndNadj }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .voAndNadj }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .voAndNadj }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .ovAndNadj }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .ovAndAdjn }
  , { walsCode := "sku", language := "Suku", iso := "sub", value := .voAndNadj }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .voAndNadj }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .voAndNadj }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .ovAndNadj }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .voAndNadj }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .other }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .voAndAdjn }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .voAndNadj }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .ovAndNadj }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .ovAndNadj }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .voAndNadj }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .other }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .other }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .voAndNadj }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .voAndNadj }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .other }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .ovAndNadj }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .ovAndNadj }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .ovAndNadj }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .ovAndAdjn }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .ovAndNadj }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .voAndNadj }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .ovAndAdjn }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .voAndNadj }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .ovAndAdjn }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .ovAndNadj }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .ovAndAdjn }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .ovAndAdjn }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .ovAndNadj }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .other }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .voAndNadj }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .ovAndAdjn }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .voAndNadj }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .ovAndNadj }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .ovAndNadj }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .voAndNadj }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .ovAndNadj }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .ovAndAdjn }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .voAndNadj }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .voAndNadj }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .voAndNadj }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .voAndNadj }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .ovAndNadj }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .voAndNadj }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .voAndAdjn }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .voAndAdjn }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .other }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .voAndNadj }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .voAndNadj }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .ovAndNadj }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .voAndNadj }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .voAndNadj }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .voAndNadj }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .voAndNadj }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .ovAndAdjn }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .ovAndAdjn }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .voAndAdjn }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .ovAndAdjn }
  , { walsCode := "tdi", language := "Tibetan (Dingri)", iso := "bod", value := .ovAndNadj }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .ovAndNadj }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .ovAndNadj }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .other }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .ovAndNadj }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .other }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .voAndNadj }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .voAndNadj }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .ovAndAdjn }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .ovAndAdjn }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .other }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .other }
  , { walsCode := "tia", language := "Tima", iso := "tms", value := .voAndNadj }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .voAndNadj }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .ovAndAdjn }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .voAndAdjn }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .other }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .other }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .voAndAdjn }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .voAndNadj }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .other }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .voAndAdjn }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .ovAndNadj }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .other }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .voAndNadj }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .voAndNadj }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .voAndNadj }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .ovAndNadj }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .ovAndAdjn }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .other }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .voAndAdjn }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .voAndNadj }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .other }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .ovAndAdjn }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .ovAndAdjn }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .ovAndAdjn }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .voAndAdjn }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .ovAndAdjn }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .ovAndNadj }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .other }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .voAndNadj }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .voAndNadj }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .ovAndAdjn }
  , { walsCode := "tum", language := "Tumleo", iso := "tmq", value := .voAndNadj }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .ovAndNadj }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .voAndNadj }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .ovAndNadj }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .voAndNadj }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .voAndNadj }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .ovAndAdjn }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .ovAndAdjn }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .other }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .other }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .ovAndNadj }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .ovAndAdjn }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .other }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .ovAndAdjn }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .ovAndAdjn }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .ovAndAdjn }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .ovAndAdjn }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .ovAndAdjn }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .voAndAdjn }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .voAndNadj }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .voAndNadj }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .ovAndNadj }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .ovAndNadj }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .voAndNadj }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .ovAndNadj }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .voAndNadj }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .ovAndNadj }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .voAndNadj }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .ovAndAdjn }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .other }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .ovAndNadj }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .ovAndNadj }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .ovAndAdjn }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .ovAndNadj }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .ovAndAdjn }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .ovAndAdjn }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .ovAndNadj }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .ovAndNadj }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .voAndNadj }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .voAndNadj }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .voAndNadj }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .ovAndNadj }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .ovAndNadj }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .ovAndAdjn }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .voAndNadj }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .ovAndNadj }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .ovAndAdjn }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .ovAndNadj }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .other }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .other }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .ovAndNadj }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .ovAndNadj }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .other }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .voAndNadj }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .voAndNadj }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .other }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .other }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .other }
  , { walsCode := "was", language := "Washo", iso := "was", value := .ovAndAdjn }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .ovAndNadj }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .voAndNadj }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .ovAndNadj }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .voAndNadj }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .voAndAdjn }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .voAndNadj }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .ovAndNadj }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .voAndNadj }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .ovAndNadj }
  , { walsCode := "wn", language := "Wik Ngathana", iso := "wig", value := .ovAndNadj }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .other }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .other }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .other }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .ovAndNadj }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .ovAndAdjn }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .voAndNadj }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .voAndNadj }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .voAndNadj }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .ovAndNadj }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .ovAndNadj }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .ovAndNadj }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .voAndNadj }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .voAndAdjn }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .ovAndAdjn }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .voAndNadj }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .ovAndAdjn }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .ovAndAdjn }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .ovAndNadj }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .ovAndNadj }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .ovAndAdjn }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .voAndNadj }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .voAndNadj }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .ovAndAdjn }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .ovAndAdjn }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .other }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .voAndNadj }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .ovAndNadj }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .ovAndNadj }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .other }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .other }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .voAndAdjn }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .voAndAdjn }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .voAndNadj }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .ovAndNadj }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .voAndAdjn }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .ovAndAdjn }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .ovAndAdjn }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .ovAndAdjn }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .voAndNadj }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .other }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .other }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .ovAndAdjn }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .voAndAdjn }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .voAndNadj }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .voAndNadj }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .voAndNadj }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .voAndNadj }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .other }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .ovAndAdjn }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .ovAndNadj }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .voAndAdjn }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .voAndAdjn }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .voAndNadj }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .ovAndNadj }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .ovAndNadj }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .ovAndNadj }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .ovAndNadj }
  ]

/-- Complete WALS 97A dataset (1316 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1316 := by native_decide

theorem count_ovAndAdjn :
    (allData.filter (·.value == .ovAndAdjn)).length = 216 := by native_decide
theorem count_ovAndNadj :
    (allData.filter (·.value == .ovAndNadj)).length = 332 := by native_decide
theorem count_voAndAdjn :
    (allData.filter (·.value == .voAndAdjn)).length = 114 := by native_decide
theorem count_voAndNadj :
    (allData.filter (·.value == .voAndNadj)).length = 456 := by native_decide
theorem count_other :
    (allData.filter (·.value == .other)).length = 198 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F97A
