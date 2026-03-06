/-!
# WALS Feature 95A: Relationship between the Order of Object and Verb and the Order of Adposition and Noun Phrase
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 95A`.

Chapter 95, 1142 languages.
-/

namespace Core.WALS.F95A

/-- WALS 95A values. -/
inductive RelationshipBetweenTheOrderOfObjectAndVerbAndTheOrderOfAdpositionAndNounPhrase where
  | ovAndPostpositions  -- OV and Postpositions (472 languages)
  | ovAndPrepositions  -- OV and Prepositions (14 languages)
  | voAndPostpositions  -- VO and Postpositions (42 languages)
  | voAndPrepositions  -- VO and Prepositions (456 languages)
  | other  -- Other (158 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 95A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : RelationshipBetweenTheOrderOfObjectAndVerbAndTheOrderOfAdpositionAndNounPhrase
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .other }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .other }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .ovAndPostpositions }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .ovAndPostpositions }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .voAndPrepositions }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .ovAndPostpositions }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .voAndPrepositions }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .other }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .voAndPostpositions }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .ovAndPostpositions }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .voAndPrepositions }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .voAndPrepositions }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .other }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .ovAndPostpositions }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .voAndPostpositions }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .ovAndPostpositions }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .other }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .voAndPrepositions }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .voAndPrepositions }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .ovAndPostpositions }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .voAndPrepositions }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .other }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .other }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .ovAndPostpositions }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .other }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .ovAndPostpositions }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .other }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .voAndPrepositions }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .voAndPrepositions }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .voAndPrepositions }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .ovAndPostpositions }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .ovAndPostpositions }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .voAndPrepositions }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .voAndPrepositions }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .voAndPrepositions }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .ovAndPostpositions }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .ovAndPostpositions }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .ovAndPostpositions }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .other }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .voAndPrepositions }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .voAndPrepositions }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .ovAndPostpositions }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .voAndPrepositions }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .ovAndPostpositions }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .other }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .other }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .voAndPrepositions }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .ovAndPostpositions }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .ovAndPostpositions }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .ovAndPostpositions }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .ovAndPostpositions }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .other }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .voAndPrepositions }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .voAndPrepositions }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .voAndPrepositions }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .voAndPrepositions }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .voAndPrepositions }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .voAndPrepositions }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .voAndPrepositions }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .ovAndPostpositions }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .voAndPrepositions }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .ovAndPostpositions }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .other }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .ovAndPostpositions }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .voAndPrepositions }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .voAndPrepositions }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .ovAndPostpositions }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .ovAndPostpositions }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .ovAndPostpositions }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .voAndPrepositions }
  , { walsCode := "au", language := "Au", iso := "avt", value := .voAndPrepositions }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .ovAndPostpositions }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .other }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .ovAndPostpositions }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .ovAndPostpositions }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .voAndPrepositions }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .ovAndPostpositions }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .voAndPrepositions }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .voAndPrepositions }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .other }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .voAndPrepositions }
  , { walsCode := "bgs", language := "Baga Sitemu", iso := "bsp", value := .voAndPostpositions }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .voAndPrepositions }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .other }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .other }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .voAndPrepositions }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .voAndPrepositions }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .voAndPrepositions }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .voAndPrepositions }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .voAndPrepositions }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .ovAndPostpositions }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .ovAndPostpositions }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .voAndPrepositions }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .voAndPrepositions }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .ovAndPostpositions }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .voAndPostpositions }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .ovAndPostpositions }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .voAndPrepositions }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .ovAndPostpositions }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .voAndPrepositions }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .ovAndPostpositions }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .voAndPostpositions }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .voAndPrepositions }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .ovAndPostpositions }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .ovAndPostpositions }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .voAndPrepositions }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .voAndPrepositions }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .ovAndPostpositions }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .ovAndPostpositions }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .ovAndPostpositions }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .voAndPrepositions }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .other }
  , { walsCode := "blu", language := "Bena-Lulua", iso := "lua", value := .voAndPrepositions }
  , { walsCode := "bse", language := "Berber (Ayt Seghrouchen Middle Atlas)", iso := "rif", value := .voAndPrepositions }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .voAndPrepositions }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .voAndPrepositions }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .voAndPrepositions }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .ovAndPostpositions }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .ovAndPostpositions }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .ovAndPostpositions }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .ovAndPostpositions }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .voAndPrepositions }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .voAndPrepositions }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .voAndPrepositions }
  , { walsCode := "bia", language := "Bila", iso := "bip", value := .voAndPrepositions }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .ovAndPostpositions }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .ovAndPostpositions }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .voAndPostpositions }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .other }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .ovAndPostpositions }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .voAndPrepositions }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .other }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .voAndPrepositions }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .ovAndPostpositions }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .voAndPrepositions }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .ovAndPostpositions }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .voAndPrepositions }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .voAndPrepositions }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .ovAndPostpositions }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .voAndPrepositions }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .ovAndPostpositions }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .voAndPrepositions }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .voAndPrepositions }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .ovAndPostpositions }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .voAndPrepositions }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .voAndPrepositions }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .voAndPrepositions }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .voAndPrepositions }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .other }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .ovAndPostpositions }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .ovAndPostpositions }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .ovAndPostpositions }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .voAndPrepositions }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .other }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .ovAndPostpositions }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .ovAndPostpositions }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .voAndPrepositions }
  , { walsCode := "dok", language := "Bwele", iso := "ngc", value := .voAndPrepositions }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .ovAndPostpositions }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .ovAndPostpositions }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .voAndPrepositions }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .other }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .ovAndPostpositions }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .other }
  , { walsCode := "car", language := "Carib", iso := "car", value := .ovAndPostpositions }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .ovAndPostpositions }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .ovAndPostpositions }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .voAndPrepositions }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .ovAndPostpositions }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .other }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .voAndPrepositions }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .voAndPrepositions }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .other }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .other }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .voAndPrepositions }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .ovAndPostpositions }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .ovAndPostpositions }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .voAndPrepositions }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .voAndPrepositions }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .ovAndPostpositions }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .other }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .ovAndPostpositions }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .voAndPrepositions }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .ovAndPostpositions }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .ovAndPostpositions }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .ovAndPostpositions }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .ovAndPostpositions }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .voAndPrepositions }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .voAndPrepositions }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .voAndPrepositions }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .voAndPrepositions }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .voAndPrepositions }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .ovAndPostpositions }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .voAndPrepositions }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .ovAndPostpositions }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .ovAndPostpositions }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .ovAndPostpositions }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .voAndPrepositions }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .voAndPrepositions }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .voAndPrepositions }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .ovAndPostpositions }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .voAndPrepositions }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .ovAndPostpositions }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .ovAndPostpositions }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .voAndPostpositions }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .voAndPrepositions }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .ovAndPostpositions }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .voAndPrepositions }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .other }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .voAndPrepositions }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .voAndPostpositions }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .voAndPrepositions }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .voAndPostpositions }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .ovAndPostpositions }
  , { walsCode := "cuc", language := "Cuica", iso := "", value := .voAndPrepositions }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .ovAndPostpositions }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .voAndPrepositions }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .voAndPrepositions }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .other }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .ovAndPostpositions }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .voAndPostpositions }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .voAndPostpositions }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .ovAndPostpositions }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .other }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .ovAndPostpositions }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .ovAndPostpositions }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .voAndPrepositions }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .ovAndPostpositions }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .ovAndPostpositions }
  , { walsCode := "des", language := "Desano", iso := "des", value := .ovAndPostpositions }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .other }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .ovAndPostpositions }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .voAndPrepositions }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .ovAndPostpositions }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .ovAndPostpositions }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .ovAndPostpositions }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .ovAndPostpositions }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .other }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .voAndPrepositions }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .other }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .other }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .other }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .ovAndPostpositions }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .ovAndPostpositions }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .ovAndPostpositions }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .ovAndPostpositions }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .voAndPrepositions }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .voAndPrepositions }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .other }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .ovAndPostpositions }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .other }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .voAndPrepositions }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .voAndPrepositions }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .ovAndPostpositions }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .ovAndPostpositions }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .ovAndPostpositions }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .other }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .ovAndPostpositions }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .ovAndPostpositions }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .voAndPrepositions }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .ovAndPostpositions }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .voAndPrepositions }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .ovAndPostpositions }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .other }
  , { walsCode := "ene", language := "Enets", iso := "", value := .ovAndPostpositions }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .voAndPrepositions }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .voAndPrepositions }
  , { walsCode := "eng", language := "English", iso := "eng", value := .voAndPrepositions }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .ovAndPostpositions }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .voAndPrepositions }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .ovAndPostpositions }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .voAndPrepositions }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .voAndPostpositions }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .ovAndPostpositions }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .ovAndPostpositions }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .ovAndPostpositions }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .voAndPostpositions }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .voAndPrepositions }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .ovAndPostpositions }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .voAndPrepositions }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .voAndPostpositions }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .ovAndPostpositions }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .other }
  , { walsCode := "for", language := "Fore", iso := "for", value := .ovAndPostpositions }
  , { walsCode := "fre", language := "French", iso := "fra", value := .voAndPrepositions }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .other }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .voAndPrepositions }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .voAndPrepositions }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .ovAndPostpositions }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .ovAndPostpositions }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .voAndPrepositions }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .voAndPrepositions }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .voAndPrepositions }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .voAndPrepositions }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .ovAndPostpositions }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .ovAndPostpositions }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .ovAndPostpositions }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .voAndPrepositions }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .voAndPrepositions }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .ovAndPostpositions }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .voAndPrepositions }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .voAndPrepositions }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .voAndPrepositions }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .ovAndPostpositions }
  , { walsCode := "ger", language := "German", iso := "deu", value := .other }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .other }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .ovAndPostpositions }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .other }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .voAndPrepositions }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .voAndPrepositions }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .voAndPrepositions }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .voAndPrepositions }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .ovAndPostpositions }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .ovAndPostpositions }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .other }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .ovAndPostpositions }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .voAndPostpositions }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .voAndPrepositions }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .ovAndPostpositions }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .ovAndPostpositions }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .voAndPostpositions }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .voAndPostpositions }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .other }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .voAndPrepositions }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .voAndPrepositions }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .ovAndPostpositions }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .other }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .ovAndPostpositions }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .other }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .voAndPrepositions }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .voAndPrepositions }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .other }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .other }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .other }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .other }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .ovAndPostpositions }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .other }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .voAndPrepositions }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .ovAndPostpositions }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .ovAndPostpositions }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .voAndPrepositions }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .voAndPrepositions }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .ovAndPostpositions }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .ovAndPostpositions }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .ovAndPostpositions }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .voAndPrepositions }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .voAndPrepositions }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .voAndPrepositions }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .voAndPrepositions }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .ovAndPostpositions }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .voAndPrepositions }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .voAndPrepositions }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .voAndPrepositions }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .voAndPrepositions }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .voAndPrepositions }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .ovAndPostpositions }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .voAndPrepositions }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .ovAndPostpositions }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .ovAndPostpositions }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .voAndPrepositions }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .ovAndPostpositions }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .voAndPrepositions }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .ovAndPostpositions }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .voAndPrepositions }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .ovAndPostpositions }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .ovAndPostpositions }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .ovAndPostpositions }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .voAndPrepositions }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .voAndPrepositions }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .ovAndPostpositions }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .voAndPostpositions }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .ovAndPostpositions }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .ovAndPostpositions }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .other }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .other }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .voAndPrepositions }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .ovAndPostpositions }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .voAndPrepositions }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .voAndPrepositions }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .other }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .ovAndPostpositions }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .ovAndPostpositions }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .voAndPrepositions }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .voAndPrepositions }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .voAndPrepositions }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .voAndPrepositions }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .voAndPrepositions }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .ovAndPostpositions }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .voAndPrepositions }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .voAndPrepositions }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .ovAndPostpositions }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .other }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .voAndPrepositions }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .voAndPrepositions }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .ovAndPostpositions }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .voAndPostpositions }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .ovAndPrepositions }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .voAndPrepositions }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .voAndPrepositions }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .voAndPrepositions }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .other }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .voAndPrepositions }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .voAndPrepositions }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .voAndPrepositions }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .voAndPrepositions }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .ovAndPostpositions }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .other }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .voAndPrepositions }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .other }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .ovAndPostpositions }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .ovAndPostpositions }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .other }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .ovAndPostpositions }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .ovAndPostpositions }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .ovAndPostpositions }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .ovAndPostpositions }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .voAndPrepositions }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .voAndPrepositions }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .voAndPostpositions }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .ovAndPostpositions }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .ovAndPostpositions }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .voAndPrepositions }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .voAndPrepositions }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .ovAndPostpositions }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .voAndPrepositions }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .voAndPrepositions }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .ovAndPostpositions }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .other }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .ovAndPostpositions }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .ovAndPostpositions }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .ovAndPostpositions }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .ovAndPostpositions }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .ovAndPostpositions }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .ovAndPostpositions }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .voAndPrepositions }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .ovAndPostpositions }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .other }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .voAndPrepositions }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .voAndPrepositions }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .ovAndPostpositions }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .ovAndPostpositions }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .ovAndPostpositions }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .ovAndPostpositions }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .voAndPrepositions }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .voAndPrepositions }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .ovAndPostpositions }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .ovAndPostpositions }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .ovAndPostpositions }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .other }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .voAndPrepositions }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .voAndPrepositions }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .voAndPrepositions }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .voAndPrepositions }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .ovAndPostpositions }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .other }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .ovAndPostpositions }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .voAndPostpositions }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .ovAndPostpositions }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .voAndPrepositions }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .other }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .ovAndPostpositions }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .other }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .other }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .voAndPrepositions }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .ovAndPostpositions }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .other }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .voAndPrepositions }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .ovAndPostpositions }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .ovAndPostpositions }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .voAndPrepositions }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .ovAndPostpositions }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .ovAndPostpositions }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .ovAndPostpositions }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .ovAndPostpositions }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .ovAndPostpositions }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .ovAndPostpositions }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .ovAndPostpositions }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .ovAndPostpositions }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .voAndPrepositions }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .voAndPrepositions }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .voAndPrepositions }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .ovAndPostpositions }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .voAndPrepositions }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .voAndPrepositions }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .voAndPrepositions }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .ovAndPostpositions }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .voAndPrepositions }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .ovAndPostpositions }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .voAndPrepositions }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .voAndPrepositions }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .ovAndPostpositions }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .voAndPrepositions }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .voAndPostpositions }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .other }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .ovAndPostpositions }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .other }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .ovAndPostpositions }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .ovAndPostpositions }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .voAndPrepositions }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .ovAndPostpositions }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "kok", language := "Kokborok", iso := "trp", value := .ovAndPostpositions }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .voAndPrepositions }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .ovAndPostpositions }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .ovAndPostpositions }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .ovAndPostpositions }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .voAndPrepositions }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .ovAndPostpositions }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .voAndPostpositions }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .voAndPrepositions }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .other }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .ovAndPostpositions }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .ovAndPostpositions }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .voAndPostpositions }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .ovAndPostpositions }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .other }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .ovAndPostpositions }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .voAndPrepositions }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .voAndPostpositions }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .ovAndPostpositions }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .ovAndPostpositions }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .ovAndPostpositions }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .voAndPrepositions }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .ovAndPostpositions }
  , { walsCode := "kkq", language := "Kuikúro", iso := "kui", value := .ovAndPostpositions }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .ovAndPrepositions }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .ovAndPostpositions }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .ovAndPostpositions }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .ovAndPostpositions }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .ovAndPostpositions }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .voAndPrepositions }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .ovAndPrepositions }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .ovAndPostpositions }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .other }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .ovAndPostpositions }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .voAndPrepositions }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .voAndPrepositions }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .voAndPrepositions }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .ovAndPostpositions }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .ovAndPostpositions }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .ovAndPostpositions }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .ovAndPostpositions }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .ovAndPostpositions }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .ovAndPostpositions }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .voAndPrepositions }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .voAndPrepositions }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .voAndPrepositions }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .voAndPrepositions }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .ovAndPostpositions }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .voAndPrepositions }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .ovAndPostpositions }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .ovAndPostpositions }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .ovAndPostpositions }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .ovAndPostpositions }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .ovAndPostpositions }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .other }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .voAndPrepositions }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .ovAndPostpositions }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .voAndPrepositions }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .voAndPrepositions }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .voAndPrepositions }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .voAndPrepositions }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .ovAndPostpositions }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .voAndPrepositions }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .ovAndPostpositions }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .voAndPrepositions }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .other }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .voAndPrepositions }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .voAndPostpositions }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .voAndPrepositions }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .other }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .ovAndPostpositions }
  , { walsCode := "les", language := "Lese", iso := "les", value := .other }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .voAndPrepositions }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .voAndPrepositions }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .ovAndPostpositions }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .ovAndPostpositions }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .voAndPrepositions }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .other }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .voAndPrepositions }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .ovAndPostpositions }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .voAndPrepositions }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .other }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .voAndPostpositions }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .voAndPrepositions }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .voAndPrepositions }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .voAndPrepositions }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .ovAndPostpositions }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .voAndPrepositions }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .other }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .other }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .voAndPrepositions }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .ovAndPostpositions }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .voAndPrepositions }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .voAndPrepositions }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .voAndPrepositions }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .other }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .voAndPrepositions }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .ovAndPostpositions }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .voAndPrepositions }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .ovAndPostpositions }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .voAndPrepositions }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .voAndPrepositions }
  , { walsCode := "mgh", language := "Magahi", iso := "mag", value := .ovAndPostpositions }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .ovAndPostpositions }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .ovAndPostpositions }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .voAndPostpositions }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .ovAndPostpositions }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .ovAndPostpositions }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .voAndPostpositions }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .other }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .ovAndPostpositions }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .ovAndPostpositions }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .voAndPrepositions }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .voAndPrepositions }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .voAndPrepositions }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .voAndPrepositions }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .voAndPrepositions }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .voAndPrepositions }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .voAndPrepositions }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .ovAndPostpositions }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .ovAndPostpositions }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .ovAndPostpositions }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .other }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .ovAndPostpositions }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .voAndPrepositions }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .ovAndPrepositions }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .voAndPrepositions }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .ovAndPostpositions }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .ovAndPostpositions }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .ovAndPostpositions }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .voAndPrepositions }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .ovAndPostpositions }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .voAndPrepositions }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .other }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .other }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .ovAndPostpositions }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .ovAndPostpositions }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .voAndPrepositions }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .ovAndPostpositions }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .ovAndPostpositions }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .ovAndPostpositions }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .voAndPrepositions }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .ovAndPostpositions }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .ovAndPostpositions }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .voAndPrepositions }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .other }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .ovAndPostpositions }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .ovAndPostpositions }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .ovAndPostpositions }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .voAndPrepositions }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .ovAndPostpositions }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .voAndPrepositions }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .voAndPrepositions }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .other }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .other }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .other }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .voAndPrepositions }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .voAndPrepositions }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .voAndPrepositions }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .voAndPrepositions }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .ovAndPostpositions }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .ovAndPostpositions }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .ovAndPostpositions }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .ovAndPostpositions }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .other }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .ovAndPostpositions }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .voAndPrepositions }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .ovAndPostpositions }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .ovAndPostpositions }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .voAndPrepositions }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .other }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .ovAndPostpositions }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .ovAndPostpositions }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .ovAndPostpositions }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .other }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .other }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .voAndPrepositions }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .voAndPrepositions }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .voAndPrepositions }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .voAndPrepositions }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .voAndPrepositions }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .voAndPrepositions }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .ovAndPostpositions }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .voAndPrepositions }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .voAndPrepositions }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .other }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .voAndPrepositions }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .ovAndPostpositions }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .ovAndPostpositions }
  , { walsCode := "mqf", language := "Momuna", iso := "mqf", value := .ovAndPostpositions }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .voAndPrepositions }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .voAndPrepositions }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .voAndPrepositions }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .ovAndPostpositions }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .other }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .ovAndPostpositions }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .other }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .voAndPrepositions }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .ovAndPostpositions }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .voAndPostpositions }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .other }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .other }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .ovAndPostpositions }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .voAndPrepositions }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .voAndPrepositions }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .voAndPrepositions }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .voAndPrepositions }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .voAndPrepositions }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .ovAndPostpositions }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .ovAndPostpositions }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .voAndPrepositions }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .other }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .other }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .other }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .voAndPrepositions }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .voAndPrepositions }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .voAndPrepositions }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .voAndPrepositions }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .ovAndPostpositions }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .ovAndPostpositions }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .ovAndPostpositions }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .ovAndPostpositions }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .voAndPrepositions }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .voAndPrepositions }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .voAndPrepositions }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .voAndPrepositions }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .voAndPrepositions }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .ovAndPostpositions }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .ovAndPostpositions }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .voAndPrepositions }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .voAndPrepositions }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .ovAndPostpositions }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .ovAndPostpositions }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .ovAndPostpositions }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .ovAndPostpositions }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .ovAndPostpositions }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .ovAndPostpositions }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .other }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .ovAndPostpositions }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .voAndPrepositions }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .voAndPrepositions }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .voAndPrepositions }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .voAndPrepositions }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .voAndPrepositions }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .ovAndPostpositions }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .ovAndPostpositions }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .ovAndPrepositions }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .ovAndPostpositions }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .ovAndPostpositions }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .ovAndPostpositions }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .ovAndPostpositions }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .other }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .other }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .ovAndPostpositions }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .voAndPrepositions }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .other }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .voAndPrepositions }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .ovAndPostpositions }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .other }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .voAndPrepositions }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .voAndPrepositions }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .other }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .voAndPrepositions }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .voAndPrepositions }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .voAndPrepositions }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .ovAndPostpositions }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .other }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .voAndPrepositions }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .voAndPrepositions }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .voAndPrepositions }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .voAndPrepositions }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .voAndPrepositions }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .ovAndPostpositions }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .voAndPostpositions }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .voAndPrepositions }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .ovAndPostpositions }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .other }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .voAndPrepositions }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .voAndPrepositions }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .voAndPrepositions }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .voAndPrepositions }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .ovAndPostpositions }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .other }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .voAndPrepositions }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .other }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .ovAndPostpositions }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .voAndPrepositions }
  , { walsCode := "nyr", language := "Nyangumarda", iso := "nna", value := .other }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .ovAndPostpositions }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .ovAndPostpositions }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .other }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .voAndPrepositions }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .other }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .voAndPrepositions }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .voAndPrepositions }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .voAndPrepositions }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .ovAndPostpositions }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .voAndPrepositions }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .ovAndPostpositions }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .ovAndPostpositions }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .ovAndPostpositions }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .ovAndPostpositions }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .ovAndPostpositions }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .ovAndPostpositions }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .ovAndPostpositions }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .voAndPrepositions }
  , { walsCode := "owi", language := "Owininga", iso := "owi", value := .ovAndPostpositions }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .voAndPrepositions }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .voAndPrepositions }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .other }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .voAndPrepositions }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .voAndPrepositions }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .voAndPrepositions }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .voAndPrepositions }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .other }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .voAndPrepositions }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .voAndPrepositions }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .ovAndPostpositions }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .other }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .voAndPrepositions }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .ovAndPostpositions }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .voAndPrepositions }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .voAndPrepositions }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .ovAndPostpositions }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .ovAndPostpositions }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .voAndPrepositions }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .other }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .ovAndPostpositions }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .voAndPrepositions }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .ovAndPrepositions }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .voAndPrepositions }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .ovAndPostpositions }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .ovAndPostpositions }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .ovAndPostpositions }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .other }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .voAndPrepositions }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .voAndPrepositions }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .voAndPrepositions }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .other }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .voAndPrepositions }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .voAndPrepositions }
  , { walsCode := "pmn", language := "Pomo (Northern)", iso := "pej", value := .ovAndPostpositions }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .ovAndPostpositions }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .voAndPrepositions }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .voAndPrepositions }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .voAndPrepositions }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .ovAndPostpositions }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .voAndPrepositions }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .ovAndPostpositions }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .ovAndPostpositions }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .other }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .ovAndPostpositions }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .ovAndPrepositions }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .ovAndPostpositions }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .ovAndPostpositions }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .ovAndPostpositions }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .ovAndPostpositions }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .voAndPrepositions }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .ovAndPostpositions }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .voAndPrepositions }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .ovAndPostpositions }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .ovAndPostpositions }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .ovAndPostpositions }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .ovAndPostpositions }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .ovAndPostpositions }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .other }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .voAndPrepositions }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .voAndPrepositions }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .voAndPrepositions }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .voAndPrepositions }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .voAndPrepositions }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .ovAndPostpositions }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .ovAndPostpositions }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .voAndPrepositions }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .voAndPrepositions }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .ovAndPostpositions }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .voAndPostpositions }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .voAndPrepositions }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .voAndPrepositions }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .ovAndPostpositions }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .voAndPrepositions }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .ovAndPostpositions }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .voAndPostpositions }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .voAndPrepositions }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .ovAndPostpositions }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .voAndPrepositions }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .ovAndPostpositions }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .ovAndPostpositions }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .ovAndPostpositions }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .ovAndPostpositions }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .ovAndPostpositions }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .ovAndPostpositions }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .ovAndPostpositions }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .voAndPrepositions }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .voAndPrepositions }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .ovAndPostpositions }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .ovAndPostpositions }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .ovAndPostpositions }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .voAndPrepositions }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .ovAndPostpositions }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .other }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .voAndPrepositions }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .ovAndPostpositions }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .voAndPrepositions }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .ovAndPostpositions }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .voAndPrepositions }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .ovAndPostpositions }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .ovAndPostpositions }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .ovAndPostpositions }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .ovAndPostpositions }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .voAndPrepositions }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .ovAndPostpositions }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .ovAndPostpositions }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .ovAndPostpositions }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .voAndPrepositions }
  , { walsCode := "ryu", language := "Shuri", iso := "ryu", value := .ovAndPostpositions }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .voAndPrepositions }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .voAndPrepositions }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .ovAndPostpositions }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .ovAndPostpositions }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .voAndPrepositions }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .ovAndPostpositions }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .ovAndPostpositions }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .voAndPrepositions }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .voAndPrepositions }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .ovAndPostpositions }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .ovAndPostpositions }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .voAndPrepositions }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .ovAndPostpositions }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .ovAndPostpositions }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .voAndPrepositions }
  , { walsCode := "so", language := "So", iso := "teu", value := .voAndPrepositions }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .voAndPrepositions }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .other }
  , { walsCode := "som", language := "Somali", iso := "som", value := .other }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .voAndPrepositions }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .ovAndPrepositions }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .voAndPrepositions }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .ovAndPostpositions }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .voAndPrepositions }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .voAndPrepositions }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .voAndPrepositions }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .voAndPrepositions }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .ovAndPostpositions }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .voAndPrepositions }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .voAndPrepositions }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .ovAndPostpositions }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .ovAndPostpositions }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .voAndPrepositions }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .voAndPrepositions }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .voAndPrepositions }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .ovAndPostpositions }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .voAndPrepositions }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .ovAndPostpositions }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .voAndPrepositions }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .ovAndPrepositions }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .ovAndPostpositions }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .ovAndPostpositions }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .voAndPrepositions }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .ovAndPostpositions }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .ovAndPostpositions }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .voAndPrepositions }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .ovAndPostpositions }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .ovAndPostpositions }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .ovAndPrepositions }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .ovAndPostpositions }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .other }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .ovAndPostpositions }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .ovAndPostpositions }
  , { walsCode := "tsr", language := "Taushiro", iso := "trr", value := .voAndPostpositions }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .voAndPrepositions }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .ovAndPostpositions }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .other }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .voAndPrepositions }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .ovAndPostpositions }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .ovAndPostpositions }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .voAndPrepositions }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .voAndPrepositions }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .other }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .ovAndPostpositions }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .voAndPrepositions }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .voAndPrepositions }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .voAndPrepositions }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .voAndPostpositions }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .voAndPostpositions }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .voAndPrepositions }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .ovAndPostpositions }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .voAndPrepositions }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .voAndPrepositions }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .voAndPrepositions }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .voAndPrepositions }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .voAndPrepositions }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .ovAndPostpositions }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .voAndPrepositions }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .ovAndPostpositions }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .ovAndPostpositions }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .other }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .voAndPrepositions }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .voAndPrepositions }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .ovAndPrepositions }
  ]

private def allData_2 : List Datapoint :=
  [ { walsCode := "tgr", language := "Tigré", iso := "tig", value := .ovAndPrepositions }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .ovAndPostpositions }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .other }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .voAndPrepositions }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .voAndPrepositions }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .ovAndPostpositions }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .voAndPostpositions }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .voAndPrepositions }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .other }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .voAndPrepositions }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .voAndPrepositions }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .ovAndPostpositions }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .ovAndPostpositions }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .ovAndPrepositions }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .voAndPrepositions }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .voAndPrepositions }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .voAndPrepositions }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .voAndPrepositions }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .ovAndPostpositions }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .ovAndPostpositions }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .voAndPrepositions }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .voAndPrepositions }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .other }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .ovAndPostpositions }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .ovAndPostpositions }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .ovAndPostpositions }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .voAndPrepositions }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .ovAndPostpositions }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .voAndPrepositions }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .voAndPrepositions }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .ovAndPostpositions }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .ovAndPostpositions }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .voAndPrepositions }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .ovAndPostpositions }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .other }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .voAndPrepositions }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .ovAndPostpositions }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .voAndPrepositions }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .voAndPrepositions }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .ovAndPostpositions }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .ovAndPostpositions }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .other }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .ovAndPostpositions }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .ovAndPostpositions }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .ovAndPrepositions }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .ovAndPostpositions }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .ovAndPostpositions }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .voAndPrepositions }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .voAndPrepositions }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .other }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .ovAndPostpositions }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .ovAndPostpositions }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .ovAndPostpositions }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .voAndPrepositions }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .voAndPrepositions }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .voAndPrepositions }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .ovAndPostpositions }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .ovAndPostpositions }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .voAndPrepositions }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .ovAndPostpositions }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .ovAndPostpositions }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .ovAndPostpositions }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .ovAndPostpositions }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .ovAndPostpositions }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .other }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .ovAndPostpositions }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .voAndPrepositions }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .voAndPrepositions }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .other }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .ovAndPostpositions }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .ovAndPostpositions }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .other }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .voAndPostpositions }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .ovAndPostpositions }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .ovAndPostpositions }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .ovAndPostpositions }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .other }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .ovAndPostpositions }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .ovAndPostpositions }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .voAndPostpositions }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .other }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .voAndPrepositions }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .voAndPrepositions }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .voAndPrepositions }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .other }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .other }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .other }
  , { walsCode := "was", language := "Washo", iso := "was", value := .ovAndPostpositions }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .ovAndPostpositions }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .ovAndPostpositions }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .ovAndPostpositions }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .other }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .voAndPrepositions }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .other }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .voAndPrepositions }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .voAndPrepositions }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .other }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .other }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .other }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .other }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .voAndPrepositions }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .voAndPrepositions }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .voAndPrepositions }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .ovAndPostpositions }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .voAndPrepositions }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .voAndPrepositions }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .ovAndPostpositions }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .voAndPostpositions }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .ovAndPostpositions }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .ovAndPostpositions }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .ovAndPostpositions }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .voAndPrepositions }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .ovAndPostpositions }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .ovAndPostpositions }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .ovAndPostpositions }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .other }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .ovAndPostpositions }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .ovAndPostpositions }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .ovAndPostpositions }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .ovAndPostpositions }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .other }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .voAndPrepositions }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .voAndPrepositions }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .ovAndPostpositions }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .voAndPostpositions }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .ovAndPostpositions }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .ovAndPostpositions }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .voAndPrepositions }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .other }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .other }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .voAndPrepositions }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .voAndPrepositions }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .voAndPrepositions }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .voAndPrepositions }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .other }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .ovAndPostpositions }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .voAndPrepositions }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .voAndPostpositions }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .voAndPrepositions }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .ovAndPostpositions }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .ovAndPostpositions }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .ovAndPostpositions }
  ]

/-- Complete WALS 95A dataset (1142 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1142 := by native_decide

theorem count_ovAndPostpositions :
    (allData.filter (·.value == .ovAndPostpositions)).length = 472 := by native_decide
theorem count_ovAndPrepositions :
    (allData.filter (·.value == .ovAndPrepositions)).length = 14 := by native_decide
theorem count_voAndPostpositions :
    (allData.filter (·.value == .voAndPostpositions)).length = 42 := by native_decide
theorem count_voAndPrepositions :
    (allData.filter (·.value == .voAndPrepositions)).length = 456 := by native_decide
theorem count_other :
    (allData.filter (·.value == .other)).length = 158 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F95A
