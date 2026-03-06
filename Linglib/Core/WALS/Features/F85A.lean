/-!
# WALS Feature 85A: Order of Adposition and Noun Phrase
@cite{dryer-2013a}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 85A`.

Chapter 85, 1184 languages.
-/

namespace Core.WALS.F85A

/-- WALS 85A values. -/
inductive AdpositionNPOrder where
  | postpositions  -- Postpositions (577 languages)
  | prepositions  -- Prepositions (511 languages)
  | inpositions  -- Inpositions (8 languages)
  | noDominantOrder  -- No dominant order (58 languages)
  | noAdpositions  -- No adpositions (30 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 85A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : AdpositionNPOrder
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .noDominantOrder }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .postpositions }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .postpositions }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .prepositions }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .postpositions }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .noAdpositions }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .prepositions }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .prepositions }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .postpositions }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .postpositions }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .prepositions }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .prepositions }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .postpositions }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .postpositions }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .postpositions }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .postpositions }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .postpositions }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .prepositions }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .prepositions }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .postpositions }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .prepositions }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .postpositions }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noDominantOrder }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .postpositions }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .noDominantOrder }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .postpositions }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .prepositions }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .prepositions }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .prepositions }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .prepositions }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .postpositions }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .postpositions }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .prepositions }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .postpositions }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .prepositions }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .prepositions }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .postpositions }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .postpositions }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .postpositions }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noDominantOrder }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .prepositions }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .postpositions }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .prepositions }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .postpositions }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .prepositions }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .postpositions }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .inpositions }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .prepositions }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .prepositions }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .postpositions }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .postpositions }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .postpositions }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .postpositions }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .postpositions }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .prepositions }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .prepositions }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .prepositions }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .prepositions }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .prepositions }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .prepositions }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .prepositions }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .postpositions }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .prepositions }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .postpositions }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .postpositions }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .postpositions }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .prepositions }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .prepositions }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .postpositions }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .postpositions }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noAdpositions }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .postpositions }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .postpositions }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .prepositions }
  , { walsCode := "au", language := "Au", iso := "avt", value := .prepositions }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .postpositions }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .postpositions }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .postpositions }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .postpositions }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .prepositions }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .postpositions }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .prepositions }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .prepositions }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .postpositions }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .prepositions }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .prepositions }
  , { walsCode := "bgs", language := "Baga Sitemu", iso := "bsp", value := .postpositions }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .prepositions }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .noDominantOrder }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .noDominantOrder }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .prepositions }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .prepositions }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .prepositions }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .prepositions }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .prepositions }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .postpositions }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .postpositions }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .prepositions }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .prepositions }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .postpositions }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .postpositions }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .postpositions }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .prepositions }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .postpositions }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .prepositions }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .postpositions }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .postpositions }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .prepositions }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .postpositions }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .postpositions }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .prepositions }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .prepositions }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .postpositions }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .postpositions }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .postpositions }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .prepositions }
  , { walsCode := "blu", language := "Bena-Lulua", iso := "lua", value := .prepositions }
  , { walsCode := "bga", language := "Benga", iso := "bng", value := .prepositions }
  , { walsCode := "brq", language := "Bera", iso := "brf", value := .prepositions }
  , { walsCode := "bse", language := "Berber (Ayt Seghrouchen Middle Atlas)", iso := "rif", value := .prepositions }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .prepositions }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .prepositions }
  , { walsCode := "bmz", language := "Berber (Mzab)", iso := "mzb", value := .prepositions }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .prepositions }
  , { walsCode := "bsi", language := "Berber (Siwa)", iso := "siz", value := .prepositions }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .postpositions }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .postpositions }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .postpositions }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .postpositions }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .prepositions }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .prepositions }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .prepositions }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .postpositions }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .postpositions }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .postpositions }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .noDominantOrder }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .postpositions }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .prepositions }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .noDominantOrder }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .prepositions }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .noAdpositions }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .postpositions }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .prepositions }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .postpositions }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .postpositions }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .prepositions }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .prepositions }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .postpositions }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .prepositions }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .postpositions }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .postpositions }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .prepositions }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .prepositions }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .postpositions }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .prepositions }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .prepositions }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .prepositions }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .prepositions }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .noAdpositions }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .inpositions }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .postpositions }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .postpositions }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .postpositions }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .prepositions }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .noDominantOrder }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .postpositions }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .postpositions }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .prepositions }
  , { walsCode := "dok", language := "Bwele", iso := "ngc", value := .prepositions }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .postpositions }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .postpositions }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .prepositions }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noAdpositions }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .postpositions }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .postpositions }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .postpositions }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noDominantOrder }
  , { walsCode := "car", language := "Carib", iso := "car", value := .postpositions }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .postpositions }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .postpositions }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .prepositions }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .postpositions }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .postpositions }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .prepositions }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .prepositions }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .noDominantOrder }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .postpositions }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .prepositions }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .prepositions }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .postpositions }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .postpositions }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .prepositions }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .prepositions }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .postpositions }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .postpositions }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .postpositions }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .prepositions }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .postpositions }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .postpositions }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .postpositions }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .postpositions }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .prepositions }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .prepositions }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .prepositions }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .prepositions }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .prepositions }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .postpositions }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .prepositions }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .postpositions }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .postpositions }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .postpositions }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .prepositions }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .prepositions }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .prepositions }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .postpositions }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .prepositions }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .postpositions }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .postpositions }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .postpositions }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .prepositions }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .postpositions }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .prepositions }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .postpositions }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .prepositions }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .postpositions }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .prepositions }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noAdpositions }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .postpositions }
  , { walsCode := "cuc", language := "Cuica", iso := "", value := .prepositions }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .postpositions }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .prepositions }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .prepositions }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .postpositions }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .postpositions }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .postpositions }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .postpositions }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .postpositions }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .postpositions }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .prepositions }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .postpositions }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .postpositions }
  , { walsCode := "des", language := "Desano", iso := "des", value := .postpositions }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .noAdpositions }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .postpositions }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .prepositions }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .postpositions }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .postpositions }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .postpositions }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .postpositions }
  , { walsCode := "dng", language := "Ding", iso := "diz", value := .prepositions }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noDominantOrder }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .prepositions }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .postpositions }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .postpositions }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .postpositions }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .postpositions }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .prepositions }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .prepositions }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .postpositions }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .noDominantOrder }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .prepositions }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .prepositions }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .postpositions }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .postpositions }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .postpositions }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .prepositions }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noAdpositions }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .postpositions }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .postpositions }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .prepositions }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .postpositions }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .prepositions }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .postpositions }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .postpositions }
  , { walsCode := "ene", language := "Enets", iso := "", value := .postpositions }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .prepositions }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .prepositions }
  , { walsCode := "eng", language := "English", iso := "eng", value := .prepositions }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .postpositions }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .prepositions }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .postpositions }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .prepositions }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .postpositions }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .postpositions }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .postpositions }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .postpositions }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .postpositions }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .prepositions }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .postpositions }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .prepositions }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .postpositions }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .postpositions }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .noDominantOrder }
  , { walsCode := "for", language := "Fore", iso := "for", value := .postpositions }
  , { walsCode := "fre", language := "French", iso := "fra", value := .prepositions }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .prepositions }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .prepositions }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .postpositions }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .postpositions }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .prepositions }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .prepositions }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .prepositions }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .postpositions }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .prepositions }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .postpositions }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .postpositions }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .postpositions }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .prepositions }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .prepositions }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .postpositions }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .prepositions }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .prepositions }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .prepositions }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .postpositions }
  , { walsCode := "ger", language := "German", iso := "deu", value := .prepositions }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .postpositions }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .prepositions }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .prepositions }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .prepositions }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .prepositions }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .prepositions }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .postpositions }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .postpositions }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .inpositions }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .postpositions }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .postpositions }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .prepositions }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .postpositions }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .postpositions }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .postpositions }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .postpositions }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .postpositions }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .prepositions }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .prepositions }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .postpositions }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .noDominantOrder }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .postpositions }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .prepositions }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .prepositions }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .noDominantOrder }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .postpositions }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .postpositions }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noDominantOrder }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .prepositions }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .postpositions }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .prepositions }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .postpositions }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .prepositions }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .prepositions }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .postpositions }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .postpositions }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .postpositions }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .prepositions }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .prepositions }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .prepositions }
  , { walsCode := "hwr", language := "Hawrami", iso := "hac", value := .prepositions }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .prepositions }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .postpositions }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .prepositions }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .prepositions }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .prepositions }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .prepositions }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .prepositions }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .postpositions }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .prepositions }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .postpositions }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .postpositions }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .prepositions }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .postpositions }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .prepositions }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .postpositions }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .prepositions }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .postpositions }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .postpositions }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .postpositions }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .prepositions }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .prepositions }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .postpositions }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .postpositions }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .postpositions }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .postpositions }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .postpositions }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .noDominantOrder }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .prepositions }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .postpositions }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .prepositions }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .prepositions }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .postpositions }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .postpositions }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .prepositions }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .prepositions }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .prepositions }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .prepositions }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .prepositions }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .postpositions }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .prepositions }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .prepositions }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .postpositions }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .postpositions }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .prepositions }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .prepositions }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .postpositions }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .postpositions }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .postpositions }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .prepositions }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .prepositions }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .prepositions }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .prepositions }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noAdpositions }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .noDominantOrder }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .prepositions }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .prepositions }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .prepositions }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .prepositions }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .postpositions }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .noDominantOrder }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .prepositions }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .postpositions }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .postpositions }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .postpositions }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .postpositions }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .postpositions }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .postpositions }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .postpositions }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .prepositions }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .prepositions }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .postpositions }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .postpositions }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .postpositions }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .prepositions }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .prepositions }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .postpositions }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .prepositions }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .noAdpositions }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .prepositions }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .postpositions }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .noDominantOrder }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .postpositions }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .postpositions }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .postpositions }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .postpositions }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .postpositions }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .postpositions }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .prepositions }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .postpositions }
  , { walsCode := "kmi", language := "Kami", iso := "kcu", value := .prepositions }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .postpositions }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .prepositions }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .prepositions }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .postpositions }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .postpositions }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .postpositions }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .postpositions }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .prepositions }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .prepositions }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .prepositions }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .postpositions }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .postpositions }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .postpositions }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .postpositions }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .prepositions }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .prepositions }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .prepositions }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .prepositions }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .postpositions }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .postpositions }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .postpositions }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .postpositions }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .postpositions }
  , { walsCode := "ktu", language := "Katu", iso := "", value := .prepositions }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .prepositions }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .postpositions }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .postpositions }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noDominantOrder }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noAdpositions }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .prepositions }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .postpositions }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .noDominantOrder }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .prepositions }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .postpositions }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .postpositions }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .prepositions }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .postpositions }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .postpositions }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .postpositions }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .postpositions }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .postpositions }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .postpositions }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .postpositions }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .postpositions }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .prepositions }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .prepositions }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .prepositions }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .postpositions }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .prepositions }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .prepositions }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .noAdpositions }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .prepositions }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .postpositions }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .prepositions }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .postpositions }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .prepositions }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noAdpositions }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .prepositions }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .postpositions }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .postpositions }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .prepositions }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .postpositions }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .prepositions }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .postpositions }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .postpositions }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .postpositions }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .postpositions }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .prepositions }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .postpositions }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .postpositions }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .prepositions }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .postpositions }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .postpositions }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .postpositions }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .prepositions }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .postpositions }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .postpositions }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .prepositions }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .noDominantOrder }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .postpositions }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .postpositions }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .postpositions }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .postpositions }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noDominantOrder }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .postpositions }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .prepositions }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .postpositions }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .postpositions }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .postpositions }
  , { walsCode := "kpo", language := "Kposo", iso := "kpo", value := .postpositions }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .postpositions }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .prepositions }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .postpositions }
  , { walsCode := "kkq", language := "Kuikúro", iso := "kui", value := .postpositions }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .prepositions }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .postpositions }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .postpositions }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .postpositions }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .postpositions }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .prepositions }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .prepositions }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .postpositions }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noAdpositions }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .inpositions }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .postpositions }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .prepositions }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .prepositions }
  , { walsCode := "kwm", language := "Kwami", iso := "ksq", value := .prepositions }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .prepositions }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noAdpositions }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .postpositions }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .postpositions }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .postpositions }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .postpositions }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .postpositions }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .postpositions }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .prepositions }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .prepositions }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .prepositions }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .prepositions }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .postpositions }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .prepositions }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .postpositions }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .postpositions }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .postpositions }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .postpositions }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .postpositions }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noDominantOrder }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .prepositions }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .postpositions }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .prepositions }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .prepositions }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .prepositions }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .prepositions }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .prepositions }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .postpositions }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .prepositions }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .postpositions }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .prepositions }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .prepositions }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .postpositions }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .prepositions }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .postpositions }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .postpositions }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .prepositions }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .prepositions }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .postpositions }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .postpositions }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .prepositions }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .prepositions }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .postpositions }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .prepositions }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .postpositions }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .postpositions }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .prepositions }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .prepositions }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .prepositions }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .postpositions }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .prepositions }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .prepositions }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .postpositions }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .postpositions }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .prepositions }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .postpositions }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .prepositions }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .prepositions }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .prepositions }
  , { walsCode := "jlu", language := "Luwo", iso := "lwo", value := .prepositions }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .postpositions }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .prepositions }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .postpositions }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .prepositions }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .postpositions }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .prepositions }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .prepositions }
  , { walsCode := "mgh", language := "Magahi", iso := "mag", value := .postpositions }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .postpositions }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .postpositions }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .postpositions }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .postpositions }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .postpositions }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .postpositions }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noDominantOrder }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .postpositions }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .postpositions }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .prepositions }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .prepositions }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .prepositions }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .prepositions }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .prepositions }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .prepositions }
  , { walsCode := "mmi", language := "Mambai", iso := "mcs", value := .prepositions }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .prepositions }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .postpositions }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .postpositions }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .postpositions }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noDominantOrder }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .postpositions }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .prepositions }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .prepositions }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .prepositions }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .postpositions }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .postpositions }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .postpositions }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .prepositions }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .postpositions }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .prepositions }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noDominantOrder }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .prepositions }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .postpositions }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .postpositions }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .prepositions }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .postpositions }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .postpositions }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .postpositions }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .prepositions }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .postpositions }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noAdpositions }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .postpositions }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .prepositions }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .prepositions }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .postpositions }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .postpositions }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .postpositions }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .prepositions }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .postpositions }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .prepositions }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .prepositions }
  , { walsCode := "mzn", language := "Mazanderani", iso := "mzn", value := .postpositions }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .prepositions }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .noDominantOrder }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .noDominantOrder }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .prepositions }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .prepositions }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .prepositions }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .prepositions }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .postpositions }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .postpositions }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .postpositions }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .postpositions }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .noAdpositions }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .postpositions }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .prepositions }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .postpositions }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .noAdpositions }
  , { walsCode := "mig", language := "Migama", iso := "mmy", value := .prepositions }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .postpositions }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .prepositions }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .prepositions }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .postpositions }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .postpositions }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .postpositions }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .prepositions }
  , { walsCode := "mxa", language := "Mixtec (Atatlahuca)", iso := "mib", value := .prepositions }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .prepositions }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .prepositions }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .prepositions }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .prepositions }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .prepositions }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .prepositions }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .postpositions }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .prepositions }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .postpositions }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .prepositions }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .prepositions }
  , { walsCode := "mko", language := "Mokilko", iso := "moz", value := .prepositions }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .postpositions }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .postpositions }
  , { walsCode := "mqf", language := "Momuna", iso := "mqf", value := .postpositions }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .prepositions }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .prepositions }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .prepositions }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .postpositions }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noDominantOrder }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .postpositions }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .noDominantOrder }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .prepositions }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .postpositions }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .postpositions }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .noDominantOrder }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .postpositions }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .postpositions }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .prepositions }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .prepositions }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .prepositions }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .prepositions }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .prepositions }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .postpositions }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .postpositions }
  , { walsCode := "mnz", language := "Munzombo", iso := "moj", value := .prepositions }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .prepositions }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noDominantOrder }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noDominantOrder }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .prepositions }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .prepositions }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .prepositions }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .prepositions }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .noAdpositions }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .postpositions }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .postpositions }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .postpositions }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .postpositions }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .prepositions }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .prepositions }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .prepositions }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .prepositions }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .prepositions }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .postpositions }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .postpositions }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .prepositions }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .prepositions }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .prepositions }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .postpositions }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .postpositions }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .postpositions }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .postpositions }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .postpositions }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .postpositions }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .noDominantOrder }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .postpositions }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .prepositions }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .prepositions }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .prepositions }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .prepositions }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .prepositions }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .postpositions }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .postpositions }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .prepositions }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .postpositions }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .postpositions }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .postpositions }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .postpositions }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .postpositions }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .prepositions }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noAdpositions }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .prepositions }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .postpositions }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .postpositions }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .prepositions }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .prepositions }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .postpositions }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noAdpositions }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .prepositions }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .prepositions }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .prepositions }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .postpositions }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .prepositions }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .prepositions }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .prepositions }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .prepositions }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .prepositions }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .postpositions }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .postpositions }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .prepositions }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .postpositions }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .noDominantOrder }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .prepositions }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .prepositions }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .prepositions }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .prepositions }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .postpositions }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .prepositions }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .prepositions }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noAdpositions }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .postpositions }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .prepositions }
  , { walsCode := "nyr", language := "Nyangumarda", iso := "nna", value := .noDominantOrder }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .postpositions }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .postpositions }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .inpositions }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .prepositions }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noDominantOrder }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .prepositions }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .prepositions }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .prepositions }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noAdpositions }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .postpositions }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .prepositions }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noAdpositions }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .postpositions }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .postpositions }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .postpositions }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .postpositions }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .postpositions }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .postpositions }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .postpositions }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .prepositions }
  , { walsCode := "owi", language := "Owininga", iso := "owi", value := .postpositions }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .prepositions }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .prepositions }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .noDominantOrder }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .prepositions }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .prepositions }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .prepositions }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .prepositions }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .postpositions }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .prepositions }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .prepositions }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .postpositions }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .prepositions }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .postpositions }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .prepositions }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .prepositions }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .postpositions }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .postpositions }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .prepositions }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .postpositions }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .postpositions }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .prepositions }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .prepositions }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .noAdpositions }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .prepositions }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .postpositions }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .postpositions }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .postpositions }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .prepositions }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .prepositions }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .prepositions }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .noDominantOrder }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .prepositions }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .prepositions }
  , { walsCode := "pmn", language := "Pomo (Northern)", iso := "pej", value := .postpositions }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .postpositions }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .prepositions }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .prepositions }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .prepositions }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .postpositions }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .prepositions }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .postpositions }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .postpositions }
  , { walsCode := "puq", language := "Puquina", iso := "puq", value := .postpositions }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .postpositions }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noDominantOrder }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .postpositions }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .prepositions }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .postpositions }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .postpositions }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .postpositions }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .postpositions }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .postpositions }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .prepositions }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .postpositions }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .prepositions }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .postpositions }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .postpositions }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .postpositions }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .postpositions }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .postpositions }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .prepositions }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .prepositions }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .prepositions }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .prepositions }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .prepositions }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .postpositions }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .postpositions }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .prepositions }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .prepositions }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .postpositions }
  , { walsCode := "saa", language := "Sa'a", iso := "apb", value := .prepositions }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .postpositions }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .prepositions }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .prepositions }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .postpositions }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .prepositions }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .postpositions }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .postpositions }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .prepositions }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .postpositions }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .prepositions }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .postpositions }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .postpositions }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .postpositions }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .postpositions }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .postpositions }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .postpositions }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .postpositions }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .prepositions }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .prepositions }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .postpositions }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .postpositions }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .postpositions }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .postpositions }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .prepositions }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .postpositions }
  , { walsCode := "sen", language := "Sena", iso := "seh", value := .prepositions }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .prepositions }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .postpositions }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .prepositions }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .postpositions }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .prepositions }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .postpositions }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .postpositions }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .postpositions }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .postpositions }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .prepositions }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .postpositions }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .postpositions }
  , { walsCode := "shy", language := "Shira Yughur", iso := "yuy", value := .postpositions }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .postpositions }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .prepositions }
  , { walsCode := "ryu", language := "Shuri", iso := "ryu", value := .postpositions }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .prepositions }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .prepositions }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .postpositions }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .postpositions }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .prepositions }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .postpositions }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .postpositions }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .prepositions }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .prepositions }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .postpositions }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .postpositions }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .prepositions }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noAdpositions }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .postpositions }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .postpositions }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .prepositions }
  , { walsCode := "so", language := "So", iso := "teu", value := .prepositions }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .prepositions }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .noDominantOrder }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noDominantOrder }
  , { walsCode := "sge", language := "Songe", iso := "sop", value := .prepositions }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .prepositions }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .postpositions }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .prepositions }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .prepositions }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .postpositions }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .prepositions }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .prepositions }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .prepositions }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .prepositions }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .postpositions }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .prepositions }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .prepositions }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .postpositions }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .postpositions }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .prepositions }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .prepositions }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .postpositions }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .prepositions }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .postpositions }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .prepositions }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .postpositions }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .prepositions }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .prepositions }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .postpositions }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .postpositions }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .prepositions }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .postpositions }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .postpositions }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .prepositions }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .postpositions }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .postpositions }
  , { walsCode := "tbx", language := "Tangbe", iso := "skj", value := .postpositions }
  ]

private def allData_2 : List Datapoint :=
  [ { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .prepositions }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .postpositions }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .noDominantOrder }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .postpositions }
  , { walsCode := "tsm", language := "Tasmanian", iso := "", value := .postpositions }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .postpositions }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .postpositions }
  , { walsCode := "tsr", language := "Taushiro", iso := "trr", value := .postpositions }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .prepositions }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .postpositions }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .noDominantOrder }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .prepositions }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .postpositions }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .postpositions }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .prepositions }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .prepositions }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .noDominantOrder }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .postpositions }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .prepositions }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .prepositions }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .prepositions }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .postpositions }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .postpositions }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .prepositions }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .postpositions }
  , { walsCode := "trt", language := "Ternate", iso := "tft", value := .prepositions }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .prepositions }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .prepositions }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .prepositions }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .prepositions }
  , { walsCode := "thd", language := "Thadou", iso := "tcz", value := .postpositions }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .prepositions }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .postpositions }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .prepositions }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .postpositions }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .postpositions }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .prepositions }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .prepositions }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .prepositions }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .prepositions }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .postpositions }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .prepositions }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .prepositions }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .postpositions }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .postpositions }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .prepositions }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .prepositions }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .prepositions }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .postpositions }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .postpositions }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .prepositions }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .prepositions }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .prepositions }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .prepositions }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .prepositions }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .postpositions }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .postpositions }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .prepositions }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .prepositions }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .postpositions }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .postpositions }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .postpositions }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .postpositions }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .prepositions }
  , { walsCode := "tgo", language := "Tsogo", iso := "tsv", value := .prepositions }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .postpositions }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .prepositions }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .prepositions }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .postpositions }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .postpositions }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .prepositions }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .postpositions }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .noDominantOrder }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .prepositions }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .postpositions }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .prepositions }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .prepositions }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .postpositions }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .postpositions }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .postpositions }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .postpositions }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .prepositions }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .postpositions }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .postpositions }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .prepositions }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .prepositions }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .inpositions }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .postpositions }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .postpositions }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .postpositions }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .prepositions }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .prepositions }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .prepositions }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .postpositions }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .postpositions }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .prepositions }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .postpositions }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .postpositions }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .postpositions }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .postpositions }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .postpositions }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .noDominantOrder }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .postpositions }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .prepositions }
  , { walsCode := "vif", language := "Vili", iso := "vif", value := .prepositions }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .prepositions }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .noDominantOrder }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .postpositions }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .postpositions }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .noDominantOrder }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .postpositions }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .postpositions }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .postpositions }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .postpositions }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .postpositions }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .postpositions }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .postpositions }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .postpositions }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .prepositions }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .prepositions }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .prepositions }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .inpositions }
  , { walsCode := "was", language := "Washo", iso := "was", value := .postpositions }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .postpositions }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .postpositions }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .postpositions }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .postpositions }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .noDominantOrder }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .prepositions }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .noDominantOrder }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .prepositions }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noAdpositions }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .prepositions }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .postpositions }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noDominantOrder }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .noDominantOrder }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .prepositions }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .prepositions }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .prepositions }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .postpositions }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .postpositions }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .postpositions }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .prepositions }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .prepositions }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .postpositions }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .postpositions }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .postpositions }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .postpositions }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .postpositions }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .prepositions }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .postpositions }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .postpositions }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .postpositions }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .inpositions }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .postpositions }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .postpositions }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .postpositions }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .postpositions }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noAdpositions }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .postpositions }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .noDominantOrder }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .prepositions }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .prepositions }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .postpositions }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .postpositions }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .postpositions }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .postpositions }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .prepositions }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noDominantOrder }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .noAdpositions }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .prepositions }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .prepositions }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .prepositions }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .prepositions }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .postpositions }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .postpositions }
  , { walsCode := "zen", language := "Zenaga", iso := "zen", value := .prepositions }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .prepositions }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .postpositions }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noAdpositions }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .prepositions }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .postpositions }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .postpositions }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .postpositions }
  ]

/-- Complete WALS 85A dataset (1184 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1184 := by native_decide

theorem count_postpositions :
    (allData.filter (·.value == .postpositions)).length = 577 := by native_decide
theorem count_prepositions :
    (allData.filter (·.value == .prepositions)).length = 511 := by native_decide
theorem count_inpositions :
    (allData.filter (·.value == .inpositions)).length = 8 := by native_decide
theorem count_noDominantOrder :
    (allData.filter (·.value == .noDominantOrder)).length = 58 := by native_decide
theorem count_noAdpositions :
    (allData.filter (·.value == .noAdpositions)).length = 30 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F85A
