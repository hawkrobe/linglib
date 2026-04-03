import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 81A: Order of Subject, Object and Verb
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 81A`.

Chapter 81, 1376 languages.
-/

namespace Core.WALS.F81A

/-- WALS 81A values. -/
inductive BasicWordOrder where
  | sov  -- SOV (564 languages)
  | svo  -- SVO (488 languages)
  | vso  -- VSO (95 languages)
  | vos  -- VOS (25 languages)
  | ovs  -- OVS (11 languages)
  | osv  -- OSV (4 languages)
  | noDominantOrder  -- No dominant order (189 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint BasicWordOrder) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .svo }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .noDominantOrder }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .svo }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .svo }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .sov }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .svo }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .sov }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .sov }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .svo }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noDominantOrder }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .svo }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .svo }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .svo }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noDominantOrder }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .sov }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .svo }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .sov }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .noDominantOrder }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .svo }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .sov }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .sov }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .svo }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .vso }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .vso }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .sov }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .svo }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .noDominantOrder }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .svo }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .sov }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .sov }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .sov }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noDominantOrder }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .svo }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .sov }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .svo }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .sov }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .noDominantOrder }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .sov }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .svo }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .svo }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .svo }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .sov }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .sov }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .sov }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .noDominantOrder }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .vos }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .sov }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .svo }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .sov }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .sov }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .noDominantOrder }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .sov }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .svo }
  , { walsCode := "ayi", language := "Anyi", iso := "any", value := .svo }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .noDominantOrder }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .svo }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .sov }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .sov }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noDominantOrder }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .sov }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .sov }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .svo }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .sov }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .svo }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .svo }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .svo }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .svo }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .vso }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noDominantOrder }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .svo }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .svo }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .sov }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .sov }
  , { walsCode := "ari", language := "Aribwatsa", iso := "laz", value := .svo }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noDominantOrder }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .sov }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .svo }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .svo }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .sov }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .sov }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .sov }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .ovs }
  , { walsCode := "atm", language := "Atacameño", iso := "kuz", value := .sov }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .sov }
  , { walsCode := "ats", language := "Atsugewi", iso := "atw", value := .noDominantOrder }
  , { walsCode := "au", language := "Au", iso := "avt", value := .svo }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .sov }
  , { walsCode := "avk", language := "Avikam", iso := "avi", value := .svo }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .noDominantOrder }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .sov }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .sov }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .sov }
  , { walsCode := "awy", language := "Awyi", iso := "auw", value := .sov }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .svo }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .sov }
  , { walsCode := "ayr", language := "Ayoreo", iso := "ayo", value := .svo }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .sov }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .sov }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .svo }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .svo }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .noDominantOrder }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .sov }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .svo }
  , { walsCode := "bgs", language := "Baga Sitemu", iso := "bsp", value := .svo }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .svo }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .svo }
  , { walsCode := "bdw", language := "Baham", iso := "bdw", value := .sov }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .svo }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .noDominantOrder }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .noDominantOrder }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .svo }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .svo }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .svo }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .svo }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .svo }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .sov }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .sov }
  , { walsCode := "bgz", language := "Banggi", iso := "bdg", value := .svo }
  , { walsCode := "bgm", language := "Bangime", iso := "dba", value := .sov }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .svo }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .svo }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .sov }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .svo }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .sov }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .sov }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .noDominantOrder }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noDominantOrder }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .svo }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .sov }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .svo }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .svo }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .sov }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noDominantOrder }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .vos }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .vos }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .sov }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .sov }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .sov }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .vso }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .noDominantOrder }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .sov }
  , { walsCode := "brq", language := "Bera", iso := "brf", value := .svo }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .noDominantOrder }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .vso }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .vso }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .svo }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .sov }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .svo }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .sov }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .sov }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .sov }
  , { walsCode := "bhu", language := "Bhumij", iso := "unr", value := .sov }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .svo }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .svo }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .noDominantOrder }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .sov }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .noDominantOrder }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .svo }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .sov }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .svo }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .noDominantOrder }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .svo }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .svo }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .sov }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .noDominantOrder }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .sov }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .svo }
  , { walsCode := "boq", language := "Bokar", iso := "", value := .sov }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .sov }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .svo }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .svo }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .sov }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .noDominantOrder }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .svo }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .svo }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .sov }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .sov }
  , { walsCode := "bub", language := "Bubi", iso := "bvb", value := .svo }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .svo }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .svo }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .svo }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .svo }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .svo }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .svo }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .sov }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .svo }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .noDominantOrder }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .sov }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .sov }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .sov }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .svo }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .svo }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .sov }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .sov }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .svo }
  , { walsCode := "dok", language := "Bwele", iso := "ngc", value := .svo }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .sov }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .vos }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .sov }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noDominantOrder }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .noDominantOrder }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .sov }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .sov }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .svo }
  , { walsCode := "car", language := "Carib", iso := "car", value := .sov }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .sov }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .sov }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .svo }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .sov }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .noDominantOrder }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .sov }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .vos }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .vso }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .svo }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .sov }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .noDominantOrder }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .svo }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .svo }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .sov }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .vso }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .sov }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .vso }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .vso }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .sov }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .sov }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .noDominantOrder }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .sov }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .noDominantOrder }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .svo }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .vso }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .vos }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .vso }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .vso }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .vos }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .sov }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .sov }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .sov }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .sov }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .sov }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .svo }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .svo }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .vos }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noDominantOrder }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .vos }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .sov }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .noDominantOrder }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .sov }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .svo }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .sov }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noDominantOrder }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .svo }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .vso }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .svo }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noDominantOrder }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .noDominantOrder }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .sov }
  , { walsCode := "cua", language := "Cua", iso := "cua", value := .svo }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .ovs }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .sov }
  , { walsCode := "cuc", language := "Cuica", iso := "", value := .svo }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .sov }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .svo }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .vos }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .noDominantOrder }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .sov }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .svo }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .svo }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .sov }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .noDominantOrder }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .sov }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .sov }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .svo }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .sov }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .sov }
  , { walsCode := "day", language := "Day", iso := "dai", value := .svo }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .svo }
  , { walsCode := "des", language := "Desano", iso := "des", value := .sov }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .sov }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .sov }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .noDominantOrder }
  , { walsCode := "dhb", language := "Dharumbal", iso := "xgm", value := .sov }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .sov }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .vso }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .sov }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .sov }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .sov }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noDominantOrder }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .svo }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .sov }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .sov }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .noDominantOrder }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .sov }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .noDominantOrder }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .noDominantOrder }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .sov }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .sov }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .noDominantOrder }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .svo }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .noDominantOrder }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .sov }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .svo }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noDominantOrder }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .svo }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .svo }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .svo }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .sov }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .sov }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noDominantOrder }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noDominantOrder }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .sov }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .svo }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .sov }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .svo }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .svo }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .sov }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .sov }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .svo }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .svo }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .noDominantOrder }
  , { walsCode := "ene", language := "Enets", iso := "", value := .sov }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .svo }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .svo }
  , { walsCode := "eng", language := "English", iso := "eng", value := .svo }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .sov }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .svo }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .sov }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .svo }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .sov }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .sov }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .sov }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .svo }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .svo }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noDominantOrder }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .svo }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .sov }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .sov }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .svo }
  , { walsCode := "for", language := "Fore", iso := "for", value := .sov }
  , { walsCode := "fre", language := "French", iso := "fra", value := .svo }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .noDominantOrder }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .svo }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .sov }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .svo }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .svo }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .sov }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .vso }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .sov }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .sov }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .sov }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .sov }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .sov }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noDominantOrder }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .vso }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .svo }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .svo }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .vos }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .svo }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .sov }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noDominantOrder }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .noDominantOrder }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .sov }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .noDominantOrder }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .vso }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .svo }
  , { walsCode := "gog", language := "Gogodala", iso := "ggw", value := .sov }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .svo }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .sov }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .sov }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noDominantOrder }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .sov }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .svo }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noDominantOrder }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .sov }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .sov }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .vso }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .svo }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .noDominantOrder }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .vso }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .vso }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .sov }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .sov }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .sov }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .svo }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .sov }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .noDominantOrder }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .svo }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .svo }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .svo }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .noDominantOrder }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .noDominantOrder }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .noDominantOrder }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .sov }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .sov }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noDominantOrder }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .svo }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .svo }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noDominantOrder }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .sov }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .svo }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .svo }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .vso }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .sov }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .sov }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .svo }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .svo }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .vso }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .svo }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .sov }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .vso }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .svo }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .svo }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .vso }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .svo }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .sov }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .vso }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .sov }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .ovs }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .svo }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .svo }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .vso }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .svo }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .sov }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .sov }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .sov }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .svo }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .svo }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .sov }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .sov }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .sov }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .svo }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noDominantOrder }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .sov }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .sov }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .noDominantOrder }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .sov }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .svo }
  , { walsCode := "iat", language := "Iatmul", iso := "ian", value := .sov }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .svo }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .svo }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .noDominantOrder }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .sov }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .svo }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .svo }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .svo }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .svo }
  , { walsCode := "iha", language := "Iha", iso := "ihp", value := .sov }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .sov }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .vso }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .sov }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .svo }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .vso }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .noDominantOrder }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .svo }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .svo }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .sov }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .svo }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .sov }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .sov }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .svo }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .vso }
  , { walsCode := "isi", language := "Isirawa", iso := "srl", value := .sov }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .svo }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .sov }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .svo }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .svo }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .sov }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .svo }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .vso }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .svo }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .svo }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .sov }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .svo }
  , { walsCode := "jad", language := "Jad", iso := "jda", value := .sov }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .vso }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .noDominantOrder }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .sov }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .sov }
  , { walsCode := "jrw", language := "Jarawa (in Andamans)", iso := "anq", value := .sov }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .noDominantOrder }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .sov }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .sov }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .sov }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .sov }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .svo }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .svo }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .svo }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .sov }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .svo }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .vso }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .sov }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .vso }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .svo }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .svo }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .sov }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .sov }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .sov }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .vso }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .sov }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .sov }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .sov }
  ]

private def allData_1 : List (Datapoint BasicWordOrder) :=
  [ { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .sov }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .sov }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .svo }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .sov }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .sov }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .noDominantOrder }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .svo }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .svo }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .sov }
  , { walsCode := "kbu", language := "Kanembu", iso := "kbl", value := .sov }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .sov }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .sov }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .sov }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .sov }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .svo }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .sov }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .sov }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .sov }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .noDominantOrder }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .svo }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .svo }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .svo }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .vso }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .sov }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noDominantOrder }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .sov }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .svo }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .svo }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .svo }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .svo }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .sov }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .svo }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .svo }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noDominantOrder }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .sov }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .svo }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .sov }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noDominantOrder }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .svo }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .sov }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .svo }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .svo }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .noDominantOrder }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .sov }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .svo }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .sov }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .sov }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .sov }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .sov }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .sov }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .sov }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .sov }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .sov }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .noDominantOrder }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .svo }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .svo }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .svo }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .sov }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .svo }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .svo }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noDominantOrder }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .sov }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .svo }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .sov }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .svo }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .sov }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .svo }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .sov }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .vos }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .sov }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .vos }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .svo }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noDominantOrder }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .sov }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .noDominantOrder }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .svo }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .vso }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .sov }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .sov }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .svo }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .sov }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .sov }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .sov }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .vso }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .sov }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .sov }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .svo }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .svo }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .svo }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .svo }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .svo }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .noDominantOrder }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .sov }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .vso }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .sov }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .svo }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .sov }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .sov }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .svo }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .sov }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .svo }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .sov }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .sov }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .sov }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .svo }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .vso }
  , { walsCode := "krz", language := "Kryz", iso := "kry", value := .sov }
  , { walsCode := "kkq", language := "Kuikúro", iso := "kui", value := .ovs }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .sov }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .sov }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .sov }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .sov }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .sov }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .sov }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .vso }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .sov }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .sov }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noDominantOrder }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .sov }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .sov }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .svo }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .noDominantOrder }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .svo }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noDominantOrder }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .sov }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .sov }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .osv }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .sov }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .vso }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .svo }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .svo }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .noDominantOrder }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .sov }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .svo }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .sov }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .sov }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .sov }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .sov }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .svo }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .vso }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .sov }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .noDominantOrder }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .svo }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .svo }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .svo }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .svo }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .svo }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .svo }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .sov }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .svo }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .svo }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .svo }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .noDominantOrder }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .svo }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .svo }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .svo }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .noDominantOrder }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .sov }
  , { walsCode := "les", language := "Lese", iso := "les", value := .noDominantOrder }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .svo }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .svo }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .sov }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .vso }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .noDominantOrder }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .svo }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .svo }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .sov }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .svo }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .noDominantOrder }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .svo }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .svo }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .vos }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .svo }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .sov }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .svo }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .svo }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noDominantOrder }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .noDominantOrder }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .svo }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .svo }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .svo }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .svo }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .svo }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .svo }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noDominantOrder }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .vso }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .sov }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .svo }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noDominantOrder }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .svo }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .noDominantOrder }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .svo }
  , { walsCode := "mgh", language := "Magahi", iso := "mag", value := .sov }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .sov }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .sov }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .sov }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .svo }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .sov }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .sov }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .vso }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .svo }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .vso }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .sov }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .sov }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .svo }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .svo }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .vos }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .sov }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .svo }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .svo }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .sov }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .vso }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .vso }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .svo }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .svo }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .svo }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .sov }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .sov }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .sov }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .svo }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .sov }
  , { walsCode := "mem", language := "Manem", iso := "jet", value := .sov }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .svo }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .ovs }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .svo }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .svo }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .sov }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .sov }
  , { walsCode := "mkq", language := "Mankon", iso := "nge", value := .svo }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .sov }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .vso }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .sov }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .vso }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .svo }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .noDominantOrder }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .sov }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .sov }
  , { walsCode := "mrc", language := "Marchha", iso := "rnp", value := .sov }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .sov }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .svo }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .sov }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .sov }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .sov }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .vso }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .sov }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .svo }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .sov }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .svo }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .noDominantOrder }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .sov }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .noDominantOrder }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .sov }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .sov }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .sov }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .svo }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .sov }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .svo }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .sov }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .svo }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .svo }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .noDominantOrder }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .svo }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .svo }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .svo }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .svo }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .svo }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .svo }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .svo }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .svo }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .svo }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .svo }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noDominantOrder }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .sov }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .sov }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .noDominantOrder }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .sov }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .sov }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .svo }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .sov }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .svo }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .sov }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .sov }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .sov }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .svo }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noDominantOrder }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .sov }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .sov }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .sov }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noDominantOrder }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .noDominantOrder }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .vso }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .vso }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .vso }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .vso }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .vso }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .noDominantOrder }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .sov }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .svo }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .svo }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .svo }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .sov }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .noDominantOrder }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .svo }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .sov }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .sov }
  , { walsCode := "mqf", language := "Momuna", iso := "mqf", value := .sov }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .svo }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .svo }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .svo }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .sov }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .sov }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .sov }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noDominantOrder }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .svo }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .svo }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .sov }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .svo }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .svo }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .noDominantOrder }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .svo }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .sov }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .noDominantOrder }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .svo }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .svo }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .sov }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .svo }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .svo }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .svo }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .sov }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .sov }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .svo }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .svo }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .vso }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .sov }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .svo }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .noDominantOrder }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .svo }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .svo }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .vso }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .svo }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .svo }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .svo }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .svo }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .sov }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .noDominantOrder }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .osv }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .sov }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .sov }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .sov }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .vso }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .svo }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .svo }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .svo }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .svo }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .svo }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .sov }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .sov }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .sov }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .noDominantOrder }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .vso }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .sov }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .sov }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .sov }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .sov }
  , { walsCode := "nau", language := "Nauruan", iso := "nau", value := .noDominantOrder }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .sov }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .svo }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .svo }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .noDominantOrder }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .svo }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .svo }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .svo }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .svo }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .svo }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .sov }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .sov }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .svo }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .sov }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .sov }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .sov }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .sov }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .sov }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .noDominantOrder }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noDominantOrder }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .sov }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .svo }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noDominantOrder }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .sov }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .svo }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .noDominantOrder }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .sov }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .noDominantOrder }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .svo }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .svo }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .svo }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .svo }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noDominantOrder }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .svo }
  , { walsCode := "nbe", language := "Ngombe", iso := "ngc", value := .svo }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .svo }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .svo }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .sov }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .noDominantOrder }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .vos }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .vos }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .vso }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .vso }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .vso }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .sov }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .svo }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .svo }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .svo }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .sov }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .sov }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .svo }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .svo }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .svo }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .svo }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .svo }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .svo }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .sov }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .sov }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .noDominantOrder }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .svo }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noDominantOrder }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .svo }
  , { walsCode := "nus", language := "Nusu", iso := "nuf", value := .sov }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noDominantOrder }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .sov }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .noDominantOrder }
  , { walsCode := "nng", language := "Nyanga", iso := "nyj", value := .svo }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .noDominantOrder }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .sov }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .svo }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noDominantOrder }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .svo }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .svo }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .svo }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .sov }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noDominantOrder }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .sov }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .svo }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .sov }
  , { walsCode := "one", language := "One", iso := "aun", value := .svo }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noDominantOrder }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .sov }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .sov }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .sov }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .sov }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .sov }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .sov }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .sov }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .sov }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .sov }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .sov }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .vos }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .svo }
  , { walsCode := "owi", language := "Owininga", iso := "owi", value := .sov }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .svo }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .svo }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .svo }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .sov }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noDominantOrder }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .svo }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .svo }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .svo }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .svo }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .noDominantOrder }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .vso }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .svo }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .sov }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .noDominantOrder }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .svo }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .sov }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noDominantOrder }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .svo }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .sov }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .noDominantOrder }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .svo }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .svo }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .sov }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .svo }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .sov }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .svo }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .sov }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noDominantOrder }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .sov }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .sov }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .sov }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .noDominantOrder }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .vso }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .svo }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .svo }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .noDominantOrder }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .vso }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .svo }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .sov }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .sov }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .svo }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .svo }
  ]

private def allData_2 : List (Datapoint BasicWordOrder) :=
  [ { walsCode := "por", language := "Portuguese", iso := "por", value := .svo }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .sov }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .svo }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .sov }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .sov }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .sov }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .svo }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .sov }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .ovs }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .sov }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .sov }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .sov }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .vso }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .svo }
  , { walsCode := "ral", language := "Ralte", iso := "ral", value := .sov }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .sov }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .sov }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .sov }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .vso }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .sov }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .sov }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .sov }
  , { walsCode := "rmb", language := "Rembarnga", iso := "rmb", value := .sov }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .sov }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .sov }
  , { walsCode := "ria", language := "Riantana", iso := "ran", value := .sov }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .sov }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .svo }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .noDominantOrder }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .noDominantOrder }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .svo }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .svo }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .svo }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .svo }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .svo }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .vso }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .noDominantOrder }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .sov }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .sov }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .svo }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .svo }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .svo }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .sov }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .svo }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .svo }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .svo }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .sov }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .svo }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .sov }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .svo }
  , { walsCode := "nmd", language := "Samo", iso := "smq", value := .sov }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noDominantOrder }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .sov }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .svo }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .svo }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .sov }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .sov }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .sov }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .svo }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .sov }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .svo }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .sov }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .sov }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .sov }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .vso }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .svo }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .vos }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .ovs }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .sov }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .sov }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noDominantOrder }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .sov }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noDominantOrder }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .svo }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .sov }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .svo }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .sov }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .svo }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .sov }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .svo }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .svo }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .sov }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .noDominantOrder }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .svo }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .sov }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .sov }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .svo }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .sov }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .sov }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .sov }
  , { walsCode := "smp", language := "Shompen", iso := "sii", value := .vso }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .svo }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .sov }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .noDominantOrder }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .sov }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .svo }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .sov }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .sov }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .sov }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .sov }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .svo }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .vso }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .sov }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .sov }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .svo }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .svo }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noDominantOrder }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .sov }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .sov }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .svo }
  , { walsCode := "so", language := "So", iso := "teu", value := .vso }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .svo }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .sov }
  , { walsCode := "som", language := "Somali", iso := "som", value := .sov }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .sov }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .svo }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .sov }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .svo }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .svo }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .svo }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .svo }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .sov }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .vso }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .svo }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .svo }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .svo }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .sov }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .sov }
  , { walsCode := "sku", language := "Suku", iso := "sub", value := .svo }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .svo }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .svo }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .svo }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .sov }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .sov }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .svo }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .noDominantOrder }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .svo }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .svo }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .sov }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .sov }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .svo }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noDominantOrder }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .vso }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .vso }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .svo }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .sov }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .sov }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .sov }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .sov }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .svo }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .sov }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .svo }
  , { walsCode := "tmg", language := "Tamagario", iso := "tcg", value := .sov }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .sov }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .vso }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .sov }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .svo }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .sov }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .sov }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .sov }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .sov }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .sov }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .noDominantOrder }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .sov }
  , { walsCode := "tsr", language := "Taushiro", iso := "trr", value := .vso }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .sov }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .sov }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .vso }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .sov }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .sov }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .svo }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .svo }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .svo }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .vso }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .svo }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .noDominantOrder }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .svo }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .vso }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .svo }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .sov }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .vso }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .svo }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .svo }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .svo }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .svo }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .sov }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .sov }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .noDominantOrder }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .sov }
  , { walsCode := "tdi", language := "Tibetan (Dingri)", iso := "bod", value := .sov }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .sov }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .sov }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .sov }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .noDominantOrder }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .svo }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .svo }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .sov }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .sov }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .sov }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .noDominantOrder }
  , { walsCode := "tia", language := "Tima", iso := "tms", value := .svo }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .sov }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .vso }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .sov }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noDominantOrder }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .ovs }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .svo }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .svo }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noDominantOrder }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .svo }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .vso }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .sov }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .noDominantOrder }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .osv }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .sov }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .sov }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .svo }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .noDominantOrder }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .svo }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .noDominantOrder }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noDominantOrder }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .sov }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .svo }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .vso }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noDominantOrder }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .sov }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .sov }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .sov }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .vso }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .sov }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .sov }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .svo }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .vos }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .svo }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .sov }
  , { walsCode := "tum", language := "Tumleo", iso := "tmq", value := .svo }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .sov }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .svo }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .sov }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .svo }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .vso }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .sov }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .sov }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .noDominantOrder }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .sov }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .ovs }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .sov }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .sov }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .sov }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .vos }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noDominantOrder }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .sov }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .sov }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .sov }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .sov }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .sov }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .svo }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .svo }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .svo }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .sov }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .ovs }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .svo }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .sov }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .svo }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .ovs }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .svo }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .sov }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .sov }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .sov }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .sov }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .noDominantOrder }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .sov }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .sov }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .sov }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .svo }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .svo }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .svo }
  , { walsCode := "wwa", language := "Waama", iso := "wwa", value := .svo }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .sov }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .sov }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .noDominantOrder }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .sov }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .svo }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noDominantOrder }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .sov }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .sov }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .sov }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .noDominantOrder }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .sov }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .sov }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .svo }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noDominantOrder }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .svo }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .svo }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .vos }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .noDominantOrder }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .sov }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .svo }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .noDominantOrder }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .noDominantOrder }
  , { walsCode := "was", language := "Washo", iso := "was", value := .sov }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .sov }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .vos }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .sov }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .sov }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .vso }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .vso }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .vos }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .svo }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noDominantOrder }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .svo }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .sov }
  , { walsCode := "wn", language := "Wik Ngathana", iso := "wig", value := .osv }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noDominantOrder }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noDominantOrder }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noDominantOrder }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .sov }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .svo }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .vso }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .svo }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .sov }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .noDominantOrder }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .sov }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .sov }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .svo }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .svo }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .sov }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noDominantOrder }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .sov }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .sov }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .sov }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .sov }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .svo }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .vso }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .sov }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .sov }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .sov }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .noDominantOrder }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .noDominantOrder }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .svo }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .sov }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .sov }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .sov }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .sov }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .sov }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .svo }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .svo }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .noDominantOrder }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .svo }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .sov }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .svo }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .sov }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .sov }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .svo }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .svo }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noDominantOrder }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .noDominantOrder }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noDominantOrder }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .sov }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .svo }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .svo }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .vso }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .vso }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .vso }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .noDominantOrder }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .sov }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .sov }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .svo }
  , { walsCode := "zim", language := "Zimakani", iso := "zik", value := .sov }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .svo }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .vos }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .noDominantOrder }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .svo }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .sov }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .sov }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .sov }
  ]

/-- Complete WALS 81A dataset (1376 languages). -/
def allData : List (Datapoint BasicWordOrder) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1376 := by native_decide

theorem count_sov :
    (allData.filter (·.value == .sov)).length = 564 := by native_decide
theorem count_svo :
    (allData.filter (·.value == .svo)).length = 488 := by native_decide
theorem count_vso :
    (allData.filter (·.value == .vso)).length = 95 := by native_decide
theorem count_vos :
    (allData.filter (·.value == .vos)).length = 25 := by native_decide
theorem count_ovs :
    (allData.filter (·.value == .ovs)).length = 11 := by native_decide
theorem count_osv :
    (allData.filter (·.value == .osv)).length = 4 := by native_decide
theorem count_noDominantOrder :
    (allData.filter (·.value == .noDominantOrder)).length = 189 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F81A
