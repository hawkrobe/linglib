/-!
# WALS Feature 82A: Order of Subject and Verb
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 82A`.

Chapter 82, 1496 languages.
-/

namespace Core.WALS.F82A

/-- WALS 82A values. -/
inductive SubjectVerbOrder where
  | sv  -- SV (1192 languages)
  | vs  -- VS (194 languages)
  | noDominantOrder  -- No dominant order (110 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 82A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : SubjectVerbOrder
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .sv }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .sv }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .sv }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .sv }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .sv }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .sv }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .sv }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .sv }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .sv }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .sv }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noDominantOrder }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .sv }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .sv }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .sv }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .sv }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .sv }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .sv }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .sv }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .sv }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .sv }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .sv }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .sv }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .sv }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .sv }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .vs }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .vs }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .sv }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .sv }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .sv }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .sv }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .sv }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .sv }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .sv }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noDominantOrder }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .sv }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .sv }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .vs }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .sv }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .sv }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .noDominantOrder }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .sv }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .sv }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .sv }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .sv }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .sv }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .sv }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .sv }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .sv }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .vs }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .sv }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .vs }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .sv }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .sv }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .sv }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .sv }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .vs }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .sv }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .sv }
  , { walsCode := "ayi", language := "Anyi", iso := "any", value := .sv }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .noDominantOrder }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .sv }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .sv }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .sv }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noDominantOrder }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .sv }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .sv }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .sv }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .sv }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .sv }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .sv }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .sv }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .sv }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .vs }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .vs }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noDominantOrder }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .sv }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .sv }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .sv }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .sv }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .sv }
  , { walsCode := "ari", language := "Aribwatsa", iso := "laz", value := .sv }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .sv }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .sv }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .sv }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .sv }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .sv }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .sv }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .sv }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .vs }
  , { walsCode := "atm", language := "Atacameño", iso := "kuz", value := .sv }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .sv }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .vs }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .sv }
  , { walsCode := "au", language := "Au", iso := "avt", value := .sv }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .sv }
  , { walsCode := "avk", language := "Avikam", iso := "avi", value := .sv }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .sv }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .sv }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .sv }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .sv }
  , { walsCode := "awy", language := "Awyi", iso := "auw", value := .sv }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .sv }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .sv }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .sv }
  , { walsCode := "ayr", language := "Ayoreo", iso := "ayo", value := .sv }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .sv }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .sv }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .sv }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .sv }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .noDominantOrder }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .sv }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .sv }
  , { walsCode := "bgs", language := "Baga Sitemu", iso := "bsp", value := .sv }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .sv }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .sv }
  , { walsCode := "bdw", language := "Baham", iso := "bdw", value := .sv }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .sv }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .noDominantOrder }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .noDominantOrder }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .sv }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .sv }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .sv }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .sv }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .sv }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .sv }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .sv }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .sv }
  , { walsCode := "bgz", language := "Banggi", iso := "bdg", value := .sv }
  , { walsCode := "bgm", language := "Bangime", iso := "dba", value := .sv }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .sv }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .sv }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .sv }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .sv }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .sv }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .sv }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .noDominantOrder }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noDominantOrder }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .sv }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .sv }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .sv }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .noDominantOrder }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .sv }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .sv }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .sv }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .sv }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noDominantOrder }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .vs }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .vs }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .sv }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .sv }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .sv }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .sv }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .vs }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .noDominantOrder }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .sv }
  , { walsCode := "brq", language := "Bera", iso := "brf", value := .sv }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .noDominantOrder }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .vs }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .vs }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .sv }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .sv }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .sv }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .sv }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .sv }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .sv }
  , { walsCode := "bhu", language := "Bhumij", iso := "unr", value := .sv }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .sv }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .sv }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .vs }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .noDominantOrder }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .sv }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .noDominantOrder }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .sv }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .sv }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .sv }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .sv }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .sv }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .sv }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .sv }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .noDominantOrder }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .sv }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .sv }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .sv }
  , { walsCode := "boq", language := "Bokar", iso := "", value := .sv }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .sv }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .sv }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .sv }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .sv }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .noDominantOrder }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .sv }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .vs }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .sv }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .sv }
  , { walsCode := "bub", language := "Bubi", iso := "bvb", value := .sv }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .sv }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .sv }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .sv }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .sv }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noDominantOrder }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .sv }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .sv }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .sv }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .sv }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .sv }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .sv }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .sv }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .sv }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .sv }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .sv }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .sv }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .sv }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .sv }
  , { walsCode := "dok", language := "Bwele", iso := "ngc", value := .sv }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .sv }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .sv }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .vs }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .sv }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noDominantOrder }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .sv }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .sv }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .sv }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .sv }
  , { walsCode := "car", language := "Carib", iso := "car", value := .sv }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .sv }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .sv }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noDominantOrder }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .sv }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .noDominantOrder }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .sv }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .vs }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .vs }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .sv }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .sv }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .sv }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .sv }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .sv }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .sv }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .vs }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .sv }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .sv }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .vs }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .vs }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .sv }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .sv }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .sv }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .sv }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .noDominantOrder }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .sv }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .sv }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .sv }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .sv }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .sv }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .vs }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .vs }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .vs }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .vs }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .vs }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .sv }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .sv }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .sv }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .sv }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .sv }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .vs }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .vs }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .sv }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .vs }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .sv }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .vs }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .sv }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .noDominantOrder }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .sv }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .sv }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .vs }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .sv }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .vs }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .vs }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .sv }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .vs }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .sv }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noDominantOrder }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .noDominantOrder }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .sv }
  , { walsCode := "cua", language := "Cua", iso := "cua", value := .sv }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .vs }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .sv }
  , { walsCode := "cuc", language := "Cuica", iso := "", value := .sv }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .sv }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .sv }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .vs }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .sv }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .sv }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .sv }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .sv }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .sv }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .sv }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .sv }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .sv }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .sv }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .sv }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .sv }
  , { walsCode := "day", language := "Day", iso := "dai", value := .sv }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .sv }
  , { walsCode := "des", language := "Desano", iso := "des", value := .sv }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .sv }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .sv }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .noDominantOrder }
  , { walsCode := "dhb", language := "Dharumbal", iso := "xgm", value := .sv }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .sv }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .vs }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .sv }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .sv }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .sv }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .sv }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .sv }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .sv }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .sv }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .sv }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .noDominantOrder }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .sv }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .sv }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .sv }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .sv }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .sv }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .sv }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .vs }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noDominantOrder }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .sv }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .sv }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .sv }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noDominantOrder }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .sv }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .sv }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .sv }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .sv }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .sv }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .sv }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .sv }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .sv }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .sv }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .sv }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .sv }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .sv }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .sv }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .sv }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .sv }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .sv }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .sv }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .sv }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .sv }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .sv }
  , { walsCode := "ene", language := "Enets", iso := "", value := .sv }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .sv }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .sv }
  , { walsCode := "eng", language := "English", iso := "eng", value := .sv }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .sv }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .sv }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .sv }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .vs }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .sv }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .sv }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .sv }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .sv }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .sv }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .sv }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .sv }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .vs }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .sv }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .sv }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .sv }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .sv }
  , { walsCode := "for", language := "Fore", iso := "for", value := .sv }
  , { walsCode := "fre", language := "French", iso := "fra", value := .sv }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .sv }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .sv }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .sv }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .sv }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .sv }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .sv }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .vs }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .sv }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .sv }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .sv }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .sv }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .sv }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noDominantOrder }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .vs }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .sv }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .sv }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .sv }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .vs }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .sv }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .sv }
  , { walsCode := "ger", language := "German", iso := "deu", value := .sv }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .noDominantOrder }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .sv }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .noDominantOrder }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .vs }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .sv }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .sv }
  , { walsCode := "gog", language := "Gogodala", iso := "ggw", value := .sv }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .sv }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .sv }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .sv }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .sv }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .sv }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .sv }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noDominantOrder }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .sv }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .sv }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .vs }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .sv }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .noDominantOrder }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .vs }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .vs }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .sv }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .sv }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .sv }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .sv }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .sv }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .noDominantOrder }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .sv }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .sv }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .sv }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .noDominantOrder }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .sv }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .sv }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .sv }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .sv }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .sv }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .sv }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .sv }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .sv }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noDominantOrder }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .sv }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .sv }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .sv }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .vs }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .sv }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .sv }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .sv }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .sv }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .sv }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .sv }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .vs }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .sv }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .sv }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .vs }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .sv }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .sv }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .vs }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .sv }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .sv }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .vs }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .sv }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .vs }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .sv }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .sv }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .sv }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .vs }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .sv }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .sv }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .sv }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .sv }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .vs }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .vs }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .sv }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .sv }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .sv }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .sv }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .sv }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .sv }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .sv }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .noDominantOrder }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .sv }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .vs }
  , { walsCode := "iat", language := "Iatmul", iso := "ian", value := .sv }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .sv }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .sv }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .sv }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .sv }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .sv }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .sv }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .vs }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .sv }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .sv }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .sv }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .vs }
  , { walsCode := "iha", language := "Iha", iso := "ihp", value := .sv }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .sv }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .vs }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .sv }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .sv }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .vs }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .sv }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .sv }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .sv }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .sv }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .sv }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .sv }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .sv }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "irx", language := "Iranxe", iso := "irn", value := .sv }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .sv }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .sv }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .vs }
  , { walsCode := "isi", language := "Isirawa", iso := "srl", value := .sv }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noDominantOrder }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .sv }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .sv }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .sv }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .sv }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .sv }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .vs }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .sv }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .sv }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .sv }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .sv }
  , { walsCode := "jad", language := "Jad", iso := "jda", value := .sv }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .vs }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .noDominantOrder }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .sv }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .sv }
  , { walsCode := "jrw", language := "Jarawa (in Andamans)", iso := "anq", value := .sv }
  , { walsCode := "jwr", language := "Jarawara", iso := "jaa", value := .sv }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .noDominantOrder }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .sv }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .sv }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .sv }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .sv }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .sv }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .sv }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .sv }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .sv }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .sv }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .vs }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .sv }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .vs }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .sv }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .sv }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .sv }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .sv }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .sv }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .sv }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .vs }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .sv }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .sv }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .sv }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .sv }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .sv }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .sv }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .sv }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .vs }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .sv }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .sv }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .sv }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .sv }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .sv }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .sv }
  , { walsCode := "kbu", language := "Kanembu", iso := "kbl", value := .sv }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .sv }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .sv }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .sv }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .sv }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .vs }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .sv }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .sv }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .sv }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .sv }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .sv }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .sv }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .sv }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .vs }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .sv }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .sv }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .sv }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .sv }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .sv }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .sv }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .sv }
  , { walsCode := "ktm", language := "Kathlamet", iso := "", value := .vs }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .sv }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .sv }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .sv }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noDominantOrder }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .sv }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .sv }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .sv }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .sv }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .sv }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .sv }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .sv }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .sv }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .sv }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .sv }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .sv }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .sv }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .sv }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .sv }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .sv }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .sv }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .sv }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .sv }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .sv }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .sv }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .sv }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .sv }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .sv }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .sv }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .sv }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .sv }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .vs }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .sv }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .sv }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .sv }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .sv }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .sv }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .sv }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .sv }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .vs }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .sv }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .vs }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .sv }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .sv }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .sv }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .noDominantOrder }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .sv }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .vs }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .sv }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .sv }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .sv }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .sv }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .sv }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .sv }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .vs }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .sv }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .sv }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .sv }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .sv }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .sv }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .sv }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .sv }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .sv }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .noDominantOrder }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .sv }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .vs }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .sv }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .sv }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .sv }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .sv }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .sv }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .sv }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .sv }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .sv }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .sv }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .sv }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .sv }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .sv }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .vs }
  , { walsCode := "krz", language := "Kryz", iso := "kry", value := .sv }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .sv }
  , { walsCode := "kkq", language := "Kuikúro", iso := "kui", value := .sv }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .sv }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .sv }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .sv }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .sv }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .sv }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .sv }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .sv }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .vs }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .sv }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .sv }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .vs }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .sv }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .sv }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .sv }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .sv }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .noDominantOrder }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .sv }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .sv }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .sv }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .sv }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .sv }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .sv }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .sv }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .vs }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .sv }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .sv }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .noDominantOrder }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .sv }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .sv }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .sv }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .sv }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .sv }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .sv }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .sv }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .sv }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .vs }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .sv }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .sv }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .sv }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .sv }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .sv }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .sv }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .sv }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noDominantOrder }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .sv }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .sv }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .sv }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .sv }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .sv }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .sv }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .sv }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .sv }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .sv }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .sv }
  , { walsCode := "les", language := "Lese", iso := "les", value := .sv }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .sv }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .sv }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .sv }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .sv }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .vs }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .sv }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .noDominantOrder }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .sv }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .sv }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .sv }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .sv }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .sv }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .noDominantOrder }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .sv }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .vs }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .sv }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .sv }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .sv }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .sv }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .sv }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .sv }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .sv }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .sv }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .sv }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .sv }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .sv }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .sv }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .sv }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .sv }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .vs }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .sv }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .sv }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .vs }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noDominantOrder }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .sv }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .noDominantOrder }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .sv }
  , { walsCode := "mgh", language := "Magahi", iso := "mag", value := .sv }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .sv }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .sv }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .sv }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .noDominantOrder }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .sv }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .sv }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .sv }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .vs }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .sv }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .vs }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .sv }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .sv }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .sv }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .sv }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .vs }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .sv }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .sv }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .sv }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .sv }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .sv }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .vs }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .vs }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .sv }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .sv }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .sv }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .sv }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .sv }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .sv }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .sv }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .sv }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .sv }
  , { walsCode := "mem", language := "Manem", iso := "jet", value := .sv }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .sv }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .sv }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .sv }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .sv }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .sv }
  , { walsCode := "mgq", language := "Mango", iso := "mge", value := .sv }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .sv }
  , { walsCode := "mkq", language := "Mankon", iso := "nge", value := .sv }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .sv }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .vs }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .sv }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .vs }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .vs }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .noDominantOrder }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .sv }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .sv }
  , { walsCode := "mrc", language := "Marchha", iso := "rnp", value := .sv }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .sv }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .sv }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .sv }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .sv }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .sv }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .vs }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .sv }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .sv }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .sv }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .sv }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .noDominantOrder }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .sv }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .noDominantOrder }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .sv }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .sv }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .sv }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .sv }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .sv }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .sv }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .sv }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .sv }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .sv }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .vs }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .noDominantOrder }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .sv }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .sv }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .sv }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .sv }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .sv }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .sv }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .sv }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .sv }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .sv }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .sv }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noDominantOrder }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .sv }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .sv }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .sv }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .sv }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .noDominantOrder }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .vs }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .sv }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .sv }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .sv }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .sv }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .sv }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .sv }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .sv }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .sv }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .sv }
  , { walsCode := "mil", language := "Milang", iso := "", value := .sv }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .sv }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noDominantOrder }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .sv }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .sv }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .sv }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .sv }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .noDominantOrder }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .vs }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .vs }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .vs }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .vs }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .vs }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .noDominantOrder }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .sv }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .sv }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .vs }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .sv }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .sv }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .noDominantOrder }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noDominantOrder }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .sv }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .sv }
  , { walsCode := "mqf", language := "Momuna", iso := "mqf", value := .sv }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .sv }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .sv }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .sv }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .sv }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .sv }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .sv }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noDominantOrder }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .sv }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .sv }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .sv }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .sv }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .sv }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .sv }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .sv }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .sv }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .sv }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .sv }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .vs }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .noDominantOrder }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .sv }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .sv }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .sv }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .sv }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .sv }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .vs }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .sv }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .sv }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .sv }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .sv }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .sv }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .vs }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .sv }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .sv }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .sv }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .sv }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .sv }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .vs }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .sv }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .noDominantOrder }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .sv }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .sv }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .sv }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .vs }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .sv }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .sv }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .sv }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .sv }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .sv }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .sv }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .vs }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .vs }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .sv }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noDominantOrder }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .sv }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .sv }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .sv }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .sv }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .sv }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .sv }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .vs }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .vs }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .sv }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .sv }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .sv }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .sv }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .sv }
  , { walsCode := "nau", language := "Nauruan", iso := "nau", value := .noDominantOrder }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .sv }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .sv }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .sv }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .sv }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .sv }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .sv }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .sv }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .sv }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .sv }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .sv }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .sv }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .noDominantOrder }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .sv }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .sv }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .sv }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .sv }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .sv }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .sv }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noDominantOrder }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .sv }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .sv }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .sv }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noDominantOrder }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .sv }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .sv }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .noDominantOrder }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .sv }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .sv }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .sv }
  , { walsCode := "ngr", language := "Ngarinyeri", iso := "nay", value := .vs }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .sv }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .sv }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .sv }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .sv }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .sv }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .sv }
  , { walsCode := "nbe", language := "Ngombe", iso := "ngc", value := .sv }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .sv }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .sv }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .sv }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .noDominantOrder }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .vs }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .vs }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .sv }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .vs }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .vs }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .vs }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .sv }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .sv }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .sv }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .sv }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .sv }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .sv }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .sv }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .sv }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .sv }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .sv }
  ]

private def allData_2 : List Datapoint :=
  [ { walsCode := "nto", language := "Ntomba", iso := "nto", value := .sv }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .sv }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .sv }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .sv }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .sv }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .sv }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noDominantOrder }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .sv }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .sv }
  , { walsCode := "nus", language := "Nusu", iso := "nuf", value := .sv }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .vs }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .sv }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .noDominantOrder }
  , { walsCode := "nng", language := "Nyanga", iso := "nyj", value := .sv }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .sv }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .noDominantOrder }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .sv }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .sv }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .sv }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .vs }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .sv }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .sv }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .sv }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .sv }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .vs }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .sv }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .sv }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .sv }
  , { walsCode := "one", language := "One", iso := "aun", value := .sv }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .vs }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .sv }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .sv }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .sv }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .sv }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .sv }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .sv }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .sv }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .sv }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .sv }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .sv }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .sv }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .vs }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .sv }
  , { walsCode := "owi", language := "Owininga", iso := "owi", value := .sv }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .sv }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .sv }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .sv }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .sv }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .vs }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .sv }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .sv }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .sv }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .sv }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .vs }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .vs }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .sv }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .sv }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .sv }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .sv }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .sv }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noDominantOrder }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .sv }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .sv }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .sv }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .sv }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .vs }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .sv }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .sv }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .sv }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .sv }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .vs }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .sv }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .vs }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .sv }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .sv }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .sv }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .sv }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .noDominantOrder }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .vs }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .sv }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .sv }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .sv }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .vs }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noDominantOrder }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .sv }
  , { walsCode := "pmn", language := "Pomo (Northern)", iso := "pej", value := .sv }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .sv }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .noDominantOrder }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .sv }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .sv }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .sv }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .sv }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .sv }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .sv }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .sv }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .sv }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .sv }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .sv }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .sv }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .sv }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .sv }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .sv }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .vs }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .sv }
  , { walsCode := "ral", language := "Ralte", iso := "ral", value := .sv }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .sv }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .sv }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .sv }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .vs }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .sv }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .sv }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .sv }
  , { walsCode := "rmb", language := "Rembarnga", iso := "rmb", value := .sv }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .sv }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .sv }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .sv }
  , { walsCode := "ria", language := "Riantana", iso := "ran", value := .sv }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .sv }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .sv }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .noDominantOrder }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .noDominantOrder }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .sv }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .sv }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .sv }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .sv }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .sv }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .vs }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .vs }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .vs }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .sv }
  , { walsCode := "rnd", language := "Rundi", iso := "run", value := .sv }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .sv }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .sv }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .sv }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .sv }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .sv }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .sv }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .sv }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .sv }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .sv }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .vs }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .sv }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .sv }
  , { walsCode := "nmd", language := "Samo", iso := "smq", value := .sv }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .vs }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .sv }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .sv }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .sv }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .sv }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .sv }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .sv }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .sv }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .sv }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .sv }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .sv }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .sv }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .sv }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .vs }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .sv }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .vs }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .vs }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .sv }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .sv }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .sv }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noDominantOrder }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .sv }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noDominantOrder }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .sv }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .sv }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .sv }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .sv }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .sv }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .sv }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .sv }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .sv }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .sv }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .noDominantOrder }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .sv }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .sv }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .sv }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .sv }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .sv }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .sv }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .sv }
  , { walsCode := "smp", language := "Shompen", iso := "sii", value := .vs }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .sv }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .sv }
  , { walsCode := "ryu", language := "Shuri", iso := "ryu", value := .sv }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .vs }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .sv }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .sv }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .sv }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .sv }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .sv }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .sv }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .vs }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .sv }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .sv }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .sv }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .sv }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .vs }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .sv }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .sv }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .sv }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .sv }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noDominantOrder }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .sv }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .sv }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .sv }
  , { walsCode := "so", language := "So", iso := "teu", value := .vs }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .sv }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .sv }
  , { walsCode := "som", language := "Somali", iso := "som", value := .sv }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .sv }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .sv }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .sv }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .sv }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .sv }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .sv }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .sv }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noDominantOrder }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .sv }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .vs }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .sv }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .sv }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .sv }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .sv }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .sv }
  , { walsCode := "sku", language := "Suku", iso := "sub", value := .sv }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .sv }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .sv }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .sv }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .sv }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .sv }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .sv }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .noDominantOrder }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .sv }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .sv }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .sv }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .sv }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .sv }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .sv }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .vs }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .vs }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .sv }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .sv }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .sv }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .sv }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .sv }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .sv }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .sv }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .sv }
  , { walsCode := "tmg", language := "Tamagario", iso := "tcg", value := .sv }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .sv }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .vs }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .sv }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .sv }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .sv }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .sv }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .sv }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .sv }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .sv }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .sv }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .noDominantOrder }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .vs }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .sv }
  , { walsCode := "tsr", language := "Taushiro", iso := "trr", value := .vs }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .vs }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .sv }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .sv }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .vs }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .sv }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .sv }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .sv }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .sv }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .sv }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .vs }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .sv }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .sv }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .vs }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .vs }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .vs }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .vs }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .sv }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .sv }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .vs }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .sv }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .sv }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .sv }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .sv }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .sv }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .sv }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .vs }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .sv }
  , { walsCode := "tdi", language := "Tibetan (Dingri)", iso := "bod", value := .sv }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .sv }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .sv }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .sv }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .sv }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .sv }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .sv }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .sv }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .sv }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .sv }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .sv }
  , { walsCode := "tia", language := "Tima", iso := "tms", value := .sv }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .sv }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .vs }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .sv }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noDominantOrder }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .vs }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .sv }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .sv }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .sv }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .sv }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .vs }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .sv }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .noDominantOrder }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .sv }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .sv }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .sv }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .vs }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noDominantOrder }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .noDominantOrder }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .sv }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .vs }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .sv }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .sv }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .sv }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .vs }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .sv }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .sv }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .sv }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .sv }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .vs }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .sv }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .vs }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .sv }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .sv }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .sv }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .vs }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .sv }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .sv }
  , { walsCode := "tum", language := "Tumleo", iso := "tmq", value := .sv }
  , { walsCode := "tnb", language := "Tunebo", iso := "tuf", value := .sv }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .sv }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .sv }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .sv }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .sv }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .vs }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .sv }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .sv }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .noDominantOrder }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .sv }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .sv }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .vs }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .sv }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .sv }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .sv }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .vs }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noDominantOrder }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .sv }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .sv }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .sv }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .sv }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .sv }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .sv }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .sv }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .sv }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .sv }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .sv }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .sv }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .sv }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .sv }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .vs }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .sv }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .sv }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .sv }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .sv }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .sv }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .sv }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .noDominantOrder }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .sv }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .sv }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .sv }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .sv }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .sv }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .sv }
  , { walsCode := "wwa", language := "Waama", iso := "wwa", value := .sv }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .sv }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .sv }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .noDominantOrder }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .sv }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .sv }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noDominantOrder }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .sv }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .sv }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .sv }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .sv }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .sv }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .sv }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .sv }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .sv }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noDominantOrder }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .sv }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .sv }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .vs }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .noDominantOrder }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .sv }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .sv }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .noDominantOrder }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .vs }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .noDominantOrder }
  , { walsCode := "was", language := "Washo", iso := "was", value := .sv }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .sv }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .sv }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .vs }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .sv }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .sv }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .sv }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .vs }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .vs }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .vs }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .sv }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noDominantOrder }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .sv }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .sv }
  , { walsCode := "wn", language := "Wik Ngathana", iso := "wig", value := .sv }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noDominantOrder }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noDominantOrder }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .sv }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .sv }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .sv }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .sv }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .vs }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .sv }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .sv }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .vs }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .sv }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .sv }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .sv }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .sv }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .sv }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .sv }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .vs }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .sv }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .sv }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .sv }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .sv }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .sv }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .noDominantOrder }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .vs }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .sv }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .sv }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .sv }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .noDominantOrder }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .vs }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .sv }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .sv }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .sv }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .sv }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .sv }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .sv }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .sv }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .sv }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .vs }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .sv }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .sv }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .sv }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .sv }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .sv }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .sv }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .sv }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noDominantOrder }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .sv }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .sv }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .sv }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .sv }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .sv }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .vs }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .vs }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .vs }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .vs }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .sv }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .sv }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .sv }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .sv }
  , { walsCode := "zim", language := "Zimakani", iso := "zik", value := .sv }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .sv }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .vs }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .vs }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .sv }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .sv }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .sv }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .sv }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .sv }
  ]

/-- Complete WALS 82A dataset (1496 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1496 := by native_decide

theorem count_sv :
    (allData.filter (·.value == .sv)).length = 1192 := by native_decide
theorem count_vs :
    (allData.filter (·.value == .vs)).length = 194 := by native_decide
theorem count_noDominantOrder :
    (allData.filter (·.value == .noDominantOrder)).length = 110 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F82A
