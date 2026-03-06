/-!
# WALS Feature 83A: Order of Object and Verb
@cite{dryer-2013a}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 83A`.

Chapter 83, 1518 languages.
-/

namespace Core.WALS.F83A

/-- WALS 83A values. -/
inductive ObjectVerbOrder where
  | ov  -- OV (712 languages)
  | vo  -- VO (705 languages)
  | noDominantOrder  -- No dominant order (101 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 83A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ObjectVerbOrder
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .vo }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .noDominantOrder }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .vo }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .vo }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .ov }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .ov }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .vo }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .ov }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .ov }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .vo }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noDominantOrder }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .vo }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .ov }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .vo }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .ov }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .vo }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noDominantOrder }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .ov }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .vo }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .ov }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .noDominantOrder }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .vo }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .ov }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .ov }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .vo }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .vo }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .vo }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .ov }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .vo }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .noDominantOrder }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .vo }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .ov }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .ov }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noDominantOrder }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .vo }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .ov }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .vo }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .vo }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .ov }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .ov }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .ov }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .vo }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .vo }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .vo }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .ov }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .ov }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .ov }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .ov }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .vo }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .vo }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .ov }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .vo }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .ov }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .vo }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .ov }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .ov }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .vo }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .ov }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .vo }
  , { walsCode := "ayi", language := "Anyi", iso := "any", value := .vo }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .noDominantOrder }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .vo }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .ov }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .ov }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .ov }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .ov }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .ov }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noDominantOrder }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .ov }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .vo }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .vo }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .vo }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .vo }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .vo }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .vo }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .vo }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .ov }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .vo }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .vo }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .ov }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .ov }
  , { walsCode := "ari", language := "Aribwatsa", iso := "laz", value := .vo }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noDominantOrder }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .ov }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .vo }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .vo }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .ov }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .ov }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .ov }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .ov }
  , { walsCode := "atm", language := "Atacameño", iso := "kuz", value := .ov }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .ov }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .vo }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .ov }
  , { walsCode := "au", language := "Au", iso := "avt", value := .vo }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .ov }
  , { walsCode := "avk", language := "Avikam", iso := "avi", value := .vo }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .noDominantOrder }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .ov }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .ov }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .ov }
  , { walsCode := "awy", language := "Awyi", iso := "auw", value := .ov }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .vo }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .ov }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .vo }
  , { walsCode := "ayr", language := "Ayoreo", iso := "ayo", value := .vo }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .ov }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .ov }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .vo }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .vo }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .noDominantOrder }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .ov }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .vo }
  , { walsCode := "bgs", language := "Baga Sitemu", iso := "bsp", value := .vo }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .vo }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .vo }
  , { walsCode := "bdw", language := "Baham", iso := "bdw", value := .ov }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .vo }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .vo }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .vo }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .vo }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .vo }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .vo }
  , { walsCode := "blg", language := "Balangao", iso := "blw", value := .vo }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .vo }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .vo }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .ov }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .ov }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .ov }
  , { walsCode := "bgz", language := "Banggi", iso := "bdg", value := .vo }
  , { walsCode := "bgm", language := "Bangime", iso := "dba", value := .ov }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .vo }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .vo }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .ov }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .vo }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .ov }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .ov }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .vo }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .ov }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .vo }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .ov }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .ov }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .vo }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .ov }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .vo }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .ov }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .ov }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .vo }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .vo }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .vo }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .ov }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .ov }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .ov }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .ov }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .vo }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .noDominantOrder }
  , { walsCode := "blu", language := "Bena-Lulua", iso := "lua", value := .vo }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .ov }
  , { walsCode := "brq", language := "Bera", iso := "brf", value := .vo }
  , { walsCode := "bse", language := "Berber (Ayt Seghrouchen Middle Atlas)", iso := "rif", value := .vo }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .vo }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .vo }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .vo }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .vo }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .ov }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .vo }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .ov }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .ov }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .ov }
  , { walsCode := "bhu", language := "Bhumij", iso := "unr", value := .ov }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .vo }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .vo }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .vo }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .ov }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .ov }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .vo }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .vo }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .ov }
  , { walsCode := "big", language := "Binga", iso := "yul", value := .vo }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .vo }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .ov }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .vo }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .vo }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .ov }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .vo }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .ov }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .vo }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .ov }
  , { walsCode := "boq", language := "Bokar", iso := "", value := .ov }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .ov }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .vo }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .vo }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .ov }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .vo }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .ov }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .vo }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .vo }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .vo }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .ov }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .ov }
  , { walsCode := "bub", language := "Bubi", iso := "bvb", value := .vo }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .vo }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .vo }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .vo }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .ov }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .ov }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .ov }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .vo }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .vo }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .vo }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .ov }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .vo }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .noDominantOrder }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .ov }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .ov }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .ov }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .vo }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .vo }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .ov }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .ov }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .vo }
  , { walsCode := "dok", language := "Bwele", iso := "ngc", value := .vo }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .ov }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .ov }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .vo }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .ov }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .vo }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .noDominantOrder }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .ov }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .ov }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .vo }
  , { walsCode := "car", language := "Carib", iso := "car", value := .ov }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .ov }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .ov }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .vo }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .ov }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .noDominantOrder }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .ov }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .vo }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .vo }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .vo }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .ov }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .noDominantOrder }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .vo }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .vo }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .ov }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .vo }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .ov }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .ov }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .vo }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .vo }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .ov }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .ov }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .noDominantOrder }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .ov }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .ov }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .vo }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .ov }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .ov }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .ov }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .ov }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .vo }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .vo }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .vo }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .vo }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .vo }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .ov }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .ov }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .vo }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .ov }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .ov }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .ov }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .vo }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .vo }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .vo }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .vo }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .ov }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .vo }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .ov }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .ov }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .ov }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .vo }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .vo }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .ov }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .vo }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noDominantOrder }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .vo }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .vo }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .vo }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .vo }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .vo }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .ov }
  , { walsCode := "cua", language := "Cua", iso := "cua", value := .vo }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .ov }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .ov }
  , { walsCode := "cuc", language := "Cuica", iso := "", value := .vo }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .ov }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .vo }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .vo }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .noDominantOrder }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .ov }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .vo }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .vo }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .ov }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .noDominantOrder }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .ov }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .ov }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .vo }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .ov }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .ov }
  , { walsCode := "day", language := "Day", iso := "dai", value := .vo }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .vo }
  , { walsCode := "des", language := "Desano", iso := "des", value := .ov }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .ov }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .ov }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .noDominantOrder }
  , { walsCode := "dhb", language := "Dharumbal", iso := "xgm", value := .ov }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .ov }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .vo }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .ov }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .ov }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .ov }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .ov }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noDominantOrder }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .vo }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .ov }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .ov }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .noDominantOrder }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .ov }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .noDominantOrder }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .noDominantOrder }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .ov }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .ov }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .ov }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .ov }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .vo }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .vo }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .noDominantOrder }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .ov }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .vo }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .vo }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .vo }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .vo }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .ov }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .vo }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .ov }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .ov }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .ov }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noDominantOrder }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .ov }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .ov }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .vo }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .ov }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .vo }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .vo }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .ov }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .ov }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .vo }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .vo }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .ov }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .noDominantOrder }
  , { walsCode := "ene", language := "Enets", iso := "", value := .ov }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .vo }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .vo }
  , { walsCode := "eng", language := "English", iso := "eng", value := .vo }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .ov }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .vo }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .ov }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .vo }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .vo }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .ov }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .ov }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .ov }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .vo }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .vo }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .ov }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .vo }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .vo }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .ov }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .ov }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .vo }
  , { walsCode := "for", language := "Fore", iso := "for", value := .ov }
  , { walsCode := "fre", language := "French", iso := "fra", value := .vo }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .noDominantOrder }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .vo }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .ov }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .ov }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .vo }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .vo }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .vo }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .ov }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .vo }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .ov }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .ov }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .ov }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .ov }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .ov }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .vo }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .vo }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .ov }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .vo }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .vo }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .vo }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .vo }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .ov }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noDominantOrder }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .noDominantOrder }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .ov }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .noDominantOrder }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .vo }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .vo }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .ov }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .vo }
  , { walsCode := "gog", language := "Gogodala", iso := "ggw", value := .ov }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .vo }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .ov }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .ov }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .ov }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .ov }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .vo }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .vo }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .ov }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .ov }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .vo }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .vo }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .noDominantOrder }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .vo }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .vo }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .ov }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .ov }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .ov }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .vo }
  , { walsCode := "gir", language := "Gula Iro", iso := "glj", value := .vo }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .ov }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .noDominantOrder }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .vo }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .vo }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .vo }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .noDominantOrder }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .noDominantOrder }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .noDominantOrder }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .ov }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .ov }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noDominantOrder }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .vo }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .ov }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .vo }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .ov }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .vo }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .vo }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .vo }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .ov }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .ov }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .ov }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .ov }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .vo }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .vo }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .vo }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .vo }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .ov }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .vo }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .vo }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .vo }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .vo }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .vo }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .ov }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .vo }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .ov }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .ov }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .vo }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .ov }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .vo }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .ov }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .vo }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .vo }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .ov }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .ov }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .ov }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .vo }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .vo }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .ov }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .ov }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .ov }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .vo }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .vo }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .ov }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .ov }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .noDominantOrder }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .ov }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .vo }
  , { walsCode := "iat", language := "Iatmul", iso := "ian", value := .ov }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .ov }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .vo }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .vo }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .noDominantOrder }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .ov }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .ov }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .vo }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .vo }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .vo }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "igb", language := "Igbo", iso := "ibo", value := .vo }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .vo }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .vo }
  , { walsCode := "iha", language := "Iha", iso := "ihp", value := .ov }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .ov }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .vo }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .ov }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .vo }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .vo }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .ov }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .noDominantOrder }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .vo }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .vo }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .ov }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .vo }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .ov }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .ov }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .vo }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .vo }
  , { walsCode := "isi", language := "Isirawa", iso := "srl", value := .ov }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .vo }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .ov }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .vo }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .vo }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .ov }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .vo }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .vo }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .vo }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .vo }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .ov }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .vo }
  , { walsCode := "jad", language := "Jad", iso := "jda", value := .ov }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .vo }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .noDominantOrder }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .ov }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .ov }
  , { walsCode := "jrw", language := "Jarawa (in Andamans)", iso := "anq", value := .ov }
  , { walsCode := "jwr", language := "Jarawara", iso := "jaa", value := .ov }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .noDominantOrder }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .ov }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .ov }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .ov }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .ov }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .ov }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .vo }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .vo }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .vo }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .ov }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .ov }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .vo }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .vo }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .ov }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .vo }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .vo }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .vo }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .vo }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .ov }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .ov }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .ov }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .ov }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .vo }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .ov }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .ov }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .ov }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .ov }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .ov }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .ov }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .vo }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .vo }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .ov }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .ov }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .noDominantOrder }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .vo }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .vo }
  , { walsCode := "xns", language := "Kanashi", iso := "xns", value := .ov }
  , { walsCode := "kbu", language := "Kanembu", iso := "kbl", value := .ov }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .ov }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .ov }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .ov }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .ov }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .vo }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .vo }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .ov }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .ov }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .ov }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .noDominantOrder }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .vo }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .vo }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .vo }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .vo }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .ov }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noDominantOrder }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .ov }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .vo }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .vo }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .vo }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .vo }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .ov }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .vo }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .vo }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noDominantOrder }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .ov }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .vo }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .ov }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noDominantOrder }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .vo }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .ov }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .vo }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .vo }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .ov }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .ov }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .vo }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .ov }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .ov }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .ov }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .ov }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .ov }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .ov }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .ov }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .ov }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .ov }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .vo }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .vo }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .vo }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .ov }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .vo }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .vo }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .vo }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .ov }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .vo }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .ov }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .vo }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .ov }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .vo }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .ov }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .vo }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .ov }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .vo }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .vo }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noDominantOrder }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .ov }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .noDominantOrder }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .vo }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .vo }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .ov }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .ov }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .vo }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .ov }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .ov }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .ov }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .vo }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .ov }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .ov }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .ov }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .vo }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .ov }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .vo }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .vo }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .vo }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .ov }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .vo }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .ov }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .ov }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .vo }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .ov }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .vo }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .ov }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .ov }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .vo }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .ov }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .vo }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .ov }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .ov }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .ov }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .ov }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .vo }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .vo }
  , { walsCode := "krz", language := "Kryz", iso := "kry", value := .ov }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .ov }
  , { walsCode := "kkq", language := "Kuikúro", iso := "kui", value := .ov }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .ov }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .ov }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .ov }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .ov }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .ov }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .ov }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .ov }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .vo }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .ov }
  , { walsCode := "kus", language := "Kusunda", iso := "kgg", value := .ov }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .vo }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .ov }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .ov }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .ov }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .vo }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .vo }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .vo }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .ov }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .ov }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .ov }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .ov }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .ov }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .ov }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .ov }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .vo }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .vo }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .vo }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .vo }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .ov }
  , { walsCode := "laf", language := "Lafofa", iso := "laf", value := .ov }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .vo }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .ov }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .ov }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .ov }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .ov }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .ov }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .vo }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .vo }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .ov }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .vo }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .vo }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .vo }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .vo }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .vo }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .ov }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .vo }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .ov }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .vo }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .vo }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .vo }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .noDominantOrder }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .vo }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .vo }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .vo }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .noDominantOrder }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .ov }
  , { walsCode := "les", language := "Lese", iso := "les", value := .noDominantOrder }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .vo }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .vo }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .ov }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .ov }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .vo }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .ov }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .noDominantOrder }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .vo }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .vo }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .ov }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .vo }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .noDominantOrder }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .vo }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .vo }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .vo }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .vo }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .ov }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .vo }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .vo }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noDominantOrder }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .noDominantOrder }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .vo }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .ov }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .vo }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .vo }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .vo }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .vo }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .vo }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noDominantOrder }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .vo }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .ov }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .vo }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .vo }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .ov }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .vo }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .vo }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .vo }
  , { walsCode := "mgh", language := "Magahi", iso := "mag", value := .ov }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .ov }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .ov }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .ov }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .vo }
  , { walsCode := "mrs", language := "Mairasi", iso := "zrs", value := .ov }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .ov }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .ov }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .vo }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .vo }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .vo }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .ov }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .ov }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .vo }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .vo }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .vo }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .ov }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .ov }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .vo }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .vo }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .ov }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .vo }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .vo }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .vo }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .vo }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .vo }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .ov }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .ov }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .ov }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .ov }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .vo }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .ov }
  , { walsCode := "mem", language := "Manem", iso := "jet", value := .ov }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .vo }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .ov }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .vo }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .vo }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .ov }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .ov }
  , { walsCode := "mkq", language := "Mankon", iso := "nge", value := .vo }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .ov }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .vo }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .ov }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .vo }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .vo }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .noDominantOrder }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .ov }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .ov }
  , { walsCode := "mrc", language := "Marchha", iso := "rnp", value := .ov }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .ov }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .vo }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .ov }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .ov }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .ov }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .ov }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .vo }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .ov }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .vo }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .ov }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .vo }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .vo }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .ov }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .noDominantOrder }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .ov }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .ov }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .ov }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .vo }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .ov }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .vo }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .ov }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .vo }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .vo }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .vo }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .noDominantOrder }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .vo }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .vo }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .vo }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .vo }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .vo }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .vo }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .vo }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .vo }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .vo }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .vo }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .vo }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .vo }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .ov }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .ov }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .ov }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .ov }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .noDominantOrder }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .ov }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .ov }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .vo }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .ov }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .vo }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .ov }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .ov }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .ov }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .ov }
  , { walsCode := "mil", language := "Milang", iso := "", value := .ov }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .vo }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noDominantOrder }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .ov }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .ov }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .ov }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noDominantOrder }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .noDominantOrder }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .vo }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .vo }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .vo }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .vo }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .vo }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .vo }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .ov }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .vo }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .vo }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .vo }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .ov }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .noDominantOrder }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .vo }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .ov }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .ov }
  , { walsCode := "mqf", language := "Momuna", iso := "mqf", value := .ov }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .vo }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .vo }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .vo }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .ov }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .ov }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .ov }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noDominantOrder }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .ov }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .vo }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .vo }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .ov }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .vo }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .vo }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .noDominantOrder }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .vo }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .ov }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .ov }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .vo }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .vo }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .vo }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .vo }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .ov }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .ov }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .vo }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .vo }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .vo }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .ov }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .ov }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .vo }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .vo }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .vo }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .ov }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .vo }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .noDominantOrder }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .vo }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .vo }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .vo }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .vo }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .vo }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .vo }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .vo }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .ov }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .vo }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .ov }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .ov }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .ov }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .ov }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .ov }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .vo }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .vo }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .vo }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .vo }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .ov }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .vo }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .vo }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .ov }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .ov }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .ov }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .vo }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .vo }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .ov }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .ov }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .ov }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .ov }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .ov }
  , { walsCode := "nau", language := "Nauruan", iso := "nau", value := .vo }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .ov }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .vo }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .vo }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .ov }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .vo }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .vo }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .vo }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .vo }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .vo }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .ov }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .ov }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .vo }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .ov }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .ov }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .ov }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .ov }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .ov }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .noDominantOrder }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noDominantOrder }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .ov }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .vo }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .ov }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noDominantOrder }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .ov }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .vo }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .ov }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .ov }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .ov }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .noDominantOrder }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .vo }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .vo }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .vo }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noDominantOrder }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .ov }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .vo }
  , { walsCode := "nbe", language := "Ngombe", iso := "ngc", value := .vo }
  ]

private def allData_2 : List Datapoint :=
  [ { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .vo }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .vo }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .ov }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .noDominantOrder }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .vo }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .vo }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .ov }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .vo }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .vo }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .vo }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .ov }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .vo }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .vo }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .vo }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .ov }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .ov }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .vo }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .vo }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .vo }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .vo }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .vo }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .vo }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .ov }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .ov }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .noDominantOrder }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .vo }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noDominantOrder }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .ov }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .vo }
  , { walsCode := "nus", language := "Nusu", iso := "nuf", value := .ov }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .vo }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .ov }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .vo }
  , { walsCode := "nng", language := "Nyanga", iso := "nyj", value := .vo }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .ov }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .vo }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .ov }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .ov }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .vo }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .vo }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .vo }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .vo }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .vo }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .ov }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .vo }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .ov }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .vo }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .ov }
  , { walsCode := "one", language := "One", iso := "aun", value := .vo }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .vo }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .ov }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .ov }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .ov }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .ov }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .ov }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .ov }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .ov }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .ov }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .ov }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .ov }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .ov }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .vo }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .vo }
  , { walsCode := "owi", language := "Owininga", iso := "owi", value := .ov }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .vo }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .vo }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .vo }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .ov }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .vo }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .vo }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .vo }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .vo }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .vo }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .noDominantOrder }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .vo }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .vo }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .ov }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .noDominantOrder }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .vo }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .ov }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .vo }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .vo }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .ov }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .ov }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .vo }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noDominantOrder }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .ov }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .vo }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .ov }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .ov }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .vo }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .ov }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .vo }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .ov }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .ov }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .ov }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .ov }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .noDominantOrder }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .vo }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .vo }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .vo }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .noDominantOrder }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .vo }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .vo }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .ov }
  , { walsCode := "pmn", language := "Pomo (Northern)", iso := "pej", value := .ov }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .ov }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .vo }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .vo }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .vo }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .ov }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .vo }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .ov }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .ov }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .vo }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .ov }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .ov }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .ov }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .ov }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .ov }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .ov }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .vo }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .vo }
  , { walsCode := "ral", language := "Ralte", iso := "ral", value := .ov }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .ov }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .ov }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .ov }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .vo }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .ov }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .ov }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .ov }
  , { walsCode := "rmb", language := "Rembarnga", iso := "rmb", value := .ov }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .ov }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .ov }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .ov }
  , { walsCode := "ria", language := "Riantana", iso := "ran", value := .ov }
  , { walsCode := "rik", language := "Rikbaktsa", iso := "rkb", value := .ov }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .vo }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .noDominantOrder }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .vo }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .vo }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .vo }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .vo }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .vo }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .vo }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .vo }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .vo }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .vo }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .ov }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .ov }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .vo }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .vo }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .vo }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .ov }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .vo }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .vo }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .vo }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .ov }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .vo }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .ov }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .vo }
  , { walsCode := "nmd", language := "Samo", iso := "smq", value := .ov }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .vo }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .ov }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .vo }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .vo }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .ov }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .ov }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .ov }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .vo }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .ov }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .vo }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .ov }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .ov }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .ov }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .vo }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .vo }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .vo }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .ov }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .ov }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .ov }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .ov }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .vo }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .ov }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noDominantOrder }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .vo }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .ov }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .vo }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .ov }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .vo }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .ov }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .vo }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .vo }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .ov }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .vo }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .vo }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .ov }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .ov }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .vo }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .ov }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .ov }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .ov }
  , { walsCode := "smp", language := "Shompen", iso := "sii", value := .vo }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .vo }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .ov }
  , { walsCode := "ryu", language := "Shuri", iso := "ryu", value := .ov }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .vo }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .ov }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .vo }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .ov }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .ov }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .ov }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .ov }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .vo }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .ov }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .ov }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .vo }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .ov }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .vo }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .ov }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .ov }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .vo }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .vo }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .vo }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .ov }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .ov }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .vo }
  , { walsCode := "so", language := "So", iso := "teu", value := .vo }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .vo }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .ov }
  , { walsCode := "som", language := "Somali", iso := "som", value := .ov }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .ov }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .vo }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .ov }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .vo }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .vo }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .vo }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .ov }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .vo }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .ov }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .vo }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .vo }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .vo }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .vo }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .ov }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .ov }
  , { walsCode := "sku", language := "Suku", iso := "sub", value := .vo }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .vo }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .vo }
  , { walsCode := "slg", language := "Sulung", iso := "suv", value := .ov }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .vo }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .ov }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .ov }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .vo }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .vo }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .vo }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .vo }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .ov }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .ov }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .vo }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .ov }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .vo }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .vo }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .vo }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .ov }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .ov }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .ov }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .ov }
  , { walsCode := "tal", language := "Talinga", iso := "tlj", value := .vo }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .ov }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .ov }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .vo }
  , { walsCode := "tmg", language := "Tamagario", iso := "tcg", value := .ov }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .ov }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .vo }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .ov }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .ov }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .vo }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .ov }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .ov }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .ov }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .ov }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .ov }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .vo }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .vo }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .ov }
  , { walsCode := "tsr", language := "Taushiro", iso := "trr", value := .vo }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .vo }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .ov }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .ov }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .vo }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .ov }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .ov }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .vo }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .vo }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .vo }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .vo }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .ov }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .vo }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .vo }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .vo }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .vo }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .vo }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .vo }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .ov }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .vo }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .vo }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .vo }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .vo }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .vo }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .ov }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .ov }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .vo }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .ov }
  , { walsCode := "tdi", language := "Tibetan (Dingri)", iso := "bod", value := .ov }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .ov }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .ov }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .ov }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .ov }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .noDominantOrder }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .vo }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .vo }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .ov }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .ov }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .ov }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .noDominantOrder }
  , { walsCode := "tia", language := "Tima", iso := "tms", value := .vo }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .ov }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .vo }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .ov }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .vo }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .ov }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .vo }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .vo }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noDominantOrder }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .vo }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .vo }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .ov }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .vo }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .ov }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .ov }
  , { walsCode := "tod", language := "Tod", iso := "sbu", value := .ov }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .vo }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .vo }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .vo }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .vo }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .vo }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .ov }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .ov }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .vo }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .vo }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noDominantOrder }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .ov }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .ov }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .ov }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .vo }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .ov }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .vo }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .vo }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .ov }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .ov }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .vo }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .vo }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .vo }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .ov }
  , { walsCode := "tum", language := "Tumleo", iso := "tmq", value := .vo }
  , { walsCode := "tnb", language := "Tunebo", iso := "tuf", value := .ov }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .ov }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .vo }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .ov }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .vo }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .vo }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .ov }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .ov }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .noDominantOrder }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .ov }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .ov }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .ov }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .ov }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .ov }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .ov }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .vo }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .vo }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .ov }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .ov }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .ov }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .ov }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .ov }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .vo }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .vo }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .vo }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .ov }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .ov }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .vo }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .ov }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .vo }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .ov }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .vo }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .ov }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .ov }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .ov }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .ov }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .ov }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .ov }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .ov }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .ov }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .ov }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .ov }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .vo }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .vo }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .vo }
  , { walsCode := "wwa", language := "Waama", iso := "wwa", value := .vo }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .ov }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .ov }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .ov }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .ov }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .vo }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .vo }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .ov }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .ov }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .ov }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .noDominantOrder }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .ov }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .ov }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .ov }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .vo }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noDominantOrder }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .vo }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .vo }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .vo }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .noDominantOrder }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .ov }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .vo }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .noDominantOrder }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .vo }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .noDominantOrder }
  , { walsCode := "was", language := "Washo", iso := "was", value := .ov }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .ov }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .ov }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .vo }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .ov }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .ov }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .ov }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .vo }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .vo }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .vo }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .vo }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .ov }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .vo }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .ov }
  , { walsCode := "wn", language := "Wik Ngathana", iso := "wig", value := .ov }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noDominantOrder }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noDominantOrder }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noDominantOrder }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .ov }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .ov }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .vo }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .vo }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .vo }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .ov }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .vo }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .ov }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .ov }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .vo }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .vo }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .ov }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .vo }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .ov }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .ov }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .ov }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .ov }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .ov }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .vo }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .vo }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .ov }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .ov }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .ov }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .vo }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .noDominantOrder }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .vo }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .ov }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .ov }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .ov }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .ov }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .ov }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .vo }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .vo }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .vo }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .vo }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .ov }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .vo }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .ov }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .ov }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .ov }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .vo }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noDominantOrder }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .ov }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noDominantOrder }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .ov }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .vo }
  ]

private def allData_3 : List Datapoint :=
  [ { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .vo }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .vo }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .vo }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .vo }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .vo }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .noDominantOrder }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .ov }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .ov }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .vo }
  , { walsCode := "zim", language := "Zimakani", iso := "zik", value := .ov }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .vo }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .vo }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .vo }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .vo }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .ov }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .ov }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .ov }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .ov }
  ]

/-- Complete WALS 83A dataset (1518 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1 ++ allData_2 ++ allData_3

-- Count verification
theorem total_count : allData.length = 1518 := by native_decide

theorem count_ov :
    (allData.filter (·.value == .ov)).length = 712 := by native_decide
theorem count_vo :
    (allData.filter (·.value == .vo)).length = 705 := by native_decide
theorem count_noDominantOrder :
    (allData.filter (·.value == .noDominantOrder)).length = 101 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F83A
