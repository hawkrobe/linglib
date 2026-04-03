import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 88A: Order of Demonstrative and Noun
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 88A`.

Chapter 88, 1225 languages.
-/

namespace Core.WALS.F88A

/-- WALS 88A values. -/
inductive DemonstrativeNounOrder where
  | demonstrativeNoun  -- Demonstrative-Noun (542 languages)
  | nounDemonstrative  -- Noun-Demonstrative (562 languages)
  | demonstrativePrefix  -- Demonstrative prefix (9 languages)
  | demonstrativeSuffix  -- Demonstrative suffix (28 languages)
  | demonstrativeBeforeAndAfterNoun  -- Demonstrative before and after Noun (17 languages)
  | mixed  -- Mixed (67 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint DemonstrativeNounOrder) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .nounDemonstrative }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .demonstrativeNoun }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .demonstrativeNoun }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .nounDemonstrative }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .nounDemonstrative }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .nounDemonstrative }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .demonstrativeNoun }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .demonstrativeNoun }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .demonstrativeNoun }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .nounDemonstrative }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .nounDemonstrative }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .nounDemonstrative }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .demonstrativeNoun }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .nounDemonstrative }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .nounDemonstrative }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .demonstrativePrefix }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .nounDemonstrative }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .nounDemonstrative }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .nounDemonstrative }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .demonstrativeSuffix }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .mixed }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .demonstrativeNoun }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .nounDemonstrative }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .nounDemonstrative }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .nounDemonstrative }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .nounDemonstrative }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .demonstrativeNoun }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .demonstrativeNoun }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .demonstrativeNoun }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .demonstrativeNoun }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .nounDemonstrative }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .nounDemonstrative }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .demonstrativeNoun }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .demonstrativeNoun }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .nounDemonstrative }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .demonstrativeNoun }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .nounDemonstrative }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .nounDemonstrative }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .demonstrativeNoun }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .nounDemonstrative }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .demonstrativeNoun }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .demonstrativeNoun }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .nounDemonstrative }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .nounDemonstrative }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .demonstrativeNoun }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .nounDemonstrative }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .nounDemonstrative }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .nounDemonstrative }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .nounDemonstrative }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .nounDemonstrative }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .demonstrativeNoun }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .nounDemonstrative }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .demonstrativeNoun }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .demonstrativeSuffix }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .nounDemonstrative }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .nounDemonstrative }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .demonstrativeNoun }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .demonstrativeNoun }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .nounDemonstrative }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .demonstrativeNoun }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .nounDemonstrative }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .mixed }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .mixed }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .demonstrativeNoun }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .demonstrativeNoun }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .mixed }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .demonstrativeNoun }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .nounDemonstrative }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .demonstrativeNoun }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .demonstrativeNoun }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .demonstrativeNoun }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .demonstrativeNoun }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .nounDemonstrative }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .nounDemonstrative }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .nounDemonstrative }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .nounDemonstrative }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .demonstrativeNoun }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .demonstrativeNoun }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .demonstrativeNoun }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .nounDemonstrative }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .demonstrativeNoun }
  , { walsCode := "ats", language := "Atsugewi", iso := "atw", value := .demonstrativeNoun }
  , { walsCode := "au", language := "Au", iso := "avt", value := .nounDemonstrative }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .demonstrativeNoun }
  , { walsCode := "avk", language := "Avikam", iso := "avi", value := .nounDemonstrative }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .nounDemonstrative }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .demonstrativeNoun }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .demonstrativeNoun }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .demonstrativeNoun }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .nounDemonstrative }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .demonstrativeNoun }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .nounDemonstrative }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .demonstrativeNoun }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .nounDemonstrative }
  , { walsCode := "bgs", language := "Baga Sitemu", iso := "bsp", value := .nounDemonstrative }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .nounDemonstrative }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .nounDemonstrative }
  , { walsCode := "bdw", language := "Baham", iso := "bdw", value := .nounDemonstrative }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .nounDemonstrative }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .nounDemonstrative }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .nounDemonstrative }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .nounDemonstrative }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .nounDemonstrative }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .demonstrativeNoun }
  , { walsCode := "blg", language := "Balangao", iso := "blw", value := .demonstrativeNoun }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .nounDemonstrative }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .nounDemonstrative }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .demonstrativeNoun }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .mixed }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .demonstrativeNoun }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .demonstrativeNoun }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .nounDemonstrative }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .demonstrativeNoun }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .nounDemonstrative }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .nounDemonstrative }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .demonstrativeNoun }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .demonstrativeNoun }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .nounDemonstrative }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .nounDemonstrative }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .demonstrativeNoun }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .nounDemonstrative }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .demonstrativeNoun }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .nounDemonstrative }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .nounDemonstrative }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .nounDemonstrative }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .demonstrativeNoun }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .nounDemonstrative }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .nounDemonstrative }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .demonstrativeNoun }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .mixed }
  , { walsCode := "bse", language := "Berber (Ayt Seghrouchen Middle Atlas)", iso := "rif", value := .nounDemonstrative }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .nounDemonstrative }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .demonstrativeNoun }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .mixed }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .nounDemonstrative }
  , { walsCode := "bsi", language := "Berber (Siwa)", iso := "siz", value := .nounDemonstrative }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .nounDemonstrative }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .demonstrativeSuffix }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .demonstrativeNoun }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .nounDemonstrative }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .nounDemonstrative }
  , { walsCode := "bnr", language := "Bilinarra", iso := "nbj", value := .demonstrativeNoun }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .nounDemonstrative }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .demonstrativeNoun }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .nounDemonstrative }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .nounDemonstrative }
  , { walsCode := "big", language := "Binga", iso := "yul", value := .demonstrativeSuffix }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .nounDemonstrative }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .mixed }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .demonstrativeNoun }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .nounDemonstrative }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .demonstrativeNoun }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .mixed }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .demonstrativeNoun }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .nounDemonstrative }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .demonstrativeNoun }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .nounDemonstrative }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .nounDemonstrative }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .nounDemonstrative }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .demonstrativeNoun }
  , { walsCode := "bub", language := "Bubi", iso := "bvb", value := .demonstrativeNoun }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .nounDemonstrative }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .nounDemonstrative }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .nounDemonstrative }
  , { walsCode := "buj", language := "Bujeba", iso := "nmg", value := .nounDemonstrative }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .demonstrativeNoun }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .nounDemonstrative }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .nounDemonstrative }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .demonstrativeNoun }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .demonstrativeNoun }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .demonstrativeNoun }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .nounDemonstrative }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .demonstrativeSuffix }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .demonstrativeNoun }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .nounDemonstrative }
  , { walsCode := "dok", language := "Bwele", iso := "ngc", value := .nounDemonstrative }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .demonstrativeNoun }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .demonstrativeNoun }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .demonstrativeNoun }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .demonstrativeNoun }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .nounDemonstrative }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .demonstrativeNoun }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .demonstrativeNoun }
  , { walsCode := "car", language := "Carib", iso := "car", value := .demonstrativeNoun }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .demonstrativeNoun }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .demonstrativeNoun }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .demonstrativeNoun }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .demonstrativeNoun }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .demonstrativeNoun }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .nounDemonstrative }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .demonstrativeNoun }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .nounDemonstrative }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .demonstrativeNoun }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .demonstrativeNoun }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .demonstrativeNoun }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .nounDemonstrative }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .nounDemonstrative }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .demonstrativeNoun }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .demonstrativeNoun }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .mixed }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .demonstrativeNoun }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .demonstrativeNoun }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .nounDemonstrative }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .mixed }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .demonstrativeNoun }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .demonstrativeNoun }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .nounDemonstrative }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .nounDemonstrative }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .nounDemonstrative }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .mixed }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .demonstrativeNoun }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .demonstrativeNoun }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .demonstrativeNoun }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .nounDemonstrative }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .demonstrativeNoun }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .nounDemonstrative }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .nounDemonstrative }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .demonstrativeNoun }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .demonstrativePrefix }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .demonstrativeNoun }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .demonstrativeNoun }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .nounDemonstrative }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .demonstrativeNoun }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .demonstrativePrefix }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .demonstrativeNoun }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .mixed }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .demonstrativeNoun }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .nounDemonstrative }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .demonstrativeNoun }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .demonstrativeNoun }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .nounDemonstrative }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .demonstrativeNoun }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .demonstrativeNoun }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .nounDemonstrative }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .nounDemonstrative }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .nounDemonstrative }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .nounDemonstrative }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .nounDemonstrative }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .demonstrativeNoun }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .nounDemonstrative }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .nounDemonstrative }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .demonstrativeNoun }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .demonstrativeNoun }
  , { walsCode := "day", language := "Day", iso := "dai", value := .nounDemonstrative }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .nounDemonstrative }
  , { walsCode := "des", language := "Desano", iso := "des", value := .demonstrativeNoun }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .nounDemonstrative }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .mixed }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .demonstrativeNoun }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .demonstrativeNoun }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .nounDemonstrative }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .nounDemonstrative }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .demonstrativeNoun }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .nounDemonstrative }
  , { walsCode := "dng", language := "Ding", iso := "diz", value := .nounDemonstrative }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .demonstrativeSuffix }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .nounDemonstrative }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .demonstrativeNoun }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .mixed }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .demonstrativeNoun }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .demonstrativeNoun }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .demonstrativeNoun }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .demonstrativeNoun }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .demonstrativeNoun }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .mixed }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .demonstrativeNoun }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .nounDemonstrative }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .nounDemonstrative }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .nounDemonstrative }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .nounDemonstrative }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .demonstrativeNoun }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .demonstrativeNoun }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .demonstrativeNoun }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .nounDemonstrative }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .demonstrativeNoun }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .nounDemonstrative }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .nounDemonstrative }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .demonstrativeNoun }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .demonstrativeNoun }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .demonstrativeNoun }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .nounDemonstrative }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .nounDemonstrative }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .nounDemonstrative }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .nounDemonstrative }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .mixed }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .nounDemonstrative }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .demonstrativeNoun }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .nounDemonstrative }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .nounDemonstrative }
  , { walsCode := "eng", language := "English", iso := "eng", value := .demonstrativeNoun }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .demonstrativeNoun }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .nounDemonstrative }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .demonstrativeNoun }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .demonstrativeNoun }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .demonstrativeNoun }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .nounDemonstrative }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .nounDemonstrative }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .nounDemonstrative }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .nounDemonstrative }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .demonstrativeNoun }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .nounDemonstrative }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .demonstrativeNoun }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .nounDemonstrative }
  , { walsCode := "for", language := "Fore", iso := "for", value := .demonstrativeNoun }
  , { walsCode := "fre", language := "French", iso := "fra", value := .demonstrativeNoun }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .demonstrativeNoun }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .nounDemonstrative }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .demonstrativeNoun }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .nounDemonstrative }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .nounDemonstrative }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .nounDemonstrative }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .demonstrativeNoun }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .nounDemonstrative }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .demonstrativeNoun }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .demonstrativeNoun }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .demonstrativeNoun }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .nounDemonstrative }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .demonstrativeNoun }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .nounDemonstrative }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .nounDemonstrative }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .nounDemonstrative }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .nounDemonstrative }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .demonstrativeNoun }
  , { walsCode := "ger", language := "German", iso := "deu", value := .demonstrativeNoun }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .demonstrativeNoun }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .nounDemonstrative }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .nounDemonstrative }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .demonstrativeNoun }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .nounDemonstrative }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .nounDemonstrative }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .nounDemonstrative }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .demonstrativeNoun }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .demonstrativeNoun }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nounDemonstrative }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .demonstrativeNoun }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .mixed }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .demonstrativeNoun }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .demonstrativeNoun }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .demonstrativeNoun }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .demonstrativeNoun }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .demonstrativeSuffix }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .nounDemonstrative }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .demonstrativeNoun }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .nounDemonstrative }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .nounDemonstrative }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .nounDemonstrative }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .demonstrativeNoun }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .nounDemonstrative }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .mixed }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .demonstrativeNoun }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .demonstrativeNoun }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .demonstrativeNoun }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .nounDemonstrative }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .nounDemonstrative }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .demonstrativeNoun }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .demonstrativeNoun }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .demonstrativeNoun }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .demonstrativeNoun }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .nounDemonstrative }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .demonstrativeNoun }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .nounDemonstrative }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .demonstrativeNoun }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .nounDemonstrative }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .nounDemonstrative }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .mixed }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .demonstrativeNoun }
  , { walsCode := "hwr", language := "Hawrami", iso := "hac", value := .demonstrativeNoun }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .nounDemonstrative }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .demonstrativeNoun }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .nounDemonstrative }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .demonstrativeNoun }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .nounDemonstrative }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .nounDemonstrative }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .demonstrativeNoun }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .demonstrativeNoun }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .nounDemonstrative }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .nounDemonstrative }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .nounDemonstrative }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .mixed }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .demonstrativeNoun }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .demonstrativeNoun }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .mixed }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .demonstrativeNoun }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .demonstrativeNoun }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .demonstrativeNoun }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .nounDemonstrative }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .demonstrativeNoun }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .demonstrativeNoun }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .demonstrativeNoun }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .demonstrativeNoun }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .nounDemonstrative }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .nounDemonstrative }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .nounDemonstrative }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .nounDemonstrative }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .demonstrativeNoun }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .nounDemonstrative }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .demonstrativeNoun }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .demonstrativeNoun }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .nounDemonstrative }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .demonstrativeNoun }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .nounDemonstrative }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .nounDemonstrative }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .nounDemonstrative }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .demonstrativeNoun }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .demonstrativeSuffix }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .nounDemonstrative }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .demonstrativeNoun }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .mixed }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .nounDemonstrative }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .demonstrativeSuffix }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .demonstrativeNoun }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .nounDemonstrative }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .demonstrativeNoun }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .nounDemonstrative }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .nounDemonstrative }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .nounDemonstrative }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .demonstrativeNoun }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .demonstrativeNoun }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .demonstrativeNoun }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .demonstrativeNoun }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .nounDemonstrative }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .nounDemonstrative }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .nounDemonstrative }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .demonstrativeNoun }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .nounDemonstrative }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .nounDemonstrative }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .mixed }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .nounDemonstrative }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .demonstrativeNoun }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .demonstrativeNoun }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .demonstrativeNoun }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .demonstrativeNoun }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .demonstrativeNoun }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .mixed }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .nounDemonstrative }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .nounDemonstrative }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .nounDemonstrative }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .demonstrativeNoun }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .demonstrativeNoun }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .demonstrativeNoun }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .mixed }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .nounDemonstrative }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .nounDemonstrative }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .nounDemonstrative }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .demonstrativeNoun }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .nounDemonstrative }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .demonstrativeNoun }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .demonstrativeNoun }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .nounDemonstrative }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .demonstrativeNoun }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .nounDemonstrative }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .nounDemonstrative }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .nounDemonstrative }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .nounDemonstrative }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .demonstrativeNoun }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .demonstrativeNoun }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .nounDemonstrative }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .nounDemonstrative }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .nounDemonstrative }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .demonstrativeNoun }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .demonstrativeNoun }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .demonstrativeNoun }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .demonstrativeNoun }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .nounDemonstrative }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .nounDemonstrative }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .nounDemonstrative }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .nounDemonstrative }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .demonstrativeNoun }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .demonstrativeNoun }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .demonstrativeNoun }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .demonstrativeNoun }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .nounDemonstrative }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .nounDemonstrative }
  , { walsCode := "ktm", language := "Kathlamet", iso := "", value := .demonstrativeNoun }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .nounDemonstrative }
  , { walsCode := "ktu", language := "Katu", iso := "", value := .nounDemonstrative }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .nounDemonstrative }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .mixed }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .nounDemonstrative }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .demonstrativeNoun }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .nounDemonstrative }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .demonstrativeNoun }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .nounDemonstrative }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .nounDemonstrative }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .demonstrativeNoun }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .demonstrativeNoun }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .nounDemonstrative }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .demonstrativeNoun }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .demonstrativeNoun }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .demonstrativeNoun }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .demonstrativeNoun }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .demonstrativeNoun }
  ]

private def allData_1 : List (Datapoint DemonstrativeNounOrder) :=
  [ { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .nounDemonstrative }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .nounDemonstrative }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .demonstrativeNoun }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .demonstrativeNoun }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .demonstrativeNoun }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .nounDemonstrative }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .nounDemonstrative }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .nounDemonstrative }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .nounDemonstrative }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .nounDemonstrative }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .demonstrativeSuffix }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .demonstrativeNoun }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .demonstrativeNoun }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .demonstrativeNoun }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .demonstrativeNoun }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .demonstrativePrefix }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .nounDemonstrative }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .nounDemonstrative }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .nounDemonstrative }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .demonstrativeNoun }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .demonstrativeNoun }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .demonstrativeNoun }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .demonstrativeNoun }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .nounDemonstrative }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .nounDemonstrative }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .nounDemonstrative }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .nounDemonstrative }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .demonstrativeNoun }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .demonstrativeNoun }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .demonstrativeNoun }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .demonstrativeNoun }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .nounDemonstrative }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .nounDemonstrative }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .nounDemonstrative }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .nounDemonstrative }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .demonstrativePrefix }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .nounDemonstrative }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .demonstrativeNoun }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .demonstrativeNoun }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .demonstrativeNoun }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .nounDemonstrative }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .demonstrativeNoun }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .demonstrativeNoun }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .nounDemonstrative }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .demonstrativeNoun }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .nounDemonstrative }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .nounDemonstrative }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .demonstrativeNoun }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .nounDemonstrative }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .nounDemonstrative }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .nounDemonstrative }
  , { walsCode := "krz", language := "Kryz", iso := "kry", value := .demonstrativeNoun }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .nounDemonstrative }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .mixed }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .demonstrativeNoun }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .demonstrativeNoun }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .nounDemonstrative }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .nounDemonstrative }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .demonstrativeNoun }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .mixed }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .demonstrativeNoun }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .nounDemonstrative }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .nounDemonstrative }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .demonstrativeNoun }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .nounDemonstrative }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .nounDemonstrative }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .demonstrativeNoun }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .demonstrativeNoun }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .demonstrativeNoun }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .nounDemonstrative }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .demonstrativeNoun }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .nounDemonstrative }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .nounDemonstrative }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .demonstrativeNoun }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .demonstrativeNoun }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .demonstrativeSuffix }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .nounDemonstrative }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .mixed }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .nounDemonstrative }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .nounDemonstrative }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .mixed }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .demonstrativeNoun }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .mixed }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .nounDemonstrative }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .nounDemonstrative }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .nounDemonstrative }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .nounDemonstrative }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .demonstrativeNoun }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .nounDemonstrative }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .nounDemonstrative }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .demonstrativeNoun }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .nounDemonstrative }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .nounDemonstrative }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .nounDemonstrative }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .demonstrativeNoun }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .demonstrativeNoun }
  , { walsCode := "les", language := "Lese", iso := "les", value := .nounDemonstrative }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .nounDemonstrative }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .nounDemonstrative }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .demonstrativeNoun }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .nounDemonstrative }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .demonstrativeNoun }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .demonstrativeNoun }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .mixed }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .nounDemonstrative }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .nounDemonstrative }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .demonstrativeNoun }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .nounDemonstrative }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .demonstrativeNoun }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .nounDemonstrative }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .nounDemonstrative }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .nounDemonstrative }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .nounDemonstrative }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .nounDemonstrative }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .nounDemonstrative }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .nounDemonstrative }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .demonstrativeNoun }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .mixed }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .demonstrativeNoun }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .nounDemonstrative }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .nounDemonstrative }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .nounDemonstrative }
  , { walsCode := "luy", language := "Luyia", iso := "luy", value := .nounDemonstrative }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .mixed }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .nounDemonstrative }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .nounDemonstrative }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .demonstrativeNoun }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .nounDemonstrative }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .demonstrativeNoun }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .mixed }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .demonstrativeNoun }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .nounDemonstrative }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .demonstrativeNoun }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .nounDemonstrative }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .demonstrativeNoun }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .demonstrativeNoun }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .nounDemonstrative }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .demonstrativeNoun }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .nounDemonstrative }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .nounDemonstrative }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .demonstrativeNoun }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .nounDemonstrative }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .mixed }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .nounDemonstrative }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .demonstrativeNoun }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .nounDemonstrative }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .nounDemonstrative }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .demonstrativeNoun }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .demonstrativeNoun }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .demonstrativeNoun }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .nounDemonstrative }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .demonstrativeNoun }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .nounDemonstrative }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .demonstrativeSuffix }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .demonstrativeNoun }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .demonstrativeNoun }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .nounDemonstrative }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .demonstrativeNoun }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .demonstrativeSuffix }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .nounDemonstrative }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .demonstrativeNoun }
  , { walsCode := "mgq", language := "Mango", iso := "mge", value := .nounDemonstrative }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .nounDemonstrative }
  , { walsCode := "mkq", language := "Mankon", iso := "nge", value := .nounDemonstrative }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .demonstrativeNoun }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .demonstrativeNoun }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .mixed }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .demonstrativeNoun }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .demonstrativeNoun }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .nounDemonstrative }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .demonstrativeNoun }
  , { walsCode := "mrc", language := "Marchha", iso := "rnp", value := .demonstrativeNoun }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .nounDemonstrative }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .nounDemonstrative }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .mixed }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .demonstrativeNoun }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .demonstrativeNoun }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .demonstrativeSuffix }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .demonstrativeNoun }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .nounDemonstrative }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .nounDemonstrative }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .demonstrativeNoun }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .nounDemonstrative }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .nounDemonstrative }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .demonstrativeSuffix }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .nounDemonstrative }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .nounDemonstrative }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .nounDemonstrative }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .nounDemonstrative }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .nounDemonstrative }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .nounDemonstrative }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .nounDemonstrative }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .nounDemonstrative }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .demonstrativeSuffix }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .nounDemonstrative }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .demonstrativeNoun }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .mixed }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .nounDemonstrative }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .demonstrativeNoun }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .nounDemonstrative }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .nounDemonstrative }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .nounDemonstrative }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .nounDemonstrative }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .demonstrativeNoun }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .demonstrativeNoun }
  , { walsCode := "mil", language := "Milang", iso := "", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .nounDemonstrative }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .nounDemonstrative }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .demonstrativeSuffix }
  , { walsCode := "mhl", language := "Miri (Hill):", iso := "mrg", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .demonstrativeNoun }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .demonstrativeNoun }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .demonstrativeNoun }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .demonstrativeNoun }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .demonstrativeNoun }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .nounDemonstrative }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .nounDemonstrative }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .nounDemonstrative }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .demonstrativeSuffix }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .nounDemonstrative }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .demonstrativeNoun }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .nounDemonstrative }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .demonstrativeNoun }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .nounDemonstrative }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .demonstrativeNoun }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .nounDemonstrative }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .nounDemonstrative }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .nounDemonstrative }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .demonstrativeSuffix }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .demonstrativeNoun }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .demonstrativeSuffix }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .nounDemonstrative }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .nounDemonstrative }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .nounDemonstrative }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .demonstrativeNoun }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .nounDemonstrative }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .nounDemonstrative }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .nounDemonstrative }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .demonstrativeNoun }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .nounDemonstrative }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .nounDemonstrative }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .nounDemonstrative }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .nounDemonstrative }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .demonstrativeNoun }
  , { walsCode := "mnz", language := "Munzombo", iso := "moj", value := .nounDemonstrative }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .nounDemonstrative }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .nounDemonstrative }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .nounDemonstrative }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .demonstrativeSuffix }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .nounDemonstrative }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .nounDemonstrative }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .demonstrativeNoun }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .nounDemonstrative }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .demonstrativeNoun }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .nounDemonstrative }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .nounDemonstrative }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .nounDemonstrative }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .mixed }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .nounDemonstrative }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .demonstrativeNoun }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .demonstrativeNoun }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .demonstrativeNoun }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .demonstrativeNoun }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .demonstrativeNoun }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .nounDemonstrative }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .nounDemonstrative }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .demonstrativeNoun }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .nounDemonstrative }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .demonstrativeNoun }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .nounDemonstrative }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .demonstrativeSuffix }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .demonstrativeNoun }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .demonstrativeNoun }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .nounDemonstrative }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .demonstrativeNoun }
  , { walsCode := "nau", language := "Nauruan", iso := "nau", value := .mixed }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .demonstrativeNoun }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .demonstrativeNoun }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .nounDemonstrative }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .nounDemonstrative }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .demonstrativeNoun }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .nounDemonstrative }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .nounDemonstrative }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .nounDemonstrative }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .nounDemonstrative }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .nounDemonstrative }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .nounDemonstrative }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .demonstrativeNoun }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .nounDemonstrative }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .demonstrativeNoun }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .demonstrativeNoun }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .demonstrativeNoun }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .demonstrativeNoun }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .demonstrativeNoun }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .nounDemonstrative }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .demonstrativeNoun }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .nounDemonstrative }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .demonstrativeNoun }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .nounDemonstrative }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .nounDemonstrative }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .demonstrativeNoun }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .nounDemonstrative }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .demonstrativeNoun }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .nounDemonstrative }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .nounDemonstrative }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .demonstrativeNoun }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .demonstrativeNoun }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .nounDemonstrative }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .nounDemonstrative }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .nounDemonstrative }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .nounDemonstrative }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .nounDemonstrative }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .demonstrativeNoun }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .demonstrativeNoun }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .nounDemonstrative }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .nounDemonstrative }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .demonstrativeNoun }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .nounDemonstrative }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .nounDemonstrative }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .nounDemonstrative }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .demonstrativeNoun }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .nounDemonstrative }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .nounDemonstrative }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .demonstrativeNoun }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .mixed }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .nounDemonstrative }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .demonstrativeNoun }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .demonstrativeNoun }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .nounDemonstrative }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .nounDemonstrative }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .demonstrativeNoun }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .nounDemonstrative }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .nounDemonstrative }
  , { walsCode := "nus", language := "Nusu", iso := "nuf", value := .nounDemonstrative }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .demonstrativeNoun }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .nounDemonstrative }
  , { walsCode := "nng", language := "Nyanga", iso := "nyj", value := .nounDemonstrative }
  , { walsCode := "nyr", language := "Nyangumarda", iso := "nna", value := .demonstrativeNoun }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .demonstrativeNoun }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .nounDemonstrative }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .demonstrativeNoun }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .nounDemonstrative }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .demonstrativeNoun }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .nounDemonstrative }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .demonstrativeNoun }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .nounDemonstrative }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .demonstrativeNoun }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .nounDemonstrative }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .demonstrativeNoun }
  , { walsCode := "one", language := "One", iso := "aun", value := .mixed }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .demonstrativeNoun }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .demonstrativePrefix }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .nounDemonstrative }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .nounDemonstrative }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .nounDemonstrative }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .nounDemonstrative }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .nounDemonstrative }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .mixed }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .demonstrativeNoun }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .demonstrativeNoun }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .nounDemonstrative }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .mixed }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .demonstrativeNoun }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .demonstrativeNoun }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .demonstrativeNoun }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .nounDemonstrative }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .demonstrativeNoun }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .demonstrativeNoun }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .demonstrativeNoun }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .demonstrativeNoun }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .demonstrativeNoun }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .demonstrativeNoun }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .demonstrativeNoun }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .nounDemonstrative }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .demonstrativeNoun }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .nounDemonstrative }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .demonstrativeNoun }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .demonstrativeNoun }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .demonstrativePrefix }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .demonstrativeNoun }
  , { walsCode := "ppc", language := "Piapoco", iso := "pio", value := .demonstrativeNoun }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .demonstrativeNoun }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .demonstrativeNoun }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .demonstrativeNoun }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .nounDemonstrative }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .demonstrativeNoun }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .nounDemonstrative }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .demonstrativeNoun }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .nounDemonstrative }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .nounDemonstrative }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .demonstrativeSuffix }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .demonstrativeNoun }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .demonstrativeNoun }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .demonstrativeNoun }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .nounDemonstrative }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .demonstrativeNoun }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .demonstrativeNoun }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .nounDemonstrative }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .demonstrativeNoun }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .demonstrativeNoun }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .demonstrativeNoun }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .demonstrativeNoun }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .demonstrativeNoun }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .nounDemonstrative }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .demonstrativeNoun }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .demonstrativeNoun }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .demonstrativeNoun }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .nounDemonstrative }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .demonstrativeNoun }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .nounDemonstrative }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .nounDemonstrative }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .mixed }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .demonstrativeNoun }
  , { walsCode := "rmb", language := "Rembarnga", iso := "rmb", value := .demonstrativeNoun }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .demonstrativeNoun }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .demonstrativeNoun }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .demonstrativeNoun }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .demonstrativeNoun }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .mixed }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .demonstrativeNoun }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .nounDemonstrative }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .nounDemonstrative }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .nounDemonstrative }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .nounDemonstrative }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .demonstrativeNoun }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .nounDemonstrative }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .nounDemonstrative }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .nounDemonstrative }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .demonstrativeNoun }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .demonstrativeNoun }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .nounDemonstrative }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .nounDemonstrative }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .demonstrativeNoun }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .demonstrativeNoun }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .nounDemonstrative }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .mixed }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .demonstrativeNoun }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .nounDemonstrative }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .nounDemonstrative }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .demonstrativeNoun }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .demonstrativeNoun }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .demonstrativeNoun }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .demonstrativeNoun }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .demonstrativeNoun }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .demonstrativeNoun }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .demonstrativeSuffix }
  , { walsCode := "sec", language := "Secoya", iso := "sey", value := .demonstrativeNoun }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .nounDemonstrative }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .nounDemonstrative }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .nounDemonstrative }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .demonstrativeNoun }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .nounDemonstrative }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .demonstrativeNoun }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .nounDemonstrative }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .demonstrativeNoun }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .demonstrativeNoun }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .demonstrativeNoun }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .nounDemonstrative }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .nounDemonstrative }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .demonstrativeNoun }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .demonstrativeNoun }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .nounDemonstrative }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .demonstrativeNoun }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .demonstrativeNoun }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .demonstrativeNoun }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .demonstrativeNoun }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .nounDemonstrative }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .demonstrativeNoun }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .mixed }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .demonstrativeNoun }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .mixed }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .nounDemonstrative }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .demonstrativeNoun }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .nounDemonstrative }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .demonstrativeNoun }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .demonstrativeNoun }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .demonstrativeNoun }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .nounDemonstrative }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .nounDemonstrative }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .demonstrativeNoun }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .nounDemonstrative }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .demonstrativeNoun }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .demonstrativeNoun }
  , { walsCode := "so", language := "So", iso := "teu", value := .nounDemonstrative }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .nounDemonstrative }
  , { walsCode := "som", language := "Somali", iso := "som", value := .demonstrativeSuffix }
  , { walsCode := "sge", language := "Songe", iso := "sop", value := .mixed }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .nounDemonstrative }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .nounDemonstrative }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .nounDemonstrative }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .mixed }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .demonstrativeNoun }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .demonstrativeNoun }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .demonstrativeNoun }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .nounDemonstrative }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .nounDemonstrative }
  ]

private def allData_2 : List (Datapoint DemonstrativeNounOrder) :=
  [ { walsCode := "sud", language := "Sudest", iso := "tgo", value := .nounDemonstrative }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .nounDemonstrative }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .demonstrativeNoun }
  , { walsCode := "sku", language := "Suku", iso := "sub", value := .nounDemonstrative }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .nounDemonstrative }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .nounDemonstrative }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .demonstrativeNoun }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .demonstrativeNoun }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .nounDemonstrative }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .demonstrativeNoun }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .demonstrativeNoun }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .nounDemonstrative }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .demonstrativeNoun }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .mixed }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .demonstrativeNoun }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .mixed }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .demonstrativeNoun }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .nounDemonstrative }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .demonstrativeNoun }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .demonstrativeNoun }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .demonstrativeNoun }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .nounDemonstrative }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .demonstrativeNoun }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .nounDemonstrative }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .demonstrativeNoun }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .nounDemonstrative }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .demonstrativeNoun }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .demonstrativeNoun }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .demonstrativeNoun }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .demonstrativeNoun }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .demonstrativeNoun }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .demonstrativeSuffix }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .demonstrativeNoun }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .demonstrativeSuffix }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .nounDemonstrative }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .demonstrativeNoun }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .demonstrativeNoun }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .demonstrativeNoun }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .nounDemonstrative }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .mixed }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .demonstrativeNoun }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .nounDemonstrative }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .nounDemonstrative }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .nounDemonstrative }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .nounDemonstrative }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .nounDemonstrative }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .demonstrativeNoun }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .demonstrativeNoun }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .demonstrativeNoun }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .nounDemonstrative }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .nounDemonstrative }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .nounDemonstrative }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .nounDemonstrative }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .nounDemonstrative }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .nounDemonstrative }
  , { walsCode := "thd", language := "Thadou", iso := "tcz", value := .demonstrativeNoun }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .nounDemonstrative }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .demonstrativeNoun }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .demonstrativeNoun }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .demonstrativeNoun }
  , { walsCode := "tdi", language := "Tibetan (Dingri)", iso := "bod", value := .mixed }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .nounDemonstrative }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .nounDemonstrative }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .nounDemonstrative }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .demonstrativeNoun }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .nounDemonstrative }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .nounDemonstrative }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .demonstrativeNoun }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .mixed }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .nounDemonstrative }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .nounDemonstrative }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .nounDemonstrative }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .demonstrativeNoun }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .nounDemonstrative }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .nounDemonstrative }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .demonstrativeNoun }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .nounDemonstrative }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .demonstrativeNoun }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .demonstrativeNoun }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .nounDemonstrative }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .nounDemonstrative }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .nounDemonstrative }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .demonstrativeNoun }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .nounDemonstrative }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .nounDemonstrative }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .nounDemonstrative }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .demonstrativeSuffix }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .demonstrativeNoun }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .demonstrativeNoun }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .demonstrativeNoun }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .nounDemonstrative }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .demonstrativeNoun }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .demonstrativeNoun }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .demonstrativeNoun }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .demonstrativeNoun }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .nounDemonstrative }
  , { walsCode := "tgo", language := "Tsogo", iso := "tsv", value := .nounDemonstrative }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .demonstrativeNoun }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .nounDemonstrative }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .nounDemonstrative }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .nounDemonstrative }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .demonstrativeNoun }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .nounDemonstrative }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .nounDemonstrative }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .demonstrativeNoun }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .demonstrativeNoun }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .nounDemonstrative }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .nounDemonstrative }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .nounDemonstrative }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .demonstrativeNoun }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .demonstrativeNoun }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .nounDemonstrative }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .demonstrativeNoun }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .nounDemonstrative }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .demonstrativeNoun }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .demonstrativeNoun }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .mixed }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .demonstrativePrefix }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .demonstrativeNoun }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .demonstrativeNoun }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .demonstrativeNoun }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .nounDemonstrative }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .nounDemonstrative }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .demonstrativeNoun }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .nounDemonstrative }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .demonstrativeNoun }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .nounDemonstrative }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .demonstrativeNoun }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .nounDemonstrative }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .demonstrativeNoun }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .mixed }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .demonstrativeNoun }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .nounDemonstrative }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .demonstrativeNoun }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .demonstrativeNoun }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .demonstrativeNoun }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .demonstrativeNoun }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .nounDemonstrative }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .nounDemonstrative }
  , { walsCode := "vif", language := "Vili", iso := "vif", value := .nounDemonstrative }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .nounDemonstrative }
  , { walsCode := "wwa", language := "Waama", iso := "wwa", value := .nounDemonstrative }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .nounDemonstrative }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .demonstrativeNoun }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .nounDemonstrative }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .demonstrativeNoun }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .demonstrativeNoun }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .demonstrativeNoun }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .mixed }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .demonstrativeNoun }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .demonstrativeNoun }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .demonstrativeNoun }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .demonstrativeNoun }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .demonstrativeNoun }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .nounDemonstrative }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .mixed }
  , { walsCode := "was", language := "Washo", iso := "was", value := .demonstrativeNoun }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .nounDemonstrative }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .nounDemonstrative }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .demonstrativeNoun }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .nounDemonstrative }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .demonstrativeNoun }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .nounDemonstrative }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .demonstrativeNoun }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .nounDemonstrative }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .nounDemonstrative }
  , { walsCode := "wn", language := "Wik Ngathana", iso := "wig", value := .nounDemonstrative }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .demonstrativeNoun }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .demonstrativeNoun }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .nounDemonstrative }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .demonstrativeNoun }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .nounDemonstrative }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .demonstrativeNoun }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .nounDemonstrative }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .nounDemonstrative }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .demonstrativeNoun }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .demonstrativeNoun }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .mixed }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .nounDemonstrative }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .demonstrativeNoun }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .mixed }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .demonstrativeNoun }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .nounDemonstrative }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .demonstrativeNoun }
  , { walsCode := "yns", language := "Yansi", iso := "yns", value := .nounDemonstrative }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .demonstrativeNoun }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .nounDemonstrative }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .nounDemonstrative }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .demonstrativeNoun }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .nounDemonstrative }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .nounDemonstrative }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .nounDemonstrative }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .mixed }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .nounDemonstrative }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .demonstrativeNoun }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .demonstrativeNoun }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .mixed }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .demonstrativeNoun }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .nounDemonstrative }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .demonstrativeNoun }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .demonstrativeNoun }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .demonstrativeNoun }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .demonstrativePrefix }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .demonstrativeNoun }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .nounDemonstrative }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .nounDemonstrative }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .demonstrativeNoun }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .demonstrativeNoun }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .demonstrativeBeforeAndAfterNoun }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .nounDemonstrative }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .nounDemonstrative }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .nounDemonstrative }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .nounDemonstrative }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .nounDemonstrative }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .demonstrativeNoun }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .demonstrativeNoun }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .demonstrativeNoun }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .demonstrativeNoun }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .mixed }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .demonstrativeNoun }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .demonstrativeNoun }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .demonstrativeNoun }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .demonstrativeNoun }
  ]

/-- Complete WALS 88A dataset (1225 languages). -/
def allData : List (Datapoint DemonstrativeNounOrder) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1225 := by native_decide

theorem count_demonstrativeNoun :
    (allData.filter (·.value == .demonstrativeNoun)).length = 542 := by native_decide
theorem count_nounDemonstrative :
    (allData.filter (·.value == .nounDemonstrative)).length = 562 := by native_decide
theorem count_demonstrativePrefix :
    (allData.filter (·.value == .demonstrativePrefix)).length = 9 := by native_decide
theorem count_demonstrativeSuffix :
    (allData.filter (·.value == .demonstrativeSuffix)).length = 28 := by native_decide
theorem count_demonstrativeBeforeAndAfterNoun :
    (allData.filter (·.value == .demonstrativeBeforeAndAfterNoun)).length = 17 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 67 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F88A
