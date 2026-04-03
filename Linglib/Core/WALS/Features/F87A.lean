import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 87A: Order of Adjective and Noun
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 87A`.

Chapter 87, 1367 languages.
-/

namespace Core.WALS.F87A

/-- WALS 87A values. -/
inductive AdjectiveNounOrder where
  | adjectiveNoun  -- Adjective-Noun (373 languages)
  | nounAdjective  -- Noun-Adjective (879 languages)
  | noDominantOrder  -- No dominant order (110 languages)
  | onlyInternallyHeadedRelativeClauses  -- Only internally-headed relative clauses (5 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint AdjectiveNounOrder) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .nounAdjective }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .adjectiveNoun }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .nounAdjective }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .nounAdjective }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .nounAdjective }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noDominantOrder }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .nounAdjective }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .nounAdjective }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .nounAdjective }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .nounAdjective }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .nounAdjective }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .noDominantOrder }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .nounAdjective }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noDominantOrder }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .nounAdjective }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .nounAdjective }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .nounAdjective }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .adjectiveNoun }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .nounAdjective }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .nounAdjective }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .adjectiveNoun }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .nounAdjective }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .adjectiveNoun }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .adjectiveNoun }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .adjectiveNoun }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .adjectiveNoun }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .nounAdjective }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .nounAdjective }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .nounAdjective }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .nounAdjective }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .adjectiveNoun }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noDominantOrder }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .nounAdjective }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .adjectiveNoun }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .nounAdjective }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .nounAdjective }
  , { walsCode := "amm", language := "Ama", iso := "amm", value := .noDominantOrder }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .nounAdjective }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .nounAdjective }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .nounAdjective }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .adjectiveNoun }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .nounAdjective }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .nounAdjective }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .adjectiveNoun }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .noDominantOrder }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .nounAdjective }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .adjectiveNoun }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .adjectiveNoun }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .nounAdjective }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .nounAdjective }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .nounAdjective }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .nounAdjective }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .nounAdjective }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .nounAdjective }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .nounAdjective }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .nounAdjective }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .nounAdjective }
  , { walsCode := "ayi", language := "Anyi", iso := "any", value := .nounAdjective }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .nounAdjective }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .nounAdjective }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .nounAdjective }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .nounAdjective }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .nounAdjective }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .nounAdjective }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .nounAdjective }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .nounAdjective }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .nounAdjective }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .nounAdjective }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .nounAdjective }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .nounAdjective }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .nounAdjective }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .nounAdjective }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .nounAdjective }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .nounAdjective }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .nounAdjective }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .adjectiveNoun }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .nounAdjective }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .adjectiveNoun }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .adjectiveNoun }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .adjectiveNoun }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .nounAdjective }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .nounAdjective }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .nounAdjective }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .nounAdjective }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .nounAdjective }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .adjectiveNoun }
  , { walsCode := "atm", language := "Atacameño", iso := "kuz", value := .nounAdjective }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .noDominantOrder }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .adjectiveNoun }
  , { walsCode := "au", language := "Au", iso := "avt", value := .nounAdjective }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .adjectiveNoun }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .adjectiveNoun }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .adjectiveNoun }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .nounAdjective }
  , { walsCode := "awy", language := "Awyi", iso := "auw", value := .nounAdjective }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .nounAdjective }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .adjectiveNoun }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .nounAdjective }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .adjectiveNoun }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .nounAdjective }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .nounAdjective }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .noDominantOrder }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .nounAdjective }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .nounAdjective }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .nounAdjective }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .nounAdjective }
  , { walsCode := "bdw", language := "Baham", iso := "bdw", value := .nounAdjective }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .adjectiveNoun }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .nounAdjective }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .nounAdjective }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .adjectiveNoun }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .adjectiveNoun }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .nounAdjective }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .nounAdjective }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .nounAdjective }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .adjectiveNoun }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .nounAdjective }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .adjectiveNoun }
  , { walsCode := "bgm", language := "Bangime", iso := "dba", value := .nounAdjective }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .nounAdjective }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .nounAdjective }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .nounAdjective }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .nounAdjective }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .nounAdjective }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .adjectiveNoun }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noDominantOrder }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .nounAdjective }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .nounAdjective }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .nounAdjective }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .nounAdjective }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .nounAdjective }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .nounAdjective }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .adjectiveNoun }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .nounAdjective }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .nounAdjective }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .nounAdjective }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .nounAdjective }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .nounAdjective }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noDominantOrder }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .adjectiveNoun }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .adjectiveNoun }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .adjectiveNoun }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .nounAdjective }
  , { walsCode := "blu", language := "Bena-Lulua", iso := "lua", value := .nounAdjective }
  , { walsCode := "brq", language := "Bera", iso := "brf", value := .nounAdjective }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .nounAdjective }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .nounAdjective }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .nounAdjective }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .nounAdjective }
  , { walsCode := "bsi", language := "Berber (Siwa)", iso := "siz", value := .nounAdjective }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .nounAdjective }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .nounAdjective }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .adjectiveNoun }
  , { walsCode := "bhu", language := "Bhumij", iso := "unr", value := .adjectiveNoun }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .nounAdjective }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .nounAdjective }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .noDominantOrder }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .nounAdjective }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .nounAdjective }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .adjectiveNoun }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .nounAdjective }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .nounAdjective }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .noDominantOrder }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .adjectiveNoun }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .nounAdjective }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .nounAdjective }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .adjectiveNoun }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .nounAdjective }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .adjectiveNoun }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .nounAdjective }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .noDominantOrder }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .nounAdjective }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .noDominantOrder }
  , { walsCode := "boj", language := "Bori", iso := "adi", value := .noDominantOrder }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .adjectiveNoun }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .nounAdjective }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .nounAdjective }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .nounAdjective }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .adjectiveNoun }
  , { walsCode := "bub", language := "Bubi", iso := "bvb", value := .nounAdjective }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .nounAdjective }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .nounAdjective }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .noDominantOrder }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .nounAdjective }
  , { walsCode := "buj", language := "Bujeba", iso := "nmg", value := .nounAdjective }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .adjectiveNoun }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .nounAdjective }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .nounAdjective }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .nounAdjective }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .adjectiveNoun }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .noDominantOrder }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .adjectiveNoun }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .nounAdjective }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .nounAdjective }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .nounAdjective }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .adjectiveNoun }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .nounAdjective }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .nounAdjective }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .adjectiveNoun }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .adjectiveNoun }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .adjectiveNoun }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .nounAdjective }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .noDominantOrder }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .nounAdjective }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .nounAdjective }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .adjectiveNoun }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .nounAdjective }
  , { walsCode := "car", language := "Carib", iso := "car", value := .adjectiveNoun }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .nounAdjective }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .nounAdjective }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .nounAdjective }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .nounAdjective }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .nounAdjective }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .adjectiveNoun }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .adjectiveNoun }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .nounAdjective }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .adjectiveNoun }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .nounAdjective }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .nounAdjective }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .nounAdjective }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .nounAdjective }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .nounAdjective }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .adjectiveNoun }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .noDominantOrder }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .adjectiveNoun }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .nounAdjective }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .nounAdjective }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .adjectiveNoun }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .adjectiveNoun }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .noDominantOrder }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .adjectiveNoun }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .adjectiveNoun }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .nounAdjective }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .nounAdjective }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .nounAdjective }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .noDominantOrder }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .nounAdjective }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .nounAdjective }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .nounAdjective }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .nounAdjective }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .nounAdjective }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .adjectiveNoun }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .adjectiveNoun }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .nounAdjective }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .onlyInternallyHeadedRelativeClauses }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .adjectiveNoun }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .adjectiveNoun }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .adjectiveNoun }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .nounAdjective }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .adjectiveNoun }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .adjectiveNoun }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .nounAdjective }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .nounAdjective }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .adjectiveNoun }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .adjectiveNoun }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .nounAdjective }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .nounAdjective }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .nounAdjective }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .nounAdjective }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .adjectiveNoun }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .nounAdjective }
  , { walsCode := "cuc", language := "Cuica", iso := "", value := .noDominantOrder }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .nounAdjective }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .adjectiveNoun }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .nounAdjective }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .nounAdjective }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .nounAdjective }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .nounAdjective }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .nounAdjective }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .adjectiveNoun }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .nounAdjective }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .adjectiveNoun }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .adjectiveNoun }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .adjectiveNoun }
  , { walsCode := "day", language := "Day", iso := "dai", value := .nounAdjective }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .noDominantOrder }
  , { walsCode := "des", language := "Desano", iso := "des", value := .adjectiveNoun }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .adjectiveNoun }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .nounAdjective }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .adjectiveNoun }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .adjectiveNoun }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .nounAdjective }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .onlyInternallyHeadedRelativeClauses }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .nounAdjective }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .nounAdjective }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .nounAdjective }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .nounAdjective }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .nounAdjective }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .nounAdjective }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .noDominantOrder }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .noDominantOrder }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .nounAdjective }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .nounAdjective }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .noDominantOrder }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .noDominantOrder }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .adjectiveNoun }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .adjectiveNoun }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .nounAdjective }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .nounAdjective }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .nounAdjective }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .nounAdjective }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .nounAdjective }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .nounAdjective }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .nounAdjective }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .noDominantOrder }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .nounAdjective }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .adjectiveNoun }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .nounAdjective }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .nounAdjective }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .adjectiveNoun }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .nounAdjective }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .nounAdjective }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .nounAdjective }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .nounAdjective }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .nounAdjective }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .adjectiveNoun }
  , { walsCode := "els", language := "Elseng", iso := "mrf", value := .nounAdjective }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .nounAdjective }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .nounAdjective }
  , { walsCode := "ene", language := "Enets", iso := "", value := .adjectiveNoun }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .nounAdjective }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .nounAdjective }
  , { walsCode := "eng", language := "English", iso := "eng", value := .adjectiveNoun }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .nounAdjective }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .nounAdjective }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .nounAdjective }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .noDominantOrder }
  , { walsCode := "ess", language := "Esselen", iso := "esq", value := .adjectiveNoun }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .adjectiveNoun }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .adjectiveNoun }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .adjectiveNoun }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .nounAdjective }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .nounAdjective }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .nounAdjective }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .nounAdjective }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .adjectiveNoun }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .nounAdjective }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .noDominantOrder }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .nounAdjective }
  , { walsCode := "for", language := "Fore", iso := "for", value := .adjectiveNoun }
  , { walsCode := "fre", language := "French", iso := "fra", value := .nounAdjective }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .adjectiveNoun }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .nounAdjective }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .nounAdjective }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .nounAdjective }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .nounAdjective }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .nounAdjective }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .nounAdjective }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .nounAdjective }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .adjectiveNoun }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .nounAdjective }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .noDominantOrder }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .adjectiveNoun }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .adjectiveNoun }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .nounAdjective }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .nounAdjective }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .nounAdjective }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .nounAdjective }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .adjectiveNoun }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .adjectiveNoun }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .nounAdjective }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .nounAdjective }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .adjectiveNoun }
  , { walsCode := "ger", language := "German", iso := "deu", value := .adjectiveNoun }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .adjectiveNoun }
  , { walsCode := "gil", language := "Gilaki", iso := "glk", value := .adjectiveNoun }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .noDominantOrder }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .adjectiveNoun }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .nounAdjective }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .adjectiveNoun }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .nounAdjective }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .adjectiveNoun }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .nounAdjective }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .adjectiveNoun }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .nounAdjective }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .nounAdjective }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nounAdjective }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .adjectiveNoun }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .nounAdjective }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .nounAdjective }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .nounAdjective }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .noDominantOrder }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .nounAdjective }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .adjectiveNoun }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .nounAdjective }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .nounAdjective }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .adjectiveNoun }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .nounAdjective }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .nounAdjective }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .noDominantOrder }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .noDominantOrder }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .adjectiveNoun }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .nounAdjective }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .nounAdjective }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .nounAdjective }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .noDominantOrder }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .adjectiveNoun }
  , { walsCode := "gdb", language := "Gutob", iso := "gbj", value := .adjectiveNoun }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .nounAdjective }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .nounAdjective }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .nounAdjective }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .nounAdjective }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .nounAdjective }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .nounAdjective }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .nounAdjective }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .adjectiveNoun }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .nounAdjective }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .adjectiveNoun }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .noDominantOrder }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .nounAdjective }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .nounAdjective }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .adjectiveNoun }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .nounAdjective }
  , { walsCode := "hwr", language := "Hawrami", iso := "hac", value := .nounAdjective }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .nounAdjective }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .adjectiveNoun }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .nounAdjective }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .nounAdjective }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .nounAdjective }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .adjectiveNoun }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .nounAdjective }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .nounAdjective }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .noDominantOrder }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .adjectiveNoun }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .nounAdjective }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .nounAdjective }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .nounAdjective }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .nounAdjective }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .adjectiveNoun }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .nounAdjective }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .nounAdjective }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .adjectiveNoun }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .adjectiveNoun }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .nounAdjective }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .adjectiveNoun }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .adjectiveNoun }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .adjectiveNoun }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .adjectiveNoun }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .nounAdjective }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .adjectiveNoun }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .adjectiveNoun }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .nounAdjective }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .nounAdjective }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .nounAdjective }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .adjectiveNoun }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .nounAdjective }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .adjectiveNoun }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .adjectiveNoun }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .nounAdjective }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .nounAdjective }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .adjectiveNoun }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .nounAdjective }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .nounAdjective }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .nounAdjective }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .adjectiveNoun }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .nounAdjective }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .nounAdjective }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .nounAdjective }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .adjectiveNoun }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .nounAdjective }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .nounAdjective }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .nounAdjective }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .nounAdjective }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .adjectiveNoun }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .nounAdjective }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .nounAdjective }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .nounAdjective }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .nounAdjective }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .nounAdjective }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .nounAdjective }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .nounAdjective }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noDominantOrder }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .noDominantOrder }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .adjectiveNoun }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .nounAdjective }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .nounAdjective }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .noDominantOrder }
  , { walsCode := "jbt", language := "Jabutí", iso := "jbt", value := .nounAdjective }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .nounAdjective }
  , { walsCode := "jad", language := "Jad", iso := "jda", value := .nounAdjective }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .adjectiveNoun }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .noDominantOrder }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .nounAdjective }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .adjectiveNoun }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .adjectiveNoun }
  , { walsCode := "jrw", language := "Jarawa (in Andamans)", iso := "anq", value := .nounAdjective }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .adjectiveNoun }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .nounAdjective }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .nounAdjective }
  , { walsCode := "jin", language := "Jino", iso := "jiu", value := .nounAdjective }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .adjectiveNoun }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .adjectiveNoun }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .noDominantOrder }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .nounAdjective }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .nounAdjective }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .nounAdjective }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .adjectiveNoun }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .nounAdjective }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .nounAdjective }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .noDominantOrder }
  ]

private def allData_1 : List (Datapoint AdjectiveNounOrder) :=
  [ { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .nounAdjective }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .nounAdjective }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .nounAdjective }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .nounAdjective }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .nounAdjective }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .nounAdjective }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .nounAdjective }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .adjectiveNoun }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .nounAdjective }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .nounAdjective }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .nounAdjective }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .adjectiveNoun }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .nounAdjective }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .nounAdjective }
  , { walsCode := "kbo", language := "Kambot", iso := "kbx", value := .nounAdjective }
  , { walsCode := "kmi", language := "Kami", iso := "kcu", value := .nounAdjective }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .nounAdjective }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .noDominantOrder }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .noDominantOrder }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .adjectiveNoun }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .nounAdjective }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .nounAdjective }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .nounAdjective }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .noDominantOrder }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .nounAdjective }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .adjectiveNoun }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .noDominantOrder }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .nounAdjective }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .adjectiveNoun }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .nounAdjective }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .nounAdjective }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .nounAdjective }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .nounAdjective }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .noDominantOrder }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .nounAdjective }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .nounAdjective }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .adjectiveNoun }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .nounAdjective }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .nounAdjective }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .nounAdjective }
  , { walsCode := "ktu", language := "Katu", iso := "", value := .nounAdjective }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .nounAdjective }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .adjectiveNoun }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .nounAdjective }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .nounAdjective }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .adjectiveNoun }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .nounAdjective }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .adjectiveNoun }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .nounAdjective }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .adjectiveNoun }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .nounAdjective }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .adjectiveNoun }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .adjectiveNoun }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .adjectiveNoun }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .adjectiveNoun }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .adjectiveNoun }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .nounAdjective }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .nounAdjective }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .adjectiveNoun }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .nounAdjective }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .adjectiveNoun }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .nounAdjective }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .nounAdjective }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .adjectiveNoun }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .nounAdjective }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .nounAdjective }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .nounAdjective }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .nounAdjective }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .adjectiveNoun }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .nounAdjective }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .nounAdjective }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .nounAdjective }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .adjectiveNoun }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .nounAdjective }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .nounAdjective }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .nounAdjective }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .adjectiveNoun }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .adjectiveNoun }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .noDominantOrder }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .adjectiveNoun }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .nounAdjective }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .nounAdjective }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .nounAdjective }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .nounAdjective }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .nounAdjective }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .nounAdjective }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .nounAdjective }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .adjectiveNoun }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .adjectiveNoun }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .nounAdjective }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .nounAdjective }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .adjectiveNoun }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .adjectiveNoun }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .nounAdjective }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .nounAdjective }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .adjectiveNoun }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .adjectiveNoun }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .nounAdjective }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .adjectiveNoun }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .nounAdjective }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .adjectiveNoun }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .adjectiveNoun }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .nounAdjective }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .adjectiveNoun }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .nounAdjective }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .nounAdjective }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .nounAdjective }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .nounAdjective }
  , { walsCode := "krh", language := "Krahô", iso := "xra", value := .nounAdjective }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .nounAdjective }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .adjectiveNoun }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .nounAdjective }
  , { walsCode := "krz", language := "Kryz", iso := "kry", value := .adjectiveNoun }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .nounAdjective }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .nounAdjective }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .adjectiveNoun }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .nounAdjective }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .adjectiveNoun }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .nounAdjective }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .nounAdjective }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .nounAdjective }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .nounAdjective }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .onlyInternallyHeadedRelativeClauses }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .nounAdjective }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .nounAdjective }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .adjectiveNoun }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .nounAdjective }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .adjectiveNoun }
  , { walsCode := "kwm", language := "Kwami", iso := "ksq", value := .nounAdjective }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .nounAdjective }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .nounAdjective }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .nounAdjective }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .adjectiveNoun }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .noDominantOrder }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .adjectiveNoun }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .nounAdjective }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .nounAdjective }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .nounAdjective }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .nounAdjective }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .adjectiveNoun }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .nounAdjective }
  , { walsCode := "laf", language := "Lafofa", iso := "laf", value := .noDominantOrder }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .nounAdjective }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noDominantOrder }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noDominantOrder }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .adjectiveNoun }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .nounAdjective }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .nounAdjective }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .nounAdjective }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .nounAdjective }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .adjectiveNoun }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .nounAdjective }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .noDominantOrder }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .nounAdjective }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .nounAdjective }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .nounAdjective }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .nounAdjective }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .nounAdjective }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .adjectiveNoun }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .nounAdjective }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .nounAdjective }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .nounAdjective }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .nounAdjective }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .nounAdjective }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .nounAdjective }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .adjectiveNoun }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .nounAdjective }
  , { walsCode := "les", language := "Lese", iso := "les", value := .nounAdjective }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .nounAdjective }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .nounAdjective }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .adjectiveNoun }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .adjectiveNoun }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .adjectiveNoun }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .nounAdjective }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .adjectiveNoun }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .nounAdjective }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .nounAdjective }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .adjectiveNoun }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .nounAdjective }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .adjectiveNoun }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .nounAdjective }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .nounAdjective }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .nounAdjective }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .nounAdjective }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .nounAdjective }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .nounAdjective }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .nounAdjective }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .nounAdjective }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .nounAdjective }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .nounAdjective }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .noDominantOrder }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .nounAdjective }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .nounAdjective }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .nounAdjective }
  , { walsCode := "jlu", language := "Luwo", iso := "lwo", value := .nounAdjective }
  , { walsCode := "luy", language := "Luyia", iso := "luy", value := .nounAdjective }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .adjectiveNoun }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .nounAdjective }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .nounAdjective }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .nounAdjective }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .nounAdjective }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .adjectiveNoun }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .noDominantOrder }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .nounAdjective }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .nounAdjective }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .adjectiveNoun }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .nounAdjective }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .adjectiveNoun }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .nounAdjective }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .nounAdjective }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .adjectiveNoun }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .adjectiveNoun }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .nounAdjective }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noDominantOrder }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .nounAdjective }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .nounAdjective }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .nounAdjective }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .nounAdjective }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .nounAdjective }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .adjectiveNoun }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .nounAdjective }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .nounAdjective }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .adjectiveNoun }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .noDominantOrder }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .noDominantOrder }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .nounAdjective }
  , { walsCode := "mmw", language := "Mambwe", iso := "mgr", value := .nounAdjective }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .nounAdjective }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .nounAdjective }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .nounAdjective }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .noDominantOrder }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .adjectiveNoun }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .nounAdjective }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .adjectiveNoun }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .nounAdjective }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .nounAdjective }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .nounAdjective }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .nounAdjective }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .nounAdjective }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .adjectiveNoun }
  , { walsCode := "mgq", language := "Mango", iso := "mge", value := .nounAdjective }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .nounAdjective }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .nounAdjective }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .adjectiveNoun }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .adjectiveNoun }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .nounAdjective }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .adjectiveNoun }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .nounAdjective }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .nounAdjective }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .adjectiveNoun }
  , { walsCode := "mrc", language := "Marchha", iso := "rnp", value := .adjectiveNoun }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .nounAdjective }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .adjectiveNoun }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .nounAdjective }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .nounAdjective }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .nounAdjective }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .nounAdjective }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .nounAdjective }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .nounAdjective }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .nounAdjective }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .nounAdjective }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .nounAdjective }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .nounAdjective }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .nounAdjective }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .nounAdjective }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .nounAdjective }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .nounAdjective }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .adjectiveNoun }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .nounAdjective }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .adjectiveNoun }
  , { walsCode := "mzn", language := "Mazanderani", iso := "mzn", value := .adjectiveNoun }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .nounAdjective }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .nounAdjective }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .nounAdjective }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .nounAdjective }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .nounAdjective }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .nounAdjective }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .adjectiveNoun }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .nounAdjective }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .nounAdjective }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .nounAdjective }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .nounAdjective }
  , { walsCode := "mhk", language := "Mehek", iso := "nux", value := .nounAdjective }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .nounAdjective }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noDominantOrder }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .nounAdjective }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .nounAdjective }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .nounAdjective }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .noDominantOrder }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .nounAdjective }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .adjectiveNoun }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .nounAdjective }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .nounAdjective }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .nounAdjective }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .nounAdjective }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .nounAdjective }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .noDominantOrder }
  , { walsCode := "mil", language := "Milang", iso := "", value := .adjectiveNoun }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .nounAdjective }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .nounAdjective }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .nounAdjective }
  , { walsCode := "mhl", language := "Miri (Hill):", iso := "mrg", value := .nounAdjective }
  , { walsCode := "mir", language := "Miriwung", iso := "mep", value := .noDominantOrder }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .adjectiveNoun }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .nounAdjective }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noDominantOrder }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .adjectiveNoun }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .adjectiveNoun }
  , { walsCode := "mxa", language := "Mixtec (Atatlahuca)", iso := "mib", value := .nounAdjective }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .nounAdjective }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .nounAdjective }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .nounAdjective }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .nounAdjective }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .nounAdjective }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .nounAdjective }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .nounAdjective }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .nounAdjective }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .adjectiveNoun }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .noDominantOrder }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .nounAdjective }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .nounAdjective }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .nounAdjective }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .nounAdjective }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .nounAdjective }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .nounAdjective }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .nounAdjective }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .nounAdjective }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .nounAdjective }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .adjectiveNoun }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .nounAdjective }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .nounAdjective }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .noDominantOrder }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .nounAdjective }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .nounAdjective }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .nounAdjective }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .nounAdjective }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .nounAdjective }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .nounAdjective }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .nounAdjective }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .nounAdjective }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .nounAdjective }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .nounAdjective }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .adjectiveNoun }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .nounAdjective }
  , { walsCode := "mnz", language := "Munzombo", iso := "moj", value := .adjectiveNoun }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .nounAdjective }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .nounAdjective }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .nounAdjective }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .nounAdjective }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .adjectiveNoun }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .nounAdjective }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .nounAdjective }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .adjectiveNoun }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .adjectiveNoun }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .nounAdjective }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .nounAdjective }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .nounAdjective }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .nounAdjective }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .nounAdjective }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .nounAdjective }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .nounAdjective }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .noDominantOrder }
  , { walsCode := "nah", language := "Nahali", iso := "nll", value := .adjectiveNoun }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .nounAdjective }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .nounAdjective }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .noDominantOrder }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .nounAdjective }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .noDominantOrder }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .nounAdjective }
  , { walsCode := "nkk", language := "Nakkara", iso := "nck", value := .nounAdjective }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .nounAdjective }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .adjectiveNoun }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .nounAdjective }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .nounAdjective }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .nounAdjective }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .nounAdjective }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .nounAdjective }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .nounAdjective }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .nounAdjective }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .nounAdjective }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noDominantOrder }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .nounAdjective }
  , { walsCode := "nau", language := "Nauruan", iso := "nau", value := .nounAdjective }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .nounAdjective }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .nounAdjective }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .nounAdjective }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .nounAdjective }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .nounAdjective }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .nounAdjective }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .nounAdjective }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .nounAdjective }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .adjectiveNoun }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .nounAdjective }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .nounAdjective }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .adjectiveNoun }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .nounAdjective }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .adjectiveNoun }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .adjectiveNoun }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .adjectiveNoun }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .adjectiveNoun }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .nounAdjective }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .adjectiveNoun }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .nounAdjective }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .nounAdjective }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .nounAdjective }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .nounAdjective }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .nounAdjective }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .nounAdjective }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .nounAdjective }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .adjectiveNoun }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .nounAdjective }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .nounAdjective }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .noDominantOrder }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .nounAdjective }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .adjectiveNoun }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noDominantOrder }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .nounAdjective }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .nounAdjective }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .nounAdjective }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .nounAdjective }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .nounAdjective }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .adjectiveNoun }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .adjectiveNoun }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .adjectiveNoun }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .nounAdjective }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .nounAdjective }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .adjectiveNoun }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .noDominantOrder }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .nounAdjective }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .nounAdjective }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .nounAdjective }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .adjectiveNoun }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .nounAdjective }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .nounAdjective }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .adjectiveNoun }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .nounAdjective }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .nounAdjective }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .nounAdjective }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .nounAdjective }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .nounAdjective }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .nounAdjective }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .nounAdjective }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noDominantOrder }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .nounAdjective }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .nounAdjective }
  , { walsCode := "nus", language := "Nusu", iso := "nuf", value := .nounAdjective }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noDominantOrder }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .nounAdjective }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .nounAdjective }
  , { walsCode := "nng", language := "Nyanga", iso := "nyj", value := .nounAdjective }
  , { walsCode := "nyr", language := "Nyangumarda", iso := "nna", value := .noDominantOrder }
  , { walsCode := "nyh", language := "Nyiha", iso := "nih", value := .nounAdjective }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .nounAdjective }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .adjectiveNoun }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .adjectiveNoun }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .adjectiveNoun }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .adjectiveNoun }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .noDominantOrder }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .adjectiveNoun }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .adjectiveNoun }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .noDominantOrder }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .nounAdjective }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .nounAdjective }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .adjectiveNoun }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .nounAdjective }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .nounAdjective }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .nounAdjective }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .nounAdjective }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .nounAdjective }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .nounAdjective }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .nounAdjective }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .adjectiveNoun }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .adjectiveNoun }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .nounAdjective }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .adjectiveNoun }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .adjectiveNoun }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .nounAdjective }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .adjectiveNoun }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .nounAdjective }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .adjectiveNoun }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .nounAdjective }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .nounAdjective }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .nounAdjective }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .nounAdjective }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .noDominantOrder }
  , { walsCode := "png", language := "Pangwa", iso := "pbr", value := .nounAdjective }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .adjectiveNoun }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .noDominantOrder }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .nounAdjective }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .adjectiveNoun }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .nounAdjective }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .adjectiveNoun }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .nounAdjective }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .nounAdjective }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .adjectiveNoun }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .nounAdjective }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .nounAdjective }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .nounAdjective }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .nounAdjective }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .adjectiveNoun }
  ]

private def allData_2 : List (Datapoint AdjectiveNounOrder) :=
  [ { walsCode := "pip", language := "Pipil", iso := "ppl", value := .adjectiveNoun }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .nounAdjective }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .nounAdjective }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .nounAdjective }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .nounAdjective }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .noDominantOrder }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .nounAdjective }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .nounAdjective }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .nounAdjective }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .adjectiveNoun }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .nounAdjective }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .nounAdjective }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .adjectiveNoun }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .nounAdjective }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .nounAdjective }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .nounAdjective }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .adjectiveNoun }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .nounAdjective }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .nounAdjective }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .nounAdjective }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .adjectiveNoun }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .nounAdjective }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .adjectiveNoun }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .adjectiveNoun }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .adjectiveNoun }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .nounAdjective }
  , { walsCode := "rji", language := "Raji", iso := "rji", value := .noDominantOrder }
  , { walsCode := "ral", language := "Ralte", iso := "ral", value := .nounAdjective }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .nounAdjective }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .adjectiveNoun }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .nounAdjective }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .nounAdjective }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .nounAdjective }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .nounAdjective }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .nounAdjective }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .adjectiveNoun }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .adjectiveNoun }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .adjectiveNoun }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .adjectiveNoun }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .nounAdjective }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .nounAdjective }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .nounAdjective }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .nounAdjective }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .nounAdjective }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .noDominantOrder }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .nounAdjective }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .nounAdjective }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .nounAdjective }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .nounAdjective }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .adjectiveNoun }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .adjectiveNoun }
  , { walsCode := "saa", language := "Sa'a", iso := "apb", value := .nounAdjective }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .adjectiveNoun }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .nounAdjective }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .nounAdjective }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .nounAdjective }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noDominantOrder }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .nounAdjective }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .nounAdjective }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .nounAdjective }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .nounAdjective }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .adjectiveNoun }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .nounAdjective }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .adjectiveNoun }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .adjectiveNoun }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .nounAdjective }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .nounAdjective }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .nounAdjective }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .nounAdjective }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .adjectiveNoun }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .adjectiveNoun }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .adjectiveNoun }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .nounAdjective }
  , { walsCode := "sec", language := "Secoya", iso := "sey", value := .adjectiveNoun }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .nounAdjective }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .noDominantOrder }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .nounAdjective }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .adjectiveNoun }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .adjectiveNoun }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .nounAdjective }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .nounAdjective }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .nounAdjective }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .nounAdjective }
  , { walsCode := "sen", language := "Sena", iso := "seh", value := .nounAdjective }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .nounAdjective }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .adjectiveNoun }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .onlyInternallyHeadedRelativeClauses }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .nounAdjective }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .adjectiveNoun }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .nounAdjective }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .nounAdjective }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .nounAdjective }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .nounAdjective }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .adjectiveNoun }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noDominantOrder }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .nounAdjective }
  , { walsCode := "smp", language := "Shompen", iso := "sii", value := .adjectiveNoun }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .nounAdjective }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .adjectiveNoun }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .nounAdjective }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .adjectiveNoun }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .adjectiveNoun }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .nounAdjective }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .nounAdjective }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .nounAdjective }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .nounAdjective }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .adjectiveNoun }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .nounAdjective }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .adjectiveNoun }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .adjectiveNoun }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .nounAdjective }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .nounAdjective }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .nounAdjective }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .adjectiveNoun }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .nounAdjective }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .nounAdjective }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .adjectiveNoun }
  , { walsCode := "so", language := "So", iso := "teu", value := .nounAdjective }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .nounAdjective }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .adjectiveNoun }
  , { walsCode := "som", language := "Somali", iso := "som", value := .nounAdjective }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .nounAdjective }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .noDominantOrder }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .adjectiveNoun }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .nounAdjective }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .nounAdjective }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .nounAdjective }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .nounAdjective }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .adjectiveNoun }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .nounAdjective }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .nounAdjective }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .nounAdjective }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .nounAdjective }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .adjectiveNoun }
  , { walsCode := "sku", language := "Suku", iso := "sub", value := .nounAdjective }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .nounAdjective }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .nounAdjective }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .nounAdjective }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .nounAdjective }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .nounAdjective }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .noDominantOrder }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .adjectiveNoun }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .nounAdjective }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .nounAdjective }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .nounAdjective }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .nounAdjective }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noDominantOrder }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noDominantOrder }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .nounAdjective }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .nounAdjective }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .noDominantOrder }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .nounAdjective }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .nounAdjective }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .nounAdjective }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .adjectiveNoun }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .nounAdjective }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .nounAdjective }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .adjectiveNoun }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .nounAdjective }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .adjectiveNoun }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .nounAdjective }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .adjectiveNoun }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .adjectiveNoun }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .nounAdjective }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .noDominantOrder }
  , { walsCode := "tsm", language := "Tasmanian", iso := "", value := .nounAdjective }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .nounAdjective }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .adjectiveNoun }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .adjectiveNoun }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .nounAdjective }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .nounAdjective }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .nounAdjective }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .nounAdjective }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .nounAdjective }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .adjectiveNoun }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .nounAdjective }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .nounAdjective }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .nounAdjective }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .nounAdjective }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .nounAdjective }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .nounAdjective }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .adjectiveNoun }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .adjectiveNoun }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .noDominantOrder }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .nounAdjective }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .nounAdjective }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .nounAdjective }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .nounAdjective }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .nounAdjective }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .nounAdjective }
  , { walsCode := "thd", language := "Thadou", iso := "tcz", value := .nounAdjective }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .nounAdjective }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .adjectiveNoun }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .adjectiveNoun }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .adjectiveNoun }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .adjectiveNoun }
  , { walsCode := "tdi", language := "Tibetan (Dingri)", iso := "bod", value := .nounAdjective }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .nounAdjective }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .nounAdjective }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .noDominantOrder }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .nounAdjective }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .nounAdjective }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .nounAdjective }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .adjectiveNoun }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .adjectiveNoun }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .onlyInternallyHeadedRelativeClauses }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .nounAdjective }
  , { walsCode := "tia", language := "Tima", iso := "tms", value := .nounAdjective }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .nounAdjective }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .adjectiveNoun }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .adjectiveNoun }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .noDominantOrder }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .adjectiveNoun }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .nounAdjective }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noDominantOrder }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .adjectiveNoun }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .nounAdjective }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .noDominantOrder }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .nounAdjective }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .nounAdjective }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .nounAdjective }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .nounAdjective }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .adjectiveNoun }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noDominantOrder }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .adjectiveNoun }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .nounAdjective }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noDominantOrder }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .adjectiveNoun }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .adjectiveNoun }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .adjectiveNoun }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .adjectiveNoun }
  , { walsCode := "tgo", language := "Tsogo", iso := "tsv", value := .nounAdjective }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .adjectiveNoun }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .nounAdjective }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .noDominantOrder }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .nounAdjective }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .nounAdjective }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .adjectiveNoun }
  , { walsCode := "tum", language := "Tumleo", iso := "tmq", value := .nounAdjective }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .nounAdjective }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .nounAdjective }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .nounAdjective }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .nounAdjective }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .nounAdjective }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .adjectiveNoun }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .adjectiveNoun }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .noDominantOrder }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .nounAdjective }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .adjectiveNoun }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .noDominantOrder }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .adjectiveNoun }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .adjectiveNoun }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .adjectiveNoun }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .adjectiveNoun }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .adjectiveNoun }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .adjectiveNoun }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .nounAdjective }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .nounAdjective }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .nounAdjective }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .nounAdjective }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .nounAdjective }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .nounAdjective }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .nounAdjective }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .nounAdjective }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .nounAdjective }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .adjectiveNoun }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .noDominantOrder }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .nounAdjective }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .nounAdjective }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .adjectiveNoun }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .nounAdjective }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .adjectiveNoun }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .adjectiveNoun }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .nounAdjective }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .nounAdjective }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .nounAdjective }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .nounAdjective }
  , { walsCode := "vif", language := "Vili", iso := "vif", value := .nounAdjective }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .nounAdjective }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .nounAdjective }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .nounAdjective }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .adjectiveNoun }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .nounAdjective }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .nounAdjective }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .adjectiveNoun }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .nounAdjective }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .noDominantOrder }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noDominantOrder }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .nounAdjective }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .nounAdjective }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .nounAdjective }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .nounAdjective }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .nounAdjective }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .nounAdjective }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .adjectiveNoun }
  , { walsCode := "was", language := "Washo", iso := "was", value := .adjectiveNoun }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .nounAdjective }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .nounAdjective }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .nounAdjective }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .nounAdjective }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .nounAdjective }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .adjectiveNoun }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .nounAdjective }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .nounAdjective }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .nounAdjective }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .nounAdjective }
  , { walsCode := "wn", language := "Wik Ngathana", iso := "wig", value := .nounAdjective }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .adjectiveNoun }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .nounAdjective }
  , { walsCode := "wog", language := "Wogamusin", iso := "wog", value := .nounAdjective }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .nounAdjective }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .adjectiveNoun }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .nounAdjective }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .nounAdjective }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .nounAdjective }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .nounAdjective }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .nounAdjective }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .nounAdjective }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .nounAdjective }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .adjectiveNoun }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .adjectiveNoun }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .nounAdjective }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .adjectiveNoun }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .adjectiveNoun }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .nounAdjective }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .nounAdjective }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .adjectiveNoun }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .adjectiveNoun }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .nounAdjective }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .nounAdjective }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .adjectiveNoun }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .adjectiveNoun }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .adjectiveNoun }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .nounAdjective }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .nounAdjective }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .nounAdjective }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .nounAdjective }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noDominantOrder }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .noDominantOrder }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .adjectiveNoun }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .adjectiveNoun }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .nounAdjective }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .nounAdjective }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .adjectiveNoun }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .adjectiveNoun }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .adjectiveNoun }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .adjectiveNoun }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .nounAdjective }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noDominantOrder }
  , { walsCode := "yrm", language := "Yurimangí", iso := "", value := .nounAdjective }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .adjectiveNoun }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .adjectiveNoun }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .adjectiveNoun }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .nounAdjective }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .nounAdjective }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .nounAdjective }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .nounAdjective }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .nounAdjective }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .adjectiveNoun }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .nounAdjective }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .adjectiveNoun }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .adjectiveNoun }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .nounAdjective }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .nounAdjective }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .nounAdjective }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .nounAdjective }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .nounAdjective }
  ]

/-- Complete WALS 87A dataset (1367 languages). -/
def allData : List (Datapoint AdjectiveNounOrder) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1367 := by native_decide

theorem count_adjectiveNoun :
    (allData.filter (·.value == .adjectiveNoun)).length = 373 := by native_decide
theorem count_nounAdjective :
    (allData.filter (·.value == .nounAdjective)).length = 879 := by native_decide
theorem count_noDominantOrder :
    (allData.filter (·.value == .noDominantOrder)).length = 110 := by native_decide
theorem count_onlyInternallyHeadedRelativeClauses :
    (allData.filter (·.value == .onlyInternallyHeadedRelativeClauses)).length = 5 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F87A
