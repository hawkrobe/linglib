import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 89A: Order of Numeral and Noun
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 89A`.

Chapter 89, 1154 languages.
-/

namespace Core.WALS.F89A

/-- WALS 89A values. -/
inductive NumeralNounOrder where
  | numeralNoun  -- Numeral-Noun (479 languages)
  | nounNumeral  -- Noun-Numeral (608 languages)
  | noDominantOrder  -- No dominant order (65 languages)
  | numeralOnlyModifiesVerb  -- Numeral only modifies verb (2 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint NumeralNounOrder) :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .numeralNoun }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .nounNumeral }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .nounNumeral }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .nounNumeral }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .nounNumeral }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noDominantOrder }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .nounNumeral }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .nounNumeral }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .numeralNoun }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .nounNumeral }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .nounNumeral }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noDominantOrder }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .nounNumeral }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .nounNumeral }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .nounNumeral }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .nounNumeral }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .numeralNoun }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .nounNumeral }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .numeralNoun }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .numeralNoun }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .numeralNoun }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .noDominantOrder }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .nounNumeral }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .nounNumeral }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .nounNumeral }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .nounNumeral }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .numeralNoun }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .numeralNoun }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .numeralNoun }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .nounNumeral }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .nounNumeral }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .nounNumeral }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .numeralNoun }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .nounNumeral }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .nounNumeral }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .nounNumeral }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .nounNumeral }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .nounNumeral }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .numeralNoun }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .numeralNoun }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .nounNumeral }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .nounNumeral }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .nounNumeral }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .nounNumeral }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .nounNumeral }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .nounNumeral }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .nounNumeral }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .nounNumeral }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .nounNumeral }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .nounNumeral }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .nounNumeral }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .nounNumeral }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .nounNumeral }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noDominantOrder }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .nounNumeral }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .numeralNoun }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noDominantOrder }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .numeralNoun }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .numeralNoun }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .noDominantOrder }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .numeralNoun }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .numeralNoun }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noDominantOrder }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noDominantOrder }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .nounNumeral }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .numeralNoun }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .nounNumeral }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .numeralNoun }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .numeralNoun }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .numeralNoun }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .nounNumeral }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .numeralNoun }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .nounNumeral }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .nounNumeral }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .nounNumeral }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .noDominantOrder }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .nounNumeral }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .numeralNoun }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .numeralNoun }
  , { walsCode := "au", language := "Au", iso := "avt", value := .nounNumeral }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .numeralNoun }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .numeralNoun }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .numeralNoun }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .nounNumeral }
  , { walsCode := "awy", language := "Awyi", iso := "auw", value := .nounNumeral }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .numeralNoun }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .numeralNoun }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .numeralNoun }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .nounNumeral }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .nounNumeral }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .noDominantOrder }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .nounNumeral }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .nounNumeral }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .nounNumeral }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .nounNumeral }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .numeralNoun }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .nounNumeral }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .nounNumeral }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .nounNumeral }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .nounNumeral }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .nounNumeral }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .nounNumeral }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .nounNumeral }
  , { walsCode := "bgm", language := "Bangime", iso := "dba", value := .nounNumeral }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .nounNumeral }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .nounNumeral }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .nounNumeral }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .nounNumeral }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .nounNumeral }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .numeralNoun }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .nounNumeral }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .nounNumeral }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .nounNumeral }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .numeralNoun }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .nounNumeral }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .numeralNoun }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .numeralNoun }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .numeralNoun }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .noDominantOrder }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .numeralNoun }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .nounNumeral }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .numeralNoun }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .nounNumeral }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .numeralNoun }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .numeralNoun }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .numeralNoun }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .numeralNoun }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .nounNumeral }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .nounNumeral }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .numeralNoun }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .nounNumeral }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .nounNumeral }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .numeralNoun }
  , { walsCode := "bnr", language := "Bilinarra", iso := "nbj", value := .noDominantOrder }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .nounNumeral }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .numeralNoun }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .nounNumeral }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .nounNumeral }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .nounNumeral }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .noDominantOrder }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .numeralNoun }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .nounNumeral }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .numeralNoun }
  , { walsCode := "boa", language := "Boazi (Kuni)", iso := "kvg", value := .nounNumeral }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .nounNumeral }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .nounNumeral }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .numeralNoun }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .nounNumeral }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .numeralNoun }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .nounNumeral }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .numeralNoun }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .nounNumeral }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .nounNumeral }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .numeralNoun }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .nounNumeral }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .numeralNoun }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .numeralNoun }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .nounNumeral }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .nounNumeral }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .nounNumeral }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .numeralNoun }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .nounNumeral }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .numeralNoun }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .numeralNoun }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .numeralNoun }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .numeralNoun }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .noDominantOrder }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .numeralNoun }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .numeralNoun }
  , { walsCode := "car", language := "Carib", iso := "car", value := .numeralNoun }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .numeralNoun }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .nounNumeral }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .numeralNoun }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .numeralNoun }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .numeralNoun }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .numeralNoun }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .numeralNoun }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .nounNumeral }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .numeralNoun }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .nounNumeral }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .numeralNoun }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .nounNumeral }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .numeralNoun }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .numeralNoun }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .numeralNoun }
  , { walsCode := "chd", language := "Chaudangsi", iso := "cdn", value := .numeralNoun }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .numeralNoun }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .numeralNoun }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .numeralNoun }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .numeralNoun }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .nounNumeral }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .nounNumeral }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .nounNumeral }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .nounNumeral }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .nounNumeral }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .numeralNoun }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .numeralNoun }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .numeralNoun }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .numeralNoun }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .numeralNoun }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .numeralNoun }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .numeralNoun }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .nounNumeral }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .nounNumeral }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .numeralNoun }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .numeralNoun }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .numeralNoun }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .numeralNoun }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .numeralNoun }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .numeralNoun }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .numeralNoun }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .numeralNoun }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .numeralNoun }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .numeralNoun }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .numeralNoun }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .numeralNoun }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .nounNumeral }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .numeralNoun }
  , { walsCode := "cuc", language := "Cuica", iso := "", value := .numeralNoun }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .numeralNoun }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .numeralNoun }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .nounNumeral }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .nounNumeral }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .nounNumeral }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .nounNumeral }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .numeralNoun }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .numeralNoun }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .nounNumeral }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .numeralNoun }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .numeralNoun }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .numeralNoun }
  , { walsCode := "day", language := "Day", iso := "dai", value := .nounNumeral }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .nounNumeral }
  , { walsCode := "des", language := "Desano", iso := "des", value := .noDominantOrder }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .noDominantOrder }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .nounNumeral }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .numeralNoun }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .numeralNoun }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .nounNumeral }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .nounNumeral }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .nounNumeral }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .nounNumeral }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .nounNumeral }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .nounNumeral }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .nounNumeral }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .nounNumeral }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noDominantOrder }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .nounNumeral }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .numeralNoun }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .numeralNoun }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .numeralNoun }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .nounNumeral }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .nounNumeral }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .nounNumeral }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .numeralNoun }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .nounNumeral }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .nounNumeral }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .nounNumeral }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .noDominantOrder }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .nounNumeral }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .nounNumeral }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .numeralNoun }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .nounNumeral }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .numeralNoun }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .nounNumeral }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .nounNumeral }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .nounNumeral }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .nounNumeral }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .nounNumeral }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .nounNumeral }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .nounNumeral }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .nounNumeral }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .nounNumeral }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .nounNumeral }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .noDominantOrder }
  , { walsCode := "eng", language := "English", iso := "eng", value := .numeralNoun }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .nounNumeral }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .nounNumeral }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .numeralNoun }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .numeralNoun }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .nounNumeral }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .nounNumeral }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .nounNumeral }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .numeralNoun }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .numeralNoun }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .noDominantOrder }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .nounNumeral }
  , { walsCode := "for", language := "Fore", iso := "for", value := .nounNumeral }
  , { walsCode := "fre", language := "French", iso := "fra", value := .numeralNoun }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .nounNumeral }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .nounNumeral }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .noDominantOrder }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .nounNumeral }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .noDominantOrder }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .numeralNoun }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .numeralNoun }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .nounNumeral }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .nounNumeral }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .numeralNoun }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .nounNumeral }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .nounNumeral }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noDominantOrder }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .numeralNoun }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .nounNumeral }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .nounNumeral }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .numeralNoun }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .numeralNoun }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .numeralNoun }
  , { walsCode := "ger", language := "German", iso := "deu", value := .numeralNoun }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .noDominantOrder }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .nounNumeral }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .numeralNoun }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .numeralNoun }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .nounNumeral }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .numeralNoun }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .nounNumeral }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .numeralNoun }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .numeralNoun }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nounNumeral }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .numeralNoun }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .nounNumeral }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .numeralNoun }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .numeralNoun }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .nounNumeral }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .nounNumeral }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .numeralNoun }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .nounNumeral }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .nounNumeral }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .numeralNoun }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .nounNumeral }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .nounNumeral }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .nounNumeral }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .nounNumeral }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .nounNumeral }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .numeralNoun }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .nounNumeral }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .numeralNoun }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .numeralNoun }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .numeralNoun }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .nounNumeral }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .noDominantOrder }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .nounNumeral }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .nounNumeral }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .nounNumeral }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .numeralNoun }
  , { walsCode := "hwr", language := "Hawrami", iso := "hac", value := .numeralNoun }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .nounNumeral }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .noDominantOrder }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .nounNumeral }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .numeralNoun }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .nounNumeral }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .nounNumeral }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .numeralNoun }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .numeralNoun }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .numeralNoun }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .numeralNoun }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .nounNumeral }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .numeralNoun }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .numeralNoun }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .nounNumeral }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .numeralNoun }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .numeralNoun }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .numeralNoun }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .numeralNoun }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .nounNumeral }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .numeralNoun }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .numeralNoun }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .numeralNoun }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .numeralNoun }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .nounNumeral }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .numeralNoun }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .nounNumeral }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .numeralNoun }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .numeralNoun }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .nounNumeral }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .nounNumeral }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .nounNumeral }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .numeralNoun }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .nounNumeral }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .nounNumeral }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .nounNumeral }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .numeralNoun }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .nounNumeral }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noDominantOrder }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .nounNumeral }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .nounNumeral }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .numeralNoun }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .numeralNoun }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .nounNumeral }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .numeralNoun }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .nounNumeral }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .nounNumeral }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .nounNumeral }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .numeralNoun }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .numeralNoun }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .numeralNoun }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .numeralNoun }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .nounNumeral }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .noDominantOrder }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .noDominantOrder }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .nounNumeral }
  , { walsCode := "jad", language := "Jad", iso := "jda", value := .nounNumeral }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .numeralNoun }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .noDominantOrder }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .nounNumeral }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .numeralNoun }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .numeralNoun }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .nounNumeral }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .nounNumeral }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .numeralNoun }
  , { walsCode := "joh", language := "Johari", iso := "rgk", value := .numeralNoun }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .nounNumeral }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .nounNumeral }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .numeralNoun }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .nounNumeral }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .numeralNoun }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .nounNumeral }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .nounNumeral }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .nounNumeral }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .nounNumeral }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .numeralNoun }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .numeralNoun }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .nounNumeral }
  , { walsCode := "kmi", language := "Kami", iso := "kcu", value := .nounNumeral }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .nounNumeral }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .numeralNoun }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .nounNumeral }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .numeralNoun }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .numeralNoun }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .numeralNoun }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .nounNumeral }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .nounNumeral }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .numeralNoun }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .nounNumeral }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .numeralNoun }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .noDominantOrder }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .numeralNoun }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .nounNumeral }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .nounNumeral }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .nounNumeral }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .nounNumeral }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .numeralNoun }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .numeralOnlyModifiesVerb }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .numeralNoun }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .nounNumeral }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .nounNumeral }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .nounNumeral }
  , { walsCode := "ktu", language := "Katu", iso := "", value := .numeralNoun }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .nounNumeral }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .numeralNoun }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .nounNumeral }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .numeralNoun }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .nounNumeral }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .nounNumeral }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .nounNumeral }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .numeralNoun }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .nounNumeral }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .nounNumeral }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .numeralNoun }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .numeralNoun }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .numeralNoun }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .numeralNoun }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .nounNumeral }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .nounNumeral }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .numeralNoun }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .numeralNoun }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .numeralNoun }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .nounNumeral }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .nounNumeral }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .numeralNoun }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .nounNumeral }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .nounNumeral }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .numeralNoun }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .nounNumeral }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .numeralNoun }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .numeralNoun }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .nounNumeral }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .numeralNoun }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .numeralNoun }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .nounNumeral }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .nounNumeral }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .numeralNoun }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .numeralNoun }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .numeralNoun }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .nounNumeral }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .nounNumeral }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .nounNumeral }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .nounNumeral }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .nounNumeral }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .nounNumeral }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .numeralNoun }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .numeralNoun }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .numeralNoun }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .nounNumeral }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .nounNumeral }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .numeralNoun }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .numeralNoun }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .nounNumeral }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .nounNumeral }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .numeralNoun }
  ]

private def allData_1 : List (Datapoint NumeralNounOrder) :=
  [ { walsCode := "kor", language := "Korean", iso := "kor", value := .numeralNoun }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .nounNumeral }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .numeralNoun }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .nounNumeral }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .nounNumeral }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .numeralNoun }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .nounNumeral }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .nounNumeral }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .noDominantOrder }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .nounNumeral }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .nounNumeral }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .numeralNoun }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .nounNumeral }
  , { walsCode := "krz", language := "Kryz", iso := "kry", value := .numeralNoun }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .nounNumeral }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .numeralNoun }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .nounNumeral }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .numeralNoun }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .nounNumeral }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .nounNumeral }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .numeralNoun }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .numeralNoun }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .numeralNoun }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .nounNumeral }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .nounNumeral }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .numeralNoun }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .numeralNoun }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .nounNumeral }
  , { walsCode := "kwb", language := "Kwerba", iso := "kwe", value := .nounNumeral }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .numeralNoun }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .nounNumeral }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .numeralNoun }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .nounNumeral }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .nounNumeral }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .nounNumeral }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .numeralNoun }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .nounNumeral }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .nounNumeral }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .nounNumeral }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .nounNumeral }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .nounNumeral }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .nounNumeral }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .nounNumeral }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .nounNumeral }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .numeralNoun }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .nounNumeral }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .numeralNoun }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .nounNumeral }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .nounNumeral }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .nounNumeral }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .nounNumeral }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .numeralNoun }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .nounNumeral }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .nounNumeral }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .nounNumeral }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .numeralNoun }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .nounNumeral }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .nounNumeral }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .nounNumeral }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .numeralNoun }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .nounNumeral }
  , { walsCode := "les", language := "Lese", iso := "les", value := .nounNumeral }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .nounNumeral }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .nounNumeral }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .numeralNoun }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .numeralNoun }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .nounNumeral }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .nounNumeral }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .nounNumeral }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .numeralNoun }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .nounNumeral }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .numeralNoun }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .nounNumeral }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .numeralNoun }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .nounNumeral }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .nounNumeral }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .nounNumeral }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .nounNumeral }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .numeralNoun }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .nounNumeral }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .nounNumeral }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .nounNumeral }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .nounNumeral }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .nounNumeral }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .nounNumeral }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .nounNumeral }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .nounNumeral }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .nounNumeral }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .numeralNoun }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .nounNumeral }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .nounNumeral }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .numeralNoun }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .nounNumeral }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .numeralNoun }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .numeralNoun }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .nounNumeral }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noDominantOrder }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .nounNumeral }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .nounNumeral }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .nounNumeral }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .nounNumeral }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .nounNumeral }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .numeralNoun }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .nounNumeral }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .nounNumeral }
  , { walsCode := "mto", language := "Malto", iso := "kmj", value := .numeralNoun }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .numeralNoun }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .numeralNoun }
  , { walsCode := "mmi", language := "Mambai", iso := "mcs", value := .nounNumeral }
  , { walsCode := "mmw", language := "Mambwe", iso := "mgr", value := .nounNumeral }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .nounNumeral }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .numeralNoun }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .nounNumeral }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .noDominantOrder }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .nounNumeral }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .numeralNoun }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .nounNumeral }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noDominantOrder }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .nounNumeral }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .numeralNoun }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .numeralNoun }
  , { walsCode := "mgq", language := "Mango", iso := "mge", value := .nounNumeral }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .nounNumeral }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .nounNumeral }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .numeralNoun }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .nounNumeral }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .numeralNoun }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .nounNumeral }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .numeralNoun }
  , { walsCode := "mrc", language := "Marchha", iso := "rnp", value := .numeralNoun }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .nounNumeral }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .nounNumeral }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noDominantOrder }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .nounNumeral }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .numeralNoun }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .nounNumeral }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .numeralNoun }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .nounNumeral }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .nounNumeral }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .nounNumeral }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .nounNumeral }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .nounNumeral }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .nounNumeral }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .nounNumeral }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .nounNumeral }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .numeralNoun }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .nounNumeral }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .nounNumeral }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .nounNumeral }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .nounNumeral }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .nounNumeral }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .nounNumeral }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .nounNumeral }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .nounNumeral }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .nounNumeral }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .nounNumeral }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .nounNumeral }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noDominantOrder }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .nounNumeral }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .nounNumeral }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .numeralNoun }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .nounNumeral }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .numeralNoun }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .nounNumeral }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .nounNumeral }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .numeralNoun }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .nounNumeral }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .noDominantOrder }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .nounNumeral }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .numeralNoun }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .nounNumeral }
  , { walsCode := "mhl", language := "Miri (Hill):", iso := "mrg", value := .nounNumeral }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .nounNumeral }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .numeralNoun }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .numeralNoun }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .numeralNoun }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .numeralNoun }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .numeralNoun }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .numeralNoun }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .numeralNoun }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .numeralNoun }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .numeralNoun }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .nounNumeral }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .nounNumeral }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .numeralNoun }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .nounNumeral }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .numeralNoun }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .nounNumeral }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .nounNumeral }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .nounNumeral }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .nounNumeral }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .nounNumeral }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .nounNumeral }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noDominantOrder }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .nounNumeral }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .nounNumeral }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .nounNumeral }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .nounNumeral }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .nounNumeral }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .nounNumeral }
  , { walsCode := "mpo", language := "Mpongwe", iso := "mye", value := .nounNumeral }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .nounNumeral }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .nounNumeral }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .nounNumeral }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .nounNumeral }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .numeralNoun }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .nounNumeral }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .nounNumeral }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .numeralNoun }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .noDominantOrder }
  , { walsCode := "mnz", language := "Munzombo", iso := "moj", value := .nounNumeral }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .nounNumeral }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .nounNumeral }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .nounNumeral }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .nounNumeral }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .nounNumeral }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .numeralNoun }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .numeralNoun }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .nounNumeral }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .nounNumeral }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .nounNumeral }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .nounNumeral }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .nounNumeral }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .nounNumeral }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .numeralNoun }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .numeralNoun }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .numeralNoun }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .numeralNoun }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .noDominantOrder }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .noDominantOrder }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .nounNumeral }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .numeralNoun }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .nounNumeral }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .nounNumeral }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .nounNumeral }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .nounNumeral }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .nounNumeral }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .nounNumeral }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .numeralNoun }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .numeralNoun }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .nounNumeral }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .nounNumeral }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .nounNumeral }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .nounNumeral }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .nounNumeral }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .nounNumeral }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .numeralNoun }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .numeralNoun }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .numeralNoun }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .numeralNoun }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .numeralNoun }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .numeralNoun }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .numeralNoun }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .noDominantOrder }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .nounNumeral }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .nounNumeral }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .numeralNoun }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .nounNumeral }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noDominantOrder }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .nounNumeral }
  , { walsCode := "ngg", language := "Ngan'gityemerri", iso := "nam", value := .nounNumeral }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .nounNumeral }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .nounNumeral }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .numeralNoun }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .nounNumeral }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .nounNumeral }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .numeralNoun }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .nounNumeral }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .nounNumeral }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .nounNumeral }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .nounNumeral }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .noDominantOrder }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .numeralNoun }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .noDominantOrder }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .numeralNoun }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .numeralNoun }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noDominantOrder }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .nounNumeral }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .nounNumeral }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .noDominantOrder }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .nounNumeral }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .nounNumeral }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .numeralNoun }
  , { walsCode := "nto", language := "Ntomba", iso := "nto", value := .nounNumeral }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .nounNumeral }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .nounNumeral }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .nounNumeral }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .nounNumeral }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .numeralNoun }
  , { walsCode := "yi", language := "Nuosu", iso := "iii", value := .nounNumeral }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .nounNumeral }
  , { walsCode := "nus", language := "Nusu", iso := "nuf", value := .nounNumeral }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noDominantOrder }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .nounNumeral }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .nounNumeral }
  , { walsCode := "nyh", language := "Nyiha", iso := "nih", value := .nounNumeral }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .nounNumeral }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .numeralNoun }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .nounNumeral }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .numeralNoun }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .nounNumeral }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .numeralNoun }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .numeralNoun }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .numeralNoun }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .noDominantOrder }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .nounNumeral }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .nounNumeral }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .numeralNoun }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .nounNumeral }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .noDominantOrder }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .numeralNoun }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .nounNumeral }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .nounNumeral }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .nounNumeral }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .numeralNoun }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .numeralNoun }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .nounNumeral }
  , { walsCode := "owi", language := "Owininga", iso := "owi", value := .nounNumeral }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .nounNumeral }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .numeralNoun }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .nounNumeral }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .numeralNoun }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .nounNumeral }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .numeralNoun }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .noDominantOrder }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .numeralNoun }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .numeralNoun }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .nounNumeral }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .numeralNoun }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .numeralNoun }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .numeralNoun }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .nounNumeral }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .numeralNoun }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .nounNumeral }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .numeralNoun }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .nounNumeral }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .nounNumeral }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .nounNumeral }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .numeralNoun }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .nounNumeral }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .numeralNoun }
  , { walsCode := "ppc", language := "Piapoco", iso := "pio", value := .numeralNoun }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .nounNumeral }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .numeralNoun }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .numeralNoun }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .nounNumeral }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .numeralNoun }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .nounNumeral }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .nounNumeral }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .nounNumeral }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .nounNumeral }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .nounNumeral }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .nounNumeral }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .numeralNoun }
  , { walsCode := "pmn", language := "Pomo (Northern)", iso := "pej", value := .numeralNoun }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .numeralNoun }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .nounNumeral }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .numeralNoun }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .numeralNoun }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .nounNumeral }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .nounNumeral }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .nounNumeral }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .numeralNoun }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .numeralNoun }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .nounNumeral }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .numeralNoun }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noDominantOrder }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .nounNumeral }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .numeralNoun }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .numeralNoun }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .numeralNoun }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .nounNumeral }
  , { walsCode := "ral", language := "Ralte", iso := "ral", value := .nounNumeral }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .nounNumeral }
  , { walsCode := "rpa", language := "Rang Pas", iso := "bod", value := .numeralNoun }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .numeralNoun }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .nounNumeral }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .nounNumeral }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .numeralNoun }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .numeralNoun }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .numeralNoun }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .numeralNoun }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .numeralNoun }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .numeralNoun }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .nounNumeral }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .noDominantOrder }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .nounNumeral }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .numeralNoun }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .numeralNoun }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .nounNumeral }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .noDominantOrder }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .nounNumeral }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .numeralNoun }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .numeralNoun }
  , { walsCode := "saa", language := "Sa'a", iso := "apb", value := .numeralNoun }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .nounNumeral }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .nounNumeral }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .nounNumeral }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .numeralNoun }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .nounNumeral }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .noDominantOrder }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .nounNumeral }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .nounNumeral }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .nounNumeral }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .numeralNoun }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .numeralNoun }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .numeralNoun }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .numeralNoun }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .numeralNoun }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .numeralNoun }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .nounNumeral }
  , { walsCode := "sec", language := "Secoya", iso := "sey", value := .numeralNoun }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .numeralNoun }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .numeralNoun }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .nounNumeral }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .numeralNoun }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .nounNumeral }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .numeralNoun }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .nounNumeral }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .nounNumeral }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .numeralNoun }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .nounNumeral }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .numeralNoun }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .nounNumeral }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .nounNumeral }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .nounNumeral }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .numeralNoun }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .numeralNoun }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .numeralNoun }
  , { walsCode := "smp", language := "Shompen", iso := "sii", value := .numeralNoun }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .nounNumeral }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .numeralNoun }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .numeralNoun }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .nounNumeral }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .nounNumeral }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .noDominantOrder }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .nounNumeral }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .numeralNoun }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .numeralNoun }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .nounNumeral }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .numeralNoun }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .numeralNoun }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .nounNumeral }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .nounNumeral }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .numeralNoun }
  , { walsCode := "so", language := "So", iso := "teu", value := .nounNumeral }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .nounNumeral }
  , { walsCode := "som", language := "Somali", iso := "som", value := .numeralNoun }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .numeralNoun }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .nounNumeral }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .nounNumeral }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .numeralNoun }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .nounNumeral }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .numeralNoun }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .numeralNoun }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .noDominantOrder }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .nounNumeral }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .nounNumeral }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .noDominantOrder }
  , { walsCode := "sku", language := "Suku", iso := "sub", value := .nounNumeral }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .nounNumeral }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .numeralNoun }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .nounNumeral }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .nounNumeral }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .noDominantOrder }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .numeralNoun }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .nounNumeral }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .nounNumeral }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .nounNumeral }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .nounNumeral }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .numeralNoun }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .noDominantOrder }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .numeralNoun }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .nounNumeral }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .numeralNoun }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .nounNumeral }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .numeralNoun }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .nounNumeral }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .nounNumeral }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .numeralNoun }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .numeralNoun }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .numeralNoun }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .numeralNoun }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .nounNumeral }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .numeralNoun }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .numeralNoun }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .numeralNoun }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .nounNumeral }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .nounNumeral }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .numeralNoun }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .nounNumeral }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .numeralNoun }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .nounNumeral }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .nounNumeral }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .nounNumeral }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .numeralNoun }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .numeralNoun }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .numeralNoun }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .numeralNoun }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .nounNumeral }
  ]

private def allData_2 : List (Datapoint NumeralNounOrder) :=
  [ { walsCode := "trb", language := "Teribe", iso := "tfr", value := .nounNumeral }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .nounNumeral }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .nounNumeral }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .nounNumeral }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .nounNumeral }
  , { walsCode := "thd", language := "Thadou", iso := "tcz", value := .nounNumeral }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .nounNumeral }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .nounNumeral }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .numeralNoun }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .numeralNoun }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .numeralNoun }
  , { walsCode := "tdi", language := "Tibetan (Dingri)", iso := "bod", value := .nounNumeral }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .nounNumeral }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .nounNumeral }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .nounNumeral }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .nounNumeral }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .numeralNoun }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .nounNumeral }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .numeralNoun }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .numeralNoun }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .nounNumeral }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .numeralNoun }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .numeralNoun }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .numeralNoun }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .numeralNoun }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .numeralNoun }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .numeralNoun }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .numeralNoun }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .nounNumeral }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .nounNumeral }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .numeralNoun }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .noDominantOrder }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .nounNumeral }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .nounNumeral }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .numeralNoun }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .numeralNoun }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .numeralNoun }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .numeralNoun }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .numeralNoun }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .nounNumeral }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .numeralNoun }
  , { walsCode := "tgo", language := "Tsogo", iso := "tsv", value := .nounNumeral }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .numeralNoun }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .numeralNoun }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .nounNumeral }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .numeralNoun }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .nounNumeral }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .nounNumeral }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .numeralNoun }
  , { walsCode := "tum", language := "Tumleo", iso := "tmq", value := .nounNumeral }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .nounNumeral }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .numeralNoun }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .nounNumeral }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .nounNumeral }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .numeralNoun }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .numeralNoun }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .nounNumeral }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .nounNumeral }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .numeralNoun }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .numeralNoun }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .numeralNoun }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .numeralNoun }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .numeralNoun }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .numeralNoun }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .numeralNoun }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .numeralNoun }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .nounNumeral }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .numeralNoun }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .nounNumeral }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .nounNumeral }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .nounNumeral }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noDominantOrder }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .numeralNoun }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .nounNumeral }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .numeralNoun }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .numeralNoun }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .nounNumeral }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .numeralNoun }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .numeralNoun }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .numeralNoun }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .numeralNoun }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .nounNumeral }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .nounNumeral }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .numeralNoun }
  , { walsCode := "vif", language := "Vili", iso := "vif", value := .nounNumeral }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .nounNumeral }
  , { walsCode := "wwa", language := "Waama", iso := "wwa", value := .nounNumeral }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .nounNumeral }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .nounNumeral }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .numeralNoun }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .nounNumeral }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .noDominantOrder }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .numeralNoun }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .nounNumeral }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .nounNumeral }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .nounNumeral }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .numeralNoun }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .numeralNoun }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .numeralOnlyModifiesVerb }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .numeralNoun }
  , { walsCode := "was", language := "Washo", iso := "was", value := .numeralNoun }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .nounNumeral }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .noDominantOrder }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .numeralNoun }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .nounNumeral }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .numeralNoun }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .numeralNoun }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .nounNumeral }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .nounNumeral }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .numeralNoun }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .numeralNoun }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .numeralNoun }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .numeralNoun }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .nounNumeral }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .nounNumeral }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .numeralNoun }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .nounNumeral }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .numeralNoun }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .nounNumeral }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .numeralNoun }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .numeralNoun }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .nounNumeral }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .numeralNoun }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .nounNumeral }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .numeralNoun }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .numeralNoun }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .nounNumeral }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .nounNumeral }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .nounNumeral }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .nounNumeral }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .numeralNoun }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .numeralNoun }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .numeralNoun }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .nounNumeral }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .nounNumeral }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .numeralNoun }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .numeralNoun }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .nounNumeral }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .numeralNoun }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .nounNumeral }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .numeralNoun }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .numeralNoun }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .numeralNoun }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .numeralNoun }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .nounNumeral }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .numeralNoun }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .numeralNoun }
  , { walsCode := "zen", language := "Zenaga", iso := "zen", value := .numeralNoun }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .numeralNoun }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .numeralNoun }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .numeralNoun }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .nounNumeral }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .numeralNoun }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .nounNumeral }
  ]

/-- Complete WALS 89A dataset (1154 languages). -/
def allData : List (Datapoint NumeralNounOrder) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1154 := by native_decide

theorem count_numeralNoun :
    (allData.filter (·.value == .numeralNoun)).length = 479 := by native_decide
theorem count_nounNumeral :
    (allData.filter (·.value == .nounNumeral)).length = 608 := by native_decide
theorem count_noDominantOrder :
    (allData.filter (·.value == .noDominantOrder)).length = 65 := by native_decide
theorem count_numeralOnlyModifiesVerb :
    (allData.filter (·.value == .numeralOnlyModifiesVerb)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F89A
