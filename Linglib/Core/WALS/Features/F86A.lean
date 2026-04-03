import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 86A: Order of Genitive and Noun
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 86A`.

Chapter 86, 1249 languages.
-/

namespace Core.WALS.F86A

/-- WALS 86A values. -/
inductive GenitiveNounOrder where
  | genitiveNoun  -- Genitive-Noun (685 languages)
  | nounGenitive  -- Noun-Genitive (468 languages)
  | noDominantOrder  -- No dominant order (96 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint GenitiveNounOrder) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .genitiveNoun }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .genitiveNoun }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .genitiveNoun }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .genitiveNoun }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .genitiveNoun }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .genitiveNoun }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noDominantOrder }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .genitiveNoun }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .genitiveNoun }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .genitiveNoun }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .nounGenitive }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .genitiveNoun }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .genitiveNoun }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .nounGenitive }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .genitiveNoun }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .genitiveNoun }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .genitiveNoun }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .genitiveNoun }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .genitiveNoun }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .genitiveNoun }
  , { walsCode := "awi", language := "Aekyom", iso := "awi", value := .genitiveNoun }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .genitiveNoun }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .nounGenitive }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .nounGenitive }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .nounGenitive }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .genitiveNoun }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .nounGenitive }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .noDominantOrder }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .genitiveNoun }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .genitiveNoun }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .genitiveNoun }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .genitiveNoun }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .nounGenitive }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .genitiveNoun }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .genitiveNoun }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .nounGenitive }
  , { walsCode := "amm", language := "Ama", iso := "amm", value := .genitiveNoun }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .genitiveNoun }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .genitiveNoun }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .nounGenitive }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .genitiveNoun }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .genitiveNoun }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .genitiveNoun }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .genitiveNoun }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .genitiveNoun }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .nounGenitive }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .genitiveNoun }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .genitiveNoun }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .nounGenitive }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .genitiveNoun }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .nounGenitive }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .genitiveNoun }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .noDominantOrder }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .genitiveNoun }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .genitiveNoun }
  , { walsCode := "ayi", language := "Anyi", iso := "any", value := .genitiveNoun }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .nounGenitive }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .noDominantOrder }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .genitiveNoun }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .genitiveNoun }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .genitiveNoun }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .genitiveNoun }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .genitiveNoun }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .noDominantOrder }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .nounGenitive }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .nounGenitive }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .nounGenitive }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .nounGenitive }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .nounGenitive }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .nounGenitive }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .nounGenitive }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .genitiveNoun }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noDominantOrder }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .nounGenitive }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .genitiveNoun }
  , { walsCode := "ari", language := "Aribwatsa", iso := "laz", value := .genitiveNoun }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .genitiveNoun }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .genitiveNoun }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .noDominantOrder }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .nounGenitive }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .nounGenitive }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .genitiveNoun }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .genitiveNoun }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .genitiveNoun }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .nounGenitive }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .genitiveNoun }
  , { walsCode := "au", language := "Au", iso := "avt", value := .noDominantOrder }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .genitiveNoun }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .noDominantOrder }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .genitiveNoun }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .genitiveNoun }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .genitiveNoun }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .nounGenitive }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .genitiveNoun }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .genitiveNoun }
  , { walsCode := "ayr", language := "Ayoreo", iso := "ayo", value := .genitiveNoun }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .genitiveNoun }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .genitiveNoun }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .nounGenitive }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .nounGenitive }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .nounGenitive }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .genitiveNoun }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .nounGenitive }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .nounGenitive }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .nounGenitive }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .nounGenitive }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .nounGenitive }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .nounGenitive }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .nounGenitive }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .genitiveNoun }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .nounGenitive }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .nounGenitive }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .genitiveNoun }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .nounGenitive }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .genitiveNoun }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .nounGenitive }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .nounGenitive }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .genitiveNoun }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .genitiveNoun }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .nounGenitive }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .nounGenitive }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .genitiveNoun }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .genitiveNoun }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .nounGenitive }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .nounGenitive }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .nounGenitive }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .genitiveNoun }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .genitiveNoun }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .genitiveNoun }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .nounGenitive }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .nounGenitive }
  , { walsCode := "bga", language := "Benga", iso := "bng", value := .nounGenitive }
  , { walsCode := "brq", language := "Bera", iso := "brf", value := .nounGenitive }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .nounGenitive }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .nounGenitive }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .nounGenitive }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .nounGenitive }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .noDominantOrder }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .genitiveNoun }
  , { walsCode := "bhu", language := "Bhumij", iso := "unr", value := .genitiveNoun }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .genitiveNoun }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .nounGenitive }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .noDominantOrder }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .genitiveNoun }
  , { walsCode := "bnr", language := "Bilinarra", iso := "nbj", value := .noDominantOrder }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .genitiveNoun }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .genitiveNoun }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .genitiveNoun }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .genitiveNoun }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .nounGenitive }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .genitiveNoun }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .genitiveNoun }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .nounGenitive }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .genitiveNoun }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .nounGenitive }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .genitiveNoun }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .genitiveNoun }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .nounGenitive }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .nounGenitive }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .genitiveNoun }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .nounGenitive }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .nounGenitive }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .nounGenitive }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .genitiveNoun }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .genitiveNoun }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .nounGenitive }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .nounGenitive }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .nounGenitive }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noDominantOrder }
  , { walsCode := "buw", language := "Bulu", iso := "bum", value := .nounGenitive }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .nounGenitive }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .genitiveNoun }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .genitiveNoun }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .genitiveNoun }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .genitiveNoun }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .genitiveNoun }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .nounGenitive }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .genitiveNoun }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .genitiveNoun }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .genitiveNoun }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .genitiveNoun }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .nounGenitive }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .genitiveNoun }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .genitiveNoun }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .genitiveNoun }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .genitiveNoun }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .genitiveNoun }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .genitiveNoun }
  , { walsCode := "car", language := "Carib", iso := "car", value := .genitiveNoun }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .genitiveNoun }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .genitiveNoun }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .nounGenitive }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .genitiveNoun }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .genitiveNoun }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .genitiveNoun }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .nounGenitive }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .nounGenitive }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .genitiveNoun }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .nounGenitive }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .nounGenitive }
  , { walsCode := "cme", language := "Cham (Eastern)", iso := "cjm", value := .nounGenitive }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .nounGenitive }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .genitiveNoun }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .genitiveNoun }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .nounGenitive }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .nounGenitive }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .genitiveNoun }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .genitiveNoun }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .genitiveNoun }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .genitiveNoun }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .nounGenitive }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .genitiveNoun }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .genitiveNoun }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .genitiveNoun }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .genitiveNoun }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .nounGenitive }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .nounGenitive }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .nounGenitive }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .nounGenitive }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .noDominantOrder }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .genitiveNoun }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .nounGenitive }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .genitiveNoun }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .genitiveNoun }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .genitiveNoun }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .nounGenitive }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .nounGenitive }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .nounGenitive }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .nounGenitive }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .genitiveNoun }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .nounGenitive }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .genitiveNoun }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .genitiveNoun }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .genitiveNoun }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .genitiveNoun }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .genitiveNoun }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .nounGenitive }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noDominantOrder }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .nounGenitive }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .noDominantOrder }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .nounGenitive }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .genitiveNoun }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .genitiveNoun }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .genitiveNoun }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .noDominantOrder }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .nounGenitive }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .genitiveNoun }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .genitiveNoun }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .genitiveNoun }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .genitiveNoun }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .genitiveNoun }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .genitiveNoun }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .genitiveNoun }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .genitiveNoun }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .genitiveNoun }
  , { walsCode := "day", language := "Day", iso := "dai", value := .nounGenitive }
  , { walsCode := "des", language := "Desano", iso := "des", value := .genitiveNoun }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .genitiveNoun }
  , { walsCode := "dhb", language := "Dharumbal", iso := "xgm", value := .genitiveNoun }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .genitiveNoun }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .genitiveNoun }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .nounGenitive }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .genitiveNoun }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .genitiveNoun }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .nounGenitive }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .nounGenitive }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .genitiveNoun }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .noDominantOrder }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noDominantOrder }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .genitiveNoun }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .nounGenitive }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .genitiveNoun }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .genitiveNoun }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .genitiveNoun }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .nounGenitive }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .genitiveNoun }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .genitiveNoun }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .nounGenitive }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .nounGenitive }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .nounGenitive }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .genitiveNoun }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .genitiveNoun }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .genitiveNoun }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .genitiveNoun }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .nounGenitive }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .genitiveNoun }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .genitiveNoun }
  , { walsCode := "edo", language := "Edolo", iso := "etr", value := .genitiveNoun }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .nounGenitive }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .genitiveNoun }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .genitiveNoun }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .genitiveNoun }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .nounGenitive }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .nounGenitive }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noDominantOrder }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .genitiveNoun }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .nounGenitive }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .genitiveNoun }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .nounGenitive }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .genitiveNoun }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .genitiveNoun }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .genitiveNoun }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .genitiveNoun }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .nounGenitive }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .genitiveNoun }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .nounGenitive }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .genitiveNoun }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .genitiveNoun }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .nounGenitive }
  , { walsCode := "for", language := "Fore", iso := "for", value := .genitiveNoun }
  , { walsCode := "fre", language := "French", iso := "fra", value := .nounGenitive }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .noDominantOrder }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .nounGenitive }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .genitiveNoun }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .genitiveNoun }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .nounGenitive }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .nounGenitive }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .nounGenitive }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .genitiveNoun }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .nounGenitive }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .genitiveNoun }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .genitiveNoun }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .genitiveNoun }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .genitiveNoun }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .nounGenitive }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .genitiveNoun }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .nounGenitive }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .nounGenitive }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .nounGenitive }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .genitiveNoun }
  , { walsCode := "ger", language := "German", iso := "deu", value := .nounGenitive }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .nounGenitive }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .genitiveNoun }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .nounGenitive }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .nounGenitive }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .genitiveNoun }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .genitiveNoun }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noDominantOrder }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .genitiveNoun }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .genitiveNoun }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .nounGenitive }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .genitiveNoun }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .genitiveNoun }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .genitiveNoun }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .genitiveNoun }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .nounGenitive }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .nounGenitive }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .nounGenitive }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .genitiveNoun }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .noDominantOrder }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .nounGenitive }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .noDominantOrder }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .genitiveNoun }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .genitiveNoun }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .noDominantOrder }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .genitiveNoun }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .nounGenitive }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .genitiveNoun }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .genitiveNoun }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noDominantOrder }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .genitiveNoun }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .nounGenitive }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .genitiveNoun }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .genitiveNoun }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .genitiveNoun }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .nounGenitive }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .nounGenitive }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .genitiveNoun }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .nounGenitive }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .nounGenitive }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .nounGenitive }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .genitiveNoun }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .nounGenitive }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .genitiveNoun }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .genitiveNoun }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .genitiveNoun }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .genitiveNoun }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .genitiveNoun }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .nounGenitive }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .genitiveNoun }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .genitiveNoun }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .nounGenitive }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .nounGenitive }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .genitiveNoun }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .genitiveNoun }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .nounGenitive }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .genitiveNoun }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .genitiveNoun }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .genitiveNoun }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .genitiveNoun }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .nounGenitive }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .nounGenitive }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .genitiveNoun }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .nounGenitive }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .nounGenitive }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .genitiveNoun }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .noDominantOrder }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .nounGenitive }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .nounGenitive }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .nounGenitive }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .nounGenitive }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .genitiveNoun }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .noDominantOrder }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .genitiveNoun }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .nounGenitive }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .genitiveNoun }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .genitiveNoun }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .nounGenitive }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .nounGenitive }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .genitiveNoun }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .genitiveNoun }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .genitiveNoun }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .nounGenitive }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .genitiveNoun }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .nounGenitive }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .nounGenitive }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noDominantOrder }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .noDominantOrder }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .genitiveNoun }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .nounGenitive }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .nounGenitive }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .genitiveNoun }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .nounGenitive }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .genitiveNoun }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .genitiveNoun }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .genitiveNoun }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .nounGenitive }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .genitiveNoun }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .genitiveNoun }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .genitiveNoun }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .nounGenitive }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .nounGenitive }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .genitiveNoun }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .genitiveNoun }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .genitiveNoun }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .genitiveNoun }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .nounGenitive }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .nounGenitive }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .noDominantOrder }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .nounGenitive }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .genitiveNoun }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .nounGenitive }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .genitiveNoun }
  , { walsCode := "klq", language := "Kalam", iso := "kmh", value := .genitiveNoun }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .nounGenitive }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .genitiveNoun }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .genitiveNoun }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .genitiveNoun }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .genitiveNoun }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .genitiveNoun }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .genitiveNoun }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .nounGenitive }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .noDominantOrder }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .nounGenitive }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .nounGenitive }
  , { walsCode := "kbu", language := "Kanembu", iso := "kbl", value := .nounGenitive }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .genitiveNoun }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .genitiveNoun }
  , { walsCode := "knb", language := "Kanum (Bädi)", iso := "khd", value := .genitiveNoun }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .nounGenitive }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .nounGenitive }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .nounGenitive }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .nounGenitive }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .genitiveNoun }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .noDominantOrder }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .genitiveNoun }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .genitiveNoun }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .genitiveNoun }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .genitiveNoun }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .genitiveNoun }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .nounGenitive }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .genitiveNoun }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .genitiveNoun }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .genitiveNoun }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .genitiveNoun }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .nounGenitive }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .genitiveNoun }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .nounGenitive }
  , { walsCode := "ktu", language := "Katu", iso := "", value := .nounGenitive }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .noDominantOrder }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noDominantOrder }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .genitiveNoun }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .genitiveNoun }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .genitiveNoun }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .nounGenitive }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .genitiveNoun }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .nounGenitive }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .nounGenitive }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .genitiveNoun }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .genitiveNoun }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .genitiveNoun }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .genitiveNoun }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .genitiveNoun }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .genitiveNoun }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .genitiveNoun }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .genitiveNoun }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .genitiveNoun }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .genitiveNoun }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .nounGenitive }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .genitiveNoun }
  ]

private def allData_1 : List (Datapoint GenitiveNounOrder) :=
  [ { walsCode := "khm", language := "Khmer", iso := "khm", value := .nounGenitive }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .nounGenitive }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .genitiveNoun }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .nounGenitive }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .genitiveNoun }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .genitiveNoun }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .nounGenitive }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .genitiveNoun }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .genitiveNoun }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .nounGenitive }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .nounGenitive }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .genitiveNoun }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .nounGenitive }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .genitiveNoun }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .genitiveNoun }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .genitiveNoun }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .genitiveNoun }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .genitiveNoun }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .nounGenitive }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .genitiveNoun }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .genitiveNoun }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .genitiveNoun }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .nounGenitive }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .genitiveNoun }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .genitiveNoun }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .genitiveNoun }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .nounGenitive }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .genitiveNoun }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .genitiveNoun }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .nounGenitive }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .nounGenitive }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .genitiveNoun }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .genitiveNoun }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .genitiveNoun }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .genitiveNoun }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .genitiveNoun }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .genitiveNoun }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .genitiveNoun }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .genitiveNoun }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .genitiveNoun }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .nounGenitive }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .genitiveNoun }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .genitiveNoun }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .genitiveNoun }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .genitiveNoun }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .genitiveNoun }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .genitiveNoun }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .nounGenitive }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .nounGenitive }
  , { walsCode := "krz", language := "Kryz", iso := "kry", value := .genitiveNoun }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .nounGenitive }
  , { walsCode := "kkq", language := "Kuikúro", iso := "kui", value := .genitiveNoun }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noDominantOrder }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .genitiveNoun }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .genitiveNoun }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .noDominantOrder }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .genitiveNoun }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .genitiveNoun }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .nounGenitive }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .nounGenitive }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .nounGenitive }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .nounGenitive }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .genitiveNoun }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .nounGenitive }
  , { walsCode := "kwm", language := "Kwami", iso := "ksq", value := .nounGenitive }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .nounGenitive }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .genitiveNoun }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .genitiveNoun }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .genitiveNoun }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .genitiveNoun }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .genitiveNoun }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .nounGenitive }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .genitiveNoun }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .nounGenitive }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .genitiveNoun }
  , { walsCode := "laf", language := "Lafofa", iso := "laf", value := .noDominantOrder }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .nounGenitive }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .genitiveNoun }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .genitiveNoun }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noDominantOrder }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .genitiveNoun }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noDominantOrder }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .nounGenitive }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .genitiveNoun }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .nounGenitive }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .nounGenitive }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .nounGenitive }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .nounGenitive }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .nounGenitive }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .nounGenitive }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .nounGenitive }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .genitiveNoun }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .genitiveNoun }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .nounGenitive }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .noDominantOrder }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .genitiveNoun }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .nounGenitive }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .genitiveNoun }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .genitiveNoun }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .genitiveNoun }
  , { walsCode := "les", language := "Lese", iso := "les", value := .noDominantOrder }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .genitiveNoun }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .nounGenitive }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .genitiveNoun }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .nounGenitive }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .genitiveNoun }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .nounGenitive }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .nounGenitive }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .genitiveNoun }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .genitiveNoun }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .genitiveNoun }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .genitiveNoun }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .nounGenitive }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .nounGenitive }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .nounGenitive }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .genitiveNoun }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .nounGenitive }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .nounGenitive }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .genitiveNoun }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .genitiveNoun }
  , { walsCode := "lul", language := "Lule", iso := "ule", value := .genitiveNoun }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .nounGenitive }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .nounGenitive }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .genitiveNoun }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .nounGenitive }
  , { walsCode := "jlu", language := "Luwo", iso := "lwo", value := .nounGenitive }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .nounGenitive }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .nounGenitive }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noDominantOrder }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .nounGenitive }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noDominantOrder }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .noDominantOrder }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .nounGenitive }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .genitiveNoun }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .nounGenitive }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .genitiveNoun }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .nounGenitive }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .genitiveNoun }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .genitiveNoun }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .genitiveNoun }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .genitiveNoun }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .nounGenitive }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .noDominantOrder }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .noDominantOrder }
  , { walsCode := "mkl", language := "Maklew", iso := "mgf", value := .genitiveNoun }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .nounGenitive }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .nounGenitive }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noDominantOrder }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .genitiveNoun }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .noDominantOrder }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .nounGenitive }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .nounGenitive }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .nounGenitive }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .nounGenitive }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .noDominantOrder }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .nounGenitive }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .genitiveNoun }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .genitiveNoun }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .genitiveNoun }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .noDominantOrder }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noDominantOrder }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .noDominantOrder }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .nounGenitive }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .genitiveNoun }
  , { walsCode := "mgq", language := "Mango", iso := "mge", value := .nounGenitive }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .genitiveNoun }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .genitiveNoun }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .nounGenitive }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .genitiveNoun }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .nounGenitive }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .genitiveNoun }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .noDominantOrder }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .genitiveNoun }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .genitiveNoun }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .genitiveNoun }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .nounGenitive }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .genitiveNoun }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .genitiveNoun }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .genitiveNoun }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .genitiveNoun }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .nounGenitive }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noDominantOrder }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .genitiveNoun }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .nounGenitive }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .nounGenitive }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .nounGenitive }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .nounGenitive }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .genitiveNoun }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .genitiveNoun }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .nounGenitive }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .genitiveNoun }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .genitiveNoun }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noDominantOrder }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .nounGenitive }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .genitiveNoun }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .nounGenitive }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .nounGenitive }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .nounGenitive }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .nounGenitive }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .nounGenitive }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .nounGenitive }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .nounGenitive }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .nounGenitive }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .genitiveNoun }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .genitiveNoun }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .genitiveNoun }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .genitiveNoun }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .genitiveNoun }
  , { walsCode := "mnt", language := "Mentawai", iso := "mwv", value := .nounGenitive }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .genitiveNoun }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .genitiveNoun }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .genitiveNoun }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .genitiveNoun }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .genitiveNoun }
  , { walsCode := "mii", language := "Miisiirii", iso := "", value := .genitiveNoun }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .genitiveNoun }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .nounGenitive }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .nounGenitive }
  , { walsCode := "mnv", language := "Minaveha", iso := "mvn", value := .genitiveNoun }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .genitiveNoun }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .genitiveNoun }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noDominantOrder }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .genitiveNoun }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .genitiveNoun }
  , { walsCode := "mxa", language := "Mixtec (Atatlahuca)", iso := "mib", value := .nounGenitive }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .nounGenitive }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .nounGenitive }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .nounGenitive }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .nounGenitive }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .nounGenitive }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .genitiveNoun }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .genitiveNoun }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .genitiveNoun }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .noDominantOrder }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .nounGenitive }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .genitiveNoun }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noDominantOrder }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .genitiveNoun }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .genitiveNoun }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .nounGenitive }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .nounGenitive }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .nounGenitive }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .genitiveNoun }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .genitiveNoun }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noDominantOrder }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .genitiveNoun }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .genitiveNoun }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .genitiveNoun }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .genitiveNoun }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .nounGenitive }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .nounGenitive }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .genitiveNoun }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .genitiveNoun }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .genitiveNoun }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .nounGenitive }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .genitiveNoun }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noDominantOrder }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .nounGenitive }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .nounGenitive }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .nounGenitive }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .genitiveNoun }
  , { walsCode := "mnz", language := "Munzombo", iso := "moj", value := .nounGenitive }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .nounGenitive }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .nounGenitive }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .nounGenitive }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .nounGenitive }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .genitiveNoun }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .nounGenitive }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .nounGenitive }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .nounGenitive }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .genitiveNoun }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .nounGenitive }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .genitiveNoun }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .nounGenitive }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .genitiveNoun }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .genitiveNoun }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .genitiveNoun }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .nounGenitive }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .noDominantOrder }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .nounGenitive }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .genitiveNoun }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .nounGenitive }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .genitiveNoun }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .genitiveNoun }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .nounGenitive }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .nounGenitive }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .nounGenitive }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .genitiveNoun }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .genitiveNoun }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .genitiveNoun }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .genitiveNoun }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noDominantOrder }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .genitiveNoun }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .genitiveNoun }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .nounGenitive }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .nounGenitive }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .nounGenitive }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .nounGenitive }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noDominantOrder }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .nounGenitive }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .noDominantOrder }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .genitiveNoun }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .nounGenitive }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .nounGenitive }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .genitiveNoun }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .genitiveNoun }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .genitiveNoun }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .genitiveNoun }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .genitiveNoun }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .genitiveNoun }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .genitiveNoun }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .nounGenitive }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noDominantOrder }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .nounGenitive }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .nounGenitive }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .noDominantOrder }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .nounGenitive }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .nounGenitive }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .genitiveNoun }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .genitiveNoun }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .nounGenitive }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .nounGenitive }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .nounGenitive }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .genitiveNoun }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .nounGenitive }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .nounGenitive }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .genitiveNoun }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .nounGenitive }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .nounGenitive }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .genitiveNoun }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .genitiveNoun }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .nounGenitive }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .genitiveNoun }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .nounGenitive }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .nounGenitive }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .noDominantOrder }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .genitiveNoun }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .genitiveNoun }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .genitiveNoun }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .nounGenitive }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .nounGenitive }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noDominantOrder }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .nounGenitive }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .nounGenitive }
  , { walsCode := "nng", language := "Nyanga", iso := "nyj", value := .nounGenitive }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .noDominantOrder }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .genitiveNoun }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .genitiveNoun }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .nounGenitive }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noDominantOrder }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .nounGenitive }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .noDominantOrder }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .genitiveNoun }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .genitiveNoun }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .noDominantOrder }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .genitiveNoun }
  , { walsCode := "one", language := "One", iso := "aun", value := .noDominantOrder }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noDominantOrder }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .genitiveNoun }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .genitiveNoun }
  , { walsCode := "ori", language := "Orig", iso := "tag", value := .nounGenitive }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .genitiveNoun }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .genitiveNoun }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .nounGenitive }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .nounGenitive }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .genitiveNoun }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .genitiveNoun }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .genitiveNoun }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .nounGenitive }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .nounGenitive }
  , { walsCode := "owi", language := "Owininga", iso := "owi", value := .genitiveNoun }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .nounGenitive }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .nounGenitive }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .genitiveNoun }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .nounGenitive }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .nounGenitive }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .nounGenitive }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .genitiveNoun }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .genitiveNoun }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .nounGenitive }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .genitiveNoun }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .noDominantOrder }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .nounGenitive }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .genitiveNoun }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .genitiveNoun }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .genitiveNoun }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .genitiveNoun }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .genitiveNoun }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .genitiveNoun }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .nounGenitive }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .nounGenitive }
  , { walsCode := "ppc", language := "Piapoco", iso := "pio", value := .genitiveNoun }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .genitiveNoun }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .nounGenitive }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .genitiveNoun }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .nounGenitive }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .genitiveNoun }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .genitiveNoun }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .genitiveNoun }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .genitiveNoun }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .genitiveNoun }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .nounGenitive }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noDominantOrder }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .genitiveNoun }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .nounGenitive }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .nounGenitive }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .genitiveNoun }
  , { walsCode := "pmn", language := "Pomo (Northern)", iso := "pej", value := .genitiveNoun }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .genitiveNoun }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .genitiveNoun }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .nounGenitive }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .nounGenitive }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .genitiveNoun }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .genitiveNoun }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .genitiveNoun }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .genitiveNoun }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noDominantOrder }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .genitiveNoun }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .nounGenitive }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .genitiveNoun }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .genitiveNoun }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .genitiveNoun }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .genitiveNoun }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .genitiveNoun }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .nounGenitive }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .nounGenitive }
  , { walsCode := "ral", language := "Ralte", iso := "ral", value := .genitiveNoun }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .genitiveNoun }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .genitiveNoun }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .nounGenitive }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .nounGenitive }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .genitiveNoun }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .genitiveNoun }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .genitiveNoun }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .genitiveNoun }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .genitiveNoun }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .nounGenitive }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .nounGenitive }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .nounGenitive }
  , { walsCode := "rga", language := "Ronga", iso := "rng", value := .nounGenitive }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .nounGenitive }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .nounGenitive }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .nounGenitive }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .noDominantOrder }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .genitiveNoun }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .genitiveNoun }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .nounGenitive }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .nounGenitive }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .genitiveNoun }
  , { walsCode := "saa", language := "Sa'a", iso := "apb", value := .nounGenitive }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .genitiveNoun }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .genitiveNoun }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .nounGenitive }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .genitiveNoun }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .nounGenitive }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .genitiveNoun }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .nounGenitive }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .genitiveNoun }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .nounGenitive }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .nounGenitive }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .genitiveNoun }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .genitiveNoun }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .genitiveNoun }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .genitiveNoun }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .genitiveNoun }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .genitiveNoun }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .genitiveNoun }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .nounGenitive }
  , { walsCode := "sec", language := "Secoya", iso := "sey", value := .genitiveNoun }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .nounGenitive }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .nounGenitive }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .genitiveNoun }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .genitiveNoun }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .genitiveNoun }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .genitiveNoun }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .nounGenitive }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .genitiveNoun }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .genitiveNoun }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .noDominantOrder }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .genitiveNoun }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .nounGenitive }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .nounGenitive }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .nounGenitive }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .genitiveNoun }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .nounGenitive }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .genitiveNoun }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .genitiveNoun }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .genitiveNoun }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .nounGenitive }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .nounGenitive }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .genitiveNoun }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .nounGenitive }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .genitiveNoun }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .genitiveNoun }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .nounGenitive }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .nounGenitive }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .genitiveNoun }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .genitiveNoun }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .genitiveNoun }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .nounGenitive }
  ]

private def allData_2 : List (Datapoint GenitiveNounOrder) :=
  [ { walsCode := "srn", language := "Sirionó", iso := "srq", value := .genitiveNoun }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .genitiveNoun }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .nounGenitive }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noDominantOrder }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .genitiveNoun }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .genitiveNoun }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .noDominantOrder }
  , { walsCode := "so", language := "So", iso := "teu", value := .nounGenitive }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .genitiveNoun }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .genitiveNoun }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noDominantOrder }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .nounGenitive }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .nounGenitive }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .genitiveNoun }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .genitiveNoun }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .nounGenitive }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .nounGenitive }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .nounGenitive }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .nounGenitive }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .genitiveNoun }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .genitiveNoun }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .genitiveNoun }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noDominantOrder }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .nounGenitive }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .genitiveNoun }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .genitiveNoun }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .genitiveNoun }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .nounGenitive }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .nounGenitive }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .genitiveNoun }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .genitiveNoun }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .genitiveNoun }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .nounGenitive }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .genitiveNoun }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .nounGenitive }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .noDominantOrder }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .nounGenitive }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .genitiveNoun }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .nounGenitive }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .genitiveNoun }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .genitiveNoun }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .genitiveNoun }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .genitiveNoun }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .nounGenitive }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .genitiveNoun }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .nounGenitive }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .genitiveNoun }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .genitiveNoun }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .genitiveNoun }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .genitiveNoun }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .genitiveNoun }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .nounGenitive }
  , { walsCode := "tsm", language := "Tasmanian", iso := "", value := .genitiveNoun }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .nounGenitive }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .genitiveNoun }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .genitiveNoun }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .nounGenitive }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .genitiveNoun }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .genitiveNoun }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .nounGenitive }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .genitiveNoun }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .genitiveNoun }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .nounGenitive }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .nounGenitive }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .nounGenitive }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .nounGenitive }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .nounGenitive }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .nounGenitive }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .genitiveNoun }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .nounGenitive }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .genitiveNoun }
  , { walsCode := "trt", language := "Ternate", iso := "tft", value := .genitiveNoun }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .nounGenitive }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .nounGenitive }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .genitiveNoun }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .genitiveNoun }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .nounGenitive }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .genitiveNoun }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .genitiveNoun }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .genitiveNoun }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .genitiveNoun }
  , { walsCode := "tdi", language := "Tibetan (Dingri)", iso := "bod", value := .genitiveNoun }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .genitiveNoun }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .genitiveNoun }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .genitiveNoun }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .noDominantOrder }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .genitiveNoun }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .nounGenitive }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .noDominantOrder }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .nounGenitive }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .genitiveNoun }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .nounGenitive }
  , { walsCode := "tia", language := "Tima", iso := "tms", value := .nounGenitive }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .nounGenitive }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .nounGenitive }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .genitiveNoun }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .nounGenitive }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .genitiveNoun }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .nounGenitive }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .genitiveNoun }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .nounGenitive }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .genitiveNoun }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .genitiveNoun }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .nounGenitive }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .nounGenitive }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .nounGenitive }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .nounGenitive }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .genitiveNoun }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .genitiveNoun }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .nounGenitive }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .nounGenitive }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .genitiveNoun }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .genitiveNoun }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .genitiveNoun }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .genitiveNoun }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .nounGenitive }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .genitiveNoun }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .nounGenitive }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .nounGenitive }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .nounGenitive }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .genitiveNoun }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .nounGenitive }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .genitiveNoun }
  , { walsCode := "tnb", language := "Tunebo", iso := "tuf", value := .genitiveNoun }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .nounGenitive }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .nounGenitive }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .genitiveNoun }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .nounGenitive }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .genitiveNoun }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .genitiveNoun }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .genitiveNoun }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .nounGenitive }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .genitiveNoun }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .genitiveNoun }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .nounGenitive }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .nounGenitive }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .genitiveNoun }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .genitiveNoun }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .genitiveNoun }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .genitiveNoun }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .nounGenitive }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .genitiveNoun }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .genitiveNoun }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noDominantOrder }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .nounGenitive }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .genitiveNoun }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .nounGenitive }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .genitiveNoun }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .nounGenitive }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .genitiveNoun }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .genitiveNoun }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .genitiveNoun }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .genitiveNoun }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .genitiveNoun }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .genitiveNoun }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .nounGenitive }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .genitiveNoun }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .nounGenitive }
  , { walsCode := "vif", language := "Vili", iso := "vif", value := .nounGenitive }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .nounGenitive }
  , { walsCode := "wwa", language := "Waama", iso := "wwa", value := .genitiveNoun }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .genitiveNoun }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .genitiveNoun }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .genitiveNoun }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .noDominantOrder }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .genitiveNoun }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .genitiveNoun }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .genitiveNoun }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .genitiveNoun }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .genitiveNoun }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .genitiveNoun }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noDominantOrder }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .nounGenitive }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .genitiveNoun }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .nounGenitive }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .nounGenitive }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .genitiveNoun }
  , { walsCode := "was", language := "Washo", iso := "was", value := .genitiveNoun }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .genitiveNoun }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .genitiveNoun }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .genitiveNoun }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .genitiveNoun }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .nounGenitive }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .genitiveNoun }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .genitiveNoun }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .genitiveNoun }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .genitiveNoun }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .genitiveNoun }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .genitiveNoun }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .genitiveNoun }
  , { walsCode := "wog", language := "Wogamusin", iso := "wog", value := .genitiveNoun }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .genitiveNoun }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .genitiveNoun }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .noDominantOrder }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .nounGenitive }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .nounGenitive }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .genitiveNoun }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .genitiveNoun }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .genitiveNoun }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .genitiveNoun }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .nounGenitive }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .noDominantOrder }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .genitiveNoun }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .genitiveNoun }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .genitiveNoun }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .genitiveNoun }
  , { walsCode := "ybi", language := "Yamphu", iso := "ybi", value := .genitiveNoun }
  , { walsCode := "yns", language := "Yansi", iso := "yns", value := .nounGenitive }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .nounGenitive }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .genitiveNoun }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .genitiveNoun }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .genitiveNoun }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .nounGenitive }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .nounGenitive }
  , { walsCode := "yyg", language := "Yaygir", iso := "xya", value := .genitiveNoun }
  , { walsCode := "yei", language := "Yei", iso := "jei", value := .genitiveNoun }
  , { walsCode := "ylm", language := "Yelmek", iso := "jel", value := .noDominantOrder }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .genitiveNoun }
  , { walsCode := "yiw", language := "Yi (Wuding-Luquan)", iso := "ywq", value := .genitiveNoun }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .genitiveNoun }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .genitiveNoun }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .genitiveNoun }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .noDominantOrder }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .nounGenitive }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .genitiveNoun }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .genitiveNoun }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .genitiveNoun }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .genitiveNoun }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .genitiveNoun }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .nounGenitive }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .genitiveNoun }
  , { walsCode := "yrm", language := "Yurimangí", iso := "", value := .genitiveNoun }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .genitiveNoun }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .noDominantOrder }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .noDominantOrder }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .genitiveNoun }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .nounGenitive }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .nounGenitive }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .nounGenitive }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .genitiveNoun }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .genitiveNoun }
  , { walsCode := "zen", language := "Zenaga", iso := "zen", value := .nounGenitive }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .genitiveNoun }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .genitiveNoun }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .nounGenitive }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .genitiveNoun }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .genitiveNoun }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .genitiveNoun }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .genitiveNoun }
  ]

/-- Complete WALS 86A dataset (1249 languages). -/
def allData : List (Datapoint GenitiveNounOrder) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1249 := by native_decide

theorem count_genitiveNoun :
    (allData.filter (·.value == .genitiveNoun)).length = 685 := by native_decide
theorem count_nounGenitive :
    (allData.filter (·.value == .nounGenitive)).length = 468 := by native_decide
theorem count_noDominantOrder :
    (allData.filter (·.value == .noDominantOrder)).length = 96 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F86A
