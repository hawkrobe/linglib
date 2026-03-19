import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 33A: Coding of Nominal Plurality
@cite{haspelmath-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 33A`.

Chapter 33, 1066 languages.
-/

namespace Core.WALS.F33A

/-- WALS 33A values. -/
inductive PluralityCoding where
  | pluralPrefix  -- Plural prefix (126 languages)
  | pluralSuffix  -- Plural suffix (513 languages)
  | pluralStemChange  -- Plural stem change (6 languages)
  | pluralTone  -- Plural tone (4 languages)
  | pluralCompleteReduplication  -- Plural complete reduplication (8 languages)
  | mixedMorphologicalPlural  -- Mixed morphological plural (60 languages)
  | pluralWord  -- Plural word (170 languages)
  | pluralClitic  -- Plural clitic (81 languages)
  | noPlural  -- No plural (98 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint PluralityCoding) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .pluralSuffix }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .noPlural }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .pluralSuffix }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .pluralSuffix }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .pluralWord }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noPlural }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noPlural }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .pluralSuffix }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .mixedMorphologicalPlural }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .pluralSuffix }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .noPlural }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .pluralPrefix }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .pluralWord }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .pluralWord }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .pluralSuffix }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .pluralClitic }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .mixedMorphologicalPlural }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .pluralClitic }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .pluralPrefix }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .pluralSuffix }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .pluralSuffix }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .pluralSuffix }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .noPlural }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .noPlural }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .pluralWord }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .pluralClitic }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .mixedMorphologicalPlural }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .pluralSuffix }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .pluralPrefix }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .pluralSuffix }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .pluralPrefix }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .pluralClitic }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .pluralWord }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .pluralSuffix }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .pluralPrefix }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .pluralClitic }
  , { walsCode := "ayi", language := "Anyi", iso := "any", value := .pluralPrefix }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .pluralSuffix }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .pluralSuffix }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .pluralWord }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .pluralWord }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .pluralWord }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .pluralSuffix }
  , { walsCode := "abn", language := "Arabana", iso := "ard", value := .pluralSuffix }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .mixedMorphologicalPlural }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .mixedMorphologicalPlural }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .mixedMorphologicalPlural }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .mixedMorphologicalPlural }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .mixedMorphologicalPlural }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .mixedMorphologicalPlural }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .pluralWord }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .pluralSuffix }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .pluralSuffix }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .pluralSuffix }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .pluralSuffix }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .pluralWord }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .pluralWord }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noPlural }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .pluralSuffix }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .pluralSuffix }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .pluralSuffix }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .pluralSuffix }
  , { walsCode := "avk", language := "Avikam", iso := "avi", value := .pluralWord }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .pluralSuffix }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .pluralSuffix }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .pluralSuffix }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .pluralSuffix }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .pluralSuffix }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .pluralSuffix }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .pluralSuffix }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .pluralSuffix }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .pluralPrefix }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .pluralClitic }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .pluralWord }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .pluralWord }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .pluralWord }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .pluralClitic }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .pluralClitic }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .pluralPrefix }
  , { walsCode := "blg", language := "Balangao", iso := "blw", value := .pluralPrefix }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .pluralWord }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .pluralSuffix }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .pluralSuffix }
  , { walsCode := "bnk", language := "Bankon", iso := "abb", value := .pluralPrefix }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .pluralWord }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .pluralClitic }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .pluralSuffix }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .pluralPrefix }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .pluralSuffix }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .pluralSuffix }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .noPlural }
  , { walsCode := "bry", language := "Baruya", iso := "byr", value := .pluralClitic }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .pluralSuffix }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .pluralPrefix }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .pluralSuffix }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .pluralClitic }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .pluralCompleteReduplication }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .pluralWord }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .pluralSuffix }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .pluralWord }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .pluralSuffix }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .pluralPrefix }
  , { walsCode := "blu", language := "Bena-Lulua", iso := "lua", value := .pluralPrefix }
  , { walsCode := "bga", language := "Benga", iso := "bng", value := .pluralPrefix }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .mixedMorphologicalPlural }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .mixedMorphologicalPlural }
  , { walsCode := "bmz", language := "Berber (Mzab)", iso := "mzb", value := .pluralSuffix }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .mixedMorphologicalPlural }
  , { walsCode := "bsi", language := "Berber (Siwa)", iso := "siz", value := .mixedMorphologicalPlural }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .pluralTone }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .mixedMorphologicalPlural }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .pluralSuffix }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .pluralSuffix }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .pluralSuffix }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .pluralClitic }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .pluralSuffix }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .pluralWord }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .pluralSuffix }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .noPlural }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .pluralWord }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .mixedMorphologicalPlural }
  , { walsCode := "big", language := "Binga", iso := "yul", value := .pluralSuffix }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .noPlural }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .pluralPrefix }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .noPlural }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .pluralPrefix }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .pluralSuffix }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .pluralPrefix }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .pluralClitic }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .pluralSuffix }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .pluralClitic }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .pluralPrefix }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .pluralSuffix }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .pluralSuffix }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .pluralSuffix }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .pluralPrefix }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .pluralSuffix }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .pluralSuffix }
  , { walsCode := "bun", language := "Buin", iso := "buo", value := .pluralSuffix }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .pluralSuffix }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .pluralSuffix }
  , { walsCode := "pnu", language := "Bunu (Younuo)", iso := "buh", value := .noPlural }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .pluralClitic }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .pluralSuffix }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .pluralWord }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .pluralSuffix }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .pluralSuffix }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .pluralClitic }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .pluralPrefix }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .pluralSuffix }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .pluralSuffix }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .mixedMorphologicalPlural }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .pluralSuffix }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .pluralSuffix }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .pluralWord }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noPlural }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noPlural }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .pluralSuffix }
  , { walsCode := "car", language := "Carib", iso := "car", value := .pluralSuffix }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .pluralSuffix }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .pluralSuffix }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .pluralClitic }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .pluralClitic }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .noPlural }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .pluralSuffix }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .pluralSuffix }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .pluralSuffix }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .pluralWord }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .pluralSuffix }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .pluralSuffix }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .noPlural }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .noPlural }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .pluralSuffix }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .pluralSuffix }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .pluralPrefix }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .pluralPrefix }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noPlural }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .pluralWord }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .pluralSuffix }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .noPlural }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .pluralWord }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .pluralWord }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .noPlural }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .noPlural }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .pluralSuffix }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .pluralSuffix }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .pluralSuffix }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .pluralSuffix }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .noPlural }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .pluralSuffix }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .pluralSuffix }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .pluralSuffix }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noPlural }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .pluralSuffix }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .pluralSuffix }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .pluralWord }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .pluralSuffix }
  , { walsCode := "coe", language := "Coeur d'Alene", iso := "crd", value := .pluralWord }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .pluralSuffix }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .mixedMorphologicalPlural }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .noPlural }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .pluralSuffix }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .pluralSuffix }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .pluralSuffix }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .pluralSuffix }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .pluralSuffix }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .pluralWord }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .pluralSuffix }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .pluralWord }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .pluralSuffix }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .pluralSuffix }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .pluralWord }
  , { walsCode := "day", language := "Day", iso := "dai", value := .pluralWord }
  , { walsCode := "des", language := "Desano", iso := "des", value := .pluralSuffix }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .pluralSuffix }
  , { walsCode := "dhw", language := "Dharawal", iso := "tbh", value := .pluralSuffix }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .pluralSuffix }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .pluralSuffix }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noPlural }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .pluralSuffix }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .pluralClitic }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .pluralStemChange }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .pluralPrefix }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .pluralWord }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .pluralCompleteReduplication }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .pluralSuffix }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .pluralSuffix }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .pluralSuffix }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .pluralSuffix }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noPlural }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .pluralSuffix }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .pluralClitic }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .pluralSuffix }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .pluralWord }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .pluralWord }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .pluralClitic }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .pluralSuffix }
  , { walsCode := "daw", language := "Dâw", iso := "kwa", value := .pluralClitic }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .pluralSuffix }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .pluralSuffix }
  , { walsCode := "ene", language := "Enets", iso := "", value := .pluralSuffix }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noPlural }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .pluralPrefix }
  , { walsCode := "eng", language := "English", iso := "eng", value := .pluralSuffix }
  , { walsCode := "eny", language := "Enya", iso := "gey", value := .pluralPrefix }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .pluralClitic }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .pluralWord }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .pluralWord }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .pluralSuffix }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .pluralPrefix }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .pluralSuffix }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .pluralSuffix }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .pluralClitic }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .pluralPrefix }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .pluralSuffix }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .pluralSuffix }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .pluralWord }
  , { walsCode := "for", language := "Fore", iso := "for", value := .pluralSuffix }
  , { walsCode := "fre", language := "French", iso := "fra", value := .pluralSuffix }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .pluralSuffix }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .pluralSuffix }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .mixedMorphologicalPlural }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .pluralWord }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .pluralPrefix }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .pluralSuffix }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .pluralSuffix }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .mixedMorphologicalPlural }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .pluralSuffix }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .pluralSuffix }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .pluralSuffix }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .pluralClitic }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .pluralSuffix }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .pluralPrefix }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .pluralWord }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .pluralWord }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .pluralSuffix }
  , { walsCode := "ger", language := "German", iso := "deu", value := .pluralSuffix }
  , { walsCode := "gil", language := "Gilaki", iso := "glk", value := .pluralSuffix }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .pluralSuffix }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .pluralPrefix }
  , { walsCode := "giz", language := "Giziga", iso := "gis", value := .pluralWord }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .pluralSuffix }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .pluralSuffix }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .pluralWord }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .pluralWord }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .pluralWord }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .pluralSuffix }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .pluralClitic }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .pluralSuffix }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .pluralSuffix }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .pluralSuffix }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .pluralWord }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .pluralSuffix }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .pluralSuffix }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .pluralWord }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .pluralSuffix }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .pluralSuffix }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .noPlural }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .pluralSuffix }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .pluralWord }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .pluralSuffix }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .pluralTone }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .pluralSuffix }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .pluralSuffix }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .noPlural }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .pluralSuffix }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .pluralWord }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .pluralSuffix }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .pluralClitic }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .pluralSuffix }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .pluralWord }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .pluralPrefix }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .pluralSuffix }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .pluralSuffix }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .pluralSuffix }
  , { walsCode := "hem", language := "Hemba", iso := "hem", value := .pluralPrefix }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .pluralSuffix }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .pluralSuffix }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .pluralWord }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .pluralSuffix }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .pluralSuffix }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .pluralWord }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .pluralSuffix }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .pluralSuffix }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .pluralSuffix }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .pluralPrefix }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .pluralSuffix }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .pluralSuffix }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .pluralSuffix }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .pluralPrefix }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .pluralSuffix }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .pluralSuffix }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .pluralClitic }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .noPlural }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .noPlural }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .pluralWord }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noPlural }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .pluralSuffix }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .pluralSuffix }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .pluralPrefix }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .mixedMorphologicalPlural }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .pluralSuffix }
  , { walsCode := "iha", language := "Iha", iso := "ihp", value := .mixedMorphologicalPlural }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .pluralSuffix }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .pluralSuffix }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .pluralWord }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .pluralPrefix }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noPlural }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .pluralSuffix }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .pluralCompleteReduplication }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .pluralSuffix }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .pluralSuffix }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .pluralSuffix }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .noPlural }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .pluralSuffix }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .mixedMorphologicalPlural }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .pluralSuffix }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .pluralSuffix }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .pluralSuffix }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .pluralPrefix }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .pluralPrefix }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .noPlural }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .pluralWord }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .mixedMorphologicalPlural }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .pluralSuffix }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .pluralSuffix }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .pluralSuffix }
  , { walsCode := "jel", language := "Jeli", iso := "jek", value := .pluralClitic }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .pluralWord }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .pluralSuffix }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .pluralSuffix }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .pluralPrefix }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .pluralWord }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .pluralClitic }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .pluralSuffix }
  , { walsCode := "kac", language := "Kachari", iso := "xac", value := .pluralSuffix }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .pluralSuffix }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .pluralPrefix }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .pluralPrefix }
  , { walsCode := "kai", language := "Kaian", iso := "kct", value := .pluralSuffix }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .pluralWord }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .pluralSuffix }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .pluralSuffix }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .noPlural }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .pluralSuffix }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .pluralPrefix }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .pluralWord }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .pluralSuffix }
  , { walsCode := "kbu", language := "Kanembu", iso := "kbl", value := .pluralSuffix }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .pluralSuffix }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .pluralSuffix }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .pluralPrefix }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .pluralClitic }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .pluralSuffix }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .pluralSuffix }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .pluralSuffix }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .noPlural }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .pluralWord }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .pluralPrefix }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .pluralSuffix }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .pluralClitic }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .pluralPrefix }
  , { walsCode := "ktm", language := "Kathlamet", iso := "", value := .mixedMorphologicalPlural }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .pluralPrefix }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .pluralSuffix }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .noPlural }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noPlural }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noPlural }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .noPlural }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .pluralSuffix }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .pluralClitic }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .pluralPrefix }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .pluralClitic }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .pluralSuffix }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .pluralSuffix }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .pluralSuffix }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .pluralSuffix }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .mixedMorphologicalPlural }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .pluralSuffix }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .pluralClitic }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .pluralSuffix }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .pluralClitic }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .pluralWord }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .pluralSuffix }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .pluralWord }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noPlural }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .pluralPrefix }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .mixedMorphologicalPlural }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .pluralSuffix }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .pluralWord }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .pluralPrefix }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .pluralSuffix }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .pluralSuffix }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .pluralSuffix }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .pluralSuffix }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .pluralSuffix }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .mixedMorphologicalPlural }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .pluralSuffix }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .pluralClitic }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .pluralSuffix }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .mixedMorphologicalPlural }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .pluralSuffix }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .pluralSuffix }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .pluralClitic }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .pluralSuffix }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .pluralClitic }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .pluralSuffix }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .pluralSuffix }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .pluralSuffix }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .pluralWord }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .pluralSuffix }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .pluralWord }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .pluralSuffix }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .pluralPrefix }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .pluralPrefix }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .pluralSuffix }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .pluralSuffix }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .pluralSuffix }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .pluralSuffix }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .pluralSuffix }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .pluralSuffix }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .pluralSuffix }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .pluralSuffix }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .pluralSuffix }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .pluralWord }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .pluralClitic }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .pluralSuffix }
  , { walsCode := "kpo", language := "Kposo", iso := "kpo", value := .pluralClitic }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .pluralWord }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .pluralPrefix }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .noPlural }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .pluralCompleteReduplication }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .pluralSuffix }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .pluralClitic }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .pluralWord }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .pluralSuffix }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .pluralPrefix }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .noPlural }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .pluralSuffix }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .pluralWord }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .pluralPrefix }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noPlural }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .pluralWord }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .pluralSuffix }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .pluralSuffix }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .pluralWord }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .pluralClitic }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .pluralSuffix }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .pluralStemChange }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .pluralSuffix }
  , { walsCode := "laf", language := "Lafofa", iso := "laf", value := .pluralPrefix }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .mixedMorphologicalPlural }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .pluralSuffix }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .pluralWord }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .pluralWord }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .noPlural }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .pluralCompleteReduplication }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .pluralSuffix }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .pluralSuffix }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .pluralPrefix }
  ]

private def allData_1 : List (Datapoint PluralityCoding) :=
  [ { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .pluralWord }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .pluralSuffix }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noPlural }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .pluralSuffix }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .pluralSuffix }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .pluralSuffix }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .pluralPrefix }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .pluralSuffix }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .pluralSuffix }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .pluralPrefix }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .pluralWord }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .pluralSuffix }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .pluralSuffix }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .pluralWord }
  , { walsCode := "les", language := "Lese", iso := "les", value := .pluralSuffix }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .pluralClitic }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .pluralWord }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .pluralSuffix }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .noPlural }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .pluralWord }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .pluralSuffix }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .pluralSuffix }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .pluralPrefix }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .pluralClitic }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .pluralWord }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .mixedMorphologicalPlural }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .pluralWord }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .pluralPrefix }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .pluralSuffix }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .pluralSuffix }
  , { walsCode := "lul", language := "Lule", iso := "ule", value := .pluralSuffix }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .pluralPrefix }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .pluralSuffix }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .pluralSuffix }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .pluralPrefix }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .pluralPrefix }
  , { walsCode := "jlu", language := "Luwo", iso := "lwo", value := .pluralSuffix }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .pluralSuffix }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .mixedMorphologicalPlural }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .pluralSuffix }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .pluralSuffix }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .pluralSuffix }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .pluralWord }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .pluralWord }
  , { walsCode := "mgh", language := "Magahi", iso := "mag", value := .pluralSuffix }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .pluralSuffix }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .pluralSuffix }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .pluralSuffix }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .pluralClitic }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .pluralWord }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .pluralSuffix }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .pluralClitic }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .pluralClitic }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .pluralPrefix }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noPlural }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .pluralSuffix }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .pluralClitic }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .pluralWord }
  , { walsCode := "mmi", language := "Mambai", iso := "mcs", value := .pluralSuffix }
  , { walsCode := "mmv", language := "Mamvu", iso := "mdi", value := .mixedMorphologicalPlural }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .noPlural }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .pluralSuffix }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .pluralSuffix }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .pluralSuffix }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .pluralSuffix }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .pluralSuffix }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .pluralPrefix }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .noPlural }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .pluralClitic }
  , { walsCode := "mgq", language := "Mango", iso := "mge", value := .pluralSuffix }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .pluralClitic }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .pluralSuffix }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .pluralWord }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .pluralSuffix }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .pluralWord }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .pluralWord }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .pluralPrefix }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noPlural }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .pluralSuffix }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .pluralClitic }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .pluralSuffix }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .pluralStemChange }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .pluralSuffix }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .pluralWord }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .pluralSuffix }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .pluralPrefix }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .pluralSuffix }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .pluralSuffix }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .pluralSuffix }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .pluralPrefix }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .pluralWord }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .pluralWord }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noPlural }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .pluralPrefix }
  , { walsCode := "mzn", language := "Mazanderani", iso := "mzn", value := .pluralSuffix }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .pluralSuffix }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .pluralSuffix }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .pluralClitic }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .pluralPrefix }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .pluralPrefix }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .pluralPrefix }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .pluralWord }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .pluralSuffix }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .pluralSuffix }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .pluralClitic }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .pluralSuffix }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .pluralSuffix }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .pluralSuffix }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .pluralSuffix }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .pluralSuffix }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .noPlural }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .pluralSuffix }
  , { walsCode := "mkr", language := "Mikarew", iso := "msy", value := .pluralSuffix }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .mixedMorphologicalPlural }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .pluralWord }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .pluralClitic }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noPlural }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .mixedMorphologicalPlural }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .pluralWord }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .pluralSuffix }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .pluralWord }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .pluralWord }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .noPlural }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .pluralWord }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .pluralWord }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .pluralWord }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .pluralSuffix }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .pluralWord }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .pluralClitic }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .pluralSuffix }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .pluralWord }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .pluralSuffix }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .pluralPrefix }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .pluralClitic }
  , { walsCode := "fqs", language := "Momu", iso := "fqs", value := .noPlural }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .pluralWord }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .mixedMorphologicalPlural }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .pluralSuffix }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .pluralSuffix }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .pluralSuffix }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .pluralSuffix }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .pluralPrefix }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .pluralSuffix }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .pluralSuffix }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .mixedMorphologicalPlural }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .pluralSuffix }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .pluralWord }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .pluralSuffix }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .pluralWord }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .pluralSuffix }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .pluralClitic }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .pluralSuffix }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .pluralSuffix }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .pluralPrefix }
  , { walsCode := "mnz", language := "Munzombo", iso := "moj", value := .pluralClitic }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .pluralWord }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .pluralSuffix }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .pluralSuffix }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .mixedMorphologicalPlural }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .pluralSuffix }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .pluralWord }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .pluralSuffix }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .pluralPrefix }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .pluralWord }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .pluralSuffix }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .mixedMorphologicalPlural }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .pluralClitic }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .pluralWord }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .pluralSuffix }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .pluralSuffix }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .mixedMorphologicalPlural }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .pluralSuffix }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .pluralSuffix }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .pluralWord }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .pluralWord }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .pluralSuffix }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .noPlural }
  , { walsCode := "nde", language := "Nande", iso := "nnb", value := .pluralPrefix }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .pluralSuffix }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .pluralSuffix }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .pluralClitic }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .pluralSuffix }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .pluralSuffix }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .mixedMorphologicalPlural }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .pluralPrefix }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .pluralPrefix }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .pluralPrefix }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .pluralSuffix }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .pluralWord }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .pluralSuffix }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .pluralSuffix }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .pluralSuffix }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .pluralPrefix }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .pluralClitic }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .pluralClitic }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noPlural }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .pluralSuffix }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noPlural }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .pluralSuffix }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .pluralSuffix }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .pluralPrefix }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .mixedMorphologicalPlural }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .mixedMorphologicalPlural }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .pluralTone }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .pluralSuffix }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .pluralSuffix }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .pluralPrefix }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .pluralSuffix }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .pluralSuffix }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .pluralPrefix }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noPlural }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .noPlural }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .pluralWord }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .pluralWord }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .pluralSuffix }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .pluralPrefix }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .pluralPrefix }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .pluralPrefix }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .pluralSuffix }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .pluralSuffix }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .pluralPrefix }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .pluralSuffix }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .pluralSuffix }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .pluralSuffix }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .pluralStemChange }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .pluralWord }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .pluralPrefix }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .pluralClitic }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .pluralPrefix }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .noPlural }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .pluralWord }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .pluralPrefix }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .pluralPrefix }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .noPlural }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .pluralPrefix }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .pluralPrefix }
  , { walsCode := "oir", language := "Oirat", iso := "xal", value := .pluralSuffix }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .pluralSuffix }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .pluralSuffix }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .pluralSuffix }
  , { walsCode := "one", language := "One", iso := "aun", value := .pluralSuffix }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .mixedMorphologicalPlural }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .pluralSuffix }
  , { walsCode := "ord", language := "Ordos", iso := "mvf", value := .pluralSuffix }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .pluralSuffix }
  , { walsCode := "ork", language := "Orok", iso := "oaa", value := .pluralSuffix }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .pluralCompleteReduplication }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noPlural }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .noPlural }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .pluralWord }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .pluralSuffix }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .pluralPrefix }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .pluralSuffix }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .noPlural }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .pluralWord }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .mixedMorphologicalPlural }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .pluralPrefix }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .pluralSuffix }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .mixedMorphologicalPlural }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .pluralSuffix }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .pluralPrefix }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .pluralSuffix }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .pluralSuffix }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .pluralSuffix }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .pluralSuffix }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .pluralSuffix }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noPlural }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .pluralSuffix }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .noPlural }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .pluralSuffix }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .pluralSuffix }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .pluralSuffix }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .mixedMorphologicalPlural }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .pluralSuffix }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noPlural }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noPlural }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .noPlural }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .mixedMorphologicalPlural }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .pluralSuffix }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .pluralSuffix }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .pluralSuffix }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .pluralWord }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .pluralSuffix }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .pluralClitic }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .pluralSuffix }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .pluralSuffix }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .pluralSuffix }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .mixedMorphologicalPlural }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .pluralClitic }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .pluralSuffix }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .pluralSuffix }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .pluralPrefix }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .pluralWord }
  , { walsCode := "rji", language := "Raji", iso := "rji", value := .noPlural }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .pluralClitic }
  , { walsCode := "rao", language := "Rao", iso := "rao", value := .noPlural }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .pluralWord }
  , { walsCode := "ras", language := "Rashad", iso := "ras", value := .pluralSuffix }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .pluralWord }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .pluralSuffix }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .pluralSuffix }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .pluralSuffix }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .pluralSuffix }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .pluralSuffix }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .pluralPrefix }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .pluralSuffix }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .pluralSuffix }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .pluralSuffix }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .pluralSuffix }
  , { walsCode := "saa", language := "Sa'a", iso := "apb", value := .pluralWord }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .pluralSuffix }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noPlural }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .pluralPrefix }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .pluralSuffix }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .pluralSuffix }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noPlural }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .pluralWord }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .pluralWord }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .pluralSuffix }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .pluralPrefix }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .pluralSuffix }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .pluralSuffix }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .pluralWord }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .pluralSuffix }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .pluralSuffix }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .pluralClitic }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .pluralSuffix }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .pluralClitic }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .pluralSuffix }
  , { walsCode := "sec", language := "Secoya", iso := "sey", value := .pluralSuffix }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .pluralWord }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .pluralSuffix }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .pluralSuffix }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .pluralClitic }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .pluralTone }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .pluralSuffix }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noPlural }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .pluralSuffix }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .pluralSuffix }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .pluralWord }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .pluralPrefix }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .pluralSuffix }
  , { walsCode := "shd", language := "Sherdukpen", iso := "sdp", value := .pluralSuffix }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .pluralSuffix }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .pluralSuffix }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .pluralSuffix }
  , { walsCode := "shy", language := "Shira Yughur", iso := "yuy", value := .pluralSuffix }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .pluralWord }
  , { walsCode := "smp", language := "Shompen", iso := "sii", value := .noPlural }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .pluralPrefix }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .pluralSuffix }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .noPlural }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .pluralSuffix }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .pluralWord }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .pluralSuffix }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .pluralClitic }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .pluralSuffix }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .pluralWord }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .pluralWord }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .pluralWord }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .pluralSuffix }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .pluralSuffix }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .pluralSuffix }
  , { walsCode := "so", language := "So", iso := "teu", value := .pluralSuffix }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .pluralSuffix }
  , { walsCode := "som", language := "Somali", iso := "som", value := .pluralSuffix }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .noPlural }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .pluralSuffix }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .pluralPrefix }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .pluralSuffix }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .pluralWord }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .pluralSuffix }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .pluralSuffix }
  , { walsCode := "spi", language := "Spitian", iso := "spt", value := .pluralSuffix }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .pluralPrefix }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .pluralWord }
  , { walsCode := "sub", language := "Subiya", iso := "sbs", value := .pluralPrefix }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .mixedMorphologicalPlural }
  , { walsCode := "suk", language := "Suki", iso := "sui", value := .pluralSuffix }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .pluralPrefix }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .pluralCompleteReduplication }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .pluralSuffix }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .pluralSuffix }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .pluralPrefix }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .pluralSuffix }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .pluralClitic }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .noPlural }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .pluralPrefix }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .pluralWord }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .pluralWord }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .pluralWord }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .pluralSuffix }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .pluralSuffix }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .pluralSuffix }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .pluralWord }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .pluralSuffix }
  , { walsCode := "tmg", language := "Tamagario", iso := "tcg", value := .noPlural }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .pluralWord }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .mixedMorphologicalPlural }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .pluralSuffix }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .pluralSuffix }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .pluralSuffix }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .pluralStemChange }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .pluralSuffix }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .pluralSuffix }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .mixedMorphologicalPlural }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .pluralSuffix }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .pluralSuffix }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .pluralWord }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noPlural }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .pluralWord }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .pluralSuffix }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .pluralSuffix }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .mixedMorphologicalPlural }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .pluralPrefix }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .pluralSuffix }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .pluralSuffix }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .pluralWord }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .mixedMorphologicalPlural }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .pluralSuffix }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .pluralPrefix }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .pluralPrefix }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .pluralClitic }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .pluralSuffix }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .mixedMorphologicalPlural }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .pluralWord }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .pluralWord }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .pluralSuffix }
  , { walsCode := "thn", language := "Thangmi", iso := "thf", value := .pluralSuffix }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .noPlural }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .pluralWord }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .pluralSuffix }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noPlural }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .pluralWord }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .pluralSuffix }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .mixedMorphologicalPlural }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .pluralStemChange }
  , { walsCode := "tia", language := "Tima", iso := "tms", value := .pluralPrefix }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .pluralSuffix }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .pluralClitic }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .pluralWord }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .pluralSuffix }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .pluralSuffix }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .pluralSuffix }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .pluralSuffix }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .noPlural }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .pluralSuffix }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .pluralSuffix }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .noPlural }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .pluralWord }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .pluralWord }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .pluralPrefix }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .pluralWord }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .pluralSuffix }
  , { walsCode := "trw", language := "Torwali", iso := "trw", value := .pluralSuffix }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .mixedMorphologicalPlural }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .noPlural }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .pluralWord }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .pluralClitic }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .pluralSuffix }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .pluralClitic }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .pluralPrefix }
  , { walsCode := "tgo", language := "Tsogo", iso := "tsv", value := .pluralPrefix }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .pluralSuffix }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .mixedMorphologicalPlural }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .pluralSuffix }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .pluralSuffix }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .pluralWord }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noPlural }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .pluralSuffix }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .pluralPrefix }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .pluralWord }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .pluralSuffix }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .mixedMorphologicalPlural }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .pluralSuffix }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .pluralPrefix }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .pluralWord }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .pluralSuffix }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .pluralSuffix }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .pluralWord }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .pluralSuffix }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .pluralSuffix }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .pluralSuffix }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .pluralSuffix }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .pluralSuffix }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .pluralWord }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .pluralCompleteReduplication }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .pluralWord }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noPlural }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .pluralSuffix }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .pluralWord }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .pluralSuffix }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .pluralSuffix }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .pluralSuffix }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .pluralSuffix }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .pluralSuffix }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .pluralSuffix }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .pluralWord }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .pluralWord }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .pluralWord }
  ]

private def allData_2 : List (Datapoint PluralityCoding) :=
  [ { walsCode := "wah", language := "Wahgi", iso := "", value := .noPlural }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .pluralSuffix }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .pluralSuffix }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .pluralSuffix }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .pluralWord }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .pluralSuffix }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .pluralSuffix }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .pluralSuffix }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .pluralSuffix }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .pluralSuffix }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .pluralWord }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .pluralSuffix }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .pluralPrefix }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .pluralClitic }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .pluralSuffix }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .pluralPrefix }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .pluralSuffix }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noPlural }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .pluralSuffix }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .pluralSuffix }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .noPlural }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noPlural }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .pluralSuffix }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .pluralWord }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .mixedMorphologicalPlural }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .pluralSuffix }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .noPlural }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .pluralPrefix }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .pluralWord }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .pluralClitic }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .pluralSuffix }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .pluralSuffix }
  , { walsCode := "yam", language := "Yaminahua", iso := "yaa", value := .pluralSuffix }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .pluralPrefix }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .pluralWord }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .pluralSuffix }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .pluralSuffix }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .pluralSuffix }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .pluralWord }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noPlural }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .pluralSuffix }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .pluralSuffix }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .pluralSuffix }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .pluralWord }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .pluralWord }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .pluralSuffix }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .pluralSuffix }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .pluralSuffix }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .pluralSuffix }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .pluralClitic }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .pluralSuffix }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .mixedMorphologicalPlural }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .pluralSuffix }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .pluralPrefix }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .pluralSuffix }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .pluralWord }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .pluralPrefix }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .pluralClitic }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .pluralSuffix }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .noPlural }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .pluralSuffix }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .pluralPrefix }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .pluralSuffix }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .pluralSuffix }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .pluralClitic }
  , { walsCode := "omi", language := "Ömie", iso := "aom", value := .noPlural }
  ]

/-- Complete WALS 33A dataset (1066 languages). -/
def allData : List (Datapoint PluralityCoding) := allData_0 ++ allData_1 ++ allData_2

-- Count verification
theorem total_count : allData.length = 1066 := by native_decide

theorem count_pluralPrefix :
    (allData.filter (·.value == .pluralPrefix)).length = 126 := by native_decide
theorem count_pluralSuffix :
    (allData.filter (·.value == .pluralSuffix)).length = 513 := by native_decide
theorem count_pluralStemChange :
    (allData.filter (·.value == .pluralStemChange)).length = 6 := by native_decide
theorem count_pluralTone :
    (allData.filter (·.value == .pluralTone)).length = 4 := by native_decide
theorem count_pluralCompleteReduplication :
    (allData.filter (·.value == .pluralCompleteReduplication)).length = 8 := by native_decide
theorem count_mixedMorphologicalPlural :
    (allData.filter (·.value == .mixedMorphologicalPlural)).length = 60 := by native_decide
theorem count_pluralWord :
    (allData.filter (·.value == .pluralWord)).length = 170 := by native_decide
theorem count_pluralClitic :
    (allData.filter (·.value == .pluralClitic)).length = 81 := by native_decide
theorem count_noPlural :
    (allData.filter (·.value == .noPlural)).length = 98 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F33A
