/-!
# WALS Feature 96A: Relationship between the Order of Object and Verb and the Order of Relative Clause and Noun
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 96A`.

Chapter 96, 879 languages.
-/

namespace Core.WALS.F96A

/-- WALS 96A values. -/
inductive RelationshipBetweenTheOrderOfObjectAndVerbAndTheOrderOfRelativeClauseAndNoun where
  | ovAndReln  -- OV and RelN (132 languages)
  | ovAndNrel  -- OV and NRel (113 languages)
  | voAndReln  -- VO and RelN (5 languages)
  | voAndNrel  -- VO and NRel (416 languages)
  | other  -- Other (213 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 96A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : RelationshipBetweenTheOrderOfObjectAndVerbAndTheOrderOfRelativeClauseAndNoun
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .voAndNrel }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .other }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .voAndNrel }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .ovAndNrel }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .voAndNrel }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .ovAndReln }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .ovAndNrel }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .voAndNrel }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .other }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .voAndNrel }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .ovAndReln }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .voAndNrel }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .other }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .voAndNrel }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .other }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .voAndNrel }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .ovAndReln }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .other }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .ovAndReln }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .other }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .ovAndReln }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .other }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .voAndNrel }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .ovAndNrel }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .voAndNrel }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .voAndNrel }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .ovAndReln }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .other }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .ovAndNrel }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .ovAndReln }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .voAndReln }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .voAndNrel }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .voAndNrel }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .ovAndNrel }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .voAndNrel }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .ovAndNrel }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .voAndNrel }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .other }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .other }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .ovAndNrel }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .ovAndReln }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .other }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .voAndNrel }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .voAndNrel }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .voAndNrel }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .voAndNrel }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .voAndNrel }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .voAndNrel }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .ovAndNrel }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .ovAndNrel }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .other }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .ovAndNrel }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .voAndNrel }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .voAndNrel }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .ovAndNrel }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .other }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .ovAndReln }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .ovAndReln }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .other }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .ovAndReln }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .ovAndReln }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .other }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .voAndNrel }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .voAndNrel }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .other }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .other }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .voAndNrel }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .voAndNrel }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .voAndReln }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .voAndNrel }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .voAndNrel }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .voAndNrel }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .voAndNrel }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .voAndNrel }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .ovAndReln }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .other }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .ovAndReln }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .ovAndNrel }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .voAndNrel }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .ovAndNrel }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .voAndNrel }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .ovAndNrel }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .ovAndNrel }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .ovAndReln }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .ovAndReln }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .voAndNrel }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .voAndNrel }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .voAndNrel }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .other }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .ovAndNrel }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .ovAndReln }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .voAndNrel }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .other }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .voAndNrel }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .voAndNrel }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .voAndNrel }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .ovAndNrel }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .voAndNrel }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .voAndNrel }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .voAndNrel }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .other }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .voAndNrel }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .voAndNrel }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .voAndNrel }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .voAndNrel }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .other }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .voAndNrel }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .ovAndReln }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .ovAndNrel }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .voAndNrel }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .other }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .voAndNrel }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .voAndNrel }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .voAndNrel }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .voAndNrel }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .voAndNrel }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .other }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .ovAndReln }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .voAndNrel }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .voAndNrel }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .ovAndReln }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .ovAndNrel }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .voAndNrel }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .other }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .ovAndNrel }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .voAndNrel }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .ovAndReln }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .voAndNrel }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .other }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .other }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .other }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .voAndReln }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .ovAndNrel }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .voAndNrel }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .other }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .voAndNrel }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .ovAndReln }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .other }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .other }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .voAndNrel }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .voAndNrel }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .other }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .ovAndReln }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .voAndNrel }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .voAndNrel }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .ovAndReln }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .other }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .ovAndReln }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .ovAndReln }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .voAndNrel }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .other }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .other }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .ovAndReln }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .voAndNrel }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .voAndNrel }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .voAndNrel }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .voAndNrel }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .ovAndReln }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .ovAndNrel }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .ovAndNrel }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .other }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .voAndNrel }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .voAndNrel }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .voAndNrel }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .other }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .ovAndReln }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .ovAndNrel }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .other }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .voAndNrel }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .voAndNrel }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .voAndNrel }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .ovAndNrel }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .voAndNrel }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .voAndNrel }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .other }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .ovAndNrel }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .ovAndReln }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .other }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .ovAndNrel }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .ovAndNrel }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .voAndNrel }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .ovAndReln }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .other }
  , { walsCode := "day", language := "Day", iso := "dai", value := .voAndNrel }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .voAndNrel }
  , { walsCode := "des", language := "Desano", iso := "des", value := .ovAndNrel }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .other }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .ovAndReln }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .voAndNrel }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .other }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .ovAndReln }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .ovAndReln }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .other }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .voAndNrel }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .other }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .other }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .other }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .other }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .other }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .voAndNrel }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .other }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .other }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .voAndNrel }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .voAndNrel }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .voAndNrel }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .other }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .ovAndNrel }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .voAndNrel }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .other }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .ovAndReln }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .ovAndNrel }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .other }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .voAndNrel }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .voAndNrel }
  , { walsCode := "eng", language := "English", iso := "eng", value := .voAndNrel }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .other }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .voAndNrel }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .voAndNrel }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .ovAndNrel }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .ovAndReln }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .ovAndReln }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .voAndNrel }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .voAndNrel }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .voAndNrel }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .voAndNrel }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .voAndNrel }
  , { walsCode := "fre", language := "French", iso := "fra", value := .voAndNrel }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .other }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .voAndNrel }
  , { walsCode := "fni", language := "Fulfulde (Nigerian)", iso := "fuv", value := .voAndNrel }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .ovAndNrel }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .voAndNrel }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .voAndNrel }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .voAndNrel }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .voAndNrel }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .other }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .ovAndReln }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .ovAndReln }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .ovAndNrel }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .ovAndReln }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .voAndNrel }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .voAndNrel }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .voAndNrel }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .ovAndNrel }
  , { walsCode := "ger", language := "German", iso := "deu", value := .other }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .other }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .other }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .other }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .other }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .voAndNrel }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .voAndNrel }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .voAndNrel }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .ovAndNrel }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .ovAndNrel }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .other }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .voAndNrel }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .voAndNrel }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .other }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .other }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .voAndNrel }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .voAndNrel }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .other }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .other }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .other }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .ovAndReln }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .other }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .ovAndReln }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .other }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .voAndReln }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .voAndNrel }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .ovAndReln }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .ovAndReln }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .other }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .voAndNrel }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .voAndNrel }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .voAndNrel }
  , { walsCode := "hwr", language := "Hawrami", iso := "hac", value := .other }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .voAndNrel }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .ovAndReln }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .voAndNrel }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .voAndNrel }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .voAndNrel }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .ovAndNrel }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .other }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .ovAndNrel }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .voAndNrel }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .ovAndReln }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .voAndNrel }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .voAndNrel }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .ovAndReln }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .voAndNrel }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .voAndNrel }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .ovAndNrel }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .ovAndReln }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .voAndNrel }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .other }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .ovAndReln }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .ovAndReln }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .other }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .ovAndNrel }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .voAndNrel }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .ovAndNrel }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .voAndNrel }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .voAndNrel }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .other }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .ovAndNrel }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .voAndNrel }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .voAndNrel }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .voAndNrel }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .voAndNrel }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .ovAndReln }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .voAndNrel }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .other }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .voAndNrel }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .other }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .other }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .voAndNrel }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .voAndNrel }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .ovAndNrel }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .voAndNrel }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .voAndNrel }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .voAndNrel }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .voAndNrel }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .voAndNrel }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .other }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .other }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .ovAndReln }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .other }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .ovAndReln }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .voAndNrel }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .voAndNrel }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .voAndNrel }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .ovAndReln }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .ovAndNrel }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .voAndNrel }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .voAndNrel }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .ovAndNrel }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .ovAndReln }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .ovAndNrel }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .other }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .voAndNrel }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .other }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .voAndNrel }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .voAndNrel }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .other }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .ovAndNrel }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .other }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .voAndNrel }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .voAndNrel }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .ovAndReln }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .ovAndReln }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .other }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .voAndNrel }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .voAndNrel }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .voAndNrel }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .voAndNrel }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .other }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .other }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .voAndNrel }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .voAndNrel }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .voAndNrel }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .other }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .voAndNrel }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .other }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .voAndNrel }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .ovAndReln }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .voAndNrel }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .voAndNrel }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .voAndNrel }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .other }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .ovAndNrel }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .ovAndReln }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .ovAndReln }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .ovAndReln }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .ovAndReln }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .ovAndNrel }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .ovAndReln }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .other }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .voAndNrel }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .voAndNrel }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .ovAndReln }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .voAndNrel }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .voAndNrel }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .ovAndNrel }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .other }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .voAndNrel }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .voAndNrel }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .voAndNrel }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .other }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .other }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .other }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .other }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .voAndNrel }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .voAndNrel }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .ovAndReln }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .ovAndNrel }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .other }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .voAndNrel }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .voAndNrel }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .other }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .ovAndReln }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .voAndNrel }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .ovAndReln }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .voAndNrel }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .other }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .voAndNrel }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .ovAndReln }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .voAndNrel }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .ovAndNrel }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .voAndNrel }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .voAndNrel }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .ovAndNrel }
  , { walsCode := "kkq", language := "Kuikúro", iso := "kui", value := .other }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .other }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .other }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .ovAndNrel }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .voAndNrel }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .ovAndNrel }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .other }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .ovAndNrel }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .ovAndReln }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .voAndNrel }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .ovAndNrel }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .ovAndReln }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .ovAndReln }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .ovAndReln }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .voAndNrel }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .voAndNrel }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .ovAndReln }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .other }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .other }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .other }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .voAndNrel }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .voAndNrel }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .ovAndReln }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .voAndNrel }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .voAndNrel }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .voAndNrel }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .voAndNrel }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .voAndNrel }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .other }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .voAndNrel }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .other }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .voAndNrel }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .voAndNrel }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .other }
  , { walsCode := "les", language := "Lese", iso := "les", value := .other }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .voAndNrel }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .voAndNrel }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .ovAndReln }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .ovAndReln }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .other }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .voAndNrel }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .ovAndReln }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .voAndNrel }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .other }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .other }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .voAndNrel }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .voAndNrel }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .other }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .other }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .other }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .voAndNrel }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .voAndNrel }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .voAndNrel }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .voAndNrel }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .other }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .voAndNrel }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .ovAndNrel }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .other }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .ovAndReln }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .voAndNrel }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .other }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .other }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .voAndNrel }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .other }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .ovAndNrel }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .voAndNrel }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .ovAndReln }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .voAndNrel }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .voAndNrel }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .voAndNrel }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .voAndNrel }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .voAndNrel }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .ovAndNrel }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .ovAndReln }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .voAndReln }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .voAndNrel }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .ovAndNrel }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .voAndNrel }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .ovAndReln }
  , { walsCode := "mgq", language := "Mango", iso := "mge", value := .other }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .ovAndNrel }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .ovAndReln }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .voAndNrel }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .other }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .ovAndReln }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .voAndNrel }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .other }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .voAndNrel }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .other }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .ovAndReln }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .voAndNrel }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .voAndNrel }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .ovAndNrel }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .other }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .other }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .voAndNrel }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .voAndNrel }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .voAndNrel }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .other }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .voAndNrel }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .voAndNrel }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .voAndNrel }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .voAndNrel }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .voAndNrel }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .voAndNrel }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .ovAndReln }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .other }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .other }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .voAndNrel }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .other }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .voAndNrel }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .other }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .ovAndReln }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .other }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .other }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .other }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .voAndNrel }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .voAndNrel }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .voAndNrel }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .voAndNrel }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .voAndNrel }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .voAndNrel }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .voAndNrel }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .other }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .voAndNrel }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .voAndNrel }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .voAndNrel }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .ovAndNrel }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .other }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .voAndNrel }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .other }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .voAndNrel }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .ovAndNrel }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .voAndNrel }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .voAndNrel }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .voAndNrel }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .voAndNrel }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .voAndNrel }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .other }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .ovAndReln }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .voAndNrel }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .voAndNrel }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .other }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .voAndNrel }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .other }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .voAndNrel }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .voAndNrel }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .voAndNrel }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .voAndNrel }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .voAndNrel }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .voAndNrel }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .ovAndReln }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .ovAndReln }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .voAndNrel }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .voAndNrel }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .other }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .voAndNrel }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .ovAndNrel }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .voAndNrel }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .ovAndReln }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .other }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .voAndNrel }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .other }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .ovAndReln }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .ovAndNrel }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .ovAndNrel }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .other }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .voAndNrel }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .voAndNrel }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .voAndNrel }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .voAndNrel }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .voAndNrel }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .ovAndNrel }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .ovAndReln }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .ovAndReln }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .other }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .other }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .other }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .voAndNrel }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .other }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .other }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .other }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .voAndNrel }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .voAndNrel }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .other }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .voAndNrel }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .voAndNrel }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .voAndNrel }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .ovAndReln }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .voAndNrel }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .voAndNrel }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .ovAndReln }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .voAndNrel }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .voAndNrel }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .voAndNrel }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .voAndNrel }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .ovAndNrel }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .ovAndNrel }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .other }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .voAndNrel }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .other }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .voAndNrel }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .voAndNrel }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .voAndNrel }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .voAndNrel }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .voAndNrel }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .voAndNrel }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .voAndNrel }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .other }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .other }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .ovAndNrel }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .ovAndNrel }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .other }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .voAndNrel }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .voAndNrel }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .voAndNrel }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .ovAndNrel }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .voAndNrel }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .voAndNrel }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .voAndNrel }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .other }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .other }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .other }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .voAndNrel }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .ovAndNrel }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .voAndNrel }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .ovAndNrel }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .voAndNrel }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .other }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .voAndNrel }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .ovAndNrel }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .voAndNrel }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .ovAndNrel }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .voAndNrel }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .other }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .other }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .voAndNrel }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .voAndNrel }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .other }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .voAndNrel }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .voAndNrel }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .voAndNrel }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .voAndNrel }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .voAndNrel }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .ovAndReln }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .voAndNrel }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .ovAndNrel }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .ovAndReln }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .ovAndReln }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .ovAndReln }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .voAndNrel }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .voAndNrel }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .ovAndReln }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .other }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .other }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .other }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .voAndNrel }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .voAndNrel }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .voAndNrel }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .voAndNrel }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .voAndNrel }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .voAndNrel }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .other }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .ovAndReln }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .ovAndNrel }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .voAndNrel }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .voAndNrel }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .voAndNrel }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .voAndNrel }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .ovAndNrel }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .voAndNrel }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .voAndNrel }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .ovAndNrel }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .voAndNrel }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .voAndNrel }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .other }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .other }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .ovAndNrel }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .voAndNrel }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .ovAndReln }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .ovAndReln }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .voAndNrel }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .voAndNrel }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .voAndNrel }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .other }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .other }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .voAndNrel }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .ovAndNrel }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .voAndNrel }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .other }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .voAndNrel }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .voAndNrel }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .ovAndReln }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .ovAndNrel }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .ovAndReln }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .ovAndReln }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .ovAndNrel }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .voAndNrel }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .voAndNrel }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .ovAndNrel }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .voAndNrel }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .other }
  , { walsCode := "so", language := "So", iso := "teu", value := .voAndNrel }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .voAndNrel }
  , { walsCode := "som", language := "Somali", iso := "som", value := .ovAndNrel }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .voAndNrel }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .voAndNrel }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .other }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .voAndNrel }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .other }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .voAndNrel }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .voAndNrel }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .voAndNrel }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .voAndNrel }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .other }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .voAndNrel }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .voAndNrel }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .voAndNrel }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .voAndNrel }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .voAndNrel }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .voAndNrel }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .voAndNrel }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .ovAndNrel }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .ovAndNrel }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .ovAndNrel }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .voAndNrel }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .ovAndReln }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .voAndNrel }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .ovAndReln }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .ovAndNrel }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .ovAndNrel }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .other }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .ovAndNrel }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .voAndNrel }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .ovAndReln }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .other }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .ovAndNrel }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .voAndNrel }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .ovAndReln }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .voAndNrel }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .voAndNrel }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .voAndNrel }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .ovAndNrel }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .voAndNrel }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .voAndNrel }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .voAndNrel }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .voAndNrel }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .voAndNrel }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .ovAndNrel }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .voAndNrel }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .voAndNrel }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .voAndNrel }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .voAndNrel }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .ovAndReln }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .other }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .ovAndReln }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .other }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .ovAndReln }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .other }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .voAndNrel }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .voAndNrel }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .ovAndReln }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .other }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .other }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .voAndNrel }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .voAndNrel }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .voAndNrel }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .other }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .voAndNrel }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .voAndNrel }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .ovAndReln }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .ovAndNrel }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .voAndNrel }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .voAndNrel }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .voAndNrel }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .voAndNrel }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .voAndNrel }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .voAndNrel }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .voAndNrel }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .other }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .ovAndReln }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .ovAndReln }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .voAndNrel }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .ovAndReln }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .voAndNrel }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .ovAndNrel }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .ovAndReln }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .voAndNrel }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .other }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .ovAndNrel }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .voAndNrel }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .ovAndNrel }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .voAndNrel }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .ovAndReln }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .ovAndReln }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .other }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .ovAndNrel }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .voAndNrel }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .other }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .ovAndReln }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .other }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .voAndNrel }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .voAndNrel }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .voAndNrel }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .ovAndReln }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .ovAndNrel }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .voAndNrel }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .ovAndReln }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .voAndNrel }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .other }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .ovAndNrel }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .ovAndReln }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .ovAndReln }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .ovAndNrel }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .other }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .voAndNrel }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .voAndNrel }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .ovAndNrel }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .ovAndNrel }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .voAndNrel }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .other }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .other }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .other }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .other }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .other }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .voAndNrel }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .other }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .other }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .other }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .voAndNrel }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .voAndNrel }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .ovAndNrel }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .voAndNrel }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .other }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .other }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .other }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .voAndNrel }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .voAndNrel }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .voAndNrel }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .other }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .voAndNrel }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .ovAndReln }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .voAndNrel }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .ovAndReln }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .ovAndReln }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .voAndNrel }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .ovAndNrel }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .ovAndReln }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .other }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .other }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .voAndNrel }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .ovAndNrel }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .ovAndReln }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .ovAndNrel }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .voAndNrel }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .other }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .other }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .other }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .voAndNrel }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .voAndNrel }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .other }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .ovAndReln }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .voAndNrel }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .voAndNrel }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .voAndNrel }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .other }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .ovAndNrel }
  ]

/-- Complete WALS 96A dataset (879 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 879 := by native_decide

theorem count_ovAndReln :
    (allData.filter (·.value == .ovAndReln)).length = 132 := by native_decide
theorem count_ovAndNrel :
    (allData.filter (·.value == .ovAndNrel)).length = 113 := by native_decide
theorem count_voAndReln :
    (allData.filter (·.value == .voAndReln)).length = 5 := by native_decide
theorem count_voAndNrel :
    (allData.filter (·.value == .voAndNrel)).length = 416 := by native_decide
theorem count_other :
    (allData.filter (·.value == .other)).length = 213 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F96A
