import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 90A: Order of Relative Clause and Noun
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90A`.

Chapter 90, 824 languages.
-/

namespace Core.WALS.F90A

/-- WALS 90A values. -/
inductive RelClauseNounOrder where
  | nounRelativeClause  -- Noun-Relative clause (579 languages)
  | relativeClauseNoun  -- Relative clause-Noun (141 languages)
  | internallyHeaded  -- Internally headed (24 languages)
  | correlative  -- Correlative (7 languages)
  | adjoined  -- Adjoined (8 languages)
  | doublyHeaded  -- Doubly headed (1 languages)
  | mixed  -- Mixed (64 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint RelClauseNounOrder) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .nounRelativeClause }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .nounRelativeClause }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .nounRelativeClause }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .nounRelativeClause }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .relativeClauseNoun }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .nounRelativeClause }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .nounRelativeClause }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .nounRelativeClause }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .nounRelativeClause }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .relativeClauseNoun }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .nounRelativeClause }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .nounRelativeClause }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .nounRelativeClause }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .relativeClauseNoun }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .nounRelativeClause }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .relativeClauseNoun }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .nounRelativeClause }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .relativeClauseNoun }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .nounRelativeClause }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .nounRelativeClause }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .nounRelativeClause }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .nounRelativeClause }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .relativeClauseNoun }
  , { walsCode := "amt", language := "Amdo (Themchen)", iso := "adx", value := .mixed }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .nounRelativeClause }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .relativeClauseNoun }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .relativeClauseNoun }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .nounRelativeClause }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .nounRelativeClause }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .nounRelativeClause }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .nounRelativeClause }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .nounRelativeClause }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .nounRelativeClause }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .nounRelativeClause }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .mixed }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .nounRelativeClause }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .relativeClauseNoun }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .nounRelativeClause }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .nounRelativeClause }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .nounRelativeClause }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .nounRelativeClause }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .nounRelativeClause }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .nounRelativeClause }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .nounRelativeClause }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .nounRelativeClause }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .nounRelativeClause }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .mixed }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .nounRelativeClause }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .nounRelativeClause }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .nounRelativeClause }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .nounRelativeClause }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .nounRelativeClause }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .relativeClauseNoun }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .relativeClauseNoun }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .relativeClauseNoun }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .relativeClauseNoun }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .mixed }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .nounRelativeClause }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .nounRelativeClause }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .nounRelativeClause }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .nounRelativeClause }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .nounRelativeClause }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .relativeClauseNoun }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .nounRelativeClause }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .nounRelativeClause }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .nounRelativeClause }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .nounRelativeClause }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .nounRelativeClause }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .relativeClauseNoun }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .correlative }
  , { walsCode := "brl", language := "Baragaunle", iso := "loy", value := .relativeClauseNoun }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .nounRelativeClause }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .nounRelativeClause }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .nounRelativeClause }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .nounRelativeClause }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .nounRelativeClause }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .nounRelativeClause }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .relativeClauseNoun }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .relativeClauseNoun }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .nounRelativeClause }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .nounRelativeClause }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .nounRelativeClause }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .mixed }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .nounRelativeClause }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .relativeClauseNoun }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .nounRelativeClause }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .nounRelativeClause }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .nounRelativeClause }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .nounRelativeClause }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .nounRelativeClause }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .nounRelativeClause }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .nounRelativeClause }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .nounRelativeClause }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .nounRelativeClause }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .mixed }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .nounRelativeClause }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .nounRelativeClause }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .nounRelativeClause }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .nounRelativeClause }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .mixed }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .nounRelativeClause }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .relativeClauseNoun }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .nounRelativeClause }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .nounRelativeClause }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .nounRelativeClause }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .nounRelativeClause }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .nounRelativeClause }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .nounRelativeClause }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .nounRelativeClause }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .nounRelativeClause }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .relativeClauseNoun }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .nounRelativeClause }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .nounRelativeClause }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .relativeClauseNoun }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .nounRelativeClause }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .nounRelativeClause }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .mixed }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .nounRelativeClause }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .nounRelativeClause }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .relativeClauseNoun }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .nounRelativeClause }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .nounRelativeClause }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .mixed }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .relativeClauseNoun }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .nounRelativeClause }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .nounRelativeClause }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .nounRelativeClause }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .nounRelativeClause }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .relativeClauseNoun }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .nounRelativeClause }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .nounRelativeClause }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .nounRelativeClause }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .mixed }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .relativeClauseNoun }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .nounRelativeClause }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .nounRelativeClause }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .relativeClauseNoun }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .nounRelativeClause }
  , { walsCode := "cpn", language := "Chepang", iso := "cdm", value := .relativeClauseNoun }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .relativeClauseNoun }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .nounRelativeClause }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .internallyHeaded }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .internallyHeaded }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .relativeClauseNoun }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .nounRelativeClause }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .nounRelativeClause }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .nounRelativeClause }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .nounRelativeClause }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .relativeClauseNoun }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .nounRelativeClause }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .nounRelativeClause }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .internallyHeaded }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .nounRelativeClause }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .nounRelativeClause }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .nounRelativeClause }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .mixed }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .relativeClauseNoun }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .nounRelativeClause }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .nounRelativeClause }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .nounRelativeClause }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .nounRelativeClause }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .nounRelativeClause }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .nounRelativeClause }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .nounRelativeClause }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .nounRelativeClause }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .nounRelativeClause }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .nounRelativeClause }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .relativeClauseNoun }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .nounRelativeClause }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .nounRelativeClause }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .nounRelativeClause }
  , { walsCode := "drg", language := "Dargwa", iso := "dar", value := .relativeClauseNoun }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .mixed }
  , { walsCode := "day", language := "Day", iso := "dai", value := .nounRelativeClause }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .nounRelativeClause }
  , { walsCode := "des", language := "Desano", iso := "des", value := .nounRelativeClause }
  , { walsCode := "dhm", language := "Dhimal", iso := "dhi", value := .relativeClauseNoun }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .relativeClauseNoun }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .nounRelativeClause }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .internallyHeaded }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .relativeClauseNoun }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .relativeClauseNoun }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .nounRelativeClause }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .nounRelativeClause }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .adjoined }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .nounRelativeClause }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .mixed }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .nounRelativeClause }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .internallyHeaded }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .nounRelativeClause }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .nounRelativeClause }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .nounRelativeClause }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .nounRelativeClause }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .nounRelativeClause }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .nounRelativeClause }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .nounRelativeClause }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .relativeClauseNoun }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .nounRelativeClause }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .nounRelativeClause }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .nounRelativeClause }
  , { walsCode := "eng", language := "English", iso := "eng", value := .nounRelativeClause }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .internallyHeaded }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .nounRelativeClause }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .nounRelativeClause }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .nounRelativeClause }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .relativeClauseNoun }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .relativeClauseNoun }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .nounRelativeClause }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .nounRelativeClause }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .nounRelativeClause }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .nounRelativeClause }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .nounRelativeClause }
  , { walsCode := "fre", language := "French", iso := "fra", value := .nounRelativeClause }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .nounRelativeClause }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .nounRelativeClause }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .nounRelativeClause }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .nounRelativeClause }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .nounRelativeClause }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .nounRelativeClause }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .nounRelativeClause }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .mixed }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .relativeClauseNoun }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .relativeClauseNoun }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .nounRelativeClause }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .relativeClauseNoun }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .nounRelativeClause }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .nounRelativeClause }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .nounRelativeClause }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .nounRelativeClause }
  , { walsCode := "ger", language := "German", iso := "deu", value := .nounRelativeClause }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .mixed }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .mixed }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .nounRelativeClause }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nounRelativeClause }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .nounRelativeClause }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .nounRelativeClause }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .nounRelativeClause }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .nounRelativeClause }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .nounRelativeClause }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .mixed }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .nounRelativeClause }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .nounRelativeClause }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .nounRelativeClause }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .relativeClauseNoun }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .nounRelativeClause }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .relativeClauseNoun }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .internallyHeaded }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .relativeClauseNoun }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .nounRelativeClause }
  , { walsCode := "hhu", language := "Hanga Hundi", iso := "wos", value := .relativeClauseNoun }
  , { walsCode := "han", language := "Hani", iso := "hni", value := .relativeClauseNoun }
  , { walsCode := "har", language := "Haruai", iso := "tmd", value := .mixed }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .nounRelativeClause }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .nounRelativeClause }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .nounRelativeClause }
  , { walsCode := "hwr", language := "Hawrami", iso := "hac", value := .nounRelativeClause }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .nounRelativeClause }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .relativeClauseNoun }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .nounRelativeClause }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .nounRelativeClause }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .nounRelativeClause }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .nounRelativeClause }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .correlative }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .nounRelativeClause }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .nounRelativeClause }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .relativeClauseNoun }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .nounRelativeClause }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .nounRelativeClause }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .relativeClauseNoun }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .nounRelativeClause }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .nounRelativeClause }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .nounRelativeClause }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .relativeClauseNoun }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .nounRelativeClause }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .mixed }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .relativeClauseNoun }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .relativeClauseNoun }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .nounRelativeClause }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .nounRelativeClause }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .nounRelativeClause }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .nounRelativeClause }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .nounRelativeClause }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .nounRelativeClause }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .nounRelativeClause }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .nounRelativeClause }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .nounRelativeClause }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .nounRelativeClause }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .nounRelativeClause }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .relativeClauseNoun }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .nounRelativeClause }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .internallyHeaded }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .nounRelativeClause }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .mixed }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .nounRelativeClause }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .nounRelativeClause }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .relativeClauseNoun }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .nounRelativeClause }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .nounRelativeClause }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .nounRelativeClause }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .nounRelativeClause }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .nounRelativeClause }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .nounRelativeClause }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .mixed }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .relativeClauseNoun }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .nounRelativeClause }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .relativeClauseNoun }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .nounRelativeClause }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .nounRelativeClause }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .nounRelativeClause }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .relativeClauseNoun }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .nounRelativeClause }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .nounRelativeClause }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .nounRelativeClause }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .nounRelativeClause }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .relativeClauseNoun }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .nounRelativeClause }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .mixed }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .nounRelativeClause }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .nounRelativeClause }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .nounRelativeClause }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .mixed }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .nounRelativeClause }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .nounRelativeClause }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .nounRelativeClause }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .nounRelativeClause }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .relativeClauseNoun }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .relativeClauseNoun }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .nounRelativeClause }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .nounRelativeClause }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .nounRelativeClause }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .nounRelativeClause }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .mixed }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .nounRelativeClause }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .nounRelativeClause }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .nounRelativeClause }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .nounRelativeClause }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .nounRelativeClause }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .nounRelativeClause }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .nounRelativeClause }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .relativeClauseNoun }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .nounRelativeClause }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .nounRelativeClause }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .nounRelativeClause }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .mixed }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .nounRelativeClause }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .relativeClauseNoun }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .relativeClauseNoun }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .relativeClauseNoun }
  , { walsCode := "khd", language := "Kham (Dege)", iso := "khg", value := .relativeClauseNoun }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .nounRelativeClause }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .relativeClauseNoun }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .mixed }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .nounRelativeClause }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .nounRelativeClause }
  , { walsCode := "khw", language := "Khowar", iso := "khw", value := .relativeClauseNoun }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .nounRelativeClause }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .nounRelativeClause }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .nounRelativeClause }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .internallyHeaded }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .nounRelativeClause }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .nounRelativeClause }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .nounRelativeClause }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .nounRelativeClause }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .nounRelativeClause }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .mixed }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .mixed }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .nounRelativeClause }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .nounRelativeClause }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .relativeClauseNoun }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .nounRelativeClause }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .doublyHeaded }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .nounRelativeClause }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .nounRelativeClause }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .mixed }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .relativeClauseNoun }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .nounRelativeClause }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .relativeClauseNoun }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .nounRelativeClause }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .mixed }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .nounRelativeClause }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .relativeClauseNoun }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .nounRelativeClause }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .nounRelativeClause }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .nounRelativeClause }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .nounRelativeClause }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .nounRelativeClause }
  , { walsCode := "kkq", language := "Kuikúro", iso := "kui", value := .adjoined }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .adjoined }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .mixed }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .nounRelativeClause }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .nounRelativeClause }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .nounRelativeClause }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .internallyHeaded }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .nounRelativeClause }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .relativeClauseNoun }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .nounRelativeClause }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .nounRelativeClause }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .relativeClauseNoun }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .relativeClauseNoun }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .relativeClauseNoun }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .nounRelativeClause }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .nounRelativeClause }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .relativeClauseNoun }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .mixed }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .internallyHeaded }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .mixed }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .nounRelativeClause }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .nounRelativeClause }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .relativeClauseNoun }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .nounRelativeClause }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .nounRelativeClause }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .nounRelativeClause }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .nounRelativeClause }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .nounRelativeClause }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .internallyHeaded }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .nounRelativeClause }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .nounRelativeClause }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .nounRelativeClause }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .mixed }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .nounRelativeClause }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .nounRelativeClause }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .relativeClauseNoun }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .relativeClauseNoun }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .nounRelativeClause }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .relativeClauseNoun }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .nounRelativeClause }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .nounRelativeClause }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .mixed }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .nounRelativeClause }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .nounRelativeClause }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .nounRelativeClause }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .nounRelativeClause }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .nounRelativeClause }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .nounRelativeClause }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .nounRelativeClause }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .nounRelativeClause }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .nounRelativeClause }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .nounRelativeClause }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .nounRelativeClause }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .nounRelativeClause }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .mixed }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .relativeClauseNoun }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .nounRelativeClause }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .internallyHeaded }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .mixed }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .nounRelativeClause }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .mixed }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .nounRelativeClause }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .nounRelativeClause }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .relativeClauseNoun }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .nounRelativeClause }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .nounRelativeClause }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .nounRelativeClause }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .nounRelativeClause }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .nounRelativeClause }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .nounRelativeClause }
  , { walsCode := "nmm", language := "Manange", iso := "nmm", value := .relativeClauseNoun }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .relativeClauseNoun }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .nounRelativeClause }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .nounRelativeClause }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .nounRelativeClause }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .relativeClauseNoun }
  , { walsCode := "mgq", language := "Mango", iso := "mge", value := .nounRelativeClause }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .nounRelativeClause }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .relativeClauseNoun }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .nounRelativeClause }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .relativeClauseNoun }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .nounRelativeClause }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .mixed }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .nounRelativeClause }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .adjoined }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .relativeClauseNoun }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .nounRelativeClause }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .nounRelativeClause }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .nounRelativeClause }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .correlative }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .nounRelativeClause }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .nounRelativeClause }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .nounRelativeClause }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .nounRelativeClause }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .nounRelativeClause }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .nounRelativeClause }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .nounRelativeClause }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .nounRelativeClause }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .nounRelativeClause }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .relativeClauseNoun }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .adjoined }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .nounRelativeClause }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .nounRelativeClause }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .internallyHeaded }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .nounRelativeClause }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .nounRelativeClause }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .relativeClauseNoun }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .nounRelativeClause }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .nounRelativeClause }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .nounRelativeClause }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .nounRelativeClause }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .nounRelativeClause }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .nounRelativeClause }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .nounRelativeClause }
  ]

private def allData_1 : List (Datapoint RelClauseNounOrder) :=
  [ { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .nounRelativeClause }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .nounRelativeClause }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .nounRelativeClause }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .nounRelativeClause }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .nounRelativeClause }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .nounRelativeClause }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .nounRelativeClause }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .nounRelativeClause }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .nounRelativeClause }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .nounRelativeClause }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .nounRelativeClause }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .nounRelativeClause }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .nounRelativeClause }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .nounRelativeClause }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .nounRelativeClause }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .nounRelativeClause }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .relativeClauseNoun }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .nounRelativeClause }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .nounRelativeClause }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .mixed }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .nounRelativeClause }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .nounRelativeClause }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .nounRelativeClause }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .nounRelativeClause }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .nounRelativeClause }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .nounRelativeClause }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .nounRelativeClause }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .relativeClauseNoun }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .relativeClauseNoun }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .nounRelativeClause }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .nounRelativeClause }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .mixed }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .nounRelativeClause }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .nounRelativeClause }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .nounRelativeClause }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .relativeClauseNoun }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .mixed }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .nounRelativeClause }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .nounRelativeClause }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .relativeClauseNoun }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .nounRelativeClause }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .nounRelativeClause }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .internallyHeaded }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .nounRelativeClause }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .nounRelativeClause }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .nounRelativeClause }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .nounRelativeClause }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .nounRelativeClause }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .nounRelativeClause }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .relativeClauseNoun }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .relativeClauseNoun }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .nounRelativeClause }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .nounRelativeClause }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .nounRelativeClause }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .nounRelativeClause }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .adjoined }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .mixed }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .nounRelativeClause }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .nounRelativeClause }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .nounRelativeClause }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .nounRelativeClause }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .nounRelativeClause }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .relativeClauseNoun }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .nounRelativeClause }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .nounRelativeClause }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .relativeClauseNoun }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .nounRelativeClause }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .nounRelativeClause }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .nounRelativeClause }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .nounRelativeClause }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .nounRelativeClause }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .nounRelativeClause }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .nounRelativeClause }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .nounRelativeClause }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .nounRelativeClause }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .nounRelativeClause }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .nounRelativeClause }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .nounRelativeClause }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .nounRelativeClause }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .nounRelativeClause }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .nounRelativeClause }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .nounRelativeClause }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .internallyHeaded }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .correlative }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .nounRelativeClause }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .nounRelativeClause }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .internallyHeaded }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .nounRelativeClause }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .nounRelativeClause }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .nounRelativeClause }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .nounRelativeClause }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .nounRelativeClause }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .nounRelativeClause }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .nounRelativeClause }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .nounRelativeClause }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .mixed }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .nounRelativeClause }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .nounRelativeClause }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .nounRelativeClause }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .nounRelativeClause }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .nounRelativeClause }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .nounRelativeClause }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .nounRelativeClause }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .nounRelativeClause }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .nounRelativeClause }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .nounRelativeClause }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .nounRelativeClause }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .mixed }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .nounRelativeClause }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .nounRelativeClause }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .nounRelativeClause }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .nounRelativeClause }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .nounRelativeClause }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .nounRelativeClause }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .nounRelativeClause }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .relativeClauseNoun }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .relativeClauseNoun }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .nounRelativeClause }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .nounRelativeClause }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .relativeClauseNoun }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .relativeClauseNoun }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .relativeClauseNoun }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .relativeClauseNoun }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .nounRelativeClause }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .nounRelativeClause }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .relativeClauseNoun }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .mixed }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .internallyHeaded }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .nounRelativeClause }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .nounRelativeClause }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .nounRelativeClause }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .nounRelativeClause }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .nounRelativeClause }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .nounRelativeClause }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .mixed }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .relativeClauseNoun }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .nounRelativeClause }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .nounRelativeClause }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .nounRelativeClause }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .nounRelativeClause }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .nounRelativeClause }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .nounRelativeClause }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .nounRelativeClause }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .nounRelativeClause }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .nounRelativeClause }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .nounRelativeClause }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .nounRelativeClause }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .mixed }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .mixed }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .nounRelativeClause }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .nounRelativeClause }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .relativeClauseNoun }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .relativeClauseNoun }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .nounRelativeClause }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .nounRelativeClause }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .nounRelativeClause }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .internallyHeaded }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .nounRelativeClause }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .nounRelativeClause }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .nounRelativeClause }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .mixed }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .nounRelativeClause }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .nounRelativeClause }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .relativeClauseNoun }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .nounRelativeClause }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .relativeClauseNoun }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .relativeClauseNoun }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .nounRelativeClause }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .nounRelativeClause }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .nounRelativeClause }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .nounRelativeClause }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .nounRelativeClause }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .mixed }
  , { walsCode := "so", language := "So", iso := "teu", value := .nounRelativeClause }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .nounRelativeClause }
  , { walsCode := "som", language := "Somali", iso := "som", value := .nounRelativeClause }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .nounRelativeClause }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .nounRelativeClause }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .internallyHeaded }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .nounRelativeClause }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .mixed }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .nounRelativeClause }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .nounRelativeClause }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .nounRelativeClause }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .nounRelativeClause }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .correlative }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .nounRelativeClause }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .nounRelativeClause }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .nounRelativeClause }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .nounRelativeClause }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .nounRelativeClause }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .nounRelativeClause }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .nounRelativeClause }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .nounRelativeClause }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .nounRelativeClause }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .nounRelativeClause }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .nounRelativeClause }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .relativeClauseNoun }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .nounRelativeClause }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .relativeClauseNoun }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .nounRelativeClause }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .nounRelativeClause }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .mixed }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .nounRelativeClause }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .nounRelativeClause }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .relativeClauseNoun }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .mixed }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .nounRelativeClause }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .nounRelativeClause }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .relativeClauseNoun }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .nounRelativeClause }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .nounRelativeClause }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .nounRelativeClause }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .nounRelativeClause }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .nounRelativeClause }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .nounRelativeClause }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .nounRelativeClause }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .nounRelativeClause }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .nounRelativeClause }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .nounRelativeClause }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .nounRelativeClause }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .nounRelativeClause }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .nounRelativeClause }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .nounRelativeClause }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .relativeClauseNoun }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .mixed }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .relativeClauseNoun }
  , { walsCode := "tis", language := "Tibetan (Shigatse)", iso := "bod", value := .mixed }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .relativeClauseNoun }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .nounRelativeClause }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .nounRelativeClause }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .relativeClauseNoun }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .internallyHeaded }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .nounRelativeClause }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .nounRelativeClause }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .nounRelativeClause }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .nounRelativeClause }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .nounRelativeClause }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .relativeClauseNoun }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .nounRelativeClause }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .nounRelativeClause }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .nounRelativeClause }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .nounRelativeClause }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .nounRelativeClause }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .nounRelativeClause }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .nounRelativeClause }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .nounRelativeClause }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .relativeClauseNoun }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .relativeClauseNoun }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .nounRelativeClause }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .relativeClauseNoun }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .nounRelativeClause }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .nounRelativeClause }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .relativeClauseNoun }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .nounRelativeClause }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .mixed }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .nounRelativeClause }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .nounRelativeClause }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .nounRelativeClause }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .nounRelativeClause }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .relativeClauseNoun }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .relativeClauseNoun }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .nounRelativeClause }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .nounRelativeClause }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .mixed }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .relativeClauseNoun }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .mixed }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .nounRelativeClause }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .nounRelativeClause }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .nounRelativeClause }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .relativeClauseNoun }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .nounRelativeClause }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .nounRelativeClause }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .relativeClauseNoun }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .nounRelativeClause }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .correlative }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .nounRelativeClause }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .relativeClauseNoun }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .relativeClauseNoun }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .nounRelativeClause }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .correlative }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .nounRelativeClause }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .nounRelativeClause }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .nounRelativeClause }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .nounRelativeClause }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .nounRelativeClause }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .mixed }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .mixed }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .internallyHeaded }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .nounRelativeClause }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .adjoined }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .mixed }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .nounRelativeClause }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .nounRelativeClause }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .nounRelativeClause }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .nounRelativeClause }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .nounRelativeClause }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .nounRelativeClause }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .nounRelativeClause }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .mixed }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .nounRelativeClause }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .relativeClauseNoun }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .nounRelativeClause }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .relativeClauseNoun }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .relativeClauseNoun }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .nounRelativeClause }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .nounRelativeClause }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .relativeClauseNoun }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .adjoined }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .nounRelativeClause }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .nounRelativeClause }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .relativeClauseNoun }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .nounRelativeClause }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .nounRelativeClause }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .mixed }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .internallyHeaded }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .nounRelativeClause }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .nounRelativeClause }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .relativeClauseNoun }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .nounRelativeClause }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .nounRelativeClause }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .nounRelativeClause }
  , { walsCode := "rgc", language := "rGyalrong (Caodeng)", iso := "jya", value := .internallyHeaded }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .nounRelativeClause }
  ]

/-- Complete WALS 90A dataset (824 languages). -/
def allData : List (Datapoint RelClauseNounOrder) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 824 := by native_decide

theorem count_nounRelativeClause :
    (allData.filter (·.value == .nounRelativeClause)).length = 579 := by native_decide
theorem count_relativeClauseNoun :
    (allData.filter (·.value == .relativeClauseNoun)).length = 141 := by native_decide
theorem count_internallyHeaded :
    (allData.filter (·.value == .internallyHeaded)).length = 24 := by native_decide
theorem count_correlative :
    (allData.filter (·.value == .correlative)).length = 7 := by native_decide
theorem count_adjoined :
    (allData.filter (·.value == .adjoined)).length = 8 := by native_decide
theorem count_doublyHeaded :
    (allData.filter (·.value == .doublyHeaded)).length = 1 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 64 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F90A
