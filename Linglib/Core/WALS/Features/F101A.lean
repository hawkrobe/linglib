import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 101A: Expression of Pronominal Subjects
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 101A`.

Chapter 101, 711 languages.
-/

namespace Core.WALS.F101A

/-- WALS 101A values. -/
inductive ExpressionOfPronominalSubjects where
  | obligatoryPronounsInSubjectPosition  -- Obligatory pronouns in subject position (82 languages)
  | subjectAffixesOnVerb  -- Subject affixes on verb (437 languages)
  | subjectCliticsOnVariableHost  -- Subject clitics on variable host (32 languages)
  | subjectPronounsInDifferentPosition  -- Subject pronouns in different position (67 languages)
  | optionalPronounsInSubjectPosition  -- Optional pronouns in subject position (61 languages)
  | mixed  -- Mixed (32 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint ExpressionOfPronominalSubjects) :=
  [ { walsCode := "aar", language := "Aari", iso := "aiw", value := .subjectAffixesOnVerb }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .subjectAffixesOnVerb }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .subjectAffixesOnVerb }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .subjectAffixesOnVerb }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .subjectAffixesOnVerb }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .subjectAffixesOnVerb }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .subjectAffixesOnVerb }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .subjectAffixesOnVerb }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .subjectAffixesOnVerb }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .subjectAffixesOnVerb }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .subjectAffixesOnVerb }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .mixed }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .subjectAffixesOnVerb }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .subjectAffixesOnVerb }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .subjectAffixesOnVerb }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .subjectAffixesOnVerb }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .subjectAffixesOnVerb }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .subjectAffixesOnVerb }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .subjectAffixesOnVerb }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .subjectAffixesOnVerb }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .subjectAffixesOnVerb }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .subjectAffixesOnVerb }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .subjectAffixesOnVerb }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .subjectAffixesOnVerb }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .subjectAffixesOnVerb }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .subjectAffixesOnVerb }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .subjectAffixesOnVerb }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .subjectAffixesOnVerb }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .subjectAffixesOnVerb }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .subjectAffixesOnVerb }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .subjectAffixesOnVerb }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .subjectCliticsOnVariableHost }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .subjectAffixesOnVerb }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .subjectAffixesOnVerb }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .subjectAffixesOnVerb }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .subjectAffixesOnVerb }
  , { walsCode := "ayr", language := "Ayoreo", iso := "ayo", value := .subjectAffixesOnVerb }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .subjectAffixesOnVerb }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .subjectAffixesOnVerb }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .subjectAffixesOnVerb }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .subjectAffixesOnVerb }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .subjectAffixesOnVerb }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .subjectAffixesOnVerb }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .subjectAffixesOnVerb }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .subjectAffixesOnVerb }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .subjectAffixesOnVerb }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .mixed }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .subjectAffixesOnVerb }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .subjectAffixesOnVerb }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .subjectAffixesOnVerb }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .subjectAffixesOnVerb }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .subjectAffixesOnVerb }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .subjectAffixesOnVerb }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .subjectAffixesOnVerb }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .subjectAffixesOnVerb }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .mixed }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .subjectAffixesOnVerb }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .subjectAffixesOnVerb }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .subjectCliticsOnVariableHost }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .subjectAffixesOnVerb }
  , { walsCode := "big", language := "Binga", iso := "yul", value := .subjectAffixesOnVerb }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .subjectAffixesOnVerb }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .subjectAffixesOnVerb }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .subjectAffixesOnVerb }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .subjectCliticsOnVariableHost }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .subjectAffixesOnVerb }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .subjectAffixesOnVerb }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .subjectAffixesOnVerb }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .subjectAffixesOnVerb }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .subjectAffixesOnVerb }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .mixed }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .subjectAffixesOnVerb }
  , { walsCode := "buw", language := "Bulu", iso := "bum", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .subjectAffixesOnVerb }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .subjectAffixesOnVerb }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .subjectAffixesOnVerb }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .subjectAffixesOnVerb }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .subjectAffixesOnVerb }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .subjectAffixesOnVerb }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .subjectAffixesOnVerb }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .mixed }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .subjectAffixesOnVerb }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .subjectAffixesOnVerb }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .subjectAffixesOnVerb }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .subjectAffixesOnVerb }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "chn", language := "Chantyal", iso := "chx", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .subjectCliticsOnVariableHost }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .subjectAffixesOnVerb }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .subjectAffixesOnVerb }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .subjectAffixesOnVerb }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .mixed }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .subjectAffixesOnVerb }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .subjectAffixesOnVerb }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .subjectAffixesOnVerb }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .subjectAffixesOnVerb }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .subjectAffixesOnVerb }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .subjectAffixesOnVerb }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .subjectAffixesOnVerb }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .subjectCliticsOnVariableHost }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .subjectAffixesOnVerb }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .subjectAffixesOnVerb }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .subjectCliticsOnVariableHost }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .subjectCliticsOnVariableHost }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .subjectAffixesOnVerb }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .subjectAffixesOnVerb }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .mixed }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .subjectAffixesOnVerb }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .subjectAffixesOnVerb }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .subjectAffixesOnVerb }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "des", language := "Desano", iso := "des", value := .subjectAffixesOnVerb }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .mixed }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .subjectAffixesOnVerb }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .subjectAffixesOnVerb }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .subjectAffixesOnVerb }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .subjectAffixesOnVerb }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .mixed }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .subjectAffixesOnVerb }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .subjectAffixesOnVerb }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .subjectAffixesOnVerb }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .subjectAffixesOnVerb }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .mixed }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .subjectAffixesOnVerb }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .subjectAffixesOnVerb }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .subjectAffixesOnVerb }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .subjectAffixesOnVerb }
  , { walsCode := "ene", language := "Enets", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "eng", language := "English", iso := "eng", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .subjectAffixesOnVerb }
  , { walsCode := "esm", language := "Esmeraldeño", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .subjectAffixesOnVerb }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .subjectAffixesOnVerb }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .subjectAffixesOnVerb }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .mixed }
  , { walsCode := "fre", language := "French", iso := "fra", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .subjectAffixesOnVerb }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .subjectAffixesOnVerb }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "gaa", language := "Gaagudju", iso := "gbu", value := .subjectAffixesOnVerb }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .subjectAffixesOnVerb }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .subjectAffixesOnVerb }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "ger", language := "German", iso := "deu", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .subjectAffixesOnVerb }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .subjectAffixesOnVerb }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .subjectAffixesOnVerb }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .subjectAffixesOnVerb }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .subjectAffixesOnVerb }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .subjectAffixesOnVerb }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .subjectCliticsOnVariableHost }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .subjectAffixesOnVerb }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .subjectAffixesOnVerb }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .subjectAffixesOnVerb }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .subjectAffixesOnVerb }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .subjectAffixesOnVerb }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .subjectAffixesOnVerb }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .subjectAffixesOnVerb }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .subjectAffixesOnVerb }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .subjectAffixesOnVerb }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .subjectAffixesOnVerb }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .subjectAffixesOnVerb }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .mixed }
  , { walsCode := "heh", language := "Hehe", iso := "heh", value := .subjectAffixesOnVerb }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .subjectCliticsOnVariableHost }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .subjectAffixesOnVerb }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .subjectAffixesOnVerb }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .subjectAffixesOnVerb }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .subjectAffixesOnVerb }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .subjectAffixesOnVerb }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .subjectAffixesOnVerb }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .subjectAffixesOnVerb }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .subjectAffixesOnVerb }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .subjectAffixesOnVerb }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .subjectAffixesOnVerb }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .subjectAffixesOnVerb }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .subjectAffixesOnVerb }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .subjectAffixesOnVerb }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .mixed }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .subjectAffixesOnVerb }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .subjectAffixesOnVerb }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .subjectAffixesOnVerb }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .subjectAffixesOnVerb }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .subjectAffixesOnVerb }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .mixed }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .subjectAffixesOnVerb }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "jwr", language := "Jarawara", iso := "jaa", value := .mixed }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .subjectAffixesOnVerb }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .subjectAffixesOnVerb }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .subjectAffixesOnVerb }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .subjectAffixesOnVerb }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .subjectAffixesOnVerb }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .subjectAffixesOnVerb }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .subjectAffixesOnVerb }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .subjectAffixesOnVerb }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .subjectAffixesOnVerb }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .subjectAffixesOnVerb }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .subjectAffixesOnVerb }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .subjectAffixesOnVerb }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .subjectAffixesOnVerb }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .subjectAffixesOnVerb }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .subjectAffixesOnVerb }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .subjectAffixesOnVerb }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .subjectAffixesOnVerb }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .subjectAffixesOnVerb }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .mixed }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .mixed }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .mixed }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .subjectAffixesOnVerb }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .subjectAffixesOnVerb }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .subjectAffixesOnVerb }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .subjectAffixesOnVerb }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .subjectAffixesOnVerb }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .subjectAffixesOnVerb }
  , { walsCode := "kga", language := "Kinga", iso := "zga", value := .subjectAffixesOnVerb }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .subjectAffixesOnVerb }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .subjectAffixesOnVerb }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .mixed }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .subjectAffixesOnVerb }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .subjectAffixesOnVerb }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .subjectAffixesOnVerb }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .subjectAffixesOnVerb }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .subjectCliticsOnVariableHost }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .subjectCliticsOnVariableHost }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .subjectAffixesOnVerb }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .subjectAffixesOnVerb }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .subjectAffixesOnVerb }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .mixed }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .mixed }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .subjectAffixesOnVerb }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .subjectAffixesOnVerb }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .subjectAffixesOnVerb }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .subjectAffixesOnVerb }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .subjectAffixesOnVerb }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .subjectAffixesOnVerb }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .subjectAffixesOnVerb }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .subjectAffixesOnVerb }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .subjectAffixesOnVerb }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .mixed }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "lgi", language := "Langi", iso := "lag", value := .subjectAffixesOnVerb }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .subjectAffixesOnVerb }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .subjectAffixesOnVerb }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .subjectAffixesOnVerb }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .subjectAffixesOnVerb }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .subjectAffixesOnVerb }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .subjectAffixesOnVerb }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .subjectAffixesOnVerb }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .subjectAffixesOnVerb }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .subjectAffixesOnVerb }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .subjectAffixesOnVerb }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .subjectAffixesOnVerb }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .subjectAffixesOnVerb }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .subjectAffixesOnVerb }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "luc", language := "Lucazi", iso := "lch", value := .subjectAffixesOnVerb }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .subjectAffixesOnVerb }
  , { walsCode := "lul", language := "Lule", iso := "ule", value := .subjectAffixesOnVerb }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .subjectAffixesOnVerb }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .subjectAffixesOnVerb }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .subjectAffixesOnVerb }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .subjectAffixesOnVerb }
  , { walsCode := "luy", language := "Luyia", iso := "luy", value := .subjectAffixesOnVerb }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .subjectAffixesOnVerb }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .subjectAffixesOnVerb }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .subjectAffixesOnVerb }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .subjectAffixesOnVerb }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .subjectAffixesOnVerb }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .subjectCliticsOnVariableHost }
  , { walsCode := "mkd", language := "Makonde", iso := "kde", value := .subjectAffixesOnVerb }
  , { walsCode := "mua", language := "Makua", iso := "mgh", value := .subjectAffixesOnVerb }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .subjectAffixesOnVerb }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .mixed }
  , { walsCode := "mmw", language := "Mambwe", iso := "mgr", value := .subjectAffixesOnVerb }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .subjectAffixesOnVerb }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .subjectAffixesOnVerb }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .subjectAffixesOnVerb }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .subjectAffixesOnVerb }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .subjectAffixesOnVerb }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .subjectAffixesOnVerb }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .subjectAffixesOnVerb }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .subjectAffixesOnVerb }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .subjectAffixesOnVerb }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .subjectAffixesOnVerb }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .subjectAffixesOnVerb }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .subjectAffixesOnVerb }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .subjectAffixesOnVerb }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .subjectAffixesOnVerb }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .subjectAffixesOnVerb }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .subjectAffixesOnVerb }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .subjectAffixesOnVerb }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .subjectAffixesOnVerb }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .mixed }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .subjectCliticsOnVariableHost }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .subjectAffixesOnVerb }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .subjectAffixesOnVerb }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .subjectAffixesOnVerb }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "mir", language := "Miriwung", iso := "mep", value := .subjectAffixesOnVerb }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .subjectAffixesOnVerb }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .mixed }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "mlm", language := "Mlabri (Minor)", iso := "mra", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "mcc", language := "Mochica", iso := "omc", value := .subjectAffixesOnVerb }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .subjectAffixesOnVerb }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .subjectAffixesOnVerb }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .subjectAffixesOnVerb }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .subjectAffixesOnVerb }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .subjectAffixesOnVerb }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .subjectAffixesOnVerb }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .subjectAffixesOnVerb }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .subjectAffixesOnVerb }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .subjectAffixesOnVerb }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .subjectAffixesOnVerb }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .subjectCliticsOnVariableHost }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .subjectAffixesOnVerb }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .subjectCliticsOnVariableHost }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .subjectAffixesOnVerb }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .subjectAffixesOnVerb }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .subjectAffixesOnVerb }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .subjectAffixesOnVerb }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .subjectAffixesOnVerb }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .subjectAffixesOnVerb }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .subjectAffixesOnVerb }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .subjectAffixesOnVerb }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .subjectAffixesOnVerb }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .subjectAffixesOnVerb }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .subjectAffixesOnVerb }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .subjectAffixesOnVerb }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .subjectAffixesOnVerb }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .subjectAffixesOnVerb }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .subjectAffixesOnVerb }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .subjectAffixesOnVerb }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .mixed }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .subjectAffixesOnVerb }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .subjectAffixesOnVerb }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .subjectCliticsOnVariableHost }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .subjectAffixesOnVerb }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .subjectCliticsOnVariableHost }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .mixed }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .mixed }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .subjectAffixesOnVerb }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .subjectAffixesOnVerb }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .subjectAffixesOnVerb }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .subjectAffixesOnVerb }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .subjectAffixesOnVerb }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .subjectAffixesOnVerb }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .subjectCliticsOnVariableHost }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .subjectAffixesOnVerb }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "nyn", language := "Nyigina", iso := "nyh", value := .subjectAffixesOnVerb }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .subjectAffixesOnVerb }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .subjectCliticsOnVariableHost }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .subjectAffixesOnVerb }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .subjectAffixesOnVerb }
  ]

private def allData_1 : List (Datapoint ExpressionOfPronominalSubjects) :=
  [ { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .subjectAffixesOnVerb }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .subjectCliticsOnVariableHost }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .subjectAffixesOnVerb }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .subjectAffixesOnVerb }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .subjectAffixesOnVerb }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .subjectAffixesOnVerb }
  , { walsCode := "ory", language := "Orya", iso := "ury", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .subjectAffixesOnVerb }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .subjectAffixesOnVerb }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .subjectAffixesOnVerb }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .subjectAffixesOnVerb }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .subjectAffixesOnVerb }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "pam", language := "Pame", iso := "pmz", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .subjectAffixesOnVerb }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .subjectAffixesOnVerb }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .subjectCliticsOnVariableHost }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .subjectAffixesOnVerb }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .subjectAffixesOnVerb }
  , { walsCode := "pwn", language := "Pawnee", iso := "paw", value := .subjectAffixesOnVerb }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .subjectAffixesOnVerb }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .subjectAffixesOnVerb }
  , { walsCode := "pog", language := "Pogoro", iso := "poy", value := .subjectAffixesOnVerb }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .subjectAffixesOnVerb }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .subjectCliticsOnVariableHost }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .subjectAffixesOnVerb }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .subjectAffixesOnVerb }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .subjectCliticsOnVariableHost }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .subjectAffixesOnVerb }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .subjectAffixesOnVerb }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .subjectAffixesOnVerb }
  , { walsCode := "rim", language := "Rimi", iso := "rim", value := .subjectAffixesOnVerb }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .subjectCliticsOnVariableHost }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .subjectAffixesOnVerb }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .subjectAffixesOnVerb }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .subjectAffixesOnVerb }
  , { walsCode := "rru", language := "Runyoro-Rutooro", iso := "nyo", value := .subjectAffixesOnVerb }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .subjectAffixesOnVerb }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .subjectAffixesOnVerb }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .subjectAffixesOnVerb }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .subjectAffixesOnVerb }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .subjectAffixesOnVerb }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .subjectAffixesOnVerb }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .subjectAffixesOnVerb }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .subjectAffixesOnVerb }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .subjectAffixesOnVerb }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .subjectAffixesOnVerb }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .subjectAffixesOnVerb }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .subjectAffixesOnVerb }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .subjectAffixesOnVerb }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .subjectAffixesOnVerb }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .subjectAffixesOnVerb }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .subjectAffixesOnVerb }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .subjectAffixesOnVerb }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .subjectAffixesOnVerb }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .subjectAffixesOnVerb }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .subjectAffixesOnVerb }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .subjectAffixesOnVerb }
  , { walsCode := "so", language := "So", iso := "teu", value := .subjectAffixesOnVerb }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .subjectAffixesOnVerb }
  , { walsCode := "som", language := "Somali", iso := "som", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .subjectAffixesOnVerb }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .subjectAffixesOnVerb }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .subjectAffixesOnVerb }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .subjectAffixesOnVerb }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .subjectAffixesOnVerb }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .subjectAffixesOnVerb }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .subjectAffixesOnVerb }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .subjectAffixesOnVerb }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .subjectAffixesOnVerb }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .subjectAffixesOnVerb }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .subjectAffixesOnVerb }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .subjectAffixesOnVerb }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .subjectAffixesOnVerb }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .subjectAffixesOnVerb }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .subjectAffixesOnVerb }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .subjectAffixesOnVerb }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .subjectAffixesOnVerb }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .subjectAffixesOnVerb }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .subjectAffixesOnVerb }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .mixed }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .subjectAffixesOnVerb }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .subjectAffixesOnVerb }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .subjectAffixesOnVerb }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .subjectAffixesOnVerb }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .mixed }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .subjectAffixesOnVerb }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .subjectAffixesOnVerb }
  , { walsCode := "tmc", language := "Timucua", iso := "tjm", value := .subjectAffixesOnVerb }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .subjectAffixesOnVerb }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .subjectAffixesOnVerb }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .subjectAffixesOnVerb }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .subjectAffixesOnVerb }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .subjectAffixesOnVerb }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .subjectAffixesOnVerb }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .subjectAffixesOnVerb }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "tsn", language := "Tsonga", iso := "tso", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .subjectAffixesOnVerb }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .subjectAffixesOnVerb }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "tki", language := "Tuki", iso := "bag", value := .subjectAffixesOnVerb }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .subjectAffixesOnVerb }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .subjectAffixesOnVerb }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .subjectAffixesOnVerb }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .subjectAffixesOnVerb }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .subjectAffixesOnVerb }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .subjectAffixesOnVerb }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .subjectAffixesOnVerb }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .subjectAffixesOnVerb }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .subjectAffixesOnVerb }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .subjectAffixesOnVerb }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .subjectAffixesOnVerb }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .subjectAffixesOnVerb }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .subjectAffixesOnVerb }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .subjectAffixesOnVerb }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .subjectAffixesOnVerb }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .subjectAffixesOnVerb }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .subjectAffixesOnVerb }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .subjectCliticsOnVariableHost }
  , { walsCode := "uyg", language := "Uyghur", iso := "uig", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .subjectAffixesOnVerb }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .obligatoryPronounsInSubjectPosition }
  , { walsCode := "ven", language := "Venda", iso := "ven", value := .subjectAffixesOnVerb }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "wai", language := "Wai Wai", iso := "waw", value := .subjectAffixesOnVerb }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .subjectAffixesOnVerb }
  , { walsCode := "wlm", language := "Walmatjari", iso := "wmt", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .subjectAffixesOnVerb }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .subjectAffixesOnVerb }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .subjectAffixesOnVerb }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .subjectAffixesOnVerb }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .subjectCliticsOnVariableHost }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .subjectCliticsOnVariableHost }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .subjectAffixesOnVerb }
  , { walsCode := "was", language := "Washo", iso := "was", value := .subjectAffixesOnVerb }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .subjectCliticsOnVariableHost }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .subjectCliticsOnVariableHost }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .subjectAffixesOnVerb }
  , { walsCode := "wed", language := "Wedau", iso := "wed", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .subjectAffixesOnVerb }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .subjectAffixesOnVerb }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .subjectAffixesOnVerb }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .subjectAffixesOnVerb }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .subjectPronounsInDifferentPosition }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .subjectAffixesOnVerb }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .subjectCliticsOnVariableHost }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .mixed }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .subjectAffixesOnVerb }
  , { walsCode := "yao", language := "Yao (in Malawi)", iso := "yao", value := .subjectAffixesOnVerb }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .mixed }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .subjectAffixesOnVerb }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .subjectAffixesOnVerb }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .subjectAffixesOnVerb }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .subjectAffixesOnVerb }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .subjectCliticsOnVariableHost }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .subjectAffixesOnVerb }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .subjectAffixesOnVerb }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .subjectCliticsOnVariableHost }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .subjectAffixesOnVerb }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .subjectAffixesOnVerb }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .optionalPronounsInSubjectPosition }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .subjectAffixesOnVerb }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .subjectAffixesOnVerb }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .subjectAffixesOnVerb }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .subjectAffixesOnVerb }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .subjectAffixesOnVerb }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .subjectAffixesOnVerb }
  ]

/-- Complete WALS 101A dataset (711 languages). -/
def allData : List (Datapoint ExpressionOfPronominalSubjects) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 711 := by native_decide

theorem count_obligatoryPronounsInSubjectPosition :
    (allData.filter (·.value == .obligatoryPronounsInSubjectPosition)).length = 82 := by native_decide
theorem count_subjectAffixesOnVerb :
    (allData.filter (·.value == .subjectAffixesOnVerb)).length = 437 := by native_decide
theorem count_subjectCliticsOnVariableHost :
    (allData.filter (·.value == .subjectCliticsOnVariableHost)).length = 32 := by native_decide
theorem count_subjectPronounsInDifferentPosition :
    (allData.filter (·.value == .subjectPronounsInDifferentPosition)).length = 67 := by native_decide
theorem count_optionalPronounsInSubjectPosition :
    (allData.filter (·.value == .optionalPronounsInSubjectPosition)).length = 61 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 32 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F101A
