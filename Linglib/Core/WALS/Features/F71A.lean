/-!
# WALS Feature 71A: The Prohibitive
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 71A`.

Chapter 71, 496 languages.
-/

namespace Core.WALS.F71A

/-- WALS 71A values. -/
inductive Prohibitive where
  | normalImperativeNormalNegative  -- Normal imperative + normal negative (113 languages)
  | normalImperativeSpecialNegative  -- Normal imperative + special negative (182 languages)
  | specialImperativeNormalNegative  -- Special imperative + normal negative (55 languages)
  | specialImperativeSpecialNegative  -- Special imperative + special negative (146 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 71A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : Prohibitive
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 71A dataset (496 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .specialImperativeNormalNegative }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .normalImperativeSpecialNegative }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .specialImperativeSpecialNegative }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .specialImperativeSpecialNegative }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .normalImperativeSpecialNegative }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .normalImperativeSpecialNegative }
  , { walsCode := "agu", language := "Aguacatec", iso := "agu", value := .normalImperativeSpecialNegative }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .normalImperativeSpecialNegative }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .normalImperativeNormalNegative }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .specialImperativeSpecialNegative }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .normalImperativeSpecialNegative }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .specialImperativeSpecialNegative }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .specialImperativeSpecialNegative }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .specialImperativeNormalNegative }
  , { walsCode := "ago", language := "Angolar", iso := "aoa", value := .normalImperativeNormalNegative }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .normalImperativeSpecialNegative }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .normalImperativeSpecialNegative }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .normalImperativeNormalNegative }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .specialImperativeSpecialNegative }
  , { walsCode := "abb", language := "Arabic (Chadian)", iso := "shu", value := .specialImperativeNormalNegative }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .specialImperativeNormalNegative }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .normalImperativeSpecialNegative }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .specialImperativeNormalNegative }
  , { walsCode := "anl", language := "Arabic (North Levantine Spoken)", iso := "apc", value := .specialImperativeNormalNegative }
  , { walsCode := "apa", language := "Arabic (Palestinian)", iso := "ajp", value := .normalImperativeNormalNegative }
  , { walsCode := "ars", language := "Arabic (San'ani)", iso := "ayn", value := .specialImperativeSpecialNegative }
  , { walsCode := "ark", language := "Araki", iso := "akr", value := .normalImperativeSpecialNegative }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .specialImperativeSpecialNegative }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .normalImperativeSpecialNegative }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .normalImperativeSpecialNegative }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .specialImperativeNormalNegative }
  , { walsCode := "au", language := "Au", iso := "avt", value := .normalImperativeNormalNegative }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .normalImperativeSpecialNegative }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .specialImperativeSpecialNegative }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .normalImperativeSpecialNegative }
  , { walsCode := "ayr", language := "Ayoreo", iso := "ayo", value := .normalImperativeNormalNegative }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .normalImperativeNormalNegative }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .specialImperativeNormalNegative }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .specialImperativeSpecialNegative }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .normalImperativeSpecialNegative }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .normalImperativeNormalNegative }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .normalImperativeSpecialNegative }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .specialImperativeSpecialNegative }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .normalImperativeNormalNegative }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .normalImperativeSpecialNegative }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .normalImperativeNormalNegative }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .normalImperativeNormalNegative }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .normalImperativeSpecialNegative }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .normalImperativeSpecialNegative }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .normalImperativeSpecialNegative }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .specialImperativeSpecialNegative }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .normalImperativeNormalNegative }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .specialImperativeNormalNegative }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .specialImperativeSpecialNegative }
  , { walsCode := "bhu", language := "Bhumij", iso := "unr", value := .specialImperativeSpecialNegative }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .normalImperativeNormalNegative }
  , { walsCode := "brz", language := "Birri", iso := "bvq", value := .normalImperativeNormalNegative }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .specialImperativeSpecialNegative }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .specialImperativeSpecialNegative }
  , { walsCode := "bdk", language := "Budukh", iso := "bdk", value := .specialImperativeSpecialNegative }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .specialImperativeNormalNegative }
  , { walsCode := "buk", language := "Bukusu", iso := "bxk", value := .specialImperativeSpecialNegative }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .specialImperativeSpecialNegative }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .normalImperativeSpecialNegative }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .normalImperativeNormalNegative }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .specialImperativeNormalNegative }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .specialImperativeSpecialNegative }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .normalImperativeNormalNegative }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .normalImperativeSpecialNegative }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .normalImperativeSpecialNegative }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .specialImperativeNormalNegative }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .normalImperativeNormalNegative }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .normalImperativeSpecialNegative }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .normalImperativeSpecialNegative }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .normalImperativeSpecialNegative }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .specialImperativeNormalNegative }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .specialImperativeNormalNegative }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .specialImperativeNormalNegative }
  , { walsCode := "cte", language := "Chinantec (Tepetotutla)", iso := "cnt", value := .specialImperativeNormalNegative }
  , { walsCode := "crg", language := "Chiriguano", iso := "gui", value := .normalImperativeSpecialNegative }
  , { walsCode := "coi", language := "Chortí", iso := "caa", value := .specialImperativeSpecialNegative }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .normalImperativeSpecialNegative }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .specialImperativeSpecialNegative }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .normalImperativeSpecialNegative }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .specialImperativeSpecialNegative }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .normalImperativeNormalNegative }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .specialImperativeNormalNegative }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .normalImperativeSpecialNegative }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .normalImperativeNormalNegative }
  , { walsCode := "dbd", language := "Dabida", iso := "dav", value := .specialImperativeSpecialNegative }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .specialImperativeNormalNegative }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .specialImperativeSpecialNegative }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .normalImperativeNormalNegative }
  , { walsCode := "des", language := "Desano", iso := "des", value := .specialImperativeNormalNegative }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .normalImperativeNormalNegative }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .specialImperativeSpecialNegative }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .specialImperativeSpecialNegative }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .specialImperativeSpecialNegative }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .normalImperativeNormalNegative }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .normalImperativeNormalNegative }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .normalImperativeNormalNegative }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .specialImperativeSpecialNegative }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .specialImperativeNormalNegative }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .normalImperativeNormalNegative }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .specialImperativeSpecialNegative }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .normalImperativeNormalNegative }
  , { walsCode := "emc", language := "Embera Chami", iso := "cmi", value := .normalImperativeSpecialNegative }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .normalImperativeSpecialNegative }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .normalImperativeSpecialNegative }
  , { walsCode := "eng", language := "English", iso := "eng", value := .normalImperativeNormalNegative }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .normalImperativeSpecialNegative }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .normalImperativeNormalNegative }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .specialImperativeNormalNegative }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .specialImperativeNormalNegative }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .normalImperativeNormalNegative }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .normalImperativeSpecialNegative }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .normalImperativeNormalNegative }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .normalImperativeSpecialNegative }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .normalImperativeSpecialNegative }
  , { walsCode := "fre", language := "French", iso := "fra", value := .normalImperativeNormalNegative }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .normalImperativeNormalNegative }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .normalImperativeSpecialNegative }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .normalImperativeSpecialNegative }
  , { walsCode := "fue", language := "Futuna (East)", iso := "fud", value := .normalImperativeSpecialNegative }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .specialImperativeNormalNegative }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .normalImperativeSpecialNegative }
  , { walsCode := "glc", language := "Galician", iso := "glg", value := .specialImperativeNormalNegative }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .specialImperativeSpecialNegative }
  , { walsCode := "ger", language := "German", iso := "deu", value := .normalImperativeNormalNegative }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .normalImperativeSpecialNegative }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .specialImperativeSpecialNegative }
  , { walsCode := "goj", language := "Gojri", iso := "gju", value := .normalImperativeSpecialNegative }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .specialImperativeNormalNegative }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .specialImperativeSpecialNegative }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .specialImperativeSpecialNegative }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .specialImperativeSpecialNegative }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .specialImperativeSpecialNegative }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .normalImperativeSpecialNegative }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .normalImperativeSpecialNegative }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .normalImperativeNormalNegative }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .specialImperativeSpecialNegative }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .normalImperativeNormalNegative }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .normalImperativeNormalNegative }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .specialImperativeSpecialNegative }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .normalImperativeSpecialNegative }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .specialImperativeSpecialNegative }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .normalImperativeSpecialNegative }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .specialImperativeSpecialNegative }
  , { walsCode := "her", language := "Herero", iso := "her", value := .specialImperativeSpecialNegative }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .normalImperativeSpecialNegative }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .normalImperativeNormalNegative }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .normalImperativeSpecialNegative }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .normalImperativeSpecialNegative }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .normalImperativeSpecialNegative }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .specialImperativeSpecialNegative }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .normalImperativeNormalNegative }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .normalImperativeNormalNegative }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .normalImperativeNormalNegative }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .normalImperativeNormalNegative }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .normalImperativeSpecialNegative }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .normalImperativeSpecialNegative }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .specialImperativeSpecialNegative }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .normalImperativeSpecialNegative }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .normalImperativeSpecialNegative }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .normalImperativeSpecialNegative }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .normalImperativeSpecialNegative }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .normalImperativeSpecialNegative }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .specialImperativeNormalNegative }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .normalImperativeSpecialNegative }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .normalImperativeNormalNegative }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .specialImperativeNormalNegative }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .normalImperativeSpecialNegative }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .specialImperativeNormalNegative }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .specialImperativeSpecialNegative }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .normalImperativeSpecialNegative }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .normalImperativeSpecialNegative }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .normalImperativeSpecialNegative }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .specialImperativeSpecialNegative }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .normalImperativeSpecialNegative }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .specialImperativeSpecialNegative }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .specialImperativeSpecialNegative }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .normalImperativeNormalNegative }
  , { walsCode := "krt", language := "Karata", iso := "kpt", value := .specialImperativeSpecialNegative }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .specialImperativeSpecialNegative }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .normalImperativeSpecialNegative }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .specialImperativeSpecialNegative }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .normalImperativeSpecialNegative }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .specialImperativeSpecialNegative }
  , { walsCode := "kei", language := "Kei", iso := "kei", value := .normalImperativeSpecialNegative }
  , { walsCode := "kyg", language := "Kenyang", iso := "ken", value := .specialImperativeSpecialNegative }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .specialImperativeSpecialNegative }
  , { walsCode := "krq", language := "Kerek", iso := "krk", value := .specialImperativeSpecialNegative }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .normalImperativeSpecialNegative }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .specialImperativeNormalNegative }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .normalImperativeNormalNegative }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .normalImperativeSpecialNegative }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .normalImperativeSpecialNegative }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .normalImperativeSpecialNegative }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .normalImperativeSpecialNegative }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .normalImperativeSpecialNegative }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .normalImperativeSpecialNegative }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .specialImperativeSpecialNegative }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .specialImperativeSpecialNegative }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .specialImperativeSpecialNegative }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .normalImperativeSpecialNegative }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .normalImperativeNormalNegative }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .specialImperativeSpecialNegative }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .normalImperativeNormalNegative }
  , { walsCode := "kow", language := "Ko (Winye)", iso := "kst", value := .specialImperativeSpecialNegative }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .specialImperativeSpecialNegative }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .normalImperativeNormalNegative }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .specialImperativeSpecialNegative }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .specialImperativeSpecialNegative }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .normalImperativeSpecialNegative }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .normalImperativeSpecialNegative }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .specialImperativeSpecialNegative }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .normalImperativeSpecialNegative }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .normalImperativeSpecialNegative }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .specialImperativeSpecialNegative }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .specialImperativeSpecialNegative }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .normalImperativeNormalNegative }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .specialImperativeSpecialNegative }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .specialImperativeSpecialNegative }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .normalImperativeSpecialNegative }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .specialImperativeSpecialNegative }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .normalImperativeSpecialNegative }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .specialImperativeSpecialNegative }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .specialImperativeSpecialNegative }
  , { walsCode := "kwr", language := "Kwamera", iso := "tnk", value := .normalImperativeSpecialNegative }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .normalImperativeSpecialNegative }
  , { walsCode := "lno", language := "Ladino", iso := "lad", value := .specialImperativeNormalNegative }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .normalImperativeSpecialNegative }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .normalImperativeNormalNegative }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .specialImperativeSpecialNegative }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .normalImperativeNormalNegative }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .specialImperativeSpecialNegative }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .specialImperativeSpecialNegative }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .normalImperativeNormalNegative }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .specialImperativeSpecialNegative }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .normalImperativeNormalNegative }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .specialImperativeSpecialNegative }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .specialImperativeSpecialNegative }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .normalImperativeSpecialNegative }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .normalImperativeNormalNegative }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .specialImperativeNormalNegative }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .normalImperativeNormalNegative }
  , { walsCode := "lob", language := "Lobi", iso := "lob", value := .specialImperativeSpecialNegative }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .normalImperativeSpecialNegative }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .normalImperativeSpecialNegative }
  , { walsCode := "loz", language := "Lozi", iso := "loz", value := .specialImperativeSpecialNegative }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .normalImperativeNormalNegative }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .specialImperativeSpecialNegative }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .specialImperativeSpecialNegative }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .normalImperativeNormalNegative }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .specialImperativeSpecialNegative }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .specialImperativeSpecialNegative }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .specialImperativeSpecialNegative }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .normalImperativeSpecialNegative }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .normalImperativeNormalNegative }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .specialImperativeNormalNegative }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .specialImperativeSpecialNegative }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .normalImperativeSpecialNegative }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .specialImperativeSpecialNegative }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .normalImperativeSpecialNegative }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .specialImperativeSpecialNegative }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .normalImperativeSpecialNegative }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .normalImperativeSpecialNegative }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .normalImperativeSpecialNegative }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .normalImperativeSpecialNegative }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .normalImperativeSpecialNegative }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .specialImperativeSpecialNegative }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .specialImperativeSpecialNegative }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .normalImperativeSpecialNegative }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .specialImperativeSpecialNegative }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .specialImperativeSpecialNegative }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .normalImperativeNormalNegative }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .normalImperativeSpecialNegative }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .specialImperativeNormalNegative }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .normalImperativeSpecialNegative }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .specialImperativeSpecialNegative }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .normalImperativeSpecialNegative }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .normalImperativeSpecialNegative }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .specialImperativeNormalNegative }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .normalImperativeSpecialNegative }
  , { walsCode := "mbg", language := "Mbugu", iso := "mhd", value := .specialImperativeSpecialNegative }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .specialImperativeNormalNegative }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .specialImperativeSpecialNegative }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .normalImperativeSpecialNegative }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .normalImperativeSpecialNegative }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .specialImperativeSpecialNegative }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .normalImperativeSpecialNegative }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .normalImperativeSpecialNegative }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .specialImperativeSpecialNegative }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .normalImperativeSpecialNegative }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .normalImperativeNormalNegative }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .normalImperativeNormalNegative }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .normalImperativeSpecialNegative }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .normalImperativeSpecialNegative }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .specialImperativeSpecialNegative }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .specialImperativeNormalNegative }
  , { walsCode := "mul", language := "Mulao", iso := "mlm", value := .normalImperativeSpecialNegative }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .normalImperativeNormalNegative }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .normalImperativeSpecialNegative }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .normalImperativeSpecialNegative }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .specialImperativeSpecialNegative }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .specialImperativeSpecialNegative }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .specialImperativeSpecialNegative }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .normalImperativeSpecialNegative }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .normalImperativeSpecialNegative }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .normalImperativeNormalNegative }
  , { walsCode := "npn", language := "Naga Pidgin", iso := "nag", value := .normalImperativeNormalNegative }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .normalImperativeNormalNegative }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .normalImperativeSpecialNegative }
  , { walsCode := "ntn", language := "Nateni", iso := "ntm", value := .normalImperativeSpecialNegative }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .specialImperativeSpecialNegative }
  , { walsCode := "ndg", language := "Ndogo", iso := "ndz", value := .normalImperativeNormalNegative }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .normalImperativeNormalNegative }
  , { walsCode := "nel", language := "Nelemwa", iso := "nee", value := .normalImperativeSpecialNegative }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .specialImperativeSpecialNegative }
  , { walsCode := "nen", language := "Nenets (Forest)", iso := "yrk", value := .specialImperativeSpecialNegative }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .specialImperativeSpecialNegative }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .normalImperativeSpecialNegative }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .specialImperativeSpecialNegative }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .normalImperativeSpecialNegative }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .normalImperativeSpecialNegative }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .specialImperativeSpecialNegative }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .normalImperativeNormalNegative }
  , { walsCode := "nub", language := "Nubi", iso := "kcn", value := .normalImperativeSpecialNegative }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .normalImperativeSpecialNegative }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .normalImperativeSpecialNegative }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .normalImperativeSpecialNegative }
  , { walsCode := "nnn", language := "Nuni (Northern)", iso := "nuv", value := .normalImperativeSpecialNegative }
  , { walsCode := "nng", language := "Nyanga", iso := "nyj", value := .specialImperativeNormalNegative }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .normalImperativeSpecialNegative }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .normalImperativeNormalNegative }
  , { walsCode := "oka", language := "Okanagan", iso := "oka", value := .specialImperativeSpecialNegative }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .normalImperativeSpecialNegative }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .normalImperativeSpecialNegative }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .specialImperativeSpecialNegative }
  , { walsCode := "oix", language := "Otomí (Ixtenco)", iso := "otz", value := .normalImperativeSpecialNegative }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .normalImperativeSpecialNegative }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .specialImperativeSpecialNegative }
  , { walsCode := "pta", language := "Paita", iso := "duf", value := .normalImperativeSpecialNegative }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .normalImperativeSpecialNegative }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .specialImperativeSpecialNegative }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .normalImperativeNormalNegative }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .specialImperativeSpecialNegative }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .normalImperativeSpecialNegative }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .specialImperativeNormalNegative }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .specialImperativeSpecialNegative }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .normalImperativeSpecialNegative }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .normalImperativeSpecialNegative }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .normalImperativeNormalNegative }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .normalImperativeNormalNegative }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .normalImperativeSpecialNegative }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .normalImperativeSpecialNegative }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .normalImperativeNormalNegative }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .normalImperativeNormalNegative }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .normalImperativeNormalNegative }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .normalImperativeNormalNegative }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .specialImperativeNormalNegative }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .normalImperativeSpecialNegative }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .normalImperativeSpecialNegative }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .normalImperativeSpecialNegative }
  , { walsCode := "qta", language := "Quechua (Tarma)", iso := "qvn", value := .specialImperativeSpecialNegative }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .specialImperativeSpecialNegative }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .normalImperativeNormalNegative }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .normalImperativeNormalNegative }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .specialImperativeSpecialNegative }
  , { walsCode := "rav", language := "Romani (Ajia Varvara)", iso := "rmn", value := .normalImperativeSpecialNegative }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .normalImperativeSpecialNegative }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .specialImperativeNormalNegative }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .normalImperativeNormalNegative }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .normalImperativeNormalNegative }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .normalImperativeNormalNegative }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .normalImperativeSpecialNegative }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .normalImperativeNormalNegative }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .specialImperativeSpecialNegative }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .normalImperativeSpecialNegative }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .normalImperativeSpecialNegative }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .specialImperativeNormalNegative }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .normalImperativeSpecialNegative }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .normalImperativeSpecialNegative }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .normalImperativeSpecialNegative }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .normalImperativeSpecialNegative }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .specialImperativeNormalNegative }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .normalImperativeSpecialNegative }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .normalImperativeNormalNegative }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .normalImperativeSpecialNegative }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .normalImperativeSpecialNegative }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .normalImperativeNormalNegative }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .specialImperativeSpecialNegative }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .normalImperativeNormalNegative }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .normalImperativeNormalNegative }
  , { walsCode := "so", language := "So", iso := "teu", value := .normalImperativeNormalNegative }
  , { walsCode := "sou", language := "Sorbian (Upper)", iso := "hsb", value := .normalImperativeSpecialNegative }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .specialImperativeSpecialNegative }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .specialImperativeNormalNegative }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .specialImperativeSpecialNegative }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .specialImperativeSpecialNegative }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .normalImperativeSpecialNegative }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .normalImperativeSpecialNegative }
  , { walsCode := "sva", language := "Svan", iso := "sva", value := .specialImperativeNormalNegative }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .specialImperativeSpecialNegative }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .normalImperativeNormalNegative }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .normalImperativeSpecialNegative }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .normalImperativeSpecialNegative }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .specialImperativeSpecialNegative }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .specialImperativeSpecialNegative }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .normalImperativeNormalNegative }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .normalImperativeNormalNegative }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .normalImperativeSpecialNegative }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .normalImperativeSpecialNegative }
  , { walsCode := "tem", language := "Tem", iso := "kdh", value := .specialImperativeSpecialNegative }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .specialImperativeSpecialNegative }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .normalImperativeNormalNegative }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .specialImperativeNormalNegative }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .normalImperativeNormalNegative }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .normalImperativeSpecialNegative }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .normalImperativeSpecialNegative }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .normalImperativeSpecialNegative }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .specialImperativeNormalNegative }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .normalImperativeSpecialNegative }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .normalImperativeNormalNegative }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .specialImperativeSpecialNegative }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .normalImperativeSpecialNegative }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .normalImperativeSpecialNegative }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .normalImperativeSpecialNegative }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .normalImperativeNormalNegative }
  , { walsCode := "tor", language := "Toratán", iso := "rth", value := .specialImperativeSpecialNegative }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .specialImperativeSpecialNegative }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .normalImperativeNormalNegative }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .normalImperativeNormalNegative }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .specialImperativeNormalNegative }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .specialImperativeSpecialNegative }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .normalImperativeSpecialNegative }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .normalImperativeNormalNegative }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .specialImperativeSpecialNegative }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .specialImperativeSpecialNegative }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .specialImperativeSpecialNegative }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .specialImperativeNormalNegative }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .normalImperativeNormalNegative }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .normalImperativeSpecialNegative }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .specialImperativeNormalNegative }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .normalImperativeNormalNegative }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .specialImperativeSpecialNegative }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .normalImperativeNormalNegative }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .normalImperativeNormalNegative }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .normalImperativeNormalNegative }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .specialImperativeSpecialNegative }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .normalImperativeSpecialNegative }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .normalImperativeNormalNegative }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .normalImperativeNormalNegative }
  , { walsCode := "vag", language := "Vagla", iso := "vag", value := .normalImperativeSpecialNegative }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .specialImperativeNormalNegative }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .normalImperativeSpecialNegative }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .specialImperativeNormalNegative }
  , { walsCode := "wll", language := "Wallisian", iso := "wls", value := .normalImperativeSpecialNegative }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .normalImperativeNormalNegative }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .normalImperativeNormalNegative }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .normalImperativeNormalNegative }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .specialImperativeNormalNegative }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .normalImperativeSpecialNegative }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .normalImperativeNormalNegative }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .normalImperativeSpecialNegative }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .normalImperativeNormalNegative }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .specialImperativeSpecialNegative }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .specialImperativeNormalNegative }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .normalImperativeSpecialNegative }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .specialImperativeSpecialNegative }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .normalImperativeSpecialNegative }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .normalImperativeNormalNegative }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .specialImperativeSpecialNegative }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .specialImperativeSpecialNegative }
  , { walsCode := "wwr", language := "Woiwurrung", iso := "wyi", value := .specialImperativeSpecialNegative }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .normalImperativeSpecialNegative }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .normalImperativeSpecialNegative }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .normalImperativeNormalNegative }
  , { walsCode := "ykm", language := "Yakoma", iso := "yky", value := .normalImperativeSpecialNegative }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .specialImperativeSpecialNegative }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .normalImperativeSpecialNegative }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .specialImperativeSpecialNegative }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .normalImperativeSpecialNegative }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .specialImperativeSpecialNegative }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .normalImperativeNormalNegative }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .normalImperativeSpecialNegative }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .specialImperativeSpecialNegative }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .normalImperativeNormalNegative }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .specialImperativeSpecialNegative }
  , { walsCode := "yrm", language := "Yurimangí", iso := "", value := .normalImperativeNormalNegative }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .specialImperativeNormalNegative }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .specialImperativeSpecialNegative }
  , { walsCode := "zen", language := "Zenaga", iso := "zen", value := .specialImperativeNormalNegative }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .specialImperativeSpecialNegative }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .specialImperativeSpecialNegative }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .normalImperativeSpecialNegative }
  ]

-- Count verification
theorem total_count : allData.length = 496 := by native_decide

theorem count_normalImperativeNormalNegative :
    (allData.filter (·.value == .normalImperativeNormalNegative)).length = 113 := by native_decide
theorem count_normalImperativeSpecialNegative :
    (allData.filter (·.value == .normalImperativeSpecialNegative)).length = 182 := by native_decide
theorem count_specialImperativeNormalNegative :
    (allData.filter (·.value == .specialImperativeNormalNegative)).length = 55 := by native_decide
theorem count_specialImperativeSpecialNegative :
    (allData.filter (·.value == .specialImperativeSpecialNegative)).length = 146 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F71A
