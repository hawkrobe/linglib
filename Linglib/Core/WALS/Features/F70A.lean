import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 70A: The Morphological Imperative
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 70A`.

Chapter 70, 548 languages.
-/

namespace Core.WALS.F70A

/-- WALS 70A values. -/
inductive MorphologicalImperative where
  | secondSingularAndSecondPlural  -- Second singular and second plural (292 languages)
  | secondSingular  -- Second singular (43 languages)
  | secondPlural  -- Second plural (2 languages)
  | secondPersonNumberNeutral  -- Second person number-neutral (89 languages)
  | noSecondPersonImperatives  -- No second-person imperatives (122 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint MorphologicalImperative) :=
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .secondSingularAndSecondPlural }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .noSecondPersonImperatives }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noSecondPersonImperatives }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .secondSingularAndSecondPlural }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .secondSingularAndSecondPlural }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .secondSingularAndSecondPlural }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .secondPersonNumberNeutral }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .secondPersonNumberNeutral }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .secondSingular }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .secondSingularAndSecondPlural }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .secondSingular }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .secondSingular }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noSecondPersonImperatives }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .secondSingularAndSecondPlural }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .secondSingularAndSecondPlural }
  , { walsCode := "ago", language := "Angolar", iso := "aoa", value := .secondPersonNumberNeutral }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .noSecondPersonImperatives }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .secondPersonNumberNeutral }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .secondSingularAndSecondPlural }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .secondPersonNumberNeutral }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .secondSingular }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .secondPlural }
  , { walsCode := "abb", language := "Arabic (Chadian)", iso := "shu", value := .secondSingularAndSecondPlural }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .secondSingularAndSecondPlural }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .secondSingularAndSecondPlural }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .secondSingularAndSecondPlural }
  , { walsCode := "anl", language := "Arabic (North Levantine Spoken)", iso := "apc", value := .secondSingularAndSecondPlural }
  , { walsCode := "apa", language := "Arabic (Palestinian)", iso := "ajp", value := .noSecondPersonImperatives }
  , { walsCode := "ars", language := "Arabic (San'ani)", iso := "ayn", value := .secondSingularAndSecondPlural }
  , { walsCode := "ark", language := "Araki", iso := "akr", value := .noSecondPersonImperatives }
  , { walsCode := "ard", language := "Arandai", iso := "jbj", value := .secondSingularAndSecondPlural }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .secondSingularAndSecondPlural }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .secondSingularAndSecondPlural }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .secondSingularAndSecondPlural }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .secondPersonNumberNeutral }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .secondSingularAndSecondPlural }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .secondSingularAndSecondPlural }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .noSecondPersonImperatives }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .secondSingularAndSecondPlural }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .secondPersonNumberNeutral }
  , { walsCode := "ayr", language := "Ayoreo", iso := "ayo", value := .secondSingularAndSecondPlural }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .secondSingularAndSecondPlural }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .secondSingularAndSecondPlural }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noSecondPersonImperatives }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .secondSingularAndSecondPlural }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .secondPersonNumberNeutral }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .secondPersonNumberNeutral }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .secondSingularAndSecondPlural }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .secondSingularAndSecondPlural }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .secondPersonNumberNeutral }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noSecondPersonImperatives }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .secondSingularAndSecondPlural }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .secondSingularAndSecondPlural }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .secondSingularAndSecondPlural }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .secondSingularAndSecondPlural }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .secondSingularAndSecondPlural }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .secondSingularAndSecondPlural }
  , { walsCode := "bhu", language := "Bhumij", iso := "unr", value := .noSecondPersonImperatives }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .secondSingularAndSecondPlural }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .secondPersonNumberNeutral }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .noSecondPersonImperatives }
  , { walsCode := "brz", language := "Birri", iso := "bvq", value := .secondSingularAndSecondPlural }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noSecondPersonImperatives }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .secondSingularAndSecondPlural }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .secondSingularAndSecondPlural }
  , { walsCode := "bkt", language := "Brokskat", iso := "bkk", value := .secondPersonNumberNeutral }
  , { walsCode := "bdk", language := "Budukh", iso := "bdk", value := .secondSingularAndSecondPlural }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .secondSingularAndSecondPlural }
  , { walsCode := "buk", language := "Bukusu", iso := "bxk", value := .secondSingular }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .secondSingularAndSecondPlural }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noSecondPersonImperatives }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .secondSingularAndSecondPlural }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .secondSingularAndSecondPlural }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .secondSingularAndSecondPlural }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .secondSingularAndSecondPlural }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .secondPersonNumberNeutral }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noSecondPersonImperatives }
  , { walsCode := "car", language := "Carib", iso := "car", value := .secondSingularAndSecondPlural }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .secondPersonNumberNeutral }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .secondSingular }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .secondSingularAndSecondPlural }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .secondSingularAndSecondPlural }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .secondSingularAndSecondPlural }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .secondSingularAndSecondPlural }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .secondPersonNumberNeutral }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .secondSingularAndSecondPlural }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .secondPersonNumberNeutral }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .secondSingularAndSecondPlural }
  , { walsCode := "cte", language := "Chinantec (Tepetotutla)", iso := "cnt", value := .secondPersonNumberNeutral }
  , { walsCode := "crg", language := "Chiriguano", iso := "gui", value := .secondSingular }
  , { walsCode := "coi", language := "Chortí", iso := "caa", value := .secondSingularAndSecondPlural }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noSecondPersonImperatives }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .secondSingularAndSecondPlural }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noSecondPersonImperatives }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .secondSingularAndSecondPlural }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .secondSingularAndSecondPlural }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .secondSingularAndSecondPlural }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .secondSingularAndSecondPlural }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .secondSingularAndSecondPlural }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .secondSingularAndSecondPlural }
  , { walsCode := "dbd", language := "Dabida", iso := "dav", value := .secondSingularAndSecondPlural }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .secondSingularAndSecondPlural }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .secondSingularAndSecondPlural }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .secondPersonNumberNeutral }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .secondSingularAndSecondPlural }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .secondPersonNumberNeutral }
  , { walsCode := "des", language := "Desano", iso := "des", value := .secondPersonNumberNeutral }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .secondSingularAndSecondPlural }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .secondSingularAndSecondPlural }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noSecondPersonImperatives }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .secondSingularAndSecondPlural }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .secondPersonNumberNeutral }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noSecondPersonImperatives }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noSecondPersonImperatives }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noSecondPersonImperatives }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .secondSingularAndSecondPlural }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .secondPersonNumberNeutral }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .secondSingularAndSecondPlural }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .secondSingularAndSecondPlural }
  , { walsCode := "emc", language := "Embera Chami", iso := "cmi", value := .secondSingularAndSecondPlural }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .secondSingularAndSecondPlural }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noSecondPersonImperatives }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noSecondPersonImperatives }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .secondSingularAndSecondPlural }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .secondSingularAndSecondPlural }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .secondSingularAndSecondPlural }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .secondSingularAndSecondPlural }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .secondSingularAndSecondPlural }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noSecondPersonImperatives }
  , { walsCode := "far", language := "Faroese", iso := "fao", value := .secondSingularAndSecondPlural }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noSecondPersonImperatives }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .secondSingularAndSecondPlural }
  , { walsCode := "fre", language := "French", iso := "fra", value := .secondSingular }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .secondSingular }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .secondSingularAndSecondPlural }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noSecondPersonImperatives }
  , { walsCode := "fue", language := "Futuna (East)", iso := "fud", value := .noSecondPersonImperatives }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .secondSingularAndSecondPlural }
  , { walsCode := "gll", language := "Galela", iso := "gbi", value := .noSecondPersonImperatives }
  , { walsCode := "glc", language := "Galician", iso := "glg", value := .secondSingularAndSecondPlural }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .secondSingularAndSecondPlural }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .secondPersonNumberNeutral }
  , { walsCode := "gbk", language := "Gbaya (Northwest)", iso := "gya", value := .noSecondPersonImperatives }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noSecondPersonImperatives }
  , { walsCode := "ger", language := "German", iso := "deu", value := .secondSingular }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .secondSingularAndSecondPlural }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .secondPersonNumberNeutral }
  , { walsCode := "goj", language := "Gojri", iso := "gju", value := .secondSingularAndSecondPlural }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noSecondPersonImperatives }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .secondSingular }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .secondSingularAndSecondPlural }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .secondSingularAndSecondPlural }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .secondSingular }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .secondSingularAndSecondPlural }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .secondSingularAndSecondPlural }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .secondSingularAndSecondPlural }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noSecondPersonImperatives }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .secondPersonNumberNeutral }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .secondSingularAndSecondPlural }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .noSecondPersonImperatives }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .secondSingularAndSecondPlural }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noSecondPersonImperatives }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .secondSingular }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noSecondPersonImperatives }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .secondPersonNumberNeutral }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .noSecondPersonImperatives }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .secondSingularAndSecondPlural }
  , { walsCode := "her", language := "Herero", iso := "her", value := .secondSingularAndSecondPlural }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .secondSingularAndSecondPlural }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .secondSingularAndSecondPlural }
  , { walsCode := "hmd", language := "Hmong Daw", iso := "mww", value := .noSecondPersonImperatives }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noSecondPersonImperatives }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .secondSingularAndSecondPlural }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .secondSingularAndSecondPlural }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noSecondPersonImperatives }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .secondPersonNumberNeutral }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noSecondPersonImperatives }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .secondSingular }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .secondPersonNumberNeutral }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .secondSingularAndSecondPlural }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .secondSingular }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .secondSingularAndSecondPlural }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noSecondPersonImperatives }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .secondPersonNumberNeutral }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noSecondPersonImperatives }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .secondPersonNumberNeutral }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .noSecondPersonImperatives }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .secondSingularAndSecondPlural }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .secondSingularAndSecondPlural }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .secondSingular }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .noSecondPersonImperatives }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .secondSingular }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .secondSingularAndSecondPlural }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .secondPersonNumberNeutral }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .secondSingularAndSecondPlural }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .secondSingularAndSecondPlural }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noSecondPersonImperatives }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .secondPersonNumberNeutral }
  , { walsCode := "kdw", language := "Kadiwéu", iso := "kbc", value := .noSecondPersonImperatives }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .secondSingularAndSecondPlural }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .secondSingularAndSecondPlural }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .noSecondPersonImperatives }
  , { walsCode := "kwe", language := "Kanjobal (Western)", iso := "knj", value := .secondSingularAndSecondPlural }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .secondSingularAndSecondPlural }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .secondSingularAndSecondPlural }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .secondSingularAndSecondPlural }
  , { walsCode := "krt", language := "Karata", iso := "kpt", value := .secondPersonNumberNeutral }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .secondSingularAndSecondPlural }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .secondSingularAndSecondPlural }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .secondSingularAndSecondPlural }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noSecondPersonImperatives }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .secondPersonNumberNeutral }
  , { walsCode := "kei", language := "Kei", iso := "kei", value := .noSecondPersonImperatives }
  , { walsCode := "kyg", language := "Kenyang", iso := "ken", value := .secondSingularAndSecondPlural }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noSecondPersonImperatives }
  , { walsCode := "krq", language := "Kerek", iso := "krk", value := .secondSingularAndSecondPlural }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .secondSingularAndSecondPlural }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .secondSingularAndSecondPlural }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .secondSingularAndSecondPlural }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .secondSingularAndSecondPlural }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .secondPersonNumberNeutral }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .secondSingularAndSecondPlural }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noSecondPersonImperatives }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noSecondPersonImperatives }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noSecondPersonImperatives }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .secondSingularAndSecondPlural }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .noSecondPersonImperatives }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .secondSingularAndSecondPlural }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .secondSingularAndSecondPlural }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .secondSingularAndSecondPlural }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .secondPersonNumberNeutral }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .secondPersonNumberNeutral }
  , { walsCode := "kow", language := "Ko (Winye)", iso := "kst", value := .secondPersonNumberNeutral }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .secondSingularAndSecondPlural }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .secondSingularAndSecondPlural }
  , { walsCode := "kod", language := "Kodava", iso := "kfa", value := .secondSingularAndSecondPlural }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .secondSingularAndSecondPlural }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .secondPersonNumberNeutral }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .secondSingular }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .secondPersonNumberNeutral }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .noSecondPersonImperatives }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .secondPersonNumberNeutral }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .secondPersonNumberNeutral }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .secondSingularAndSecondPlural }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .noSecondPersonImperatives }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .secondSingularAndSecondPlural }
  , { walsCode := "kui", language := "Kui (in India)", iso := "kxu", value := .secondSingularAndSecondPlural }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .secondSingularAndSecondPlural }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .secondSingularAndSecondPlural }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .secondSingularAndSecondPlural }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .secondSingularAndSecondPlural }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .secondSingularAndSecondPlural }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .noSecondPersonImperatives }
  , { walsCode := "kwr", language := "Kwamera", iso := "tnk", value := .secondSingularAndSecondPlural }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .secondSingularAndSecondPlural }
  , { walsCode := "lno", language := "Ladino", iso := "lad", value := .secondSingularAndSecondPlural }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .secondSingularAndSecondPlural }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .noSecondPersonImperatives }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .secondSingularAndSecondPlural }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .secondPlural }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .secondSingularAndSecondPlural }
  , { walsCode := "laz", language := "Laz", iso := "lzz", value := .secondSingularAndSecondPlural }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .secondSingularAndSecondPlural }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .secondPersonNumberNeutral }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .secondPersonNumberNeutral }
  , { walsCode := "lil", language := "Lillooet", iso := "lil", value := .secondSingularAndSecondPlural }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .secondSingularAndSecondPlural }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .noSecondPersonImperatives }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .secondSingular }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .secondSingularAndSecondPlural }
  , { walsCode := "lob", language := "Lobi", iso := "lob", value := .secondPersonNumberNeutral }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .secondPersonNumberNeutral }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .noSecondPersonImperatives }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .secondPersonNumberNeutral }
  , { walsCode := "loz", language := "Lozi", iso := "loz", value := .secondSingularAndSecondPlural }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .secondPersonNumberNeutral }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .secondSingularAndSecondPlural }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .secondSingularAndSecondPlural }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noSecondPersonImperatives }
  , { walsCode := "mle", language := "Maale", iso := "mdy", value := .secondSingularAndSecondPlural }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .secondSingularAndSecondPlural }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .secondSingularAndSecondPlural }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .secondSingularAndSecondPlural }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .secondPersonNumberNeutral }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .secondSingularAndSecondPlural }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .secondPersonNumberNeutral }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .secondSingularAndSecondPlural }
  , { walsCode := "mlt", language := "Maltese", iso := "mlt", value := .secondSingularAndSecondPlural }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .secondSingularAndSecondPlural }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .noSecondPersonImperatives }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .secondSingularAndSecondPlural }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noSecondPersonImperatives }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .secondSingular }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .secondSingularAndSecondPlural }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .secondSingularAndSecondPlural }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .secondSingularAndSecondPlural }
  , { walsCode := "mnx", language := "Manx", iso := "glv", value := .secondPersonNumberNeutral }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noSecondPersonImperatives }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .secondSingularAndSecondPlural }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noSecondPersonImperatives }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .secondPersonNumberNeutral }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .secondSingularAndSecondPlural }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .secondSingularAndSecondPlural }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .secondSingularAndSecondPlural }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .secondSingularAndSecondPlural }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .secondPersonNumberNeutral }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .secondSingularAndSecondPlural }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .secondSingularAndSecondPlural }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noSecondPersonImperatives }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .secondPersonNumberNeutral }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .secondSingularAndSecondPlural }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .secondPersonNumberNeutral }
  , { walsCode := "mbg", language := "Mbugu", iso := "mhd", value := .secondSingularAndSecondPlural }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .secondSingularAndSecondPlural }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .secondPersonNumberNeutral }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .secondPersonNumberNeutral }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .secondPersonNumberNeutral }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .secondPersonNumberNeutral }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .secondSingularAndSecondPlural }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .secondPersonNumberNeutral }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .noSecondPersonImperatives }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .secondSingularAndSecondPlural }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .noSecondPersonImperatives }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .noSecondPersonImperatives }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .secondSingularAndSecondPlural }
  , { walsCode := "mbo", language := "Monumbo", iso := "mxk", value := .noSecondPersonImperatives }
  , { walsCode := "mop", language := "Mopan", iso := "mop", value := .secondSingularAndSecondPlural }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .secondSingularAndSecondPlural }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .secondSingularAndSecondPlural }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .secondSingularAndSecondPlural }
  , { walsCode := "mul", language := "Mulao", iso := "mlm", value := .noSecondPersonImperatives }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noSecondPersonImperatives }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .secondSingularAndSecondPlural }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .noSecondPersonImperatives }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .secondSingularAndSecondPlural }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .noSecondPersonImperatives }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .secondPersonNumberNeutral }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noSecondPersonImperatives }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .secondSingularAndSecondPlural }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .noSecondPersonImperatives }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .secondSingular }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .secondPersonNumberNeutral }
  , { walsCode := "npn", language := "Naga Pidgin", iso := "nag", value := .secondPersonNumberNeutral }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .secondSingularAndSecondPlural }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noSecondPersonImperatives }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .secondSingularAndSecondPlural }
  , { walsCode := "ntn", language := "Nateni", iso := "ntm", value := .secondSingularAndSecondPlural }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .noSecondPersonImperatives }
  , { walsCode := "ndg", language := "Ndogo", iso := "ndz", value := .secondSingular }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noSecondPersonImperatives }
  , { walsCode := "nel", language := "Nelemwa", iso := "nee", value := .noSecondPersonImperatives }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .secondSingular }
  , { walsCode := "nen", language := "Nenets (Forest)", iso := "yrk", value := .secondSingular }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .secondSingularAndSecondPlural }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .secondSingularAndSecondPlural }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noSecondPersonImperatives }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .secondSingularAndSecondPlural }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .secondSingular }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .secondSingularAndSecondPlural }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .secondPersonNumberNeutral }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .noSecondPersonImperatives }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .noSecondPersonImperatives }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .secondSingularAndSecondPlural }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .secondPersonNumberNeutral }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .secondSingular }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .secondSingular }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .secondPersonNumberNeutral }
  , { walsCode := "nub", language := "Nubi", iso := "kcn", value := .secondSingularAndSecondPlural }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .secondSingularAndSecondPlural }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noSecondPersonImperatives }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noSecondPersonImperatives }
  , { walsCode := "nng", language := "Nyanga", iso := "nyj", value := .secondSingular }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .secondPersonNumberNeutral }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .secondSingularAndSecondPlural }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .secondSingularAndSecondPlural }
  , { walsCode := "occ", language := "Occitan", iso := "oci", value := .secondSingular }
  , { walsCode := "oka", language := "Okanagan", iso := "oka", value := .secondSingularAndSecondPlural }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .secondPersonNumberNeutral }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .noSecondPersonImperatives }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .secondSingularAndSecondPlural }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .secondSingular }
  , { walsCode := "oix", language := "Otomí (Ixtenco)", iso := "otz", value := .secondSingularAndSecondPlural }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .secondSingularAndSecondPlural }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .secondSingularAndSecondPlural }
  , { walsCode := "pta", language := "Paita", iso := "duf", value := .secondSingularAndSecondPlural }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .noSecondPersonImperatives }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .secondPersonNumberNeutral }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noSecondPersonImperatives }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .secondPersonNumberNeutral }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .secondSingularAndSecondPlural }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .secondPersonNumberNeutral }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .secondSingularAndSecondPlural }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .noSecondPersonImperatives }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .secondSingularAndSecondPlural }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .noSecondPersonImperatives }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .secondSingular }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .secondPersonNumberNeutral }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .secondSingularAndSecondPlural }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noSecondPersonImperatives }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .secondPersonNumberNeutral }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .secondSingularAndSecondPlural }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .secondSingularAndSecondPlural }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .secondPersonNumberNeutral }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .secondSingularAndSecondPlural }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .secondSingular }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .secondSingularAndSecondPlural }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .secondSingularAndSecondPlural }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .secondSingularAndSecondPlural }
  , { walsCode := "qta", language := "Quechua (Tarma)", iso := "qvn", value := .secondSingularAndSecondPlural }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .secondSingularAndSecondPlural }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noSecondPersonImperatives }
  , { walsCode := "rwa", language := "Rawa", iso := "rwo", value := .secondSingularAndSecondPlural }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .secondSingularAndSecondPlural }
  , { walsCode := "rav", language := "Romani (Ajia Varvara)", iso := "rmn", value := .secondSingular }
  , { walsCode := "rka", language := "Romani (Kalderash)", iso := "rmy", value := .secondSingular }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .secondSingular }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .secondSingularAndSecondPlural }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .secondSingularAndSecondPlural }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .secondSingularAndSecondPlural }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .noSecondPersonImperatives }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .secondSingularAndSecondPlural }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noSecondPersonImperatives }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .secondSingularAndSecondPlural }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noSecondPersonImperatives }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .noSecondPersonImperatives }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .secondSingularAndSecondPlural }
  , { walsCode := "saw", language := "Sawu", iso := "hvn", value := .secondPersonNumberNeutral }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .secondPersonNumberNeutral }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .secondPersonNumberNeutral }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .secondPersonNumberNeutral }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noSecondPersonImperatives }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .secondSingular }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .secondSingularAndSecondPlural }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .secondSingularAndSecondPlural }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .secondSingularAndSecondPlural }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .secondSingularAndSecondPlural }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .secondSingularAndSecondPlural }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .secondSingularAndSecondPlural }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .noSecondPersonImperatives }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noSecondPersonImperatives }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .secondSingularAndSecondPlural }
  , { walsCode := "so", language := "So", iso := "teu", value := .secondSingularAndSecondPlural }
  , { walsCode := "sou", language := "Sorbian (Upper)", iso := "hsb", value := .secondSingularAndSecondPlural }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .secondSingularAndSecondPlural }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .secondSingularAndSecondPlural }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .secondSingularAndSecondPlural }
  , { walsCode := "sug", language := "Sungor", iso := "sjg", value := .secondSingularAndSecondPlural }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .secondSingular }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .secondPersonNumberNeutral }
  , { walsCode := "sva", language := "Svan", iso := "sva", value := .noSecondPersonImperatives }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .secondSingularAndSecondPlural }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .secondPersonNumberNeutral }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noSecondPersonImperatives }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .secondSingularAndSecondPlural }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .secondPersonNumberNeutral }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .secondSingularAndSecondPlural }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .secondSingularAndSecondPlural }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .secondSingularAndSecondPlural }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .secondSingularAndSecondPlural }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .secondSingularAndSecondPlural }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .secondSingularAndSecondPlural }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .secondSingular }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .secondSingularAndSecondPlural }
  , { walsCode := "tem", language := "Tem", iso := "kdh", value := .secondSingularAndSecondPlural }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .secondSingularAndSecondPlural }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .secondSingularAndSecondPlural }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .secondSingularAndSecondPlural }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .noSecondPersonImperatives }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noSecondPersonImperatives }
  , { walsCode := "thk", language := "Thakali", iso := "ths", value := .secondPersonNumberNeutral }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .secondSingularAndSecondPlural }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noSecondPersonImperatives }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .secondSingularAndSecondPlural }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .secondSingularAndSecondPlural }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noSecondPersonImperatives }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .secondPersonNumberNeutral }
  , { walsCode := "tms", language := "Tommo So", iso := "dto", value := .secondSingularAndSecondPlural }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .noSecondPersonImperatives }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .secondSingular }
  , { walsCode := "tor", language := "Toratán", iso := "rth", value := .secondPersonNumberNeutral }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .noSecondPersonImperatives }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .noSecondPersonImperatives }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .noSecondPersonImperatives }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noSecondPersonImperatives }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .secondSingular }
  , { walsCode := "tsa", language := "Tsakhur", iso := "tkr", value := .secondSingularAndSecondPlural }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .secondSingularAndSecondPlural }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .secondSingularAndSecondPlural }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .secondSingular }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .secondSingularAndSecondPlural }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .secondSingularAndSecondPlural }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .secondSingularAndSecondPlural }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .secondSingular }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .secondSingularAndSecondPlural }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .secondSingularAndSecondPlural }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .secondSingularAndSecondPlural }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .secondSingularAndSecondPlural }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .secondSingularAndSecondPlural }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .secondSingularAndSecondPlural }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .secondSingularAndSecondPlural }
  ]

private def allData_1 : List (Datapoint MorphologicalImperative) :=
  [ { walsCode := "uld", language := "Uldeme", iso := "udl", value := .secondSingularAndSecondPlural }
  , { walsCode := "uma", language := "Uma", iso := "ppk", value := .noSecondPersonImperatives }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .secondSingularAndSecondPlural }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noSecondPersonImperatives }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .secondSingular }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .secondSingularAndSecondPlural }
  , { walsCode := "vag", language := "Vagla", iso := "vag", value := .noSecondPersonImperatives }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .secondSingularAndSecondPlural }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .noSecondPersonImperatives }
  , { walsCode := "vot", language := "Votic", iso := "vot", value := .secondSingularAndSecondPlural }
  , { walsCode := "wll", language := "Wallisian", iso := "wls", value := .noSecondPersonImperatives }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noSecondPersonImperatives }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .secondSingularAndSecondPlural }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .secondSingularAndSecondPlural }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .secondSingularAndSecondPlural }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .secondSingularAndSecondPlural }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .noSecondPersonImperatives }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noSecondPersonImperatives }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .secondSingularAndSecondPlural }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .secondPersonNumberNeutral }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .secondPersonNumberNeutral }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .secondSingularAndSecondPlural }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .secondSingularAndSecondPlural }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .secondSingularAndSecondPlural }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .secondSingularAndSecondPlural }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .secondPersonNumberNeutral }
  , { walsCode := "wwr", language := "Woiwurrung", iso := "wyi", value := .secondSingularAndSecondPlural }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .secondPersonNumberNeutral }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .secondSingularAndSecondPlural }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noSecondPersonImperatives }
  , { walsCode := "ykm", language := "Yakoma", iso := "yky", value := .noSecondPersonImperatives }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .secondSingularAndSecondPlural }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .noSecondPersonImperatives }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .secondSingularAndSecondPlural }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .secondPersonNumberNeutral }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .secondSingularAndSecondPlural }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .secondSingularAndSecondPlural }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noSecondPersonImperatives }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .secondSingularAndSecondPlural }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .secondSingularAndSecondPlural }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .secondSingularAndSecondPlural }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .secondSingularAndSecondPlural }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .secondSingularAndSecondPlural }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .secondSingularAndSecondPlural }
  , { walsCode := "zen", language := "Zenaga", iso := "zen", value := .secondSingularAndSecondPlural }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .secondSingularAndSecondPlural }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .secondSingularAndSecondPlural }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noSecondPersonImperatives }
  ]

/-- Complete WALS 70A dataset (548 languages). -/
def allData : List (Datapoint MorphologicalImperative) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 548 := by native_decide

theorem count_secondSingularAndSecondPlural :
    (allData.filter (·.value == .secondSingularAndSecondPlural)).length = 292 := by native_decide
theorem count_secondSingular :
    (allData.filter (·.value == .secondSingular)).length = 43 := by native_decide
theorem count_secondPlural :
    (allData.filter (·.value == .secondPlural)).length = 2 := by native_decide
theorem count_secondPersonNumberNeutral :
    (allData.filter (·.value == .secondPersonNumberNeutral)).length = 89 := by native_decide
theorem count_noSecondPersonImperatives :
    (allData.filter (·.value == .noSecondPersonImperatives)).length = 122 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F70A
