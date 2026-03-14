/-!
# WALS Feature 84A: Order of Object, Oblique, and Verb
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 84A`.

Chapter 84, 500 languages.
-/

namespace Core.WALS.F84A

/-- WALS 84A values. -/
inductive ObjectObliqueVerbOrder where
  | vox  -- VOX (210 languages)
  | xvo  -- XVO (3 languages)
  | xov  -- XOV (48 languages)
  | oxv  -- OXV (27 languages)
  | ovx  -- OVX (45 languages)
  | noDominantOrder  -- No dominant order (167 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 84A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ObjectObliqueVerbOrder
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 84A dataset (500 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .noDominantOrder }
  , { walsCode := "xam", language := "/Xam", iso := "xam", value := .vox }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .vox }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .xov }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .vox }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noDominantOrder }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .noDominantOrder }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noDominantOrder }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .vox }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .noDominantOrder }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .vox }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .noDominantOrder }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noDominantOrder }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noDominantOrder }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .xov }
  , { walsCode := "ama", language := "Amara", iso := "aie", value := .vox }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .vox }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .vox }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .xov }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .vox }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .vox }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .xov }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .oxv }
  , { walsCode := "ayi", language := "Anyi", iso := "any", value := .vox }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .noDominantOrder }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .oxv }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .ovx }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .xov }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noDominantOrder }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .vox }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .vox }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .vox }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .xov }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noDominantOrder }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .noDominantOrder }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .vox }
  , { walsCode := "au", language := "Au", iso := "avt", value := .vox }
  , { walsCode := "avk", language := "Avikam", iso := "avi", value := .vox }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .noDominantOrder }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .xov }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .noDominantOrder }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .noDominantOrder }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .noDominantOrder }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .vox }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .vox }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .noDominantOrder }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .vox }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .ovx }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .oxv }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .ovx }
  , { walsCode := "bas", language := "Basaá", iso := "bas", value := .vox }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .xov }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .vox }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .vox }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .xov }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .oxv }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .noDominantOrder }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .xov }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .vox }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .vox }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .vox }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .xov }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .vox }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .vox }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .vox }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .ovx }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .vox }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noDominantOrder }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .ovx }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .vox }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .noDominantOrder }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .vox }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .noDominantOrder }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noDominantOrder }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .vox }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .noDominantOrder }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .ovx }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .noDominantOrder }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .xov }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .xvo }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .ovx }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .noDominantOrder }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .xov }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .noDominantOrder }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .vox }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .noDominantOrder }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .noDominantOrder }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .vox }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .vox }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .vox }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .vox }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .xov }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noDominantOrder }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .oxv }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .noDominantOrder }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noDominantOrder }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .vox }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noDominantOrder }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .noDominantOrder }
  , { walsCode := "cua", language := "Cua", iso := "cua", value := .vox }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .vox }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .noDominantOrder }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .noDominantOrder }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .vox }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .xov }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .oxv }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .noDominantOrder }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .xov }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noDominantOrder }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .ovx }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .noDominantOrder }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .ovx }
  , { walsCode := "djr", language := "Djaru", iso := "ddj", value := .noDominantOrder }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .noDominantOrder }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .noDominantOrder }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .vox }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .ovx }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noDominantOrder }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noDominantOrder }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .vox }
  , { walsCode := "emm", language := "Emmi", iso := "amy", value := .noDominantOrder }
  , { walsCode := "ene", language := "Enets", iso := "", value := .xov }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .vox }
  , { walsCode := "eng", language := "English", iso := "eng", value := .vox }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .ovx }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .vox }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noDominantOrder }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .vox }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .oxv }
  , { walsCode := "fre", language := "French", iso := "fra", value := .vox }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .noDominantOrder }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .vox }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .vox }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .vox }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .noDominantOrder }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .vox }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noDominantOrder }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .noDominantOrder }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .noDominantOrder }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .vox }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noDominantOrder }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .vox }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .oxv }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .vox }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .vox }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .noDominantOrder }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .vox }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .xov }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .ovx }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .noDominantOrder }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .vox }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .noDominantOrder }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .noDominantOrder }
  , { walsCode := "grg", language := "Gurr-goni", iso := "gge", value := .noDominantOrder }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noDominantOrder }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .xov }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .xvo }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .vox }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .vox }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .vox }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .vox }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .ovx }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .vox }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .xov }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .noDominantOrder }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .ovx }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .vox }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .vox }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .noDominantOrder }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .vox }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .vox }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .vox }
  , { walsCode := "iha", language := "Iha", iso := "ihp", value := .oxv }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .noDominantOrder }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .vox }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .noDominantOrder }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noDominantOrder }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .vox }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noDominantOrder }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .vox }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .vox }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .vox }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .vox }
  , { walsCode := "jam", language := "Jaminjung", iso := "djd", value := .noDominantOrder }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .xov }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .noDominantOrder }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .xov }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .vox }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .vox }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .vox }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .ovx }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .ovx }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .oxv }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .noDominantOrder }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .vox }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .oxv }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .vox }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .noDominantOrder }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .vox }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .vox }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .vox }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .oxv }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noDominantOrder }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .ovx }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .vox }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .vox }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noDominantOrder }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .vox }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .xov }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noDominantOrder }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .oxv }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .vox }
  , { walsCode := "kin", language := "Kinyarwanda", iso := "kin", value := .vox }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .vox }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noDominantOrder }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .noDominantOrder }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .ovx }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .xov }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .vox }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .vox }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .vox }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .oxv }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .vox }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .ovx }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .vox }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .noDominantOrder }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .ovx }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .vox }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .noDominantOrder }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .vox }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .oxv }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .oxv }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .vox }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .vox }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .xov }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .vox }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .vox }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .noDominantOrder }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .xov }
  , { walsCode := "lec", language := "Leko", iso := "lec", value := .noDominantOrder }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .vox }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .noDominantOrder }
  , { walsCode := "les", language := "Lese", iso := "les", value := .noDominantOrder }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .vox }
  , { walsCode := "lml", language := "Limilngan", iso := "lmc", value := .noDominantOrder }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .vox }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .oxv }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .noDominantOrder }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .vox }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .vox }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noDominantOrder }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .noDominantOrder }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .vox }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .vox }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .vox }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noDominantOrder }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .vox }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .vox }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .vox }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .vox }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .vox }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .vox }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .xvo }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .ovx }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .vox }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .vox }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .xov }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .ovx }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .ovx }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .vox }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noDominantOrder }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .noDominantOrder }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noDominantOrder }
  , { walsCode := "mrr", language := "Maringarr", iso := "zmt", value := .noDominantOrder }
  , { walsCode := "mrh", language := "Marrithiyel", iso := "mfr", value := .noDominantOrder }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .vox }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .noDominantOrder }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .oxv }
  , { walsCode := "mdl", language := "Matngele", iso := "zml", value := .noDominantOrder }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .ovx }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .vox }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .vox }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .noDominantOrder }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .vox }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .vox }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .ovx }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .ovx }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .noDominantOrder }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .vox }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .oxv }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .xov }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .vox }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noDominantOrder }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noDominantOrder }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .noDominantOrder }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .vox }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .vox }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .vox }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .vox }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .vox }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .vox }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .xov }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .vox }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .noDominantOrder }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .vox }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .noDominantOrder }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .vox }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .vox }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .noDominantOrder }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .vox }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .vox }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .vox }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .vox }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .ovx }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .noDominantOrder }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .vox }
  , { walsCode := "mwe", language := "Mwera", iso := "mwe", value := .vox }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .oxv }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .vox }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .xov }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .vox }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noDominantOrder }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .oxv }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .noDominantOrder }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .vox }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .vox }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .vox }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .xov }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .ovx }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .noDominantOrder }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noDominantOrder }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noDominantOrder }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .vox }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .noDominantOrder }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .noDominantOrder }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .vox }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noDominantOrder }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noDominantOrder }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .vox }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .ovx }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .noDominantOrder }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .vox }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .vox }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .vox }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .vox }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .vox }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .vox }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .noDominantOrder }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .vox }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noDominantOrder }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .vox }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .vox }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .oxv }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .vox }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .vox }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noDominantOrder }
  , { walsCode := "one", language := "One", iso := "aun", value := .vox }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noDominantOrder }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .xov }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .oxv }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .vox }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .vox }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .noDominantOrder }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .vox }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .noDominantOrder }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .noDominantOrder }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noDominantOrder }
  , { walsCode := "ptw", language := "Patwin", iso := "pwi", value := .noDominantOrder }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noDominantOrder }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .xov }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .noDominantOrder }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .vox }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .noDominantOrder }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .vox }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .oxv }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .xov }
  , { walsCode := "pun", language := "Pungupungu", iso := "wdj", value := .noDominantOrder }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .ovx }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .xov }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noDominantOrder }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .xov }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noDominantOrder }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .noDominantOrder }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .vox }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .vox }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .ovx }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noDominantOrder }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .noDominantOrder }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .vox }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .xov }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .noDominantOrder }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .ovx }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .vox }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .xov }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .ovx }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .vox }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noDominantOrder }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .xov }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .vox }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .noDominantOrder }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .xov }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .vox }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .vox }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .ovx }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .noDominantOrder }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .xov }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .vox }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .vox }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .vox }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .vox }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .ovx }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .ovx }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .vox }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .vox }
  , { walsCode := "tba", language := "Tabare", iso := "sst", value := .xov }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noDominantOrder }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .oxv }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .vox }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .xov }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .ovx }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .xov }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .noDominantOrder }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .xov }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .vox }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .noDominantOrder }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .vox }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .vox }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .vox }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .vox }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .vox }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .noDominantOrder }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .vox }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .vox }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .oxv }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .noDominantOrder }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noDominantOrder }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noDominantOrder }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .vox }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .vox }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .vox }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noDominantOrder }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .vox }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .noDominantOrder }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .vox }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .noDominantOrder }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .noDominantOrder }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .ovx }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noDominantOrder }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .vox }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .xov }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .noDominantOrder }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .vox }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .vox }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noDominantOrder }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .noDominantOrder }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .vox }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .vox }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .ovx }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noDominantOrder }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .noDominantOrder }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .ovx }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .vox }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .xov }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .oxv }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .vox }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .ovx }
  , { walsCode := "wan", language := "Wangkumara", iso := "xwk", value := .noDominantOrder }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .noDominantOrder }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noDominantOrder }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .vox }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .noDominantOrder }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .noDominantOrder }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .noDominantOrder }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .vox }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .vox }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .vox }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noDominantOrder }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .vox }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noDominantOrder }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .noDominantOrder }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noDominantOrder }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .vox }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .vox }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .ovx }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .noDominantOrder }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .ovx }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .vox }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .xov }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .noDominantOrder }
  , { walsCode := "ywr", language := "Yawuru", iso := "ywr", value := .noDominantOrder }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .ovx }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noDominantOrder }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .noDominantOrder }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .vox }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noDominantOrder }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .ovx }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noDominantOrder }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .vox }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .noDominantOrder }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .noDominantOrder }
  ]

-- Count verification
theorem total_count : allData.length = 500 := by native_decide

theorem count_vox :
    (allData.filter (·.value == .vox)).length = 210 := by native_decide
theorem count_xvo :
    (allData.filter (·.value == .xvo)).length = 3 := by native_decide
theorem count_xov :
    (allData.filter (·.value == .xov)).length = 48 := by native_decide
theorem count_oxv :
    (allData.filter (·.value == .oxv)).length = 27 := by native_decide
theorem count_ovx :
    (allData.filter (·.value == .ovx)).length = 45 := by native_decide
theorem count_noDominantOrder :
    (allData.filter (·.value == .noDominantOrder)).length = 167 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F84A
