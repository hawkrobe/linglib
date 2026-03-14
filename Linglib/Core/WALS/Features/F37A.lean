/-!
# WALS Feature 37A: Definite Articles
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 37A`.

Chapter 37, 620 languages.
-/

namespace Core.WALS.F37A

/-- WALS 37A values. -/
inductive DefiniteArticleType where
  | definiteWordDistinctFromDemonstrative  -- Definite word distinct from demonstrative (216 languages)
  | demonstrativeWordUsedAsDefiniteArticle  -- Demonstrative word used as definite article (69 languages)
  | definiteAffix  -- Definite affix (92 languages)
  | noDefiniteButIndefiniteArticle  -- No definite, but indefinite article (45 languages)
  | noDefiniteOrIndefiniteArticle  -- No definite or indefinite article (198 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 37A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : DefiniteArticleType
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "aar", language := "Aari", iso := "aiw", value := .definiteAffix }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .definiteAffix }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ady", language := "Adyghe (Abzakh)", iso := "ady", value := .definiteAffix }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .definiteAffix }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .definiteAffix }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .definiteAffix }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .definiteAffix }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .definiteAffix }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .definiteAffix }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .definiteAffix }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .definiteAffix }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .definiteAffix }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .definiteAffix }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .definiteAffix }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .definiteAffix }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .definiteAffix }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ats", language := "Atsugewi", iso := "atw", value := .definiteAffix }
  , { walsCode := "au", language := "Au", iso := "avt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "avk", language := "Avikam", iso := "avi", value := .definiteAffix }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .definiteAffix }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .definiteAffix }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .definiteAffix }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bsi", language := "Berber (Siwa)", iso := "siz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .definiteAffix }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .definiteAffix }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .definiteAffix }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "cmx", language := "Comox", iso := "coo", value := .definiteAffix }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .definiteAffix }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .definiteAffix }
  , { walsCode := "day", language := "Day", iso := "dai", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .definiteAffix }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .definiteAffix }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "eng", language := "English", iso := "eng", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "fre", language := "French", iso := "fra", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .definiteAffix }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .definiteAffix }
  , { walsCode := "gam", language := "Gamo", iso := "gmv", value := .definiteAffix }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .definiteAffix }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ger", language := "German", iso := "deu", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "gil", language := "Gilaki", iso := "glk", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .definiteAffix }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .definiteAffix }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .definiteAffix }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .definiteAffix }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .definiteAffix }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .definiteAffix }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .definiteAffix }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .definiteAffix }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .definiteAffix }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .definiteAffix }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .definiteAffix }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kms", language := "Kamass", iso := "xas", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .definiteAffix }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "kop", language := "Komi-Permyak", iso := "koi", value := .definiteAffix }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .definiteAffix }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .definiteAffix }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kpo", language := "Kposo", iso := "kpo", value := .definiteAffix }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .definiteAffix }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .definiteAffix }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .definiteAffix }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .definiteAffix }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lar", language := "Laragia", iso := "lrg", value := .definiteAffix }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "leb", language := "Lebeo", iso := "agh", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .definiteAffix }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .definiteAffix }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .definiteAffix }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .definiteAffix }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .definiteAffix }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "mko", language := "Mokilko", iso := "moz", value := .definiteAffix }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .definiteAffix }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .definiteAffix }
  , { walsCode := "moe", language := "Mordvin (Erzya)", iso := "myv", value := .definiteAffix }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .definiteAffix }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .definiteAffix }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .definiteAffix }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .definiteAffix }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .definiteAffix }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .definiteAffix }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .definiteAffix }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .definiteAffix }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .definiteAffix }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .definiteAffix }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .definiteAffix }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .definiteAffix }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .definiteAffix }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .definiteAffix }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .definiteAffix }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "shm", language := "Shambala", iso := "ksb", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .noDefiniteOrIndefiniteArticle }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "sro", language := "Siroi", iso := "ssd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .definiteAffix }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "som", language := "Somali", iso := "som", value := .definiteAffix }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .definiteAffix }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .definiteAffix }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .definiteAffix }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "tan", language := "Tangale", iso := "tan", value := .definiteAffix }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .definiteAffix }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .definiteAffix }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tot", language := "Totonac (Misantla)", iso := "tlc", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tgo", language := "Tsogo", iso := "tsv", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .definiteAffix }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .definiteAffix }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .definiteAffix }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "wrw", language := "Warrwa", iso := "wwr", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .definiteAffix }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .definiteAffix }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .demonstrativeWordUsedAsDefiniteArticle }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .noDefiniteButIndefiniteArticle }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .definiteAffix }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .definiteWordDistinctFromDemonstrative }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noDefiniteOrIndefiniteArticle }
  ]

/-- Complete WALS 37A dataset (620 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 620 := by native_decide

theorem count_definiteWordDistinctFromDemonstrative :
    (allData.filter (·.value == .definiteWordDistinctFromDemonstrative)).length = 216 := by native_decide
theorem count_demonstrativeWordUsedAsDefiniteArticle :
    (allData.filter (·.value == .demonstrativeWordUsedAsDefiniteArticle)).length = 69 := by native_decide
theorem count_definiteAffix :
    (allData.filter (·.value == .definiteAffix)).length = 92 := by native_decide
theorem count_noDefiniteButIndefiniteArticle :
    (allData.filter (·.value == .noDefiniteButIndefiniteArticle)).length = 45 := by native_decide
theorem count_noDefiniteOrIndefiniteArticle :
    (allData.filter (·.value == .noDefiniteOrIndefiniteArticle)).length = 198 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F37A
