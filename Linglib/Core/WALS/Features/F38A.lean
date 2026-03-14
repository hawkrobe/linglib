/-!
# WALS Feature 38A: Indefinite Articles
@cite{dryer-2013-wals}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 38A`.

Chapter 38, 534 languages.
-/

namespace Core.WALS.F38A

/-- WALS 38A values. -/
inductive IndefiniteArticleType where
  | indefiniteWordDistinctFromOne  -- Indefinite word distinct from 'one' (102 languages)
  | indefiniteWordSameAsOne  -- Indefinite word same as 'one' (112 languages)
  | indefiniteAffix  -- Indefinite affix (24 languages)
  | noIndefiniteButDefiniteArticle  -- No indefinite, but definite article (98 languages)
  | noDefiniteOrIndefiniteArticle  -- No definite or indefinite article (198 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 38A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : IndefiniteArticleType
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "aar", language := "Aari", iso := "aiw", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .indefiniteWordSameAsOne }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .indefiniteWordSameAsOne }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .indefiniteWordSameAsOne }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .indefiniteWordSameAsOne }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .indefiniteAffix }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .indefiniteWordSameAsOne }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "au", language := "Au", iso := "avt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .indefiniteWordSameAsOne }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .indefiniteWordSameAsOne }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .indefiniteWordSameAsOne }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .indefiniteWordSameAsOne }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .indefiniteWordSameAsOne }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .indefiniteWordSameAsOne }
  , { walsCode := "bsi", language := "Berber (Siwa)", iso := "siz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "bin", language := "Binandere", iso := "bhg", value := .indefiniteWordSameAsOne }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .indefiniteWordSameAsOne }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .indefiniteAffix }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .indefiniteWordSameAsOne }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .indefiniteWordSameAsOne }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .indefiniteWordSameAsOne }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .indefiniteWordSameAsOne }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .indefiniteWordSameAsOne }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .indefiniteWordSameAsOne }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .indefiniteAffix }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .indefiniteWordSameAsOne }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "eng", language := "English", iso := "eng", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "fre", language := "French", iso := "fra", value := .indefiniteWordSameAsOne }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .indefiniteAffix }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .indefiniteAffix }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ger", language := "German", iso := "deu", value := .indefiniteWordSameAsOne }
  , { walsCode := "gil", language := "Gilaki", iso := "glk", value := .indefiniteWordSameAsOne }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .indefiniteWordSameAsOne }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .indefiniteWordSameAsOne }
  , { walsCode := "gnn", language := "Gunin", iso := "gww", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .indefiniteWordSameAsOne }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .indefiniteWordSameAsOne }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .indefiniteWordSameAsOne }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .indefiniteWordSameAsOne }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .indefiniteWordSameAsOne }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .indefiniteAffix }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .indefiniteWordSameAsOne }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .indefiniteWordSameAsOne }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .indefiniteWordSameAsOne }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .indefiniteWordSameAsOne }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .indefiniteWordSameAsOne }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .indefiniteWordSameAsOne }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .indefiniteWordSameAsOne }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .indefiniteWordSameAsOne }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .indefiniteAffix }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .indefiniteWordSameAsOne }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .indefiniteWordSameAsOne }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .indefiniteWordSameAsOne }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .indefiniteAffix }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .indefiniteAffix }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "kpo", language := "Kposo", iso := "kpo", value := .indefiniteAffix }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .indefiniteAffix }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .indefiniteAffix }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .indefiniteWordSameAsOne }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .indefiniteWordSameAsOne }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .indefiniteAffix }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .indefiniteWordSameAsOne }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .indefiniteWordSameAsOne }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .indefiniteWordSameAsOne }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .indefiniteWordSameAsOne }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .indefiniteWordSameAsOne }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .indefiniteWordSameAsOne }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .indefiniteAffix }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .indefiniteWordSameAsOne }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .indefiniteWordSameAsOne }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .indefiniteWordSameAsOne }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .indefiniteWordSameAsOne }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .indefiniteAffix }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .indefiniteWordSameAsOne }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .indefiniteAffix }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "mzn", language := "Mazanderani", iso := "mzn", value := .indefiniteWordSameAsOne }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .indefiniteWordSameAsOne }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .indefiniteWordSameAsOne }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .indefiniteWordSameAsOne }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .indefiniteWordSameAsOne }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .indefiniteWordSameAsOne }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .indefiniteWordSameAsOne }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .indefiniteWordSameAsOne }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .indefiniteWordSameAsOne }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .indefiniteWordSameAsOne }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .indefiniteWordSameAsOne }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .indefiniteAffix }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .indefiniteAffix }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .indefiniteAffix }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .indefiniteWordSameAsOne }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .indefiniteWordSameAsOne }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .indefiniteWordSameAsOne }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .indefiniteWordSameAsOne }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .indefiniteWordSameAsOne }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .indefiniteWordSameAsOne }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .indefiniteWordSameAsOne }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .indefiniteWordSameAsOne }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .indefiniteWordSameAsOne }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .indefiniteWordSameAsOne }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .indefiniteWordSameAsOne }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .indefiniteWordSameAsOne }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .indefiniteWordSameAsOne }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .indefiniteWordSameAsOne }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .indefiniteWordSameAsOne }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "qaf", language := "Qafar", iso := "aar", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .indefiniteAffix }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .indefiniteWordSameAsOne }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .indefiniteWordSameAsOne }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .indefiniteWordSameAsOne }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .indefiniteWordSameAsOne }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .indefiniteWordSameAsOne }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .indefiniteWordSameAsOne }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .indefiniteWordSameAsOne }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .indefiniteWordSameAsOne }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .indefiniteWordSameAsOne }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .indefiniteWordSameAsOne }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .indefiniteWordSameAsOne }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .indefiniteWordSameAsOne }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .indefiniteWordSameAsOne }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .indefiniteAffix }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tts", language := "Tati (Southern)", iso := "tks", value := .indefiniteWordSameAsOne }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .indefiniteAffix }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .indefiniteWordSameAsOne }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .indefiniteWordSameAsOne }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .indefiniteWordSameAsOne }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .indefiniteWordSameAsOne }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .indefiniteWordSameAsOne }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .indefiniteWordSameAsOne }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .indefiniteWordSameAsOne }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .indefiniteWordSameAsOne }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .indefiniteWordSameAsOne }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .indefiniteWordSameAsOne }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .indefiniteWordSameAsOne }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .indefiniteAffix }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .indefiniteAffix }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "ura", language := "Ura", iso := "uur", value := .indefiniteWordSameAsOne }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .noIndefiniteButDefiniteArticle }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "urd", language := "Urdu", iso := "urd", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .indefiniteWordSameAsOne }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .indefiniteWordSameAsOne }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .indefiniteWordSameAsOne }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "wor", language := "Worora", iso := "wro", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .indefiniteWordSameAsOne }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .indefiniteWordDistinctFromOne }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .noDefiniteOrIndefiniteArticle }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .indefiniteWordSameAsOne }
  , { walsCode := "zar", language := "Zarma", iso := "dje", value := .indefiniteWordSameAsOne }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .noIndefiniteButDefiniteArticle }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .noDefiniteOrIndefiniteArticle }
  ]

/-- Complete WALS 38A dataset (534 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 534 := by native_decide

theorem count_indefiniteWordDistinctFromOne :
    (allData.filter (·.value == .indefiniteWordDistinctFromOne)).length = 102 := by native_decide
theorem count_indefiniteWordSameAsOne :
    (allData.filter (·.value == .indefiniteWordSameAsOne)).length = 112 := by native_decide
theorem count_indefiniteAffix :
    (allData.filter (·.value == .indefiniteAffix)).length = 24 := by native_decide
theorem count_noIndefiniteButDefiniteArticle :
    (allData.filter (·.value == .noIndefiniteButDefiniteArticle)).length = 98 := by native_decide
theorem count_noDefiniteOrIndefiniteArticle :
    (allData.filter (·.value == .noDefiniteOrIndefiniteArticle)).length = 198 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F38A
