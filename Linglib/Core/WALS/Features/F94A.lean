/-!
# WALS Feature 94A: Order of Adverbial Subordinator and Clause
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 94A`.

Chapter 94, 659 languages.
-/

namespace Core.WALS.F94A

/-- WALS 94A values. -/
inductive OrderOfAdverbialSubordinatorAndClause where
  | initialSubordinatorWord  -- Initial subordinator word (398 languages)
  | finalSubordinatorWord  -- Final subordinator word (96 languages)
  | internalSubordinatorWord  -- Internal subordinator word (8 languages)
  | subordinatingSuffix  -- Subordinating suffix (64 languages)
  | mixed  -- Mixed (93 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 94A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : OrderOfAdverbialSubordinatorAndClause
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .initialSubordinatorWord }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .initialSubordinatorWord }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .subordinatingSuffix }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .mixed }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .initialSubordinatorWord }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .initialSubordinatorWord }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .initialSubordinatorWord }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .mixed }
  , { walsCode := "adn", language := "Adynyamathanha", iso := "adt", value := .initialSubordinatorWord }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .finalSubordinatorWord }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .mixed }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .finalSubordinatorWord }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .initialSubordinatorWord }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .initialSubordinatorWord }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .initialSubordinatorWord }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .initialSubordinatorWord }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .initialSubordinatorWord }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .mixed }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .finalSubordinatorWord }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .finalSubordinatorWord }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .initialSubordinatorWord }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .mixed }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .finalSubordinatorWord }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .mixed }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .subordinatingSuffix }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .subordinatingSuffix }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .finalSubordinatorWord }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .initialSubordinatorWord }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .initialSubordinatorWord }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .initialSubordinatorWord }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .initialSubordinatorWord }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .initialSubordinatorWord }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .initialSubordinatorWord }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .initialSubordinatorWord }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .initialSubordinatorWord }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .finalSubordinatorWord }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .mixed }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .initialSubordinatorWord }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .initialSubordinatorWord }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .initialSubordinatorWord }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .finalSubordinatorWord }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .initialSubordinatorWord }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .finalSubordinatorWord }
  , { walsCode := "au", language := "Au", iso := "avt", value := .initialSubordinatorWord }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .mixed }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .mixed }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .finalSubordinatorWord }
  , { walsCode := "ayw", language := "Ayiwo", iso := "nfl", value := .initialSubordinatorWord }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .initialSubordinatorWord }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .initialSubordinatorWord }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .initialSubordinatorWord }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .initialSubordinatorWord }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .initialSubordinatorWord }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .finalSubordinatorWord }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .subordinatingSuffix }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .subordinatingSuffix }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .initialSubordinatorWord }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .initialSubordinatorWord }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .finalSubordinatorWord }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .initialSubordinatorWord }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .initialSubordinatorWord }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .initialSubordinatorWord }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .finalSubordinatorWord }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .subordinatingSuffix }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .initialSubordinatorWord }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .initialSubordinatorWord }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .initialSubordinatorWord }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .finalSubordinatorWord }
  , { walsCode := "bkb", language := "Betta Kurumba", iso := "xub", value := .finalSubordinatorWord }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .initialSubordinatorWord }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .initialSubordinatorWord }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .initialSubordinatorWord }
  , { walsCode := "bnr", language := "Bilinarra", iso := "nbj", value := .initialSubordinatorWord }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .finalSubordinatorWord }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .mixed }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .mixed }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .initialSubordinatorWord }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .initialSubordinatorWord }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .internalSubordinatorWord }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .initialSubordinatorWord }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .initialSubordinatorWord }
  , { walsCode := "bdu", language := "Budu", iso := "buu", value := .initialSubordinatorWord }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .finalSubordinatorWord }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .initialSubordinatorWord }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .initialSubordinatorWord }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .initialSubordinatorWord }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .subordinatingSuffix }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .mixed }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .initialSubordinatorWord }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .mixed }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .mixed }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .subordinatingSuffix }
  , { walsCode := "car", language := "Carib", iso := "car", value := .finalSubordinatorWord }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .finalSubordinatorWord }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .finalSubordinatorWord }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .initialSubordinatorWord }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .initialSubordinatorWord }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .initialSubordinatorWord }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .initialSubordinatorWord }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .initialSubordinatorWord }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .initialSubordinatorWord }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .finalSubordinatorWord }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .finalSubordinatorWord }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .finalSubordinatorWord }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .initialSubordinatorWord }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .initialSubordinatorWord }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .initialSubordinatorWord }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .initialSubordinatorWord }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .initialSubordinatorWord }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .finalSubordinatorWord }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .finalSubordinatorWord }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .subordinatingSuffix }
  , { walsCode := "cln", language := "Cholón", iso := "cht", value := .subordinatingSuffix }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .initialSubordinatorWord }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .initialSubordinatorWord }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .initialSubordinatorWord }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .initialSubordinatorWord }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .finalSubordinatorWord }
  , { walsCode := "cbo", language := "Chácobo", iso := "cao", value := .subordinatingSuffix }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .mixed }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .initialSubordinatorWord }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .initialSubordinatorWord }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .initialSubordinatorWord }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .initialSubordinatorWord }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .initialSubordinatorWord }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .finalSubordinatorWord }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .mixed }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .initialSubordinatorWord }
  , { walsCode := "des", language := "Desano", iso := "des", value := .finalSubordinatorWord }
  , { walsCode := "dhr", language := "Dhargari", iso := "dhr", value := .initialSubordinatorWord }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .initialSubordinatorWord }
  , { walsCode := "dms", language := "Dimasa", iso := "dis", value := .finalSubordinatorWord }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .initialSubordinatorWord }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .initialSubordinatorWord }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .initialSubordinatorWord }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .subordinatingSuffix }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .mixed }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .initialSubordinatorWord }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .finalSubordinatorWord }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .initialSubordinatorWord }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .initialSubordinatorWord }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .finalSubordinatorWord }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .initialSubordinatorWord }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .initialSubordinatorWord }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .initialSubordinatorWord }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .mixed }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .subordinatingSuffix }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .initialSubordinatorWord }
  , { walsCode := "eng", language := "English", iso := "eng", value := .initialSubordinatorWord }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .mixed }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .finalSubordinatorWord }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .initialSubordinatorWord }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .mixed }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .subordinatingSuffix }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .initialSubordinatorWord }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .initialSubordinatorWord }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .initialSubordinatorWord }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .initialSubordinatorWord }
  , { walsCode := "fre", language := "French", iso := "fra", value := .initialSubordinatorWord }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .initialSubordinatorWord }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .subordinatingSuffix }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .initialSubordinatorWord }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .initialSubordinatorWord }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .initialSubordinatorWord }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .subordinatingSuffix }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .subordinatingSuffix }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .initialSubordinatorWord }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .initialSubordinatorWord }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .finalSubordinatorWord }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .initialSubordinatorWord }
  , { walsCode := "ger", language := "German", iso := "deu", value := .initialSubordinatorWord }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .finalSubordinatorWord }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .initialSubordinatorWord }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .initialSubordinatorWord }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .finalSubordinatorWord }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .initialSubordinatorWord }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .initialSubordinatorWord }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .initialSubordinatorWord }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .initialSubordinatorWord }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .subordinatingSuffix }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .initialSubordinatorWord }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .initialSubordinatorWord }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .subordinatingSuffix }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .finalSubordinatorWord }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .initialSubordinatorWord }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .initialSubordinatorWord }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .initialSubordinatorWord }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .subordinatingSuffix }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .initialSubordinatorWord }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .finalSubordinatorWord }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .initialSubordinatorWord }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .finalSubordinatorWord }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .initialSubordinatorWord }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .finalSubordinatorWord }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .initialSubordinatorWord }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .subordinatingSuffix }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .initialSubordinatorWord }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .initialSubordinatorWord }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .finalSubordinatorWord }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .finalSubordinatorWord }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .initialSubordinatorWord }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .initialSubordinatorWord }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .subordinatingSuffix }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .mixed }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .initialSubordinatorWord }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .initialSubordinatorWord }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .mixed }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .initialSubordinatorWord }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .initialSubordinatorWord }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .initialSubordinatorWord }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .mixed }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .subordinatingSuffix }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .initialSubordinatorWord }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .subordinatingSuffix }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .initialSubordinatorWord }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .initialSubordinatorWord }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .initialSubordinatorWord }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .initialSubordinatorWord }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .initialSubordinatorWord }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .initialSubordinatorWord }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .finalSubordinatorWord }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .finalSubordinatorWord }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .subordinatingSuffix }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .finalSubordinatorWord }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .initialSubordinatorWord }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .initialSubordinatorWord }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .finalSubordinatorWord }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .initialSubordinatorWord }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .initialSubordinatorWord }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .mixed }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .initialSubordinatorWord }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .initialSubordinatorWord }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .initialSubordinatorWord }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .mixed }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .initialSubordinatorWord }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .mixed }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .mixed }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .mixed }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .mixed }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .initialSubordinatorWord }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .initialSubordinatorWord }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .finalSubordinatorWord }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .initialSubordinatorWord }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .mixed }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .mixed }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .subordinatingSuffix }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .initialSubordinatorWord }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .finalSubordinatorWord }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .initialSubordinatorWord }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .subordinatingSuffix }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .finalSubordinatorWord }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .subordinatingSuffix }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .initialSubordinatorWord }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .mixed }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .initialSubordinatorWord }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .initialSubordinatorWord }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .initialSubordinatorWord }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .initialSubordinatorWord }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .initialSubordinatorWord }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .subordinatingSuffix }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .initialSubordinatorWord }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .initialSubordinatorWord }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .initialSubordinatorWord }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .initialSubordinatorWord }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .initialSubordinatorWord }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .subordinatingSuffix }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .mixed }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .initialSubordinatorWord }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .subordinatingSuffix }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .finalSubordinatorWord }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .mixed }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .subordinatingSuffix }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .finalSubordinatorWord }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .finalSubordinatorWord }
  , { walsCode := "kku", language := "Korku", iso := "kfq", value := .finalSubordinatorWord }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .initialSubordinatorWord }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .initialSubordinatorWord }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .initialSubordinatorWord }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .initialSubordinatorWord }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .initialSubordinatorWord }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .finalSubordinatorWord }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .initialSubordinatorWord }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .initialSubordinatorWord }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .subordinatingSuffix }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .initialSubordinatorWord }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .initialSubordinatorWord }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .initialSubordinatorWord }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .internalSubordinatorWord }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .finalSubordinatorWord }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .initialSubordinatorWord }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .subordinatingSuffix }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .initialSubordinatorWord }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .initialSubordinatorWord }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .mixed }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .finalSubordinatorWord }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .finalSubordinatorWord }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .finalSubordinatorWord }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .initialSubordinatorWord }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .initialSubordinatorWord }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .finalSubordinatorWord }
  , { walsCode := "lmb", language := "Lamba", iso := "lam", value := .initialSubordinatorWord }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .initialSubordinatorWord }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .initialSubordinatorWord }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .initialSubordinatorWord }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .mixed }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .initialSubordinatorWord }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .initialSubordinatorWord }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .initialSubordinatorWord }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .finalSubordinatorWord }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .finalSubordinatorWord }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .subordinatingSuffix }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .subordinatingSuffix }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .initialSubordinatorWord }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .initialSubordinatorWord }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .initialSubordinatorWord }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .initialSubordinatorWord }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .initialSubordinatorWord }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .initialSubordinatorWord }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .mixed }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .initialSubordinatorWord }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .initialSubordinatorWord }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .initialSubordinatorWord }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .internalSubordinatorWord }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .initialSubordinatorWord }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .mixed }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .finalSubordinatorWord }
  , { walsCode := "mag", language := "Magar", iso := "mgp", value := .initialSubordinatorWord }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .initialSubordinatorWord }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .mixed }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .initialSubordinatorWord }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .initialSubordinatorWord }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .initialSubordinatorWord }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .initialSubordinatorWord }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .initialSubordinatorWord }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .finalSubordinatorWord }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .subordinatingSuffix }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .initialSubordinatorWord }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .initialSubordinatorWord }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .initialSubordinatorWord }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .initialSubordinatorWord }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .finalSubordinatorWord }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .finalSubordinatorWord }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .initialSubordinatorWord }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .initialSubordinatorWord }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .mixed }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .initialSubordinatorWord }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .initialSubordinatorWord }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .subordinatingSuffix }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .initialSubordinatorWord }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .mixed }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .finalSubordinatorWord }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .subordinatingSuffix }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .initialSubordinatorWord }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .initialSubordinatorWord }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .initialSubordinatorWord }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .initialSubordinatorWord }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .initialSubordinatorWord }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .initialSubordinatorWord }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .initialSubordinatorWord }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .initialSubordinatorWord }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .initialSubordinatorWord }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .mixed }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .initialSubordinatorWord }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .mixed }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .initialSubordinatorWord }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .initialSubordinatorWord }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .initialSubordinatorWord }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .initialSubordinatorWord }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .subordinatingSuffix }
  , { walsCode := "mki", language := "Mikasuki", iso := "mik", value := .subordinatingSuffix }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .subordinatingSuffix }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .initialSubordinatorWord }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .initialSubordinatorWord }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .finalSubordinatorWord }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .initialSubordinatorWord }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .initialSubordinatorWord }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .initialSubordinatorWord }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .initialSubordinatorWord }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .initialSubordinatorWord }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .initialSubordinatorWord }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .finalSubordinatorWord }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .initialSubordinatorWord }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .initialSubordinatorWord }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .initialSubordinatorWord }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .initialSubordinatorWord }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .initialSubordinatorWord }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .initialSubordinatorWord }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .internalSubordinatorWord }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .initialSubordinatorWord }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .mixed }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .initialSubordinatorWord }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .mixed }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .mixed }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .mixed }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .initialSubordinatorWord }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .initialSubordinatorWord }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .initialSubordinatorWord }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .initialSubordinatorWord }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .initialSubordinatorWord }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .subordinatingSuffix }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .mixed }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .initialSubordinatorWord }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .initialSubordinatorWord }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .finalSubordinatorWord }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .finalSubordinatorWord }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .initialSubordinatorWord }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .mixed }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .initialSubordinatorWord }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .initialSubordinatorWord }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .initialSubordinatorWord }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .initialSubordinatorWord }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .initialSubordinatorWord }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .finalSubordinatorWord }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .mixed }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .mixed }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .mixed }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .initialSubordinatorWord }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .initialSubordinatorWord }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .initialSubordinatorWord }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .finalSubordinatorWord }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .mixed }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .initialSubordinatorWord }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .initialSubordinatorWord }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .initialSubordinatorWord }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .initialSubordinatorWord }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .initialSubordinatorWord }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .initialSubordinatorWord }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .initialSubordinatorWord }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .internalSubordinatorWord }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .initialSubordinatorWord }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .initialSubordinatorWord }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .initialSubordinatorWord }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .initialSubordinatorWord }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .subordinatingSuffix }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .subordinatingSuffix }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .initialSubordinatorWord }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .mixed }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .internalSubordinatorWord }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .initialSubordinatorWord }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .mixed }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .initialSubordinatorWord }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .initialSubordinatorWord }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .initialSubordinatorWord }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .initialSubordinatorWord }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .initialSubordinatorWord }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .finalSubordinatorWord }
  , { walsCode := "oss", language := "Ossetic", iso := "oss", value := .mixed }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .initialSubordinatorWord }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .initialSubordinatorWord }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .initialSubordinatorWord }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .initialSubordinatorWord }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .initialSubordinatorWord }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .initialSubordinatorWord }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .initialSubordinatorWord }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .initialSubordinatorWord }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .initialSubordinatorWord }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .initialSubordinatorWord }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .initialSubordinatorWord }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .initialSubordinatorWord }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .mixed }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .mixed }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .initialSubordinatorWord }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .initialSubordinatorWord }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .initialSubordinatorWord }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .initialSubordinatorWord }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .initialSubordinatorWord }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .subordinatingSuffix }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .subordinatingSuffix }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .initialSubordinatorWord }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .finalSubordinatorWord }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .subordinatingSuffix }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .initialSubordinatorWord }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .mixed }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .subordinatingSuffix }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .initialSubordinatorWord }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .mixed }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .initialSubordinatorWord }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .finalSubordinatorWord }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .subordinatingSuffix }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .finalSubordinatorWord }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .initialSubordinatorWord }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .initialSubordinatorWord }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .initialSubordinatorWord }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .initialSubordinatorWord }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .initialSubordinatorWord }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .mixed }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .mixed }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .initialSubordinatorWord }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .initialSubordinatorWord }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .initialSubordinatorWord }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .initialSubordinatorWord }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .initialSubordinatorWord }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .initialSubordinatorWord }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .initialSubordinatorWord }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .finalSubordinatorWord }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .mixed }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .initialSubordinatorWord }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .initialSubordinatorWord }
  , { walsCode := "sav", language := "Savi", iso := "sdg", value := .mixed }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .finalSubordinatorWord }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .mixed }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .finalSubordinatorWord }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .initialSubordinatorWord }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .finalSubordinatorWord }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .initialSubordinatorWord }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .mixed }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .finalSubordinatorWord }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .initialSubordinatorWord }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .subordinatingSuffix }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .finalSubordinatorWord }
  , { walsCode := "sim", language := "Simeulue", iso := "smr", value := .initialSubordinatorWord }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .mixed }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .mixed }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .initialSubordinatorWord }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .finalSubordinatorWord }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .finalSubordinatorWord }
  , { walsCode := "siu", language := "Siuslaw", iso := "sis", value := .initialSubordinatorWord }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .mixed }
  , { walsCode := "sod", language := "Soddo", iso := "gru", value := .mixed }
  , { walsCode := "som", language := "Somali", iso := "som", value := .initialSubordinatorWord }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .initialSubordinatorWord }
  , { walsCode := "srb", language := "Sorbian", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "tou", language := "Southern Toussian", iso := "wib", value := .initialSubordinatorWord }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .initialSubordinatorWord }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .initialSubordinatorWord }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .initialSubordinatorWord }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .initialSubordinatorWord }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .initialSubordinatorWord }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .initialSubordinatorWord }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .initialSubordinatorWord }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .initialSubordinatorWord }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .initialSubordinatorWord }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .initialSubordinatorWord }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .initialSubordinatorWord }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .initialSubordinatorWord }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .finalSubordinatorWord }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .initialSubordinatorWord }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .initialSubordinatorWord }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .subordinatingSuffix }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .initialSubordinatorWord }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .subordinatingSuffix }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .initialSubordinatorWord }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .subordinatingSuffix }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .finalSubordinatorWord }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .mixed }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .initialSubordinatorWord }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .mixed }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .mixed }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .initialSubordinatorWord }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .mixed }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .mixed }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .initialSubordinatorWord }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .mixed }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .initialSubordinatorWord }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .initialSubordinatorWord }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .initialSubordinatorWord }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .initialSubordinatorWord }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .initialSubordinatorWord }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .initialSubordinatorWord }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .initialSubordinatorWord }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .initialSubordinatorWord }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .initialSubordinatorWord }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .mixed }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .finalSubordinatorWord }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .initialSubordinatorWord }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .initialSubordinatorWord }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .mixed }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .finalSubordinatorWord }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .initialSubordinatorWord }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .initialSubordinatorWord }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .mixed }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .mixed }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .initialSubordinatorWord }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .finalSubordinatorWord }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .initialSubordinatorWord }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .initialSubordinatorWord }
  , { walsCode := "tlo", language := "Tobelo", iso := "tlb", value := .initialSubordinatorWord }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .initialSubordinatorWord }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .initialSubordinatorWord }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .initialSubordinatorWord }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .subordinatingSuffix }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .initialSubordinatorWord }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .initialSubordinatorWord }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .subordinatingSuffix }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .subordinatingSuffix }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .initialSubordinatorWord }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .mixed }
  , { walsCode := "tgh", language := "Tuareg (Ghat)", iso := "thv", value := .initialSubordinatorWord }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .mixed }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .finalSubordinatorWord }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .initialSubordinatorWord }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .subordinatingSuffix }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .initialSubordinatorWord }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .mixed }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .initialSubordinatorWord }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .initialSubordinatorWord }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .mixed }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .subordinatingSuffix }
  , { walsCode := "udi", language := "Udi", iso := "udi", value := .initialSubordinatorWord }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .finalSubordinatorWord }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .initialSubordinatorWord }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .initialSubordinatorWord }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .initialSubordinatorWord }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .finalSubordinatorWord }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .initialSubordinatorWord }
  , { walsCode := "uru", language := "Uru", iso := "ure", value := .subordinatingSuffix }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .finalSubordinatorWord }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .initialSubordinatorWord }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .initialSubordinatorWord }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .initialSubordinatorWord }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .initialSubordinatorWord }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .internalSubordinatorWord }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .initialSubordinatorWord }
  , { walsCode := "wbn", language := "Wambon", iso := "wms", value := .finalSubordinatorWord }
  , { walsCode := "wme", language := "Wambule", iso := "wme", value := .initialSubordinatorWord }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .mixed }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .initialSubordinatorWord }
  , { walsCode := "wau", language := "Waunana", iso := "noa", value := .mixed }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .finalSubordinatorWord }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .initialSubordinatorWord }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .initialSubordinatorWord }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .initialSubordinatorWord }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .initialSubordinatorWord }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .initialSubordinatorWord }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .subordinatingSuffix }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .initialSubordinatorWord }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .initialSubordinatorWord }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .initialSubordinatorWord }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .initialSubordinatorWord }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .mixed }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .mixed }
  , { walsCode := "yns", language := "Yansi", iso := "yns", value := .initialSubordinatorWord }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .initialSubordinatorWord }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .mixed }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .initialSubordinatorWord }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .subordinatingSuffix }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .initialSubordinatorWord }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .finalSubordinatorWord }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .finalSubordinatorWord }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .internalSubordinatorWord }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .subordinatingSuffix }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .initialSubordinatorWord }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .initialSubordinatorWord }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .mixed }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .mixed }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .initialSubordinatorWord }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .mixed }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .mixed }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .initialSubordinatorWord }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .initialSubordinatorWord }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .subordinatingSuffix }
  ]

/-- Complete WALS 94A dataset (659 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 659 := by native_decide

theorem count_initialSubordinatorWord :
    (allData.filter (·.value == .initialSubordinatorWord)).length = 398 := by native_decide
theorem count_finalSubordinatorWord :
    (allData.filter (·.value == .finalSubordinatorWord)).length = 96 := by native_decide
theorem count_internalSubordinatorWord :
    (allData.filter (·.value == .internalSubordinatorWord)).length = 8 := by native_decide
theorem count_subordinatingSuffix :
    (allData.filter (·.value == .subordinatingSuffix)).length = 64 := by native_decide
theorem count_mixed :
    (allData.filter (·.value == .mixed)).length = 93 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F94A
