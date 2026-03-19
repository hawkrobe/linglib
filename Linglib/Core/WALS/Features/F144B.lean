/-!
# WALS Feature 144B: Position of negative words relative to beginning and end of clause and with respect to adjacency to verb
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144B`.

Chapter 144, 609 languages.
-/

namespace Core.WALS.F144B

/-- WALS 144B values. -/
inductive PositionOfNegativeWordsRelativeToBeginningAndEndOfClauseAndWithRespectToAdjacencyToVerb where
  | beginningNotImmedPreverbal  -- Beginning, not immed preverbal (44 languages)
  | preverbalNotBeginningOrImmed  -- Preverbal, not beginning or immed (18 languages)
  | immedPreverbal  -- Immed preverbal (339 languages)
  | immedPostverbal  -- Immed postverbal (92 languages)
  | postverbalNotImmedOrEnd  -- Postverbal, not immed or end (1 languages)
  | endNotImmedPostverbal  -- End, not immed postverbal (115 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144B datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PositionOfNegativeWordsRelativeToBeginningAndEndOfClauseAndWithRespectToAdjacencyToVerb
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "ani", language := "//Ani", iso := "hnh", value := .immedPostverbal }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .immedPreverbal }
  , { walsCode := "aba", language := "Abau", iso := "aau", value := .immedPostverbal }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .immedPostverbal }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .immedPreverbal }
  , { walsCode := "adg", language := "Adang", iso := "adn", value := .immedPostverbal }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .endNotImmedPostverbal }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .immedPreverbal }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .immedPreverbal }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .immedPreverbal }
  , { walsCode := "aja", language := "Aja", iso := "aja", value := .endNotImmedPostverbal }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .immedPreverbal }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .immedPreverbal }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .immedPreverbal }
  , { walsCode := "als", language := "Alsea", iso := "aes", value := .immedPreverbal }
  , { walsCode := "aln", language := "Alune", iso := "alp", value := .endNotImmedPostverbal }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .endNotImmedPostverbal }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .immedPreverbal }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .immedPostverbal }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .endNotImmedPostverbal }
  , { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .immedPreverbal }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .immedPostverbal }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .immedPreverbal }
  , { walsCode := "ane", language := "Anêm", iso := "anz", value := .endNotImmedPostverbal }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .immedPreverbal }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .immedPreverbal }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .immedPreverbal }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .immedPreverbal }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .immedPreverbal }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .endNotImmedPostverbal }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .immedPreverbal }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .endNotImmedPostverbal }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .immedPreverbal }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .immedPostverbal }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .immedPreverbal }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .immedPostverbal }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .immedPreverbal }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .immedPreverbal }
  , { walsCode := "bac", language := "Bachamal", iso := "wdj", value := .beginningNotImmedPreverbal }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .endNotImmedPostverbal }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .endNotImmedPostverbal }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .immedPreverbal }
  , { walsCode := "bak", language := "Baka (in Cameroon)", iso := "bkc", value := .endNotImmedPostverbal }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .endNotImmedPostverbal }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .immedPreverbal }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "bnn", language := "Banoni", iso := "bcm", value := .immedPreverbal }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .immedPostverbal }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .immedPreverbal }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .endNotImmedPostverbal }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .immedPreverbal }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .immedPreverbal }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .immedPreverbal }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .immedPreverbal }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .immedPreverbal }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .immedPreverbal }
  , { walsCode := "bzi", language := "Bauzi", iso := "bvz", value := .immedPostverbal }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .immedPostverbal }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .immedPreverbal }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .immedPostverbal }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .immedPreverbal }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .immedPreverbal }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .immedPreverbal }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .immedPreverbal }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .endNotImmedPostverbal }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .immedPostverbal }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .immedPreverbal }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .immedPreverbal }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .immedPreverbal }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .endNotImmedPostverbal }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .immedPostverbal }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .endNotImmedPostverbal }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .endNotImmedPostverbal }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .immedPreverbal }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .endNotImmedPostverbal }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .beginningNotImmedPreverbal }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .immedPreverbal }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .endNotImmedPostverbal }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .immedPostverbal }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .immedPostverbal }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .immedPreverbal }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .immedPostverbal }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .immedPreverbal }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .immedPreverbal }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .endNotImmedPostverbal }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .immedPreverbal }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .immedPreverbal }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .immedPreverbal }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .immedPreverbal }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .immedPostverbal }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .immedPostverbal }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .immedPostverbal }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .immedPreverbal }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .immedPreverbal }
  , { walsCode := "ckl", language := "Chinook (Lower)", iso := "chh", value := .immedPreverbal }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .beginningNotImmedPreverbal }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .immedPostverbal }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .immedPreverbal }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .immedPreverbal }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .immedPreverbal }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .immedPreverbal }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .beginningNotImmedPreverbal }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .immedPreverbal }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .immedPreverbal }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .immedPreverbal }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .beginningNotImmedPreverbal }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .immedPreverbal }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .immedPreverbal }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .immedPreverbal }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .immedPreverbal }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .immedPostverbal }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .immedPreverbal }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .immedPostverbal }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .beginningNotImmedPreverbal }
  , { walsCode := "djn", language := "Djinang", iso := "dji", value := .beginningNotImmedPreverbal }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .immedPreverbal }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .immedPreverbal }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .immedPreverbal }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .endNotImmedPostverbal }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .immedPreverbal }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .immedPreverbal }
  , { walsCode := "dua", language := "Duala", iso := "dua", value := .immedPreverbal }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .endNotImmedPostverbal }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .immedPostverbal }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .immedPostverbal }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .immedPostverbal }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .endNotImmedPostverbal }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .immedPreverbal }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .immedPreverbal }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .endNotImmedPostverbal }
  , { walsCode := "eng", language := "English", iso := "eng", value := .immedPreverbal }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .immedPostverbal }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .immedPreverbal }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .immedPreverbal }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .immedPreverbal }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .immedPreverbal }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .immedPreverbal }
  , { walsCode := "fre", language := "French", iso := "fra", value := .immedPostverbal }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .immedPreverbal }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .endNotImmedPostverbal }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .immedPreverbal }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .immedPreverbal }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .immedPreverbal }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .immedPreverbal }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .beginningNotImmedPreverbal }
  , { walsCode := "gbs", language := "Gbaya (Southwest)", iso := "gso", value := .endNotImmedPostverbal }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .endNotImmedPostverbal }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .immedPreverbal }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .endNotImmedPostverbal }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .immedPreverbal }
  , { walsCode := "ger", language := "German", iso := "deu", value := .endNotImmedPostverbal }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .immedPreverbal }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .endNotImmedPostverbal }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .immedPreverbal }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .immedPreverbal }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .immedPreverbal }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .beginningNotImmedPreverbal }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .beginningNotImmedPreverbal }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .immedPreverbal }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .endNotImmedPostverbal }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .immedPreverbal }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .immedPreverbal }
  , { walsCode := "ggu", language := "Gureng Gureng", iso := "gnr", value := .beginningNotImmedPreverbal }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .immedPreverbal }
  , { walsCode := "gwo", language := "Gworok", iso := "kcg", value := .endNotImmedPostverbal }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .beginningNotImmedPreverbal }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .immedPreverbal }
  , { walsCode := "hlu", language := "Halkomelem (Upriver)", iso := "hur", value := .immedPreverbal }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .endNotImmedPostverbal }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .immedPreverbal }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .immedPreverbal }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .immedPreverbal }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .immedPreverbal }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .immedPreverbal }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .immedPreverbal }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .immedPreverbal }
  , { walsCode := "lic", language := "Hlai (Baoding)", iso := "lic", value := .immedPreverbal }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .immedPostverbal }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .immedPreverbal }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .immedPreverbal }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .immedPreverbal }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .immedPostverbal }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .immedPreverbal }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .immedPreverbal }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .immedPreverbal }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .immedPostverbal }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .immedPreverbal }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .immedPostverbal }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .immedPreverbal }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .immedPostverbal }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .immedPreverbal }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .endNotImmedPostverbal }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .immedPreverbal }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .immedPostverbal }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .immedPreverbal }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .immedPreverbal }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .endNotImmedPostverbal }
  , { walsCode := "inn", language := "Innamincka", iso := "ynd", value := .beginningNotImmedPreverbal }
  , { walsCode := "iqu", language := "Iquito", iso := "iqu", value := .beginningNotImmedPreverbal }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .endNotImmedPostverbal }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .immedPreverbal }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .immedPreverbal }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .immedPostverbal }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .endNotImmedPostverbal }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .endNotImmedPostverbal }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .immedPreverbal }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .endNotImmedPostverbal }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .immedPreverbal }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .endNotImmedPostverbal }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .endNotImmedPostverbal }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .immedPreverbal }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .immedPreverbal }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .immedPostverbal }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .immedPostverbal }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .immedPreverbal }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .immedPostverbal }
  , { walsCode := "kmw", language := "Kamu", iso := "xmu", value := .immedPreverbal }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .immedPreverbal }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .endNotImmedPostverbal }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .immedPostverbal }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .endNotImmedPostverbal }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .endNotImmedPostverbal }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .immedPreverbal }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .immedPostverbal }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .immedPostverbal }
  , { walsCode := "ksn", language := "Kasong", iso := "cog", value := .immedPreverbal }
  , { walsCode := "kti", language := "Kati (in West Papua, Indonesia)", iso := "kts", value := .immedPostverbal }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .endNotImmedPostverbal }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .immedPostverbal }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .endNotImmedPostverbal }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .endNotImmedPostverbal }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .endNotImmedPostverbal }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .immedPreverbal }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .immedPreverbal }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .immedPreverbal }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .immedPreverbal }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .immedPostverbal }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .immedPostverbal }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .immedPreverbal }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .beginningNotImmedPreverbal }
  , { walsCode := "kie", language := "Kire", iso := "geb", value := .immedPostverbal }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .immedPreverbal }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .immedPreverbal }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .endNotImmedPostverbal }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .beginningNotImmedPreverbal }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "shp", language := "Klikitat", iso := "yak", value := .immedPreverbal }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .immedPreverbal }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .immedPostverbal }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .immedPreverbal }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .immedPreverbal }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .immedPreverbal }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .endNotImmedPostverbal }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .immedPreverbal }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .immedPostverbal }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .immedPreverbal }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .immedPreverbal }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .immedPreverbal }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .immedPreverbal }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .endNotImmedPostverbal }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .immedPreverbal }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .immedPreverbal }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .immedPreverbal }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .immedPreverbal }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .immedPreverbal }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .immedPostverbal }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .immedPreverbal }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .endNotImmedPostverbal }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .endNotImmedPostverbal }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .endNotImmedPostverbal }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .immedPreverbal }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .immedPostverbal }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .immedPostverbal }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .endNotImmedPostverbal }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .endNotImmedPostverbal }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .immedPostverbal }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .immedPreverbal }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .immedPreverbal }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .immedPostverbal }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .endNotImmedPostverbal }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .immedPostverbal }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .immedPostverbal }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .endNotImmedPostverbal }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .endNotImmedPostverbal }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .immedPreverbal }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .endNotImmedPostverbal }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .immedPreverbal }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .endNotImmedPostverbal }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .endNotImmedPostverbal }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .beginningNotImmedPreverbal }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .endNotImmedPostverbal }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .endNotImmedPostverbal }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .endNotImmedPostverbal }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .endNotImmedPostverbal }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .endNotImmedPostverbal }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .immedPreverbal }
  , { walsCode := "mcd", language := "Macedonian", iso := "mkd", value := .immedPreverbal }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .immedPreverbal }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .immedPostverbal }
  , { walsCode := "mda", language := "Mada (in Cameroon)", iso := "mxu", value := .endNotImmedPostverbal }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .immedPreverbal }
  , { walsCode := "mgi", language := "Magi", iso := "mgu", value := .immedPreverbal }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .immedPreverbal }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .beginningNotImmedPreverbal }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .immedPreverbal }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .immedPreverbal }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .immedPreverbal }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .endNotImmedPostverbal }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .immedPreverbal }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .immedPreverbal }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .immedPreverbal }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .immedPreverbal }
  , { walsCode := "mkg", language := "Mandinka (Gambian)", iso := "mnk", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .endNotImmedPostverbal }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .immedPreverbal }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .immedPreverbal }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .immedPreverbal }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .immedPreverbal }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .beginningNotImmedPreverbal }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .beginningNotImmedPreverbal }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .immedPostverbal }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .beginningNotImmedPreverbal }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .endNotImmedPostverbal }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .beginningNotImmedPreverbal }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .immedPreverbal }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .immedPreverbal }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .endNotImmedPostverbal }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .immedPreverbal }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .endNotImmedPostverbal }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .endNotImmedPostverbal }
  , { walsCode := "mhu", language := "Mbalanhu", iso := "lnb", value := .immedPreverbal }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .endNotImmedPostverbal }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .endNotImmedPostverbal }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .immedPostverbal }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .endNotImmedPostverbal }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .immedPostverbal }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .endNotImmedPostverbal }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .endNotImmedPostverbal }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .immedPostverbal }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .endNotImmedPostverbal }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .endNotImmedPostverbal }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .immedPreverbal }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .immedPreverbal }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .immedPreverbal }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .immedPreverbal }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .immedPostverbal }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .immedPreverbal }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .immedPreverbal }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .immedPostverbal }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .beginningNotImmedPreverbal }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .endNotImmedPostverbal }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .immedPreverbal }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .endNotImmedPostverbal }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .immedPreverbal }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .endNotImmedPostverbal }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .endNotImmedPostverbal }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .immedPreverbal }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .endNotImmedPostverbal }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .immedPreverbal }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .endNotImmedPostverbal }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .endNotImmedPostverbal }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .immedPreverbal }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .immedPreverbal }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .immedPreverbal }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .beginningNotImmedPreverbal }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .endNotImmedPostverbal }
  , { walsCode := "msq", language := "Musqueam", iso := "hur", value := .immedPreverbal }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .immedPreverbal }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .immedPreverbal }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .immedPreverbal }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .immedPreverbal }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .immedPreverbal }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .beginningNotImmedPreverbal }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .immedPostverbal }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .immedPostverbal }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .immedPreverbal }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .immedPreverbal }
  , { walsCode := "nak", language := "Nakanai", iso := "nak", value := .immedPreverbal }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .immedPreverbal }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .immedPostverbal }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .immedPostverbal }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .immedPreverbal }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .immedPostverbal }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .immedPreverbal }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .beginningNotImmedPreverbal }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .endNotImmedPostverbal }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .immedPreverbal }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .immedPreverbal }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .immedPreverbal }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .immedPreverbal }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .immedPreverbal }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .beginningNotImmedPreverbal }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .endNotImmedPostverbal }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .immedPreverbal }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .beginningNotImmedPreverbal }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .endNotImmedPostverbal }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .beginningNotImmedPreverbal }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .endNotImmedPostverbal }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .immedPostverbal }
  , { walsCode := "ngu", language := "Nguna", iso := "llp", value := .immedPreverbal }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .immedPreverbal }
  , { walsCode := "nca", language := "Nicobarese (Car)", iso := "caq", value := .immedPreverbal }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .immedPreverbal }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .immedPreverbal }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .immedPreverbal }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .immedPreverbal }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .immedPostverbal }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .endNotImmedPostverbal }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .beginningNotImmedPreverbal }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .immedPreverbal }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .immedPreverbal }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .endNotImmedPostverbal }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .immedPreverbal }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .endNotImmedPostverbal }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .immedPreverbal }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .immedPreverbal }
  , { walsCode := "oks", language := "Oksapmin", iso := "opm", value := .immedPreverbal }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .endNotImmedPostverbal }
  , { walsCode := "one", language := "One", iso := "aun", value := .endNotImmedPostverbal }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .immedPreverbal }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .immedPostverbal }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .immedPostverbal }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .immedPreverbal }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .endNotImmedPostverbal }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .beginningNotImmedPreverbal }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .beginningNotImmedPreverbal }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .immedPreverbal }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .immedPreverbal }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .immedPreverbal }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .immedPreverbal }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .immedPreverbal }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .endNotImmedPostverbal }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .immedPreverbal }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .immedPostverbal }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .immedPreverbal }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .endNotImmedPostverbal }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .immedPreverbal }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .immedPreverbal }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .immedPreverbal }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .immedPreverbal }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .immedPreverbal }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .immedPreverbal }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .immedPostverbal }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .immedPreverbal }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .immedPreverbal }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .immedPreverbal }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .beginningNotImmedPreverbal }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .immedPreverbal }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .endNotImmedPostverbal }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .immedPreverbal }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .immedPreverbal }
  , { walsCode := "cos", language := "Rumsien", iso := "", value := .immedPreverbal }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .immedPreverbal }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .immedPreverbal }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .endNotImmedPostverbal }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .immedPreverbal }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .immedPostverbal }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .immedPreverbal }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .immedPreverbal }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .immedPreverbal }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .immedPreverbal }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .immedPostverbal }
  , { walsCode := "sme", language := "Seme", iso := "sif", value := .immedPostverbal }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .immedPreverbal }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .endNotImmedPostverbal }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .immedPostverbal }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .endNotImmedPostverbal }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .immedPreverbal }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .immedPreverbal }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .immedPostverbal }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .immedPreverbal }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .immedPreverbal }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .immedPreverbal }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .immedPostverbal }
  , { walsCode := "sil", language := "Sila", iso := "dau", value := .immedPreverbal }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .immedPreverbal }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .endNotImmedPostverbal }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .immedPreverbal }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .immedPostverbal }
  , { walsCode := "ssa", language := "Sisaala", iso := "sil", value := .immedPreverbal }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .immedPreverbal }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .immedPostverbal }
  , { walsCode := "slo", language := "Slovene", iso := "slv", value := .immedPreverbal }
  , { walsCode := "so", language := "So", iso := "teu", value := .immedPreverbal }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .immedPreverbal }
  , { walsCode := "som", language := "Somali", iso := "som", value := .immedPreverbal }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .immedPreverbal }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .endNotImmedPostverbal }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .immedPreverbal }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "squ", language := "Squamish", iso := "squ", value := .immedPreverbal }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .immedPreverbal }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .immedPreverbal }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .immedPreverbal }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .immedPostverbal }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .endNotImmedPostverbal }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .immedPostverbal }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .immedPreverbal }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .immedPreverbal }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .immedPreverbal }
  , { walsCode := "trr", language := "Tairora", iso := "tbg", value := .beginningNotImmedPreverbal }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .immedPreverbal }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .immedPreverbal }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .immedPreverbal }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .immedPreverbal }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .immedPreverbal }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .immedPreverbal }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .immedPreverbal }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .beginningNotImmedPreverbal }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .immedPreverbal }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .beginningNotImmedPreverbal }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .immedPreverbal }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .immedPreverbal }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .endNotImmedPostverbal }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .immedPostverbal }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .beginningNotImmedPreverbal }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .immedPreverbal }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .immedPreverbal }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .immedPreverbal }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .immedPreverbal }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .endNotImmedPostverbal }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .immedPreverbal }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .immedPostverbal }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .immedPreverbal }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .immedPreverbal }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .immedPreverbal }
  , { walsCode := "tiv", language := "Tiv", iso := "tiv", value := .endNotImmedPostverbal }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .immedPreverbal }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .immedPreverbal }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .immedPreverbal }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .immedPreverbal }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .immedPreverbal }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .immedPreverbal }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .immedPostverbal }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .immedPostverbal }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .immedPreverbal }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .immedPreverbal }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "tpr", language := "Tupuri", iso := "tui", value := .endNotImmedPostverbal }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .immedPreverbal }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .immedPreverbal }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .immedPreverbal }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .immedPreverbal }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .immedPreverbal }
  , { walsCode := "udm", language := "Udmurt", iso := "udm", value := .immedPostverbal }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .immedPreverbal }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .endNotImmedPostverbal }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .immedPreverbal }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .immedPreverbal }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .immedPreverbal }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .immedPreverbal }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .immedPreverbal }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .immedPreverbal }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .immedPostverbal }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .immedPreverbal }
  , { walsCode := "vai", language := "Vai", iso := "vai", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .immedPreverbal }
  , { walsCode := "wag", language := "Wagiman", iso := "waq", value := .immedPreverbal }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .immedPreverbal }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .immedPreverbal }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .beginningNotImmedPreverbal }
  , { walsCode := "wna", language := "Wan", iso := "wan", value := .immedPostverbal }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .immedPreverbal }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .immedPreverbal }
  , { walsCode := "wrm", language := "Warembori", iso := "wsa", value := .endNotImmedPostverbal }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .immedPreverbal }
  , { walsCode := "wlw", language := "Warluwara", iso := "wrb", value := .beginningNotImmedPreverbal }
  , { walsCode := "wrb", language := "Warrnambool", iso := "gjm", value := .immedPreverbal }
  , { walsCode := "wsk", language := "Waskia", iso := "wsk", value := .immedPreverbal }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .immedPreverbal }
  , { walsCode := "wec", language := "Welsh (Colloquial)", iso := "cym", value := .postverbalNotImmedOrEnd }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .immedPreverbal }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .endNotImmedPostverbal }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .beginningNotImmedPreverbal }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .immedPreverbal }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .immedPreverbal }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .immedPreverbal }
  , { walsCode := "wom", language := "Womo", iso := "wmx", value := .immedPostverbal }
  , { walsCode := "wya", language := "Wyandot", iso := "wya", value := .immedPreverbal }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .immedPreverbal }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .immedPreverbal }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .immedPreverbal }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .preverbalNotBeginningOrImmed }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .immedPreverbal }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .immedPreverbal }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .immedPreverbal }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .immedPreverbal }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .immedPreverbal }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .beginningNotImmedPreverbal }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .immedPostverbal }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .immedPreverbal }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .beginningNotImmedPreverbal }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .beginningNotImmedPreverbal }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .immedPreverbal }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .immedPreverbal }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .immedPreverbal }
  , { walsCode := "zqo", language := "Zoque (Ostuacan)", iso := "zoc", value := .immedPreverbal }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .beginningNotImmedPreverbal }
  ]

/-- Complete WALS 144B dataset (609 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 609 := by native_decide

theorem count_beginningNotImmedPreverbal :
    (allData.filter (·.value == .beginningNotImmedPreverbal)).length = 44 := by native_decide
theorem count_preverbalNotBeginningOrImmed :
    (allData.filter (·.value == .preverbalNotBeginningOrImmed)).length = 18 := by native_decide
theorem count_immedPreverbal :
    (allData.filter (·.value == .immedPreverbal)).length = 339 := by native_decide
theorem count_immedPostverbal :
    (allData.filter (·.value == .immedPostverbal)).length = 92 := by native_decide
theorem count_postverbalNotImmedOrEnd :
    (allData.filter (·.value == .postverbalNotImmedOrEnd)).length = 1 := by native_decide
theorem count_endNotImmedPostverbal :
    (allData.filter (·.value == .endNotImmedPostverbal)).length = 115 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144B
