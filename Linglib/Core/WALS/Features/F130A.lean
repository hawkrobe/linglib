/-!
# WALS Feature 130A: Finger and Hand
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 130A`.

Chapter 130, 593 languages.
-/

namespace Core.WALS.F130A

/-- WALS 130A values. -/
inductive FingerAndHand where
  | identical  -- Identical (72 languages)
  | different  -- Different (521 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 130A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : FingerAndHand
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .different }
  , { walsCode := "arx", language := "'Are'are", iso := "alu", value := .different }
  , { walsCode := "abw", language := "Abenaki (Western)", iso := "abe", value := .different }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .different }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .different }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .different }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .different }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .different }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .different }
  , { walsCode := "agr", language := "Aguaruna", iso := "agr", value := .different }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .different }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .different }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .different }
  , { walsCode := "alg", language := "Algonquin", iso := "alq", value := .different }
  , { walsCode := "atq", language := "Alutiiq", iso := "ems", value := .different }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .identical }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .identical }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .different }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .different }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .different }
  , { walsCode := "apc", language := "Apache (Chiricahua)", iso := "apm", value := .different }
  , { walsCode := "apj", language := "Apache (Jicarilla)", iso := "apj", value := .different }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .identical }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .different }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .different }
  , { walsCode := "akr", language := "Arikara", iso := "ari", value := .different }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .different }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .different }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .identical }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .identical }
  , { walsCode := "ati", language := "Atikamekw", iso := "atj", value := .identical }
  , { walsCode := "ats", language := "Atsugewi", iso := "atw", value := .different }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .different }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .different }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .different }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .different }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .different }
  , { walsCode := "blj", language := "Baale", iso := "koe", value := .different }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .different }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .different }
  , { walsCode := "bpb", language := "Bahnar", iso := "bdq", value := .different }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .different }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .identical }
  , { walsCode := "bca", language := "Bandjalang (Casino)", iso := "bdy", value := .different }
  , { walsCode := "bwa", language := "Bandjalang (Waalubal)", iso := "bdy", value := .identical }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .identical }
  , { walsCode := "bnv", language := "Baniva", iso := "bvv", value := .different }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .different }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .different }
  , { walsCode := "mti", language := "Barí", iso := "mot", value := .different }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .different }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .different }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .different }
  , { walsCode := "bnq", language := "Beng", iso := "nhb", value := .different }
  , { walsCode := "beo", language := "Beothuk", iso := "bue", value := .identical }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .different }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .different }
  , { walsCode := "bkd", language := "Binukid", iso := "bkd", value := .different }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .different }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .different }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .different }
  , { walsCode := "bor", language := "Bora", iso := "boa", value := .different }
  , { walsCode := "brc", language := "Boruca", iso := "brn", value := .different }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .different }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .identical }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .different }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .different }
  , { walsCode := "cab", language := "Cabécar", iso := "cjp", value := .different }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .different }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .identical }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .different }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .different }
  , { walsCode := "cpa", language := "Campa Pajonal Asheninca", iso := "cjo", value := .different }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .different }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .different }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .different }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .different }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .different }
  , { walsCode := "car", language := "Carib", iso := "car", value := .different }
  , { walsCode := "crj", language := "Carijona", iso := "cbd", value := .identical }
  , { walsCode := "crl", language := "Carolinian", iso := "cal", value := .different }
  , { walsCode := "crq", language := "Carrier", iso := "crx", value := .different }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .different }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .different }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .different }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .different }
  , { walsCode := "cat", language := "Catio", iso := "cto", value := .different }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .different }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .different }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .different }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .different }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .different }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .different }
  , { walsCode := "ctt", language := "Chatino (Tataltepec)", iso := "cta", value := .different }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .identical }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .different }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .different }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .different }
  , { walsCode := "cyn", language := "Cheyenne", iso := "chy", value := .different }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .different }
  , { walsCode := "cec", language := "Chicomuceltec", iso := "cob", value := .different }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .different }
  , { walsCode := "cma", language := "Chimila", iso := "cbg", value := .different }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .different }
  , { walsCode := "csf", language := "Chinantec (San Felipe Usila)", iso := "cuc", value := .different }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .different }
  , { walsCode := "crg", language := "Chiriguano", iso := "gui", value := .different }
  , { walsCode := "cch", language := "Chocho", iso := "coz", value := .different }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .different }
  , { walsCode := "col", language := "Chol", iso := "ctu", value := .different }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .different }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .different }
  , { walsCode := "crt", language := "Chorote", iso := "", value := .different }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .different }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .different }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .different }
  , { walsCode := "cuu", language := "Chuukese", iso := "chk", value := .different }
  , { walsCode := "cla", language := "Clallam", iso := "clm", value := .different }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .identical }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .different }
  , { walsCode := "cog", language := "Cogui", iso := "kog", value := .different }
  , { walsCode := "clc", language := "Colac", iso := "", value := .different }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .different }
  , { walsCode := "cmc", language := "Comecrudo", iso := "xcm", value := .identical }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .different }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .different }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .different }
  , { walsCode := "crk", language := "Creek", iso := "mus", value := .different }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .different }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .different }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .different }
  , { walsCode := "ctc", language := "Cuicatec", iso := "", value := .different }
  , { walsCode := "cut", language := "Cuitlatec", iso := "cuy", value := .different }
  , { walsCode := "cur", language := "Curripaco", iso := "kpc", value := .different }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .different }
  , { walsCode := "dak", language := "Dakota", iso := "dak", value := .different }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .different }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .different }
  , { walsCode := "dgx", language := "Degexit'an", iso := "ing", value := .different }
  , { walsCode := "des", language := "Desano", iso := "des", value := .different }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .identical }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .different }
  , { walsCode := "csk", language := "Diola-Kasa", iso := "csk", value := .different }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .identical }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .different }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .identical }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .different }
  , { walsCode := "dca", language := "Dumagat (Casiguran)", iso := "dgc", value := .different }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .different }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .different }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .different }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .different }
  , { walsCode := "ena", language := "Enga", iso := "enq", value := .different }
  , { walsCode := "eng", language := "English", iso := "eng", value := .different }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .different }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .identical }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .different }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .different }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .different }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .different }
  , { walsCode := "for", language := "Fore", iso := "for", value := .different }
  , { walsCode := "fox", language := "Fox", iso := "sac", value := .different }
  , { walsCode := "fre", language := "French", iso := "fra", value := .different }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .different }
  , { walsCode := "gad", language := "Gade", iso := "ged", value := .different }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .different }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .different }
  , { walsCode := "ger", language := "German", iso := "deu", value := .different }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .different }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .different }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .different }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .different }
  , { walsCode := "gre", language := "Greenlandic (East)", iso := "kal", value := .different }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .different }
  , { walsCode := "gjj", language := "Guajajara", iso := "gub", value := .different }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .different }
  , { walsCode := "gna", language := "Guana", iso := "gva", value := .different }
  , { walsCode := "gno", language := "Guanano", iso := "gvc", value := .different }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .different }
  , { walsCode := "gto", language := "Guató", iso := "gta", value := .different }
  , { walsCode := "gyb", language := "Guayabero", iso := "guo", value := .different }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .different }
  , { walsCode := "grm", language := "Gurma", iso := "gux", value := .different }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .different }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .different }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .different }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .different }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .identical }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .different }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .different }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .different }
  , { walsCode := "hmd", language := "Hmong Daw", iso := "mww", value := .different }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .different }
  , { walsCode := "hmb", language := "Huambisa", iso := "hub", value := .different }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .different }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .different }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .different }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .different }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .different }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .different }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .different }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .different }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .identical }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .different }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .different }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .different }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .different }
  , { walsCode := "ill", language := "Illinois", iso := "mia", value := .different }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .different }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .different }
  , { walsCode := "iql", language := "Inuktitut (Quebec-Labrador)", iso := "ike", value := .different }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .different }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .different }
  , { walsCode := "itw", language := "Itawis", iso := "itv", value := .different }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .different }
  , { walsCode := "ixc", language := "Ixcatec", iso := "ixc", value := .different }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .different }
  , { walsCode := "inu", language := "Iñupiaq", iso := "esi", value := .identical }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .different }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .different }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .different }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .identical }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .different }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .different }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .different }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .different }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .different }
  , { walsCode := "klz", language := "Kalanga", iso := "kck", value := .different }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .identical }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .different }
  , { walsCode := "kgt", language := "Kangiryuarmiut", iso := "ikt", value := .different }
  , { walsCode := "kea", language := "Kanjobal (Eastern)", iso := "kjb", value := .different }
  , { walsCode := "kwe", language := "Kanjobal (Western)", iso := "knj", value := .different }
  , { walsCode := "kky", language := "Kankanay", iso := "kne", value := .different }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .different }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .different }
  , { walsCode := "kpn", language := "Kapingamarangi", iso := "kpg", value := .different }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .different }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .identical }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .identical }
  , { walsCode := "kdg", language := "Karipuna (Panoan)", iso := "", value := .different }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .identical }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .different }
  , { walsCode := "ktu", language := "Katu", iso := "", value := .different }
  , { walsCode := "kaq", language := "Kaurna", iso := "zku", value := .identical }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .different }
  , { walsCode := "kaz", language := "Kazakh", iso := "kaz", value := .different }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .identical }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .different }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .different }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .different }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .different }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .different }
  , { walsCode := "kic", language := "Kickapoo", iso := "kic", value := .different }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .different }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .different }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .different }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .different }
  , { walsCode := "ktb", language := "Kituba", iso := "ktu", value := .different }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .different }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .different }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .different }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .different }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .different }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .different }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .different }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .different }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .different }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .different }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .different }
  , { walsCode := "kuq", language := "Kumyk", iso := "kum", value := .different }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .different }
  , { walsCode := "kth", language := "Kutchin", iso := "gwi", value := .different }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .different }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .different }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .identical }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .different }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .different }
  , { walsCode := "lau", language := "Lau", iso := "llu", value := .different }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .different }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .different }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .different }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .different }
  , { walsCode := "lnw", language := "Lonwolwol", iso := "crc", value := .different }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .different }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .different }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .different }
  , { walsCode := "mcg", language := "Macaguán", iso := "mbn", value := .different }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .different }
  , { walsCode := "mcn", language := "Macuna", iso := "myy", value := .different }
  , { walsCode := "mhc", language := "Mahican", iso := "xpq", value := .different }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .different }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .different }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .different }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .different }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .different }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .different }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .different }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .different }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .different }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .different }
  , { walsCode := "mpy", language := "Mapoyo", iso := "mcg", value := .different }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .different }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .identical }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .different }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .different }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .different }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .different }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .different }
  , { walsCode := "sum", language := "Mayangna", iso := "yan", value := .different }
  , { walsCode := "myo", language := "Mayo", iso := "mfy", value := .different }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .different }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .different }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .different }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .different }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .different }
  , { walsCode := "mic", language := "Micmac", iso := "mic", value := .different }
  , { walsCode := "mid", language := "Midob", iso := "mei", value := .different }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .different }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .different }
  , { walsCode := "mkb", language := "Miwok (Bodega)", iso := "csi", value := .different }
  , { walsCode := "mcs", language := "Miwok (Central Sierra)", iso := "csm", value := .different }
  , { walsCode := "mwl", language := "Miwok (Lake)", iso := "lmw", value := .different }
  , { walsCode := "mwn", language := "Miwok (Northern Sierra)", iso := "nsq", value := .identical }
  , { walsCode := "mwp", language := "Miwok (Plains)", iso := "pmw", value := .identical }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .different }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .different }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .different }
  , { walsCode := "mxu", language := "Mixtec (Chayuco)", iso := "mih", value := .different }
  , { walsCode := "mjc", language := "Mixtec (San Juan Colorado)", iso := "mjc", value := .different }
  , { walsCode := "mxg", language := "Mixtec (San Miguel el Grande)", iso := "mig", value := .different }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .different }
  , { walsCode := "moc", language := "Moca", iso := "moy", value := .different }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .different }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .different }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .identical }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .different }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .different }
  , { walsCode := "mtg", language := "Montagnais", iso := "moe", value := .different }
  , { walsCode := "mop", language := "Mopan", iso := "mop", value := .different }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .different }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .different }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .different }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .different }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .identical }
  , { walsCode := "mse", language := "Munsee", iso := "umu", value := .different }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .different }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .identical }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .different }
  , { walsCode := "muy", language := "Muyuw", iso := "myw", value := .different }
  , { walsCode := "nhu", language := "Nahuatl (Huauchinango)", iso := "ncj", value := .different }
  , { walsCode := "npa", language := "Nahuatl (Pajapan)", iso := "nhp", value := .different }
  , { walsCode := "nsz", language := "Nahuatl (Sierra de Zacapoaxtla)", iso := "azz", value := .different }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .different }
  , { walsCode := "nhx", language := "Nahuatl (Xalitla)", iso := "ngu", value := .different }
  , { walsCode := "nnm", language := "Nanumea", iso := "tvl", value := .different }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .different }
  , { walsCode := "nsk", language := "Naskapi", iso := "nsk", value := .different }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .identical }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .identical }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .identical }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .different }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .different }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .identical }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .different }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .identical }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .different }
  , { walsCode := "nlu", language := "Ngarluma", iso := "nrl", value := .different }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .identical }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .identical }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .different }
  , { walsCode := "nro", language := "Nharo", iso := "nhr", value := .different }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .different }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .different }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .different }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .different }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .different }
  , { walsCode := "nom", language := "Nomatsiguenga", iso := "not", value := .different }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .different }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .different }
  , { walsCode := "nuk", language := "Nukak", iso := "mbr", value := .different }
  , { walsCode := "nkr", language := "Nukuoro", iso := "nkr", value := .different }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .different }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .identical }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .different }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .different }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .different }
  , { walsCode := "nju", language := "Nyungar", iso := "nys", value := .different }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .different }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .different }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .different }
  , { walsCode := "ojm", language := "Ojibwe (Minnesota)", iso := "ciw", value := .identical }
  , { walsCode := "oka", language := "Okanagan", iso := "oka", value := .different }
  , { walsCode := "olu", language := "Olutec", iso := "plo", value := .different }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .identical }
  , { walsCode := "onn", language := "Onondaga", iso := "ono", value := .identical }
  , { walsCode := "ore", language := "Orejón", iso := "ore", value := .different }
  , { walsCode := "oko", language := "Oriya (Kotia)", iso := "ort", value := .different }
  , { walsCode := "owc", language := "Oromo (West-Central)", iso := "gaz", value := .different }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .different }
  , { walsCode := "osm", language := "Otomí (Santiago Mexquititlan)", iso := "otq", value := .different }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .identical }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .identical }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .different }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .different }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .different }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .different }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .different }
  , { walsCode := "pem", language := "Pemon", iso := "aoc", value := .different }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .different }
  , { walsCode := "ppc", language := "Piapoco", iso := "pio", value := .different }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .different }
  , { walsCode := "pin", language := "Pintupi", iso := "piu", value := .identical }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .different }
  , { walsCode := "prt", language := "Piratapuyo", iso := "pir", value := .different }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .different }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .identical }
  , { walsCode := "pla", language := "Playero", iso := "gob", value := .different }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .different }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .different }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .different }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .different }
  , { walsCode := "psv", language := "Popoloca (San Vicente Coyotepec)", iso := "pbf", value := .different }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .different }
  , { walsCode := "pcm", language := "Poqomam", iso := "poc", value := .different }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .different }
  , { walsCode := "pow", language := "Powhatan", iso := "pim", value := .different }
  , { walsCode := "pui", language := "Puinave", iso := "pui", value := .different }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .different }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .different }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .different }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .different }
  , { walsCode := "qan", language := "Quechua (Ancash)", iso := "qxa", value := .different }
  , { walsCode := "qca", language := "Quechua (Cajamarca)", iso := "qvc", value := .different }
  , { walsCode := "qec", language := "Quechua (Ecuadorean)", iso := "qug", value := .different }
  , { walsCode := "qch", language := "Quiché", iso := "quc", value := .different }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .identical }
  , { walsCode := "rad", language := "Rade", iso := "rad", value := .different }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .different }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .different }
  , { walsCode := "rng", language := "Rengao", iso := "ren", value := .different }
  , { walsCode := "rnn", language := "Rennellese", iso := "mnv", value := .different }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .different }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .different }
  , { walsCode := "rgn", language := "Roglai (Northern)", iso := "rog", value := .different }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .different }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .different }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .different }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .different }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .different }
  , { walsCode := "sss", language := "Salish (Samish Straits)", iso := "str", value := .different }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .different }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .different }
  , { walsCode := "say", language := "Sayula Popoluca", iso := "pos", value := .different }
  , { walsCode := "sec", language := "Secoya", iso := "sey", value := .different }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .different }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .different }
  , { walsCode := "smj", language := "Semai", iso := "sea", value := .different }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .identical }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .different }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .identical }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .identical }
  , { walsCode := "shw", language := "Shawnee", iso := "sjw", value := .different }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .different }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .different }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .different }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .different }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .different }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .different }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .different }
  , { walsCode := "sri", language := "Siriano", iso := "sri", value := .different }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .different }
  , { walsCode := "slv", language := "Slavey", iso := "xsl", value := .different }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .different }
  , { walsCode := "sol", language := "Solon", iso := "evn", value := .different }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .different }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .different }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .different }
  , { walsCode := "spo", language := "Spokane", iso := "spo", value := .different }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .different }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .different }
  , { walsCode := "sva", language := "Svan", iso := "sva", value := .different }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .different }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .different }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .different }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .different }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .identical }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .different }
  , { walsCode := "tnj", language := "Tanaina", iso := "tfn", value := .different }
  , { walsCode := "tnl", language := "Tanana (Lower)", iso := "taa", value := .different }
  , { walsCode := "tga", language := "Tangga", iso := "hrc", value := .different }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .different }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .different }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .different }
  , { walsCode := "toy", language := "Tasmanian (Oyster Bay to Pitwater)", iso := "", value := .identical }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .different }
  , { walsCode := "tty", language := "Tatuyo", iso := "tav", value := .different }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .different }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .different }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .different }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "trb", language := "Teribe", iso := "tfr", value := .different }
  , { walsCode := "tsj", language := "Tewa (San Juan Pueblo)", iso := "tew", value := .different }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .different }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .identical }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .different }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .different }
  , { walsCode := "tbe", language := "Tigré (Beni Amer)", iso := "tig", value := .different }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .different }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .different }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .different }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .different }
  , { walsCode := "toj", language := "Tojolabal", iso := "toj", value := .different }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .different }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .different }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .different }
  , { walsCode := "tos", language := "Totonac (Sierra)", iso := "tos", value := .different }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .different }
  , { walsCode := "trc", language := "Trique (Chicahuaxtla)", iso := "trs", value := .different }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .different }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .different }
  , { walsCode := "tsw", language := "Tswana", iso := "tsn", value := .different }
  , { walsCode := "tua", language := "Tuamotuan", iso := "pmt", value := .identical }
  , { walsCode := "tub", language := "Tubar", iso := "tbu", value := .different }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .different }
  , { walsCode := "tnb", language := "Tunebo", iso := "tuf", value := .different }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .identical }
  , { walsCode := "tup", language := "Tupi", iso := "tpn", value := .different }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .different }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .different }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .different }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .different }
  , { walsCode := "tut", language := "Tutchone (Northern)", iso := "ttm", value := .different }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .different }
  , { walsCode := "tze", language := "Tzeltal", iso := "tzh", value := .different }
  , { walsCode := "tzt", language := "Tzeltal (Tenejapa)", iso := "tzh", value := .different }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .different }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .different }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .different }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .different }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .different }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .identical }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .different }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .different }
  , { walsCode := "ved", language := "Vedda", iso := "ved", value := .different }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .different }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .identical }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .different }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .different }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .different }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .identical }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .different }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .different }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .different }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .different }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .different }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .different }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .different }
  , { walsCode := "wnb", language := "Winnebago", iso := "win", value := .identical }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .identical }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .different }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .different }
  , { walsCode := "wwr", language := "Woiwurrung", iso := "wyi", value := .different }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .different }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .different }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .identical }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .different }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .identical }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .different }
  , { walsCode := "yak", language := "Yaka", iso := "yaf", value := .different }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .identical }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .different }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .different }
  , { walsCode := "yav", language := "Yavapai", iso := "yuf", value := .different }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .identical }
  , { walsCode := "yyo", language := "Yorta Yorta", iso := "xyy", value := .different }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .different }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .different }
  , { walsCode := "yki", language := "Yuki", iso := "yuk", value := .different }
  , { walsCode := "ykp", language := "Yukpa", iso := "yup", value := .identical }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .identical }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .different }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .different }
  , { walsCode := "yrt", language := "Yuruti", iso := "yui", value := .different }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .different }
  , { walsCode := "zaj", language := "Zapotec (Juárez)", iso := "zaa", value := .different }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .different }
  , { walsCode := "zam", language := "Zapotec (Mixtepec)", iso := "zpm", value := .different }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .different }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .different }
  , { walsCode := "zfl", language := "Zoque (Francisco León)", iso := "zos", value := .different }
  , { walsCode := "zqr", language := "Zoque (Rayon)", iso := "zor", value := .different }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .different }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .different }
  ]

/-- Complete WALS 130A dataset (593 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 593 := by native_decide

theorem count_identical :
    (allData.filter (·.value == .identical)).length = 72 := by native_decide
theorem count_different :
    (allData.filter (·.value == .different)).length = 521 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F130A
