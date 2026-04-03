import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 129A: Hand and Arm
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 129A`.

Chapter 129, 617 languages.
-/

namespace Core.WALS.F129A

/-- WALS 129A values. -/
inductive HandAndArm where
  | identical  -- Identical (228 languages)
  | different  -- Different (389 languages)
  deriving DecidableEq, Repr

private def allData_0 : List (Datapoint HandAndArm) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .identical }
  , { walsCode := "arx", language := "'Are'are", iso := "alu", value := .identical }
  , { walsCode := "abw", language := "Abenaki (Western)", iso := "abe", value := .different }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .different }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .different }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .different }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .different }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .different }
  , { walsCode := "afr", language := "Afrikaans", iso := "afr", value := .different }
  , { walsCode := "agr", language := "Aguaruna", iso := "agr", value := .different }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .different }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .identical }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .different }
  , { walsCode := "ale", language := "Aleut", iso := "ale", value := .different }
  , { walsCode := "alg", language := "Algonquin", iso := "alq", value := .different }
  , { walsCode := "atq", language := "Alutiiq", iso := "ems", value := .different }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .different }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .different }
  , { walsCode := "amk", language := "Amarakaeri", iso := "amr", value := .different }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .identical }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .different }
  , { walsCode := "agt", language := "Anguthimri", iso := "awg", value := .different }
  , { walsCode := "apc", language := "Apache (Chiricahua)", iso := "apm", value := .different }
  , { walsCode := "apj", language := "Apache (Jicarilla)", iso := "apj", value := .identical }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .identical }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .different }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .identical }
  , { walsCode := "akr", language := "Arikara", iso := "ari", value := .different }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .identical }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .identical }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .different }
  , { walsCode := "atk", language := "Atakapa", iso := "aqp", value := .different }
  , { walsCode := "ati", language := "Atikamekw", iso := "atj", value := .different }
  , { walsCode := "ats", language := "Atsugewi", iso := "atw", value := .different }
  , { walsCode := "awa", language := "Awa", iso := "awb", value := .identical }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .different }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .identical }
  , { walsCode := "ayn", language := "Aynu", iso := "aib", value := .identical }
  , { walsCode := "ayo", language := "Ayomán", iso := "", value := .different }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .identical }
  , { walsCode := "blj", language := "Baale", iso := "koe", value := .identical }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .different }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .identical }
  , { walsCode := "bpb", language := "Bahnar", iso := "bdq", value := .different }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .identical }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .different }
  , { walsCode := "bca", language := "Bandjalang (Casino)", iso := "bdy", value := .different }
  , { walsCode := "bwa", language := "Bandjalang (Waalubal)", iso := "bdy", value := .different }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .different }
  , { walsCode := "bnv", language := "Baniva", iso := "bvv", value := .different }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .different }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .different }
  , { walsCode := "mti", language := "Barí", iso := "mot", value := .different }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .different }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .identical }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .different }
  , { walsCode := "bnq", language := "Beng", iso := "nhb", value := .identical }
  , { walsCode := "beo", language := "Beothuk", iso := "bue", value := .different }
  , { walsCode := "bkl", language := "Bikol", iso := "bcl", value := .different }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .different }
  , { walsCode := "bkd", language := "Binukid", iso := "bkd", value := .different }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .identical }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .different }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .identical }
  , { walsCode := "bor", language := "Bora", iso := "boa", value := .different }
  , { walsCode := "brc", language := "Boruca", iso := "brn", value := .identical }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .different }
  , { walsCode := "bnb", language := "Bunuba", iso := "bck", value := .different }
  , { walsCode := "but", language := "Buriat", iso := "bxm", value := .different }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .different }
  , { walsCode := "cab", language := "Cabécar", iso := "cjp", value := .identical }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .different }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .identical }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .identical }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .different }
  , { walsCode := "cpa", language := "Campa Pajonal Asheninca", iso := "cjo", value := .different }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .different }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .different }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .different }
  , { walsCode := "cap", language := "Capanahua", iso := "kaq", value := .different }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .different }
  , { walsCode := "car", language := "Carib", iso := "car", value := .identical }
  , { walsCode := "crj", language := "Carijona", iso := "cbd", value := .different }
  , { walsCode := "crl", language := "Carolinian", iso := "cal", value := .identical }
  , { walsCode := "crq", language := "Carrier", iso := "crx", value := .different }
  , { walsCode := "cas", language := "Cashibo", iso := "cbr", value := .different }
  , { walsCode := "csh", language := "Cashinahua", iso := "cbs", value := .different }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .different }
  , { walsCode := "ctw", language := "Catawba", iso := "chc", value := .identical }
  , { walsCode := "cat", language := "Catio", iso := "cto", value := .different }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .different }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .identical }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .different }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .different }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .identical }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .identical }
  , { walsCode := "ctt", language := "Chatino (Tataltepec)", iso := "cta", value := .identical }
  , { walsCode := "chy", language := "Chayahuita", iso := "cbt", value := .different }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .identical }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .different }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .different }
  , { walsCode := "cyn", language := "Cheyenne", iso := "chy", value := .identical }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .identical }
  , { walsCode := "cec", language := "Chicomuceltec", iso := "cob", value := .different }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .different }
  , { walsCode := "cma", language := "Chimila", iso := "cbg", value := .different }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .different }
  , { walsCode := "csf", language := "Chinantec (San Felipe Usila)", iso := "cuc", value := .identical }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .different }
  , { walsCode := "cpw", language := "Chippewa (Red Lake and Pillager)", iso := "ciw", value := .different }
  , { walsCode := "cqt", language := "Chiquitano", iso := "cax", value := .different }
  , { walsCode := "crg", language := "Chiriguano", iso := "gui", value := .different }
  , { walsCode := "cch", language := "Chocho", iso := "coz", value := .identical }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .different }
  , { walsCode := "col", language := "Chol", iso := "ctu", value := .identical }
  , { walsCode := "cho", language := "Chontal (Highland)", iso := "chd", value := .identical }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .identical }
  , { walsCode := "crt", language := "Chorote", iso := "", value := .different }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .identical }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .identical }
  , { walsCode := "cin", language := "Chumash (Ineseño)", iso := "inz", value := .identical }
  , { walsCode := "cuu", language := "Chuukese", iso := "chk", value := .identical }
  , { walsCode := "cla", language := "Clallam", iso := "clm", value := .different }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .identical }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .identical }
  , { walsCode := "cog", language := "Cogui", iso := "kog", value := .different }
  , { walsCode := "clc", language := "Colac", iso := "", value := .different }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .different }
  , { walsCode := "cmc", language := "Comecrudo", iso := "xcm", value := .identical }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .identical }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .different }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .different }
  , { walsCode := "crk", language := "Creek", iso := "mus", value := .different }
  , { walsCode := "cro", language := "Crow", iso := "cro", value := .different }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .different }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .different }
  , { walsCode := "ctc", language := "Cuicatec", iso := "", value := .different }
  , { walsCode := "cut", language := "Cuitlatec", iso := "cuy", value := .different }
  , { walsCode := "cur", language := "Curripaco", iso := "kpc", value := .different }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .identical }
  , { walsCode := "dak", language := "Dakota", iso := "dak", value := .different }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .identical }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .different }
  , { walsCode := "dgx", language := "Degexit'an", iso := "ing", value := .different }
  , { walsCode := "des", language := "Desano", iso := "des", value := .different }
  , { walsCode := "dda", language := "Dhuwal (Dätiwuy)", iso := "duj", value := .different }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .identical }
  , { walsCode := "dig", language := "Digaro", iso := "mhu", value := .different }
  , { walsCode := "csk", language := "Diola-Kasa", iso := "csk", value := .identical }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .different }
  , { walsCode := "dja", language := "Djabugay", iso := "dyy", value := .different }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .different }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .different }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .different }
  , { walsCode := "dca", language := "Dumagat (Casiguran)", iso := "dgc", value := .identical }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .different }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .identical }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .identical }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .different }
  , { walsCode := "ena", language := "Enga", iso := "enq", value := .identical }
  , { walsCode := "eng", language := "English", iso := "eng", value := .different }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .different }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .identical }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .different }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .different }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .different }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .different }
  , { walsCode := "for", language := "Fore", iso := "for", value := .identical }
  , { walsCode := "fox", language := "Fox", iso := "sac", value := .different }
  , { walsCode := "fre", language := "French", iso := "fra", value := .different }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .identical }
  , { walsCode := "gad", language := "Gade", iso := "ged", value := .identical }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .different }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .identical }
  , { walsCode := "ger", language := "German", iso := "deu", value := .different }
  , { walsCode := "gid", language := "Gidabal", iso := "gih", value := .different }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .identical }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .different }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .different }
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
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .identical }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .different }
  , { walsCode := "gny", language := "Gunya", iso := "gyy", value := .different }
  , { walsCode := "grm", language := "Gurma", iso := "gux", value := .identical }
  , { walsCode := "guu", language := "Guugu Yimidhirr", iso := "kky", value := .different }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .identical }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .different }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .identical }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .identical }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .different }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .different }
  , { walsCode := "hil", language := "Hiligaynon", iso := "hil", value := .different }
  , { walsCode := "hmd", language := "Hmong Daw", iso := "mww", value := .different }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .identical }
  , { walsCode := "hmb", language := "Huambisa", iso := "hub", value := .different }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .different }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .different }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .identical }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .different }
  , { walsCode := "hmu", language := "Huitoto (Muinane)", iso := "hux", value := .different }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .different }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .different }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .different }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .different }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .identical }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .identical }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .different }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .identical }
  , { walsCode := "ill", language := "Illinois", iso := "mia", value := .different }
  , { walsCode := "ilo", language := "Ilocano", iso := "ilo", value := .identical }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .different }
  , { walsCode := "iql", language := "Inuktitut (Quebec-Labrador)", iso := "ike", value := .different }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .different }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .different }
  , { walsCode := "itw", language := "Itawis", iso := "itv", value := .identical }
  , { walsCode := "itz", language := "Itzaj", iso := "itz", value := .identical }
  , { walsCode := "ixc", language := "Ixcatec", iso := "ixc", value := .different }
  , { walsCode := "ixi", language := "Ixil", iso := "ixl", value := .identical }
  , { walsCode := "inu", language := "Iñupiaq", iso := "esi", value := .different }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .identical }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .identical }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .identical }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .different }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .identical }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .different }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .different }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .identical }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .different }
  , { walsCode := "klz", language := "Kalanga", iso := "kck", value := .different }
  , { walsCode := "kls", language := "Kalispel", iso := "fla", value := .different }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .identical }
  , { walsCode := "kgt", language := "Kangiryuarmiut", iso := "ikt", value := .different }
  , { walsCode := "kea", language := "Kanjobal (Eastern)", iso := "kjb", value := .identical }
  , { walsCode := "kwe", language := "Kanjobal (Western)", iso := "knj", value := .identical }
  , { walsCode := "kky", language := "Kankanay", iso := "kne", value := .identical }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .different }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .identical }
  , { walsCode := "kpn", language := "Kapingamarangi", iso := "kpg", value := .identical }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .different }
  , { walsCode := "jva", language := "Karajá", iso := "kpj", value := .different }
  , { walsCode := "kkw", language := "Karankawa", iso := "zkk", value := .different }
  , { walsCode := "kdg", language := "Karipuna (Panoan)", iso := "", value := .different }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .different }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .different }
  , { walsCode := "ktu", language := "Katu", iso := "", value := .different }
  , { walsCode := "kaq", language := "Kaurna", iso := "zku", value := .different }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .different }
  , { walsCode := "kaz", language := "Kazakh", iso := "kaz", value := .identical }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .different }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .different }
  , { walsCode := "khk", language := "Khakas", iso := "kjh", value := .identical }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .identical }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .identical }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .identical }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .identical }
  , { walsCode := "kic", language := "Kickapoo", iso := "kic", value := .different }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .identical }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .identical }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .different }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .identical }
  , { walsCode := "ktb", language := "Kituba", iso := "ktu", value := .identical }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .different }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .different }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .identical }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .different }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .identical }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .identical }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .identical }
  , { walsCode := "kyn", language := "Koyukon", iso := "koy", value := .different }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .identical }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .different }
  , { walsCode := "kuq", language := "Kumyk", iso := "kum", value := .identical }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .different }
  , { walsCode := "kth", language := "Kutchin", iso := "gwi", value := .different }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .different }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .identical }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .different }
  , { walsCode := "kat", language := "Kâte", iso := "kmg", value := .identical }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .different }
  , { walsCode := "lau", language := "Lau", iso := "llu", value := .identical }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .identical }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .identical }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .identical }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .different }
  , { walsCode := "lnw", language := "Lonwolwol", iso := "crc", value := .identical }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .identical }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .different }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .different }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .identical }
  , { walsCode := "mca", language := "Maca", iso := "mca", value := .different }
  , { walsCode := "mcg", language := "Macaguán", iso := "mbn", value := .different }
  , { walsCode := "mch", language := "Machiguenga", iso := "mcb", value := .different }
  , { walsCode := "mcn", language := "Macuna", iso := "myy", value := .different }
  , { walsCode := "mdm", language := "Madimadi", iso := "dmd", value := .different }
  , { walsCode := "mhc", language := "Mahican", iso := "xpq", value := .different }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .different }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .identical }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .different }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .identical }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .identical }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .different }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .different }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .identical }
  , { walsCode := "mwb", language := "Manobo (Western Bukidnon)", iso := "mbb", value := .identical }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .identical }
  , { walsCode := "mpy", language := "Mapoyo", iso := "mcg", value := .different }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .different }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .different }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .identical }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .different }
  , { walsCode := "msh", language := "Marshallese", iso := "mah", value := .identical }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .different }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .different }
  , { walsCode := "myr", language := "Matsés", iso := "mcf", value := .different }
  , { walsCode := "sum", language := "Mayangna", iso := "yan", value := .different }
  , { walsCode := "myo", language := "Mayo", iso := "mfy", value := .different }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .identical }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .different }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .different }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .identical }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .identical }
  , { walsCode := "mic", language := "Micmac", iso := "mic", value := .different }
  , { walsCode := "mid", language := "Midob", iso := "mei", value := .identical }
  , { walsCode := "mij", language := "Miju", iso := "mxj", value := .identical }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .different }
  , { walsCode := "mkb", language := "Miwok (Bodega)", iso := "csi", value := .different }
  , { walsCode := "mcs", language := "Miwok (Central Sierra)", iso := "csm", value := .different }
  , { walsCode := "mwl", language := "Miwok (Lake)", iso := "lmw", value := .different }
  , { walsCode := "mwn", language := "Miwok (Northern Sierra)", iso := "nsq", value := .different }
  , { walsCode := "mwp", language := "Miwok (Plains)", iso := "pmw", value := .different }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .different }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .different }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .identical }
  , { walsCode := "mxu", language := "Mixtec (Chayuco)", iso := "mih", value := .identical }
  , { walsCode := "mjc", language := "Mixtec (San Juan Colorado)", iso := "mjc", value := .different }
  , { walsCode := "mxg", language := "Mixtec (San Miguel el Grande)", iso := "mig", value := .identical }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .different }
  , { walsCode := "moc", language := "Moca", iso := "moy", value := .different }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .different }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .different }
  , { walsCode := "moh", language := "Mohawk", iso := "moh", value := .different }
  , { walsCode := "moj", language := "Mojave", iso := "mov", value := .identical }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .identical }
  , { walsCode := "mtg", language := "Montagnais", iso := "moe", value := .different }
  , { walsCode := "mop", language := "Mopan", iso := "mop", value := .identical }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .identical }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .different }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .different }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .identical }
  , { walsCode := "muu", language := "Mundurukú", iso := "myu", value := .different }
  , { walsCode := "mse", language := "Munsee", iso := "umu", value := .identical }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .identical }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .different }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .different }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .different }
  , { walsCode := "muy", language := "Muyuw", iso := "myw", value := .identical }
  , { walsCode := "nhu", language := "Nahuatl (Huauchinango)", iso := "ncj", value := .different }
  , { walsCode := "npa", language := "Nahuatl (Pajapan)", iso := "nhp", value := .identical }
  , { walsCode := "nsz", language := "Nahuatl (Sierra de Zacapoaxtla)", iso := "azz", value := .identical }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .identical }
  , { walsCode := "nhx", language := "Nahuatl (Xalitla)", iso := "ngu", value := .different }
  , { walsCode := "nnt", language := "Nanticoke", iso := "nnt", value := .different }
  , { walsCode := "nnm", language := "Nanumea", iso := "tvl", value := .identical }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .identical }
  , { walsCode := "nsk", language := "Naskapi", iso := "nsk", value := .different }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .different }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .different }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .different }
  , { walsCode := "nne", language := "Nengone", iso := "nen", value := .different }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .different }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .different }
  , { walsCode := "ntj", language := "Ngaanyatjarra", iso := "ntj", value := .different }
  , { walsCode := "ngj", language := "Ngadjumaja", iso := "nju", value := .different }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .different }
  , { walsCode := "nlu", language := "Ngarluma", iso := "nrl", value := .different }
  , { walsCode := "ngw", language := "Ngawun", iso := "nxn", value := .different }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .different }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .identical }
  , { walsCode := "nbr", language := "Ngäbere", iso := "gym", value := .different }
  , { walsCode := "nro", language := "Nharo", iso := "nhr", value := .different }
  , { walsCode := "nsn", language := "Nisenan", iso := "nsz", value := .different }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .identical }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .different }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .different }
  , { walsCode := "nog", language := "Noghay", iso := "nog", value := .identical }
  , { walsCode := "nom", language := "Nomatsiguenga", iso := "not", value := .identical }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .different }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .identical }
  , { walsCode := "nuk", language := "Nukak", iso := "mbr", value := .different }
  , { walsCode := "nkr", language := "Nukuoro", iso := "nkr", value := .identical }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .different }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .different }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .different }
  , { walsCode := "nym", language := "Nyamwezi", iso := "nym", value := .identical }
  , { walsCode := "nya", language := "Nyawaygi", iso := "nyt", value := .different }
  , { walsCode := "nju", language := "Nyungar", iso := "nys", value := .different }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .identical }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .different }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .identical }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .different }
  , { walsCode := "ojm", language := "Ojibwe (Minnesota)", iso := "ciw", value := .different }
  , { walsCode := "oka", language := "Okanagan", iso := "oka", value := .identical }
  , { walsCode := "olu", language := "Olutec", iso := "plo", value := .identical }
  , { walsCode := "oma", language := "Omagua", iso := "omg", value := .different }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .different }
  , { walsCode := "onn", language := "Onondaga", iso := "ono", value := .different }
  , { walsCode := "ore", language := "Orejón", iso := "ore", value := .identical }
  , { walsCode := "oko", language := "Oriya (Kotia)", iso := "ort", value := .identical }
  , { walsCode := "owc", language := "Oromo (West-Central)", iso := "gaz", value := .different }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .different }
  , { walsCode := "osm", language := "Otomí (Santiago Mexquititlan)", iso := "otq", value := .identical }
  , { walsCode := "pkn", language := "Paakantyi", iso := "drl", value := .different }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .identical }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .different }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .identical }
  , { walsCode := "pnn", language := "Pangasinan", iso := "pag", value := .different }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .different }
  , { walsCode := "pny", language := "Panyjima", iso := "pnw", value := .different }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .different }
  , { walsCode := "pem", language := "Pemon", iso := "aoc", value := .different }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .identical }
  , { walsCode := "ppc", language := "Piapoco", iso := "pio", value := .different }
  , { walsCode := "pia", language := "Piaroa", iso := "pid", value := .different }
  , { walsCode := "pin", language := "Pintupi", iso := "piu", value := .different }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .different }
  , { walsCode := "prt", language := "Piratapuyo", iso := "pir", value := .identical }
  , { walsCode := "pir", language := "Piro", iso := "pib", value := .different }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .different }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .different }
  , { walsCode := "pla", language := "Playero", iso := "gob", value := .different }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .identical }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .different }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .different }
  , { walsCode := "psj", language := "Popoloca (San Juan Atzingo)", iso := "poe", value := .different }
  , { walsCode := "psv", language := "Popoloca (San Vicente Coyotepec)", iso := "pbf", value := .different }
  , { walsCode := "zqs", language := "Popoluca (Sierra)", iso := "poi", value := .different }
  , { walsCode := "pcm", language := "Poqomam", iso := "poc", value := .different }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .different }
  , { walsCode := "pow", language := "Powhatan", iso := "pim", value := .different }
  , { walsCode := "pui", language := "Puinave", iso := "pui", value := .different }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .identical }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .identical }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .identical }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .different }
  , { walsCode := "qan", language := "Quechua (Ancash)", iso := "qxa", value := .different }
  , { walsCode := "qca", language := "Quechua (Cajamarca)", iso := "qvc", value := .different }
  , { walsCode := "qec", language := "Quechua (Ecuadorean)", iso := "qug", value := .different }
  , { walsCode := "qch", language := "Quiché", iso := "quc", value := .identical }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .identical }
  , { walsCode := "rad", language := "Rade", iso := "rad", value := .identical }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .identical }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .different }
  , { walsCode := "rng", language := "Rengao", iso := "ren", value := .identical }
  , { walsCode := "rnn", language := "Rennellese", iso := "mnv", value := .identical }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .different }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .different }
  , { walsCode := "rgn", language := "Roglai (Northern)", iso := "rog", value := .identical }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .different }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .identical }
  , { walsCode := "sno", language := "Saami (Northern)", iso := "sme", value := .identical }
  , { walsCode := "smt", language := "Sahaptin (Umatilla)", iso := "uma", value := .identical }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .different }
  , { walsCode := "sss", language := "Salish (Samish Straits)", iso := "str", value := .different }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .identical }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .identical }
  , { walsCode := "say", language := "Sayula Popoluca", iso := "pos", value := .identical }
  , { walsCode := "sec", language := "Secoya", iso := "sey", value := .different }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .identical }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .different }
  , { walsCode := "smj", language := "Semai", iso := "sea", value := .identical }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .different }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .identical }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .identical }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .different }
  , { walsCode := "shw", language := "Shawnee", iso := "sjw", value := .different }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .different }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .different }
  , { walsCode := "shn", language := "Shona", iso := "sna", value := .identical }
  , { walsCode := "sho", language := "Shoshone", iso := "shh", value := .different }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .identical }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .identical }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .identical }
  , { walsCode := "sri", language := "Siriano", iso := "sri", value := .different }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .different }
  , { walsCode := "slv", language := "Slavey", iso := "xsl", value := .different }
  , { walsCode := "svk", language := "Slovak", iso := "slk", value := .identical }
  , { walsCode := "sol", language := "Solon", iso := "evn", value := .identical }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .identical }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .different }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .different }
  , { walsCode := "spo", language := "Spokane", iso := "spo", value := .different }
  ]

private def allData_1 : List (Datapoint HandAndArm) :=
  [ { walsCode := "squ", language := "Squamish", iso := "squ", value := .identical }
  , { walsCode := "sus", language := "Susu", iso := "sus", value := .identical }
  , { walsCode := "sva", language := "Svan", iso := "sva", value := .different }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .identical }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .different }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .different }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .different }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .identical }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .identical }
  , { walsCode := "tnj", language := "Tanaina", iso := "tfn", value := .identical }
  , { walsCode := "tnl", language := "Tanana (Lower)", iso := "taa", value := .different }
  , { walsCode := "tga", language := "Tangga", iso := "hrc", value := .identical }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .different }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .identical }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .different }
  , { walsCode := "toy", language := "Tasmanian (Oyster Bay to Pitwater)", iso := "", value := .different }
  , { walsCode := "tvo", language := "Tatar", iso := "tat", value := .identical }
  , { walsCode := "tty", language := "Tatuyo", iso := "tav", value := .different }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .different }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .different }
  , { walsCode := "tlf", language := "Telefol", iso := "tlf", value := .different }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .different }
  , { walsCode := "tsj", language := "Tewa (San Juan Pueblo)", iso := "tew", value := .different }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .different }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .different }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .identical }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .different }
  , { walsCode := "tbe", language := "Tigré (Beni Amer)", iso := "tig", value := .identical }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .different }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .different }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .identical }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .identical }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .different }
  , { walsCode := "toj", language := "Tojolabal", iso := "toj", value := .identical }
  , { walsCode := "tpi", language := "Tok Pisin", iso := "tpi", value := .identical }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .different }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .different }
  , { walsCode := "tos", language := "Totonac (Sierra)", iso := "tos", value := .different }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .different }
  , { walsCode := "trc", language := "Trique (Chicahuaxtla)", iso := "trs", value := .different }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .identical }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .different }
  , { walsCode := "tsw", language := "Tswana", iso := "tsn", value := .different }
  , { walsCode := "tua", language := "Tuamotuan", iso := "pmt", value := .identical }
  , { walsCode := "tub", language := "Tubar", iso := "tbu", value := .different }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .identical }
  , { walsCode := "tnb", language := "Tunebo", iso := "tuf", value := .different }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .different }
  , { walsCode := "tup", language := "Tupi", iso := "tpn", value := .different }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .identical }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .different }
  , { walsCode := "tkm", language := "Turkmen", iso := "tuk", value := .identical }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .different }
  , { walsCode := "tut", language := "Tutchone (Northern)", iso := "ttm", value := .different }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .different }
  , { walsCode := "tze", language := "Tzeltal", iso := "tzh", value := .identical }
  , { walsCode := "tzt", language := "Tzeltal (Tenejapa)", iso := "tzh", value := .identical }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .identical }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .different }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .identical }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .identical }
  , { walsCode := "uhi", language := "Uradhi", iso := "urf", value := .different }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .different }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .different }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .identical }
  , { walsCode := "ved", language := "Vedda", iso := "ved", value := .identical }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .different }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .different }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .different }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .different }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .different }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .different }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .different }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .different }
  , { walsCode := "wat", language := "Watjarri", iso := "wbv", value := .different }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .different }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .different }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .different }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .different }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .different }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .different }
  , { walsCode := "wnb", language := "Winnebago", iso := "win", value := .different }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .different }
  , { walsCode := "wir", language := "Wirangu", iso := "wgu", value := .different }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .different }
  , { walsCode := "wwr", language := "Woiwurrung", iso := "wyi", value := .different }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .identical }
  , { walsCode := "xer", language := "Xerénte", iso := "xer", value := .different }
  , { walsCode := "xok", language := "Xokleng", iso := "xok", value := .different }
  , { walsCode := "xar", language := "Xârâcùù", iso := "ane", value := .different }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .identical }
  , { walsCode := "yah", language := "Yahgan", iso := "yag", value := .different }
  , { walsCode := "yak", language := "Yaka", iso := "yaf", value := .identical }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .different }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .identical }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .identical }
  , { walsCode := "yav", language := "Yavapai", iso := "yuf", value := .identical }
  , { walsCode := "yyg", language := "Yaygir", iso := "xya", value := .different }
  , { walsCode := "yir", language := "Yir Yoront", iso := "yyr", value := .different }
  , { walsCode := "yyo", language := "Yorta Yorta", iso := "xyy", value := .different }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .identical }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .different }
  , { walsCode := "yki", language := "Yuki", iso := "yuk", value := .different }
  , { walsCode := "ykp", language := "Yukpa", iso := "yup", value := .identical }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .different }
  , { walsCode := "ylb", language := "Yulparija", iso := "mpj", value := .identical }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .different }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .different }
  , { walsCode := "yrt", language := "Yuruti", iso := "yui", value := .different }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .identical }
  , { walsCode := "zaj", language := "Zapotec (Juárez)", iso := "zaa", value := .identical }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .different }
  , { walsCode := "zam", language := "Zapotec (Mixtepec)", iso := "zpm", value := .identical }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .identical }
  , { walsCode := "zfl", language := "Zoque (Francisco León)", iso := "zos", value := .identical }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .different }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .identical }
  ]

/-- Complete WALS 129A dataset (617 languages). -/
def allData : List (Datapoint HandAndArm) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 617 := by native_decide

theorem count_identical :
    (allData.filter (·.value == .identical)).length = 228 := by native_decide
theorem count_different :
    (allData.filter (·.value == .different)).length = 389 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F129A
