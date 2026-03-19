import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 3A: Consonant-Vowel Ratio
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 3A`.

Chapter 3, 564 languages.
-/

namespace Core.WALS.F3A

/-- WALS 3A values. -/
inductive ConsonantVowelRatio where
  | low  -- Low (58 languages)
  | moderatelyLow  -- Moderately low (101 languages)
  | average  -- Average (234 languages)
  | moderatelyHigh  -- Moderately high (102 languages)
  | high  -- High (69 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint ConsonantVowelRatio) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .high }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .high }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .average }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .high }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .average }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .moderatelyLow }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .high }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .moderatelyHigh }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .moderatelyLow }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .moderatelyHigh }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .average }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .moderatelyLow }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .moderatelyLow }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .moderatelyLow }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .low }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .moderatelyHigh }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .moderatelyLow }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .moderatelyHigh }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .average }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .high }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .average }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .average }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .average }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .moderatelyHigh }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .moderatelyLow }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .high }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .average }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .low }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .low }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .moderatelyHigh }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .moderatelyLow }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .low }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .average }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .moderatelyLow }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .moderatelyHigh }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .moderatelyHigh }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .moderatelyLow }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .high }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .moderatelyHigh }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .high }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .low }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .average }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .high }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .average }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .average }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .high }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .moderatelyLow }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .average }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .low }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .average }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .moderatelyLow }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .average }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .average }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .average }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .moderatelyLow }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .average }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .moderatelyHigh }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .moderatelyLow }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .average }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .moderatelyHigh }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .average }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .average }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .high }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .average }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .high }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .moderatelyHigh }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .average }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .average }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .average }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .moderatelyLow }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .low }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .moderatelyHigh }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .average }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .average }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .average }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .low }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .average }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .average }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .average }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .high }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .low }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .moderatelyLow }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .high }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .moderatelyHigh }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .moderatelyHigh }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .average }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .low }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .moderatelyLow }
  , { walsCode := "car", language := "Carib", iso := "car", value := .moderatelyLow }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .average }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .moderatelyHigh }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .moderatelyLow }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .moderatelyLow }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .average }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .average }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .high }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .low }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .moderatelyHigh }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .average }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .average }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .average }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .high }
  , { walsCode := "cve", language := "Chuave", iso := "cjv", value := .moderatelyLow }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .moderatelyLow }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .moderatelyLow }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .average }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .moderatelyHigh }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .moderatelyHigh }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .low }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .high }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .moderatelyLow }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .low }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .moderatelyLow }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .moderatelyLow }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .moderatelyHigh }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .average }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .high }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .average }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .low }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .average }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .low }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .moderatelyHigh }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .high }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .moderatelyHigh }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .average }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .low }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .high }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .average }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .high }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .moderatelyLow }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .average }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .average }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .average }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .low }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .average }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .low }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .average }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .low }
  , { walsCode := "eng", language := "English", iso := "eng", value := .low }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .moderatelyLow }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .average }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .average }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .average }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .average }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .high }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .moderatelyLow }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .moderatelyLow }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .average }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .moderatelyLow }
  , { walsCode := "fre", language := "French", iso := "fra", value := .low }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .average }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .moderatelyLow }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .moderatelyLow }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .high }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .average }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .average }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .moderatelyHigh }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .average }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .average }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .moderatelyHigh }
  , { walsCode := "ger", language := "German", iso := "deu", value := .low }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .average }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .moderatelyHigh }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .average }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .moderatelyLow }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .average }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .moderatelyHigh }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .average }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .average }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .average }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .average }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .average }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .high }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .high }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .average }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .moderatelyHigh }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .low }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .moderatelyHigh }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .low }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .average }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .moderatelyHigh }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .average }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .high }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .average }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .average }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .average }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .moderatelyLow }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .average }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .average }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .high }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .average }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .average }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .average }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .moderatelyHigh }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .moderatelyLow }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .average }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .moderatelyLow }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .low }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .average }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .average }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .high }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .average }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .high }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .low }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .moderatelyHigh }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .average }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .moderatelyHigh }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .average }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .moderatelyHigh }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .low }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .moderatelyHigh }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .average }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .low }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .high }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .moderatelyLow }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .moderatelyHigh }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .average }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .moderatelyHigh }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .average }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .low }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .high }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .average }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .high }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .average }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .low }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .average }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .moderatelyHigh }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .high }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .average }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .moderatelyLow }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .average }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .average }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .average }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .average }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .average }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .low }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .moderatelyHigh }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .moderatelyLow }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .average }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .average }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .moderatelyLow }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .average }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .moderatelyLow }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .average }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .moderatelyHigh }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .average }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .moderatelyLow }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .moderatelyLow }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .average }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .average }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .average }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .low }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .moderatelyLow }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .moderatelyLow }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .high }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .low }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .moderatelyHigh }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .moderatelyLow }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .average }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .moderatelyLow }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .average }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .average }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .moderatelyLow }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .moderatelyLow }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .low }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .average }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .moderatelyHigh }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .average }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .average }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .average }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .average }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .moderatelyHigh }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .average }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .moderatelyLow }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .average }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .moderatelyHigh }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .moderatelyLow }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .average }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .average }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .average }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .average }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .high }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .average }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .high }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .average }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .high }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .average }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .high }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .moderatelyHigh }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .moderatelyHigh }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .moderatelyHigh }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .low }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .average }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .average }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .average }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .moderatelyLow }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .average }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .high }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .moderatelyHigh }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .average }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .average }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .average }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .average }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .high }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .average }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .average }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .moderatelyLow }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .average }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .moderatelyLow }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .average }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .average }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .high }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .high }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .average }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .moderatelyLow }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .average }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .average }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .average }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .moderatelyHigh }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .low }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .average }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .average }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .moderatelyLow }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .high }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .average }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .moderatelyHigh }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .average }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .high }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .average }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .low }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .moderatelyLow }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .high }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .average }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .average }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .moderatelyHigh }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .average }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .moderatelyHigh }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .average }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .moderatelyLow }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .low }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .average }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .average }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .moderatelyHigh }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .average }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .average }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .average }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .average }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .average }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .moderatelyHigh }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .moderatelyLow }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .moderatelyHigh }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .average }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .average }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .moderatelyHigh }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .moderatelyHigh }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .average }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .moderatelyLow }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .low }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .average }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .low }
  , { walsCode := "nbk", language := "Natügu", iso := "ntu", value := .average }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .high }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .average }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .average }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .average }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .moderatelyHigh }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .moderatelyHigh }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .moderatelyHigh }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .moderatelyHigh }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .moderatelyHigh }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .moderatelyLow }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .moderatelyHigh }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .moderatelyHigh }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .high }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .low }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .moderatelyHigh }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .moderatelyHigh }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .average }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .average }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .moderatelyLow }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .moderatelyLow }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .average }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .moderatelyHigh }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .high }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .average }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .low }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .moderatelyLow }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .moderatelyLow }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .average }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .moderatelyHigh }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .moderatelyLow }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .average }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .moderatelyLow }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .average }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .moderatelyHigh }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .average }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .average }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .low }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .moderatelyHigh }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .low }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .average }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .moderatelyHigh }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .average }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .high }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .moderatelyLow }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .average }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .average }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .average }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .moderatelyLow }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .moderatelyHigh }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .low }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .low }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .moderatelyHigh }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .moderatelyHigh }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .moderatelyHigh }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .high }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .average }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .high }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .moderatelyHigh }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .high }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .moderatelyHigh }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .moderatelyLow }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .moderatelyHigh }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .average }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .moderatelyHigh }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .low }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .low }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .moderatelyHigh }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .high }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .high }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .moderatelyLow }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .high }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .high }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .average }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .low }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .average }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .moderatelyLow }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .moderatelyHigh }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .moderatelyLow }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .high }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .low }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .average }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .average }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .low }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .low }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .average }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .average }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .average }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .moderatelyLow }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .moderatelyHigh }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .moderatelyHigh }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .average }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .average }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .moderatelyLow }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .moderatelyHigh }
  , { walsCode := "som", language := "Somali", iso := "som", value := .moderatelyLow }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .moderatelyHigh }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .average }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .average }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .high }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .average }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .moderatelyLow }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .high }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .average }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .moderatelyHigh }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .average }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .average }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .moderatelyHigh }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .average }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .moderatelyLow }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .average }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .moderatelyLow }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .average }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .high }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .moderatelyHigh }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .high }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .average }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .moderatelyHigh }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .moderatelyLow }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .moderatelyLow }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .high }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .moderatelyLow }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .moderatelyLow }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .average }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .average }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .moderatelyLow }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .moderatelyHigh }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .moderatelyLow }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .average }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .moderatelyHigh }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .high }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .low }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .average }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .average }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .moderatelyLow }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .moderatelyHigh }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .average }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .high }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .average }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .high }
  ]

private def allData_1 : List (Datapoint ConsonantVowelRatio) :=
  [ { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .average }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .average }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .average }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .moderatelyLow }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .average }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .moderatelyLow }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .moderatelyHigh }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .average }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .moderatelyLow }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .average }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .moderatelyLow }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .moderatelyLow }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .average }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .low }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .average }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .low }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .moderatelyHigh }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .moderatelyLow }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .moderatelyLow }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .average }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .moderatelyHigh }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .moderatelyLow }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .average }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .average }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .moderatelyLow }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .low }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .average }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .moderatelyHigh }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .average }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .average }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .moderatelyLow }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .moderatelyHigh }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .moderatelyHigh }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .low }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .average }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .average }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .average }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .low }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .moderatelyLow }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .average }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .high }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .average }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .average }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .moderatelyLow }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .average }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .average }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .moderatelyHigh }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .average }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .high }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .average }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .moderatelyHigh }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .moderatelyLow }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .average }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .moderatelyHigh }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .average }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .average }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .average }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .moderatelyHigh }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .high }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .moderatelyHigh }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .average }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .moderatelyLow }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .high }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .average }
  ]

/-- Complete WALS 3A dataset (564 languages). -/
def allData : List (Datapoint ConsonantVowelRatio) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 564 := by native_decide

theorem count_low :
    (allData.filter (·.value == .low)).length = 58 := by native_decide
theorem count_moderatelyLow :
    (allData.filter (·.value == .moderatelyLow)).length = 101 := by native_decide
theorem count_average :
    (allData.filter (·.value == .average)).length = 234 := by native_decide
theorem count_moderatelyHigh :
    (allData.filter (·.value == .moderatelyHigh)).length = 102 := by native_decide
theorem count_high :
    (allData.filter (·.value == .high)).length = 69 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F3A
