import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 1A: Consonant Inventories
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 1A`.

Chapter 1, 563 languages.
-/

namespace Core.WALS.F1A

/-- WALS 1A values. -/
inductive ConsonantInventories where
  | small  -- Small (89 languages)
  | moderatelySmall  -- Moderately small (122 languages)
  | average  -- Average (201 languages)
  | moderatelyLarge  -- Moderately large (94 languages)
  | large  -- Large (57 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint ConsonantInventories) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .large }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .large }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .moderatelySmall }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .large }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .moderatelySmall }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .small }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .large }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .moderatelySmall }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .average }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .moderatelyLarge }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .average }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .small }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .average }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .average }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .small }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .small }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .moderatelySmall }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .average }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .average }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .average }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .average }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .small }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .moderatelySmall }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .moderatelyLarge }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .average }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .average }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .average }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .small }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .small }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .moderatelyLarge }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .small }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .small }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .small }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .small }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .moderatelyLarge }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .average }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .moderatelySmall }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .large }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .moderatelyLarge }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .large }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .small }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .average }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .large }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .small }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .moderatelyLarge }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .moderatelyLarge }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .average }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .moderatelyLarge }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .moderatelySmall }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .moderatelyLarge }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .moderatelySmall }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .average }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .small }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .moderatelySmall }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .moderatelySmall }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .moderatelyLarge }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .average }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .moderatelySmall }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .moderatelySmall }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .average }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .moderatelySmall }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .average }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .moderatelyLarge }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .moderatelyLarge }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .moderatelyLarge }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .average }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .average }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .moderatelySmall }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .average }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .moderatelySmall }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .small }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .average }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .average }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .average }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .moderatelySmall }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .average }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .average }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .moderatelySmall }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .moderatelyLarge }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .large }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .average }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .small }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .average }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .average }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .moderatelySmall }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .average }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .small }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .average }
  , { walsCode := "car", language := "Carib", iso := "car", value := .moderatelySmall }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .average }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .average }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .moderatelySmall }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .average }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .average }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .moderatelySmall }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .moderatelyLarge }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .small }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .moderatelySmall }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .average }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .average }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .moderatelyLarge }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .large }
  , { walsCode := "cve", language := "Chuave", iso := "cjv", value := .small }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .moderatelySmall }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .average }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .average }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .average }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .moderatelyLarge }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .small }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .large }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .small }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .small }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .small }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .small }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .average }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .average }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .large }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .average }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .average }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .average }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .small }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .moderatelyLarge }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .large }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .average }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .average }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .average }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .average }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .average }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .average }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .small }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .average }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .average }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .moderatelyLarge }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .small }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .small }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .small }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .average }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .small }
  , { walsCode := "eng", language := "English", iso := "eng", value := .average }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .moderatelySmall }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .moderatelySmall }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .moderatelySmall }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .moderatelyLarge }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .moderatelyLarge }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .moderatelyLarge }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .small }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .moderatelySmall }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .average }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .moderatelySmall }
  , { walsCode := "fre", language := "French", iso := "fra", value := .average }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .average }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .moderatelySmall }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .small }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .large }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .small }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .moderatelySmall }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .average }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .moderatelyLarge }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .moderatelyLarge }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .moderatelyLarge }
  , { walsCode := "ger", language := "German", iso := "deu", value := .average }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .small }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .average }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .average }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .average }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .average }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .average }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .moderatelySmall }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .moderatelySmall }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .moderatelySmall }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .average }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .moderatelyLarge }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .large }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .large }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .moderatelySmall }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .average }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .small }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .moderatelyLarge }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .small }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .moderatelySmall }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .large }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .moderatelySmall }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .large }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .average }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .average }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .average }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .moderatelySmall }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .moderatelyLarge }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .large }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .moderatelyLarge }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .large }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .average }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .moderatelyLarge }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .average }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .average }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .moderatelyLarge }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .moderatelySmall }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .small }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .average }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .average }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .large }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .average }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .moderatelyLarge }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .small }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .large }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .moderatelyLarge }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .moderatelyLarge }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .average }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .average }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .small }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .moderatelyLarge }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .moderatelySmall }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .small }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .large }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .average }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .average }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .large }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .average }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .moderatelySmall }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .small }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .large }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .average }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .large }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .average }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .small }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .moderatelySmall }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .large }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .average }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .average }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .moderatelyLarge }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .average }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .moderatelyLarge }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .moderatelySmall }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .moderatelyLarge }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .average }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .average }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .moderatelySmall }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .moderatelySmall }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .average }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .average }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .moderatelySmall }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .moderatelySmall }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .average }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .moderatelySmall }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .moderatelyLarge }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .average }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .average }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .average }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .average }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .average }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .average }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .small }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .moderatelySmall }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .small }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .moderatelyLarge }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .small }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .small }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .average }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .moderatelyLarge }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .small }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .moderatelyLarge }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .average }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .average }
  , { walsCode := "kgi", language := "Konyagi", iso := "cou", value := .large }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .average }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .moderatelySmall }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .moderatelySmall }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .average }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .moderatelyLarge }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .average }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .moderatelySmall }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .moderatelySmall }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .average }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .average }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .average }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .small }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .average }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .moderatelySmall }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .average }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .moderatelySmall }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .moderatelyLarge }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .average }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .moderatelyLarge }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .moderatelySmall }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .large }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .average }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .moderatelyLarge }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .moderatelyLarge }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .large }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .average }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .moderatelyLarge }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .moderatelyLarge }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .moderatelySmall }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .moderatelyLarge }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .moderatelySmall }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .average }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .moderatelySmall }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .moderatelyLarge }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .large }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .large }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .average }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .moderatelyLarge }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .average }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .moderatelyLarge }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .large }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .moderatelySmall }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .moderatelySmall }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .average }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .small }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .average }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .average }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .moderatelySmall }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .moderatelyLarge }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .small }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .average }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .moderatelySmall }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .average }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .moderatelySmall }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .average }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .small }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .average }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .small }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .small }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .moderatelyLarge }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .average }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .average }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .moderatelySmall }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .average }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .moderatelySmall }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .small }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .small }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .large }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .average }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .average }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .average }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .moderatelyLarge }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .average }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .moderatelyLarge }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .average }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .moderatelySmall }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .small }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .moderatelySmall }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .moderatelySmall }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .average }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .small }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .average }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .moderatelySmall }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .average }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .average }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .moderatelyLarge }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .average }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .average }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .moderatelySmall }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .moderatelySmall }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .moderatelyLarge }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .average }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .moderatelySmall }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .moderatelySmall }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .small }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .average }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .small }
  , { walsCode := "nbk", language := "Natügu", iso := "ntu", value := .moderatelyLarge }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .moderatelyLarge }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .large }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .moderatelyLarge }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .moderatelySmall }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .moderatelyLarge }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .average }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .moderatelyLarge }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .average }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .moderatelyLarge }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .average }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .large }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .large }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .small }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .average }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .moderatelyLarge }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .average }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .moderatelySmall }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .average }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .average }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .average }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .average }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .large }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .moderatelyLarge }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .moderatelySmall }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .moderatelySmall }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .moderatelySmall }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .average }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .moderatelyLarge }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .average }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .moderatelySmall }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .small }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .average }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .moderatelyLarge }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .average }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .moderatelySmall }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .average }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .average }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .small }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .large }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .moderatelyLarge }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .moderatelySmall }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .average }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .small }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .moderatelySmall }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .average }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .average }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .small }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .moderatelySmall }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .moderatelySmall }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .small }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .large }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .moderatelyLarge }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .moderatelyLarge }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .large }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .small }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .average }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .moderatelyLarge }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .moderatelyLarge }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .moderatelySmall }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .small }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .moderatelyLarge }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .average }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .average }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .small }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .small }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .average }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .moderatelyLarge }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .large }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .average }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .large }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .large }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .moderatelyLarge }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .small }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .moderatelySmall }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .small }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .large }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .moderatelySmall }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .average }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .moderatelySmall }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .moderatelyLarge }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .average }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .small }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .small }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .average }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .moderatelySmall }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .moderatelySmall }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .small }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .large }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .large }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .average }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .moderatelySmall }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .average }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .moderatelyLarge }
  , { walsCode := "som", language := "Somali", iso := "som", value := .average }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .moderatelyLarge }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .moderatelySmall }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .average }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .large }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .moderatelyLarge }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .small }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .large }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .average }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .moderatelyLarge }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .average }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .moderatelySmall }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .moderatelySmall }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .moderatelySmall }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .average }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .average }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .average }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .moderatelyLarge }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .moderatelySmall }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .moderatelyLarge }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .average }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .moderatelyLarge }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .moderatelySmall }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .moderatelySmall }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .large }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .small }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .average }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .large }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .moderatelySmall }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .small }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .moderatelyLarge }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .moderatelySmall }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .moderatelyLarge }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .average }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .average }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .large }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .small }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .average }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .moderatelySmall }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .moderatelySmall }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .moderatelySmall }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .average }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .large }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .moderatelySmall }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .large }
  ]

private def allData_1 : List (Datapoint ConsonantInventories) :=
  [ { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .average }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .average }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .average }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .moderatelySmall }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .average }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .average }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .average }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .average }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .average }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .moderatelySmall }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .moderatelySmall }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .small }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .average }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .average }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .moderatelySmall }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .small }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .moderatelySmall }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .moderatelySmall }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .moderatelySmall }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .moderatelyLarge }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .small }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .moderatelySmall }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .moderatelySmall }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .moderatelySmall }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .small }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .moderatelySmall }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .moderatelySmall }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .average }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .average }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .small }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .moderatelyLarge }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .average }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .moderatelySmall }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .moderatelyLarge }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .average }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .small }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .small }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .average }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .average }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .moderatelyLarge }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .average }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .moderatelySmall }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .small }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .small }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .average }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .large }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .moderatelySmall }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .large }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .small }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .small }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .moderatelySmall }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .average }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .large }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .moderatelySmall }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .average }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .average }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .large }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .moderatelyLarge }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .moderatelyLarge }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .average }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .moderatelySmall }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .moderatelyLarge }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .average }
  ]

/-- Complete WALS 1A dataset (563 languages). -/
def allData : List (Datapoint ConsonantInventories) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 563 := by native_decide

theorem count_small :
    (allData.filter (·.value == .small)).length = 89 := by native_decide
theorem count_moderatelySmall :
    (allData.filter (·.value == .moderatelySmall)).length = 122 := by native_decide
theorem count_average :
    (allData.filter (·.value == .average)).length = 201 := by native_decide
theorem count_moderatelyLarge :
    (allData.filter (·.value == .moderatelyLarge)).length = 94 := by native_decide
theorem count_large :
    (allData.filter (·.value == .large)).length = 57 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F1A
