import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 2A: Vowel Quality Inventories
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 2A`.

Chapter 2, 564 languages.
-/

namespace Core.WALS.F2A

/-- WALS 2A values. -/
inductive VowelQualityInventories where
  | small  -- Small (2-4) (93 languages)
  | average  -- Average (5-6) (287 languages)
  | large  -- Large (7-14) (184 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint VowelQualityInventories) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .average }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .average }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .average }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .small }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .average }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .average }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .average }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .small }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .large }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .average }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .average }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .average }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .large }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .large }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .large }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .small }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .large }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .small }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .large }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .small }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .large }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .small }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .average }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .large }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .large }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .small }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .large }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .large }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .average }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .large }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .average }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .large }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .average }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .average }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .average }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .small }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .large }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .average }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .average }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .small }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .average }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .average }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .average }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .small }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .large }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .small }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .large }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .large }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .large }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .average }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .large }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .large }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .small }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .small }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .large }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .large }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .average }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .large }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .average }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .average }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .average }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .average }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .small }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .large }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .small }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .average }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .large }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .average }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .large }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .average }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .large }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .average }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .large }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .large }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .average }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .large }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .average }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .average }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .large }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .average }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .large }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .average }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .small }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .small }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .small }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .average }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .large }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .large }
  , { walsCode := "car", language := "Carib", iso := "car", value := .average }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .large }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .small }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .large }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .large }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .average }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .average }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .small }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .average }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .small }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .average }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .average }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .large }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .average }
  , { walsCode := "cve", language := "Chuave", iso := "cjv", value := .average }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .average }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .large }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .average }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .small }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .average }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .average }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .average }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .small }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .average }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .average }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .average }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .average }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .large }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .average }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .average }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .large }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .large }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .large }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .average }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .average }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .average }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .large }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .large }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .small }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .average }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .small }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .average }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .large }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .large }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .large }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .large }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .small }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .large }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .large }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .average }
  , { walsCode := "eng", language := "English", iso := "eng", value := .large }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .large }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .average }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .average }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .large }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .large }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .small }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .average }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .large }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .average }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .large }
  , { walsCode := "fre", language := "French", iso := "fra", value := .large }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .large }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .average }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .large }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .average }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .small }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .average }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .small }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .large }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .large }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .average }
  , { walsCode := "ger", language := "German", iso := "deu", value := .large }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .average }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .small }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .large }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .large }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .average }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .small }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .average }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .average }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .average }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .average }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .large }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .average }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .small }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .average }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .average }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .large }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .average }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .average }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .average }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .average }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .average }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .average }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .average }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .average }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .average }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .average }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .large }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .large }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .small }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .large }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .average }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .large }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .small }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .large }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .large }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .large }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .large }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .average }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .average }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .average }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .average }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .average }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .large }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .average }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .large }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .average }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .average }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .small }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .average }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .average }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .average }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .average }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .small }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .large }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .small }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .large }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .average }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .small }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .large }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .average }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .average }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .small }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .average }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .large }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .average }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .average }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .small }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .average }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .average }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .large }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .large }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .average }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .large }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .average }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .large }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .small }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .average }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .average }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .average }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .large }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .average }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .large }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .average }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .average }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .average }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .large }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .large }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .average }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .average }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .large }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .average }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .large }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .average }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .small }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .large }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .small }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .large }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .large }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .average }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .large }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .large }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .large }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .large }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .large }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .average }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .average }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .large }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .average }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .average }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .average }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .average }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .large }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .large }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .small }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .average }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .average }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .average }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .average }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .large }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .average }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .small }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .average }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .average }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .large }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .average }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .large }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .small }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .average }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .average }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .average }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .large }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .average }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .average }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .large }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .average }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .large }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .average }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .average }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .large }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .large }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .average }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .large }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .small }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .average }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .average }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .large }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .average }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .large }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .large }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .average }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .average }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .small }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .average }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .large }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .average }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .average }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .average }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .average }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .average }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .average }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .small }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .average }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .small }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .large }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .average }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .average }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .small }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .average }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .average }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .average }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .small }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .average }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .large }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .small }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .average }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .large }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .average }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .average }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .large }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .average }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .average }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .average }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .average }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .large }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .average }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .average }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .average }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .average }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .large }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .small }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .small }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .average }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .average }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .average }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .average }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .large }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .large }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .average }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .average }
  , { walsCode := "nbk", language := "Natügu", iso := "ntu", value := .large }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .small }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .large }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .large }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .average }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .average }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .average }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .average }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .small }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .average }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .large }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .large }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .small }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .average }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .average }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .small }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .average }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .average }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .average }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .large }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .large }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .average }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .small }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .small }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .large }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .large }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .large }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .large }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .average }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .average }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .large }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .small }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .small }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .average }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .average }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .large }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .average }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .large }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .small }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .large }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .large }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .average }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .average }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .small }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .average }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .average }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .average }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .large }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .small }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .small }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .large }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .large }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .average }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .average }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .average }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .small }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .average }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .small }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .average }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .small }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .small }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .average }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .average }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .large }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .average }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .average }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .average }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .small }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .average }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .average }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .large }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .average }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .average }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .large }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .large }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .average }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .average }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .large }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .average }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .small }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .large }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .large }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .large }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .average }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .large }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .average }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .small }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .small }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .average }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .average }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .large }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .large }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .average }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .large }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .average }
  , { walsCode := "som", language := "Somali", iso := "som", value := .large }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .average }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .average }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .average }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .small }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .large }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .average }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .large }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .large }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .average }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .average }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .average }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .small }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .average }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .large }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .average }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .large }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .average }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .small }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .small }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .small }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .large }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .average }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .large }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .large }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .average }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .average }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .large }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .large }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .average }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .average }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .average }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .average }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .average }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .small }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .small }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .average }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .average }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .average }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .large }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .small }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .average }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .small }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .average }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .average }
  ]

private def allData_1 : List (Datapoint VowelQualityInventories) :=
  [ { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .large }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .average }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .large }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .large }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .large }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .large }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .average }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .average }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .large }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .average }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .average }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .average }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .average }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .large }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .average }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .average }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .small }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .large }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .average }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .small }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .average }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .average }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .average }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .average }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .average }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .large }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .average }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .small }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .small }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .average }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .average }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .average }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .average }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .large }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .large }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .large }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .average }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .average }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .large }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .average }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .small }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .large }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .average }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .average }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .average }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .average }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .large }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .small }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .average }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .small }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .small }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .large }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .average }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .average }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .average }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .average }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .average }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .large }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .small }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .average }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .large }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .average }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .average }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .average }
  ]

/-- Complete WALS 2A dataset (564 languages). -/
def allData : List (Datapoint VowelQualityInventories) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 564 := by native_decide

theorem count_small :
    (allData.filter (·.value == .small)).length = 93 := by native_decide
theorem count_average :
    (allData.filter (·.value == .average)).length = 287 := by native_decide
theorem count_large :
    (allData.filter (·.value == .large)).length = 184 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F2A
