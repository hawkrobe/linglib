import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 12A: Syllable Structure
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 12A`.

Chapter 12, 486 languages.
-/

namespace Core.WALS.F12A

/-- WALS 12A values. -/
inductive SyllableStructure where
  | simple  -- Simple (61 languages)
  | moderatelyComplex  -- Moderately complex (274 languages)
  | complex  -- Complex (151 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 12A dataset (486 languages). -/
def allData : List (Datapoint SyllableStructure) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .moderatelyComplex }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .moderatelyComplex }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .complex }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .complex }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .simple }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .moderatelyComplex }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .moderatelyComplex }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .complex }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .moderatelyComplex }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .moderatelyComplex }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .complex }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .moderatelyComplex }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .moderatelyComplex }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .complex }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .complex }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .complex }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .complex }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .moderatelyComplex }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .moderatelyComplex }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .moderatelyComplex }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .moderatelyComplex }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .moderatelyComplex }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .complex }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .simple }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .moderatelyComplex }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .complex }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .moderatelyComplex }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .simple }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .moderatelyComplex }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .complex }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .simple }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .moderatelyComplex }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .complex }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .moderatelyComplex }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .moderatelyComplex }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .complex }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .complex }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .moderatelyComplex }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .moderatelyComplex }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .moderatelyComplex }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .moderatelyComplex }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .moderatelyComplex }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .moderatelyComplex }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .simple }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .simple }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .moderatelyComplex }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .complex }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .complex }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .complex }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .moderatelyComplex }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .moderatelyComplex }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .moderatelyComplex }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .complex }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .complex }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .complex }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .complex }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .moderatelyComplex }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .moderatelyComplex }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .moderatelyComplex }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .simple }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .moderatelyComplex }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .simple }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .complex }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .complex }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .complex }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .complex }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .complex }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .complex }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .moderatelyComplex }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .complex }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .moderatelyComplex }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .moderatelyComplex }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .moderatelyComplex }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .complex }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .moderatelyComplex }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .complex }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .complex }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .moderatelyComplex }
  , { walsCode := "car", language := "Carib", iso := "car", value := .moderatelyComplex }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .moderatelyComplex }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .simple }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .complex }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .moderatelyComplex }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .complex }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .moderatelyComplex }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .moderatelyComplex }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .moderatelyComplex }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .moderatelyComplex }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .simple }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .moderatelyComplex }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .complex }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .complex }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .moderatelyComplex }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .complex }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .moderatelyComplex }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .complex }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .moderatelyComplex }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .simple }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .moderatelyComplex }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .moderatelyComplex }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .moderatelyComplex }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .complex }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .moderatelyComplex }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .moderatelyComplex }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .moderatelyComplex }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .moderatelyComplex }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .moderatelyComplex }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .moderatelyComplex }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .moderatelyComplex }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .complex }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .moderatelyComplex }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .complex }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .complex }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .moderatelyComplex }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .moderatelyComplex }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .complex }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .moderatelyComplex }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .moderatelyComplex }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .moderatelyComplex }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .moderatelyComplex }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .simple }
  , { walsCode := "eng", language := "English", iso := "eng", value := .complex }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .moderatelyComplex }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .moderatelyComplex }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .moderatelyComplex }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .moderatelyComplex }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .complex }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .simple }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .moderatelyComplex }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .simple }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .moderatelyComplex }
  , { walsCode := "fre", language := "French", iso := "fra", value := .complex }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .complex }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .moderatelyComplex }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .moderatelyComplex }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .moderatelyComplex }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .moderatelyComplex }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .moderatelyComplex }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .moderatelyComplex }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .moderatelyComplex }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .moderatelyComplex }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .complex }
  , { walsCode := "ger", language := "German", iso := "deu", value := .complex }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .moderatelyComplex }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .moderatelyComplex }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .simple }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .complex }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .moderatelyComplex }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .moderatelyComplex }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .simple }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .complex }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .moderatelyComplex }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .simple }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .complex }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .moderatelyComplex }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .moderatelyComplex }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .complex }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .moderatelyComplex }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .simple }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .complex }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .complex }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .moderatelyComplex }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .moderatelyComplex }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .complex }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .moderatelyComplex }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .moderatelyComplex }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .simple }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .complex }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .moderatelyComplex }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .complex }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .moderatelyComplex }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .moderatelyComplex }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .simple }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .simple }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .complex }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .moderatelyComplex }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .complex }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .complex }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .moderatelyComplex }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .complex }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .moderatelyComplex }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .moderatelyComplex }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .moderatelyComplex }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .complex }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .moderatelyComplex }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .complex }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .moderatelyComplex }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .moderatelyComplex }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .moderatelyComplex }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .moderatelyComplex }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .moderatelyComplex }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .moderatelyComplex }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .moderatelyComplex }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .complex }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .moderatelyComplex }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .moderatelyComplex }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .simple }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .moderatelyComplex }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .moderatelyComplex }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .complex }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .moderatelyComplex }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .moderatelyComplex }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .moderatelyComplex }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .complex }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .moderatelyComplex }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .moderatelyComplex }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .moderatelyComplex }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .moderatelyComplex }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .moderatelyComplex }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .moderatelyComplex }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .moderatelyComplex }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .complex }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .simple }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .moderatelyComplex }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .moderatelyComplex }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .complex }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .complex }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .complex }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .moderatelyComplex }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .moderatelyComplex }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .complex }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .moderatelyComplex }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .moderatelyComplex }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .simple }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .complex }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .simple }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .moderatelyComplex }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .moderatelyComplex }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .simple }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .complex }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .moderatelyComplex }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .moderatelyComplex }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .moderatelyComplex }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .complex }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .complex }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .complex }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .complex }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .moderatelyComplex }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .complex }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .moderatelyComplex }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .moderatelyComplex }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .moderatelyComplex }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .moderatelyComplex }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .moderatelyComplex }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .moderatelyComplex }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .moderatelyComplex }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .complex }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .complex }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .simple }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .complex }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .moderatelyComplex }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .complex }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .moderatelyComplex }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .complex }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .complex }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .moderatelyComplex }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .moderatelyComplex }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .complex }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .moderatelyComplex }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .simple }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .moderatelyComplex }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .complex }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .complex }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .complex }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .moderatelyComplex }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .moderatelyComplex }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .moderatelyComplex }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .complex }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .moderatelyComplex }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .simple }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .moderatelyComplex }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .moderatelyComplex }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .moderatelyComplex }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .complex }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .moderatelyComplex }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .complex }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .moderatelyComplex }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .complex }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .moderatelyComplex }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .moderatelyComplex }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .complex }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .moderatelyComplex }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .simple }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .moderatelyComplex }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .complex }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .complex }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .moderatelyComplex }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .moderatelyComplex }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .complex }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .moderatelyComplex }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .simple }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .moderatelyComplex }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .simple }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .moderatelyComplex }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .moderatelyComplex }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .moderatelyComplex }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .moderatelyComplex }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .complex }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .simple }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .complex }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .simple }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .moderatelyComplex }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .simple }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .simple }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .moderatelyComplex }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .moderatelyComplex }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .moderatelyComplex }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .complex }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .moderatelyComplex }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .moderatelyComplex }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .moderatelyComplex }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .complex }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .moderatelyComplex }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .moderatelyComplex }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .moderatelyComplex }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .moderatelyComplex }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .moderatelyComplex }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .simple }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .moderatelyComplex }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .moderatelyComplex }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .complex }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .complex }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .moderatelyComplex }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .complex }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .moderatelyComplex }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .simple }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .moderatelyComplex }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .moderatelyComplex }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .complex }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .moderatelyComplex }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .moderatelyComplex }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .complex }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .complex }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .moderatelyComplex }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .complex }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .complex }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .moderatelyComplex }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .moderatelyComplex }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .complex }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .complex }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .moderatelyComplex }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .complex }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .complex }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .moderatelyComplex }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .complex }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .moderatelyComplex }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .moderatelyComplex }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .moderatelyComplex }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .moderatelyComplex }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .moderatelyComplex }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .complex }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .complex }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .simple }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .moderatelyComplex }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .moderatelyComplex }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .complex }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .moderatelyComplex }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .simple }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .moderatelyComplex }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .moderatelyComplex }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .complex }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .complex }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .moderatelyComplex }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .complex }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .moderatelyComplex }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .complex }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .moderatelyComplex }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .simple }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .moderatelyComplex }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .complex }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .simple }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .simple }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .moderatelyComplex }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .complex }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .complex }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .complex }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .complex }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .moderatelyComplex }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .simple }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .moderatelyComplex }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .simple }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .moderatelyComplex }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .complex }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .moderatelyComplex }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .moderatelyComplex }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .simple }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .moderatelyComplex }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .moderatelyComplex }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .moderatelyComplex }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .moderatelyComplex }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .complex }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .simple }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .moderatelyComplex }
  , { walsCode := "som", language := "Somali", iso := "som", value := .moderatelyComplex }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .complex }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .moderatelyComplex }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .moderatelyComplex }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .complex }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .complex }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .simple }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .moderatelyComplex }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .moderatelyComplex }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .simple }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .simple }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .complex }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .simple }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .moderatelyComplex }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .moderatelyComplex }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .moderatelyComplex }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .complex }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .moderatelyComplex }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .complex }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .moderatelyComplex }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .moderatelyComplex }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .moderatelyComplex }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .complex }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .moderatelyComplex }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .complex }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .moderatelyComplex }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .moderatelyComplex }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .moderatelyComplex }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .moderatelyComplex }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .moderatelyComplex }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .moderatelyComplex }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .complex }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .simple }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .moderatelyComplex }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .moderatelyComplex }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .simple }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .moderatelyComplex }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .complex }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .complex }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .complex }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .complex }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .simple }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .complex }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .moderatelyComplex }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .complex }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .complex }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .simple }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .moderatelyComplex }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .moderatelyComplex }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .moderatelyComplex }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .moderatelyComplex }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .complex }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .moderatelyComplex }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .moderatelyComplex }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .simple }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .moderatelyComplex }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .moderatelyComplex }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .simple }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .moderatelyComplex }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .simple }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .complex }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .moderatelyComplex }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .moderatelyComplex }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .moderatelyComplex }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .moderatelyComplex }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .moderatelyComplex }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .moderatelyComplex }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .moderatelyComplex }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .complex }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .complex }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .moderatelyComplex }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .complex }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .moderatelyComplex }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .moderatelyComplex }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .moderatelyComplex }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .simple }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .moderatelyComplex }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .moderatelyComplex }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .simple }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .moderatelyComplex }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .moderatelyComplex }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .moderatelyComplex }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .moderatelyComplex }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .simple }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .moderatelyComplex }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .moderatelyComplex }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .complex }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .moderatelyComplex }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .moderatelyComplex }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .complex }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .complex }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .moderatelyComplex }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .moderatelyComplex }
  ]

-- Count verification
theorem total_count : allData.length = 486 := by native_decide

theorem count_simple :
    (allData.filter (·.value == .simple)).length = 61 := by native_decide
theorem count_moderatelyComplex :
    (allData.filter (·.value == .moderatelyComplex)).length = 274 := by native_decide
theorem count_complex :
    (allData.filter (·.value == .complex)).length = 151 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F12A
