import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 18A: Absence of Common Consonants
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 18A`.

Chapter 18, 567 languages.
-/

namespace Core.WALS.F18A

/-- WALS 18A values. -/
inductive AbsenceOfCommonConsonants where
  | allPresent  -- All present (503 languages)
  | noBilabials  -- No bilabials (4 languages)
  | noFricatives  -- No fricatives (48 languages)
  | noNasals  -- No nasals (10 languages)
  | noBilabialsOrNasals  -- No bilabials or nasals (1 languages)
  | noFricativesOrNasals  -- No fricatives or nasals (1 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint AbsenceOfCommonConsonants) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .allPresent }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .allPresent }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .allPresent }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .allPresent }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .allPresent }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .allPresent }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .allPresent }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .allPresent }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .allPresent }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .allPresent }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .allPresent }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .allPresent }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .allPresent }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .allPresent }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .allPresent }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .allPresent }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .allPresent }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noFricatives }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .allPresent }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .allPresent }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .allPresent }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .allPresent }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .allPresent }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .allPresent }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .allPresent }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .allPresent }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .allPresent }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .noNasals }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .noFricatives }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .allPresent }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .allPresent }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .allPresent }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .allPresent }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .allPresent }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .allPresent }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .allPresent }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .allPresent }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .allPresent }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .allPresent }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noFricatives }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .allPresent }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .allPresent }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .allPresent }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .allPresent }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .allPresent }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .allPresent }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .allPresent }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .allPresent }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .allPresent }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .allPresent }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .allPresent }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .allPresent }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .noFricatives }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .noFricatives }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .allPresent }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .allPresent }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .allPresent }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .allPresent }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .allPresent }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .allPresent }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .allPresent }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .allPresent }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .allPresent }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .allPresent }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .allPresent }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .allPresent }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .allPresent }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .allPresent }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .allPresent }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .allPresent }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noFricatives }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .allPresent }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .allPresent }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .allPresent }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .allPresent }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .allPresent }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .allPresent }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .noFricatives }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .allPresent }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .allPresent }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .allPresent }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .noFricatives }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .allPresent }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .allPresent }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .allPresent }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .allPresent }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .allPresent }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .allPresent }
  , { walsCode := "car", language := "Carib", iso := "car", value := .allPresent }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .allPresent }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .allPresent }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .allPresent }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .allPresent }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .allPresent }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .allPresent }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .allPresent }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .allPresent }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .allPresent }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .allPresent }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .allPresent }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .allPresent }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .noBilabials }
  , { walsCode := "cve", language := "Chuave", iso := "cjv", value := .allPresent }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .allPresent }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .allPresent }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .allPresent }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .allPresent }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .allPresent }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .allPresent }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .allPresent }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .allPresent }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noNasals }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .allPresent }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .allPresent }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .allPresent }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .allPresent }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .allPresent }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .allPresent }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .allPresent }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .allPresent }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .allPresent }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .allPresent }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .allPresent }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .allPresent }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noFricatives }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .allPresent }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noFricatives }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .allPresent }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noFricatives }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .noFricatives }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .allPresent }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .allPresent }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .allPresent }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .allPresent }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noFricatives }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .allPresent }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .allPresent }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noFricatives }
  , { walsCode := "eng", language := "English", iso := "eng", value := .allPresent }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noNasals }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .allPresent }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .allPresent }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .allPresent }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .allPresent }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .noBilabialsOrNasals }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .allPresent }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .allPresent }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .allPresent }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .allPresent }
  , { walsCode := "fre", language := "French", iso := "fra", value := .allPresent }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .allPresent }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .allPresent }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .allPresent }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .allPresent }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .noFricatives }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .allPresent }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noFricatives }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .allPresent }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .allPresent }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .allPresent }
  , { walsCode := "ger", language := "German", iso := "deu", value := .allPresent }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .allPresent }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noFricatives }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .noFricatives }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .allPresent }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .allPresent }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .allPresent }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .allPresent }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .allPresent }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .allPresent }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .allPresent }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .allPresent }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .allPresent }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .allPresent }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .allPresent }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .allPresent }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .allPresent }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .allPresent }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noFricatives }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .allPresent }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .allPresent }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .allPresent }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .allPresent }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .allPresent }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .allPresent }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .allPresent }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .allPresent }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .allPresent }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .allPresent }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .allPresent }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .allPresent }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .allPresent }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .allPresent }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .allPresent }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .allPresent }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .allPresent }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .allPresent }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .allPresent }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .allPresent }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .allPresent }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .allPresent }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .allPresent }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .allPresent }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .allPresent }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .allPresent }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .allPresent }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .allPresent }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .allPresent }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .allPresent }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .allPresent }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .allPresent }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .allPresent }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .allPresent }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .allPresent }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .allPresent }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .allPresent }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .allPresent }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .allPresent }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .allPresent }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .allPresent }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .allPresent }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .allPresent }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .allPresent }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .allPresent }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .noNasals }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .allPresent }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .allPresent }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .noFricatives }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .allPresent }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .allPresent }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .allPresent }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .allPresent }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .allPresent }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .allPresent }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .allPresent }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .allPresent }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noFricatives }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .allPresent }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .allPresent }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .allPresent }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .allPresent }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .allPresent }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .allPresent }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .allPresent }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .allPresent }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .allPresent }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .allPresent }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .allPresent }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .allPresent }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .allPresent }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .allPresent }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noFricatives }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .allPresent }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .allPresent }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .allPresent }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .noNasals }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .allPresent }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .allPresent }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .allPresent }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .allPresent }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .allPresent }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .allPresent }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .allPresent }
  , { walsCode := "kgi", language := "Konyagi", iso := "cou", value := .allPresent }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .allPresent }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .allPresent }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .allPresent }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .allPresent }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .allPresent }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .allPresent }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .allPresent }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .allPresent }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .noNasals }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .allPresent }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .allPresent }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noFricatives }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .allPresent }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .allPresent }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .allPresent }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .allPresent }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .allPresent }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .allPresent }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .allPresent }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .allPresent }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .allPresent }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .allPresent }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .allPresent }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .allPresent }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .allPresent }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .allPresent }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .allPresent }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .allPresent }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noFricatives }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .allPresent }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .allPresent }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .allPresent }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .allPresent }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .allPresent }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .allPresent }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .allPresent }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .allPresent }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .allPresent }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .allPresent }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .allPresent }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .allPresent }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .allPresent }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .allPresent }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .allPresent }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .allPresent }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .allPresent }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .allPresent }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .allPresent }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .allPresent }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .allPresent }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noFricatives }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .allPresent }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .allPresent }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .allPresent }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noFricatives }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .allPresent }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .allPresent }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .allPresent }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .noFricatives }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noFricatives }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .allPresent }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .allPresent }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .allPresent }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .allPresent }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noFricatives }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .allPresent }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .noFricativesOrNasals }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .allPresent }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .allPresent }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .allPresent }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .allPresent }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .noFricatives }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .allPresent }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .allPresent }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .allPresent }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .allPresent }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .allPresent }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .allPresent }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .allPresent }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .allPresent }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .allPresent }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .allPresent }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .allPresent }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .allPresent }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .allPresent }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .allPresent }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .allPresent }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .allPresent }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noFricatives }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .allPresent }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .allPresent }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .allPresent }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .allPresent }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .allPresent }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .allPresent }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .allPresent }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .allPresent }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .allPresent }
  , { walsCode := "nbk", language := "Natügu", iso := "ntu", value := .allPresent }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .allPresent }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .allPresent }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .allPresent }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .allPresent }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .allPresent }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .allPresent }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .allPresent }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .allPresent }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .allPresent }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .allPresent }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .allPresent }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .allPresent }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .allPresent }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .allPresent }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .allPresent }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .allPresent }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .allPresent }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .allPresent }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .allPresent }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .allPresent }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .allPresent }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noFricatives }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .allPresent }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .allPresent }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .allPresent }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .allPresent }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .allPresent }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .allPresent }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .allPresent }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .allPresent }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .allPresent }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noBilabials }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .allPresent }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .allPresent }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .allPresent }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .allPresent }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .allPresent }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .allPresent }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .noFricatives }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .allPresent }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .allPresent }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .allPresent }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .allPresent }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .allPresent }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .allPresent }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .allPresent }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .allPresent }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noNasals }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noFricatives }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .allPresent }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .allPresent }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .allPresent }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .allPresent }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .allPresent }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .allPresent }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .allPresent }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .allPresent }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .allPresent }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noNasals }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .allPresent }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .allPresent }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .allPresent }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .allPresent }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .allPresent }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .allPresent }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .noNasals }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .allPresent }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .allPresent }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .allPresent }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .allPresent }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .allPresent }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .allPresent }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .allPresent }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .allPresent }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .allPresent }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .allPresent }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .allPresent }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .allPresent }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .allPresent }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .allPresent }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .allPresent }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .allPresent }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .allPresent }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .allPresent }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .allPresent }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .allPresent }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .allPresent }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .allPresent }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .allPresent }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .allPresent }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .allPresent }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .allPresent }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .allPresent }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .allPresent }
  , { walsCode := "som", language := "Somali", iso := "som", value := .allPresent }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .allPresent }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .allPresent }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .allPresent }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .allPresent }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .allPresent }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .allPresent }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .allPresent }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .allPresent }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .allPresent }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .allPresent }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .allPresent }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .allPresent }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .allPresent }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .allPresent }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .allPresent }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .allPresent }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .allPresent }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .allPresent }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .allPresent }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .allPresent }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .allPresent }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .allPresent }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .allPresent }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .allPresent }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .allPresent }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .allPresent }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .allPresent }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .allPresent }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .allPresent }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .allPresent }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .allPresent }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .allPresent }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .allPresent }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .allPresent }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .allPresent }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noBilabials }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .allPresent }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .allPresent }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .allPresent }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .allPresent }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .allPresent }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .allPresent }
  ]

private def allData_1 : List (Datapoint AbsenceOfCommonConsonants) :=
  [ { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .allPresent }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .allPresent }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .allPresent }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .allPresent }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .allPresent }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .allPresent }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .allPresent }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .allPresent }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .allPresent }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .allPresent }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .allPresent }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .allPresent }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noFricatives }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .allPresent }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .allPresent }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .allPresent }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .allPresent }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .noFricatives }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .noNasals }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noFricatives }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .allPresent }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noFricatives }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .allPresent }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .allPresent }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .allPresent }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .noFricatives }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noFricatives }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noFricatives }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .allPresent }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .allPresent }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .noFricatives }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noBilabials }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .allPresent }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .noFricatives }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .allPresent }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .allPresent }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .allPresent }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .allPresent }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .allPresent }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .allPresent }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noFricatives }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .allPresent }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .allPresent }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .noFricatives }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .allPresent }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .allPresent }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .allPresent }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .allPresent }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .allPresent }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .noFricatives }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .allPresent }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .allPresent }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noFricatives }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noFricatives }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .allPresent }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .allPresent }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .allPresent }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .allPresent }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .allPresent }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .allPresent }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .allPresent }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .allPresent }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .allPresent }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .allPresent }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .allPresent }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .allPresent }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .allPresent }
  ]

/-- Complete WALS 18A dataset (567 languages). -/
def allData : List (Datapoint AbsenceOfCommonConsonants) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 567 := by native_decide

theorem count_allPresent :
    (allData.filter (·.value == .allPresent)).length = 503 := by native_decide
theorem count_noBilabials :
    (allData.filter (·.value == .noBilabials)).length = 4 := by native_decide
theorem count_noFricatives :
    (allData.filter (·.value == .noFricatives)).length = 48 := by native_decide
theorem count_noNasals :
    (allData.filter (·.value == .noNasals)).length = 10 := by native_decide
theorem count_noBilabialsOrNasals :
    (allData.filter (·.value == .noBilabialsOrNasals)).length = 1 := by native_decide
theorem count_noFricativesOrNasals :
    (allData.filter (·.value == .noFricativesOrNasals)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F18A
