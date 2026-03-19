import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 5A: Voicing and Gaps in Plosive Systems
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 5A`.

Chapter 5, 567 languages.
-/

namespace Core.WALS.F5A

/-- WALS 5A values. -/
inductive VoicingAndGapsInPlosiveSystems where
  | other  -- Other (242 languages)
  | noneMissingInPTKBDG  -- None missing in /p t k b d g/ (255 languages)
  | missingP  -- Missing /p/ (33 languages)
  | missingG  -- Missing /g/ (34 languages)
  | bothMissing  -- Both missing (3 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint VoicingAndGapsInPlosiveSystems) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .noneMissingInPTKBDG }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .noneMissingInPTKBDG }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .other }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noneMissingInPTKBDG }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .other }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .other }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .other }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noneMissingInPTKBDG }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .missingP }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .other }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .noneMissingInPTKBDG }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .other }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .noneMissingInPTKBDG }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noneMissingInPTKBDG }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .noneMissingInPTKBDG }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .other }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noneMissingInPTKBDG }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .other }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noneMissingInPTKBDG }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .other }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .noneMissingInPTKBDG }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .other }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .missingP }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .noneMissingInPTKBDG }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .noneMissingInPTKBDG }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .other }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .other }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .missingG }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .other }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .noneMissingInPTKBDG }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .other }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .other }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .other }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .other }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .missingP }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .missingG }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noneMissingInPTKBDG }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .other }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .other }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .other }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .other }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .other }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .other }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .other }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .noneMissingInPTKBDG }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .other }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .noneMissingInPTKBDG }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .noneMissingInPTKBDG }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .other }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .noneMissingInPTKBDG }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .noneMissingInPTKBDG }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noneMissingInPTKBDG }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .other }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .other }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .noneMissingInPTKBDG }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .noneMissingInPTKBDG }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noneMissingInPTKBDG }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noneMissingInPTKBDG }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .noneMissingInPTKBDG }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .missingG }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .other }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .missingP }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .other }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .noneMissingInPTKBDG }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .missingP }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .other }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .noneMissingInPTKBDG }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .noneMissingInPTKBDG }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .noneMissingInPTKBDG }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .noneMissingInPTKBDG }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noneMissingInPTKBDG }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noneMissingInPTKBDG }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .other }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .noneMissingInPTKBDG }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noneMissingInPTKBDG }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .missingG }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noneMissingInPTKBDG }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .other }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noneMissingInPTKBDG }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noneMissingInPTKBDG }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .noneMissingInPTKBDG }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .other }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .missingG }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .other }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .other }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .noneMissingInPTKBDG }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .other }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .other }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noneMissingInPTKBDG }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noneMissingInPTKBDG }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .noneMissingInPTKBDG }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .missingG }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .other }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noneMissingInPTKBDG }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .noneMissingInPTKBDG }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .other }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .other }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .other }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .noneMissingInPTKBDG }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noneMissingInPTKBDG }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .other }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .other }
  , { walsCode := "cve", language := "Chuave", iso := "cjv", value := .missingP }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .other }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noneMissingInPTKBDG }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .missingG }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .other }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .noneMissingInPTKBDG }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .other }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .noneMissingInPTKBDG }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .other }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .missingG }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .other }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noneMissingInPTKBDG }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .noneMissingInPTKBDG }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .noneMissingInPTKBDG }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .noneMissingInPTKBDG }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .noneMissingInPTKBDG }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .noneMissingInPTKBDG }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .noneMissingInPTKBDG }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .other }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .noneMissingInPTKBDG }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .noneMissingInPTKBDG }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .other }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noneMissingInPTKBDG }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noneMissingInPTKBDG }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .other }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .missingP }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .other }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .noneMissingInPTKBDG }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .other }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .noneMissingInPTKBDG }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noneMissingInPTKBDG }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .other }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .other }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .bothMissing }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .noneMissingInPTKBDG }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .missingG }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noneMissingInPTKBDG }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noneMissingInPTKBDG }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .noneMissingInPTKBDG }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noneMissingInPTKBDG }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noneMissingInPTKBDG }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .missingP }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .other }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .other }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .missingP }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .other }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noneMissingInPTKBDG }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noneMissingInPTKBDG }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .other }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .missingP }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .other }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .other }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .other }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noneMissingInPTKBDG }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .other }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .noneMissingInPTKBDG }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .other }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .other }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noneMissingInPTKBDG }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .other }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .other }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .noneMissingInPTKBDG }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noneMissingInPTKBDG }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noneMissingInPTKBDG }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .other }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .missingG }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .other }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .other }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .noneMissingInPTKBDG }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .noneMissingInPTKBDG }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .noneMissingInPTKBDG }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .other }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .other }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .noneMissingInPTKBDG }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .other }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .missingP }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .other }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .noneMissingInPTKBDG }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noneMissingInPTKBDG }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .missingG }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .other }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .other }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .other }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .missingG }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .missingP }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noneMissingInPTKBDG }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noneMissingInPTKBDG }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .other }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noneMissingInPTKBDG }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noneMissingInPTKBDG }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noneMissingInPTKBDG }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .missingG }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .noneMissingInPTKBDG }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .noneMissingInPTKBDG }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noneMissingInPTKBDG }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .other }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noneMissingInPTKBDG }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .noneMissingInPTKBDG }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noneMissingInPTKBDG }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .missingG }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noneMissingInPTKBDG }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .other }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .noneMissingInPTKBDG }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .noneMissingInPTKBDG }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .other }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .missingG }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .noneMissingInPTKBDG }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .other }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .other }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noneMissingInPTKBDG }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .other }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .other }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .other }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .other }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .noneMissingInPTKBDG }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .noneMissingInPTKBDG }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .other }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .other }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .noneMissingInPTKBDG }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .other }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .noneMissingInPTKBDG }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .noneMissingInPTKBDG }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .other }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .noneMissingInPTKBDG }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .noneMissingInPTKBDG }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .other }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .noneMissingInPTKBDG }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noneMissingInPTKBDG }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .missingP }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .other }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .other }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noneMissingInPTKBDG }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .missingG }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .missingG }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .other }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .noneMissingInPTKBDG }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .noneMissingInPTKBDG }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .noneMissingInPTKBDG }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .bothMissing }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .other }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noneMissingInPTKBDG }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .other }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .noneMissingInPTKBDG }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .missingG }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .other }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .other }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noneMissingInPTKBDG }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noneMissingInPTKBDG }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .noneMissingInPTKBDG }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .other }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .other }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .noneMissingInPTKBDG }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .noneMissingInPTKBDG }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .missingG }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .other }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .other }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .noneMissingInPTKBDG }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .missingP }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .noneMissingInPTKBDG }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .noneMissingInPTKBDG }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .noneMissingInPTKBDG }
  , { walsCode := "kgi", language := "Konyagi", iso := "cou", value := .noneMissingInPTKBDG }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .other }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noneMissingInPTKBDG }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .other }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .noneMissingInPTKBDG }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .noneMissingInPTKBDG }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .noneMissingInPTKBDG }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .missingP }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .missingP }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .noneMissingInPTKBDG }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .noneMissingInPTKBDG }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .other }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .other }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .missingP }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .noneMissingInPTKBDG }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .missingP }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .noneMissingInPTKBDG }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .noneMissingInPTKBDG }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .noneMissingInPTKBDG }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .other }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .other }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .noneMissingInPTKBDG }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .other }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noneMissingInPTKBDG }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noneMissingInPTKBDG }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .noneMissingInPTKBDG }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .other }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .other }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .noneMissingInPTKBDG }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noneMissingInPTKBDG }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noneMissingInPTKBDG }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .missingG }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .noneMissingInPTKBDG }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .other }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noneMissingInPTKBDG }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noneMissingInPTKBDG }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .noneMissingInPTKBDG }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .noneMissingInPTKBDG }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .noneMissingInPTKBDG }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .other }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .noneMissingInPTKBDG }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .noneMissingInPTKBDG }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .other }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .other }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .missingG }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .noneMissingInPTKBDG }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .other }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .missingP }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .other }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .missingG }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noneMissingInPTKBDG }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .other }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .noneMissingInPTKBDG }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .noneMissingInPTKBDG }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .other }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .other }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .noneMissingInPTKBDG }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .other }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .other }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .noneMissingInPTKBDG }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .other }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .noneMissingInPTKBDG }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .other }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .other }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noneMissingInPTKBDG }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .other }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .other }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .other }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .other }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .other }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .other }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .noneMissingInPTKBDG }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .other }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .noneMissingInPTKBDG }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noneMissingInPTKBDG }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .noneMissingInPTKBDG }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .noneMissingInPTKBDG }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .other }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .other }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .other }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .other }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .noneMissingInPTKBDG }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .other }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .noneMissingInPTKBDG }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .other }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .noneMissingInPTKBDG }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .noneMissingInPTKBDG }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noneMissingInPTKBDG }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noneMissingInPTKBDG }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noneMissingInPTKBDG }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .other }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .other }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .other }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .other }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .noneMissingInPTKBDG }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .other }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .other }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .missingP }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .other }
  , { walsCode := "nbk", language := "Natügu", iso := "ntu", value := .other }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .other }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .noneMissingInPTKBDG }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .noneMissingInPTKBDG }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noneMissingInPTKBDG }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .other }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .noneMissingInPTKBDG }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .noneMissingInPTKBDG }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .noneMissingInPTKBDG }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .other }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .noneMissingInPTKBDG }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .noneMissingInPTKBDG }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .other }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .noneMissingInPTKBDG }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .noneMissingInPTKBDG }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .other }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .other }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noneMissingInPTKBDG }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .missingP }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .missingP }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .noneMissingInPTKBDG }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .other }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .other }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .other }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .missingG }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .other }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .missingP }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .noneMissingInPTKBDG }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noneMissingInPTKBDG }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .other }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .noneMissingInPTKBDG }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .other }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .other }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .noneMissingInPTKBDG }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .missingP }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noneMissingInPTKBDG }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .other }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .other }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noneMissingInPTKBDG }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .other }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .noneMissingInPTKBDG }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noneMissingInPTKBDG }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .other }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noneMissingInPTKBDG }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .noneMissingInPTKBDG }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .other }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noneMissingInPTKBDG }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .other }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .other }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .other }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .other }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .other }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noneMissingInPTKBDG }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .missingG }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noneMissingInPTKBDG }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .other }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .other }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .other }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .other }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noneMissingInPTKBDG }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noneMissingInPTKBDG }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .other }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noneMissingInPTKBDG }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noneMissingInPTKBDG }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .noneMissingInPTKBDG }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .other }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .other }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .noneMissingInPTKBDG }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noneMissingInPTKBDG }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .noneMissingInPTKBDG }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .noneMissingInPTKBDG }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .noneMissingInPTKBDG }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .noneMissingInPTKBDG }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .noneMissingInPTKBDG }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .other }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .other }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .other }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .other }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .other }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .other }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .other }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noneMissingInPTKBDG }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .noneMissingInPTKBDG }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .other }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .other }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .other }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .other }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .other }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .other }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .other }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .noneMissingInPTKBDG }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .noneMissingInPTKBDG }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .other }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .noneMissingInPTKBDG }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .other }
  , { walsCode := "som", language := "Somali", iso := "som", value := .missingP }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .missingP }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .noneMissingInPTKBDG }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .other }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .other }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .noneMissingInPTKBDG }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noneMissingInPTKBDG }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .missingG }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .missingG }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noneMissingInPTKBDG }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .noneMissingInPTKBDG }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noneMissingInPTKBDG }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .missingG }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noneMissingInPTKBDG }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .missingP }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .other }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .noneMissingInPTKBDG }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .noneMissingInPTKBDG }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .missingP }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .noneMissingInPTKBDG }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .missingG }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .noneMissingInPTKBDG }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .noneMissingInPTKBDG }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .noneMissingInPTKBDG }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .missingG }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .noneMissingInPTKBDG }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .missingG }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .missingG }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noneMissingInPTKBDG }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .noneMissingInPTKBDG }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .other }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .missingP }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .missingP }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .noneMissingInPTKBDG }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .other }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .noneMissingInPTKBDG }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .other }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .other }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .other }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .other }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .noneMissingInPTKBDG }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .other }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .other }
  ]

private def allData_1 : List (Datapoint VoicingAndGapsInPlosiveSystems) :=
  [ { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noneMissingInPTKBDG }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .other }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .other }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .missingP }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .other }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .noneMissingInPTKBDG }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noneMissingInPTKBDG }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noneMissingInPTKBDG }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noneMissingInPTKBDG }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .noneMissingInPTKBDG }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .other }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .bothMissing }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .other }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .other }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .other }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .noneMissingInPTKBDG }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .other }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .other }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .noneMissingInPTKBDG }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .other }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .other }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noneMissingInPTKBDG }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .other }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noneMissingInPTKBDG }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .other }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .other }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .other }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .other }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .other }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noneMissingInPTKBDG }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .other }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .other }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .other }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .other }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .missingG }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .other }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .noneMissingInPTKBDG }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .noneMissingInPTKBDG }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .other }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .noneMissingInPTKBDG }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .other }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .noneMissingInPTKBDG }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .noneMissingInPTKBDG }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .other }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .noneMissingInPTKBDG }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .other }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .missingP }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .missingG }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .missingG }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .other }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .other }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .noneMissingInPTKBDG }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .other }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .other }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .missingP }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .other }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .noneMissingInPTKBDG }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .other }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noneMissingInPTKBDG }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .noneMissingInPTKBDG }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .noneMissingInPTKBDG }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .other }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .other }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .noneMissingInPTKBDG }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .other }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .other }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .other }
  ]

/-- Complete WALS 5A dataset (567 languages). -/
def allData : List (Datapoint VoicingAndGapsInPlosiveSystems) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 567 := by native_decide

theorem count_other :
    (allData.filter (·.value == .other)).length = 242 := by native_decide
theorem count_noneMissingInPTKBDG :
    (allData.filter (·.value == .noneMissingInPTKBDG)).length = 255 := by native_decide
theorem count_missingP :
    (allData.filter (·.value == .missingP)).length = 33 := by native_decide
theorem count_missingG :
    (allData.filter (·.value == .missingG)).length = 34 := by native_decide
theorem count_bothMissing :
    (allData.filter (·.value == .bothMissing)).length = 3 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F5A
