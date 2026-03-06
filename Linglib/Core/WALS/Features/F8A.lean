/-!
# WALS Feature 8A: Lateral Consonants
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 8A`.

Chapter 8, 567 languages.
-/

namespace Core.WALS.F8A

/-- WALS 8A values. -/
inductive LateralConsonants where
  | noLaterals  -- No laterals (95 languages)
  | lNoObstruentLaterals  -- /l/, no obstruent laterals (388 languages)
  | lateralsButNoLNoObstruentLaterals  -- Laterals, but no /l/, no obstruent laterals (29 languages)
  | lAndLateralObstruent  -- /l/ and lateral obstruent (47 languages)
  | noLButLateralObstruents  -- No /l/, but lateral obstruents (8 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 8A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : LateralConsonants
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .lNoObstruentLaterals }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .noLaterals }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .lNoObstruentLaterals }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .lNoObstruentLaterals }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .lNoObstruentLaterals }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noLaterals }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noLaterals }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .lNoObstruentLaterals }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .noLButLateralObstruents }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noLaterals }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .lNoObstruentLaterals }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noLaterals }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .noLaterals }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .lAndLateralObstruent }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noLaterals }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .lNoObstruentLaterals }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .lNoObstruentLaterals }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .lNoObstruentLaterals }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .lNoObstruentLaterals }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .noLaterals }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .lNoObstruentLaterals }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .lNoObstruentLaterals }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .lNoObstruentLaterals }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .lNoObstruentLaterals }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .noLaterals }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .lNoObstruentLaterals }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .lNoObstruentLaterals }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .noLaterals }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noLaterals }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .noLaterals }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .lNoObstruentLaterals }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .lNoObstruentLaterals }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .lNoObstruentLaterals }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .lAndLateralObstruent }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .lNoObstruentLaterals }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .lNoObstruentLaterals }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noLaterals }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .lNoObstruentLaterals }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .lAndLateralObstruent }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .lAndLateralObstruent }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .lNoObstruentLaterals }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .lNoObstruentLaterals }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .lNoObstruentLaterals }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .lNoObstruentLaterals }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .lNoObstruentLaterals }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .lNoObstruentLaterals }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .lNoObstruentLaterals }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .lNoObstruentLaterals }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .lNoObstruentLaterals }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .lNoObstruentLaterals }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .lNoObstruentLaterals }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .lNoObstruentLaterals }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .lNoObstruentLaterals }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .lNoObstruentLaterals }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .lNoObstruentLaterals }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .lNoObstruentLaterals }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .lNoObstruentLaterals }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .lNoObstruentLaterals }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .lNoObstruentLaterals }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .lNoObstruentLaterals }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .lNoObstruentLaterals }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .lNoObstruentLaterals }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .lNoObstruentLaterals }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .lNoObstruentLaterals }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .lNoObstruentLaterals }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .lNoObstruentLaterals }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noLaterals }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .lNoObstruentLaterals }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .lNoObstruentLaterals }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .lNoObstruentLaterals }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noLaterals }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .lNoObstruentLaterals }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .lNoObstruentLaterals }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .lNoObstruentLaterals }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .lNoObstruentLaterals }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .lNoObstruentLaterals }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .lNoObstruentLaterals }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .lNoObstruentLaterals }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .noLaterals }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .lNoObstruentLaterals }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noLaterals }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .lNoObstruentLaterals }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .lNoObstruentLaterals }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .lNoObstruentLaterals }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noLaterals }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .lNoObstruentLaterals }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .lNoObstruentLaterals }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noLaterals }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .lNoObstruentLaterals }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .lNoObstruentLaterals }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .lNoObstruentLaterals }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .lNoObstruentLaterals }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .lNoObstruentLaterals }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .lAndLateralObstruent }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .lNoObstruentLaterals }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .lNoObstruentLaterals }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .lNoObstruentLaterals }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .lAndLateralObstruent }
  , { walsCode := "cve", language := "Chuave", iso := "cjv", value := .noLaterals }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noLButLateralObstruents }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .lNoObstruentLaterals }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .lNoObstruentLaterals }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .lAndLateralObstruent }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .noLaterals }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noLaterals }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .lAndLateralObstruent }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noLaterals }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noLaterals }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .noLaterals }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noLaterals }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .lNoObstruentLaterals }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .lNoObstruentLaterals }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .lAndLateralObstruent }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .lNoObstruentLaterals }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .lNoObstruentLaterals }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .lNoObstruentLaterals }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .lNoObstruentLaterals }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .lNoObstruentLaterals }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .noLaterals }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .lNoObstruentLaterals }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .lNoObstruentLaterals }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .lNoObstruentLaterals }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .lNoObstruentLaterals }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .lNoObstruentLaterals }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .lNoObstruentLaterals }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .noLaterals }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .lNoObstruentLaterals }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .lNoObstruentLaterals }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .lNoObstruentLaterals }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .lNoObstruentLaterals }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .lNoObstruentLaterals }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .noLaterals }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .noLaterals }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "eng", language := "English", iso := "eng", value := .lNoObstruentLaterals }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noLaterals }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .lNoObstruentLaterals }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .lNoObstruentLaterals }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .lNoObstruentLaterals }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .lNoObstruentLaterals }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .lAndLateralObstruent }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .noLaterals }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .noLaterals }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .lNoObstruentLaterals }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .lNoObstruentLaterals }
  , { walsCode := "fre", language := "French", iso := "fra", value := .lNoObstruentLaterals }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .lNoObstruentLaterals }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .lNoObstruentLaterals }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .lNoObstruentLaterals }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .lNoObstruentLaterals }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .noLaterals }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noLaterals }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .lNoObstruentLaterals }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .lNoObstruentLaterals }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .lNoObstruentLaterals }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "ger", language := "German", iso := "deu", value := .lNoObstruentLaterals }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .lNoObstruentLaterals }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .lNoObstruentLaterals }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .lNoObstruentLaterals }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .lAndLateralObstruent }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .lNoObstruentLaterals }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .lNoObstruentLaterals }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .lNoObstruentLaterals }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .lNoObstruentLaterals }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .lNoObstruentLaterals }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .lAndLateralObstruent }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .lAndLateralObstruent }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .lNoObstruentLaterals }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .lNoObstruentLaterals }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noLaterals }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .lNoObstruentLaterals }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .lNoObstruentLaterals }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .lNoObstruentLaterals }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .lNoObstruentLaterals }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .lNoObstruentLaterals }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .noLaterals }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .lNoObstruentLaterals }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .lNoObstruentLaterals }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .noLaterals }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .lNoObstruentLaterals }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .lAndLateralObstruent }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .lAndLateralObstruent }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .lNoObstruentLaterals }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .lNoObstruentLaterals }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .lNoObstruentLaterals }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .lNoObstruentLaterals }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .lNoObstruentLaterals }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noLaterals }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .lNoObstruentLaterals }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .lNoObstruentLaterals }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .lNoObstruentLaterals }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .lNoObstruentLaterals }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .lNoObstruentLaterals }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .lAndLateralObstruent }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noLaterals }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .lNoObstruentLaterals }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .lNoObstruentLaterals }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .lAndLateralObstruent }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .lNoObstruentLaterals }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .lNoObstruentLaterals }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .noLaterals }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .lNoObstruentLaterals }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noLaterals }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .lNoObstruentLaterals }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .lNoObstruentLaterals }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .lNoObstruentLaterals }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .lNoObstruentLaterals }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .lNoObstruentLaterals }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noLaterals }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .noLaterals }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .lNoObstruentLaterals }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .lNoObstruentLaterals }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .noLButLateralObstruents }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .lNoObstruentLaterals }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .noLaterals }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .lNoObstruentLaterals }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .lAndLateralObstruent }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .lNoObstruentLaterals }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .lAndLateralObstruent }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .lNoObstruentLaterals }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .lNoObstruentLaterals }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .lNoObstruentLaterals }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noLaterals }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .lNoObstruentLaterals }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .lNoObstruentLaterals }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .lNoObstruentLaterals }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .lNoObstruentLaterals }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .lNoObstruentLaterals }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .lNoObstruentLaterals }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .lNoObstruentLaterals }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .lNoObstruentLaterals }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .lNoObstruentLaterals }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .lNoObstruentLaterals }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .lNoObstruentLaterals }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .lNoObstruentLaterals }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .lNoObstruentLaterals }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .noLButLateralObstruents }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .lNoObstruentLaterals }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noLaterals }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .lNoObstruentLaterals }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .noLaterals }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .lNoObstruentLaterals }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .noLaterals }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .lAndLateralObstruent }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .lNoObstruentLaterals }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .noLaterals }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .lNoObstruentLaterals }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .lNoObstruentLaterals }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .lNoObstruentLaterals }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .lNoObstruentLaterals }
  , { walsCode := "kgi", language := "Konyagi", iso := "cou", value := .lNoObstruentLaterals }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .lNoObstruentLaterals }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .lNoObstruentLaterals }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .lNoObstruentLaterals }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .lNoObstruentLaterals }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .lNoObstruentLaterals }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .lNoObstruentLaterals }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .lNoObstruentLaterals }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .lNoObstruentLaterals }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .noLaterals }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .lNoObstruentLaterals }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .lNoObstruentLaterals }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .lNoObstruentLaterals }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .lNoObstruentLaterals }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .lNoObstruentLaterals }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .lNoObstruentLaterals }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .lNoObstruentLaterals }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .lNoObstruentLaterals }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .lNoObstruentLaterals }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noLButLateralObstruents }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .lNoObstruentLaterals }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .lAndLateralObstruent }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .noLaterals }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .lNoObstruentLaterals }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .lNoObstruentLaterals }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .lNoObstruentLaterals }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .lNoObstruentLaterals }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .lNoObstruentLaterals }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .lAndLateralObstruent }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .lNoObstruentLaterals }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .lNoObstruentLaterals }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .lNoObstruentLaterals }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .lNoObstruentLaterals }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .lNoObstruentLaterals }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .lNoObstruentLaterals }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .lNoObstruentLaterals }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .lNoObstruentLaterals }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .lNoObstruentLaterals }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .lNoObstruentLaterals }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .lAndLateralObstruent }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .lNoObstruentLaterals }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .lNoObstruentLaterals }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .lNoObstruentLaterals }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .lNoObstruentLaterals }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .lNoObstruentLaterals }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .lNoObstruentLaterals }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .lAndLateralObstruent }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .lNoObstruentLaterals }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .lNoObstruentLaterals }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .lNoObstruentLaterals }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .lNoObstruentLaterals }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .lNoObstruentLaterals }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .lNoObstruentLaterals }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .lNoObstruentLaterals }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noLaterals }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .lNoObstruentLaterals }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .lNoObstruentLaterals }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .lNoObstruentLaterals }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .lAndLateralObstruent }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .lNoObstruentLaterals }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .lNoObstruentLaterals }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .lNoObstruentLaterals }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .lNoObstruentLaterals }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .noLaterals }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noLaterals }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .lNoObstruentLaterals }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .lNoObstruentLaterals }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .lNoObstruentLaterals }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .lNoObstruentLaterals }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .lNoObstruentLaterals }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .lNoObstruentLaterals }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .lNoObstruentLaterals }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .noLaterals }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .lNoObstruentLaterals }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .noLaterals }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .lNoObstruentLaterals }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .lNoObstruentLaterals }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .lNoObstruentLaterals }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .noLaterals }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .lNoObstruentLaterals }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .lAndLateralObstruent }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .noLaterals }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .lNoObstruentLaterals }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .lNoObstruentLaterals }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .lNoObstruentLaterals }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .lNoObstruentLaterals }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .lNoObstruentLaterals }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noLaterals }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noLaterals }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .lNoObstruentLaterals }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .lNoObstruentLaterals }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .lNoObstruentLaterals }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .lNoObstruentLaterals }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noLaterals }
  , { walsCode := "nbk", language := "Natügu", iso := "ntu", value := .lNoObstruentLaterals }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .lAndLateralObstruent }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .lNoObstruentLaterals }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .lNoObstruentLaterals }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .lNoObstruentLaterals }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .lNoObstruentLaterals }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .lNoObstruentLaterals }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .lNoObstruentLaterals }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .lNoObstruentLaterals }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .lAndLateralObstruent }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .lNoObstruentLaterals }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .lNoObstruentLaterals }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .lNoObstruentLaterals }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .lAndLateralObstruent }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .noLaterals }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .lNoObstruentLaterals }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .lNoObstruentLaterals }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noLaterals }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .lNoObstruentLaterals }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .lNoObstruentLaterals }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .lNoObstruentLaterals }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .lNoObstruentLaterals }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .lNoObstruentLaterals }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noLButLateralObstruents }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .lNoObstruentLaterals }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .lNoObstruentLaterals }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .lNoObstruentLaterals }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .lNoObstruentLaterals }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .noLaterals }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .lNoObstruentLaterals }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .lNoObstruentLaterals }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .lNoObstruentLaterals }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .lNoObstruentLaterals }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .lNoObstruentLaterals }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .lNoObstruentLaterals }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .lNoObstruentLaterals }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .lNoObstruentLaterals }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .noLaterals }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .lNoObstruentLaterals }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .lNoObstruentLaterals }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noLaterals }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .lNoObstruentLaterals }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .lNoObstruentLaterals }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .lNoObstruentLaterals }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noLaterals }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .lNoObstruentLaterals }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .lNoObstruentLaterals }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .lNoObstruentLaterals }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .lNoObstruentLaterals }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .lNoObstruentLaterals }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .lNoObstruentLaterals }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .lNoObstruentLaterals }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .lNoObstruentLaterals }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .lNoObstruentLaterals }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .lNoObstruentLaterals }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .lAndLateralObstruent }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .lNoObstruentLaterals }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noLaterals }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noLaterals }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .lNoObstruentLaterals }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .lNoObstruentLaterals }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .noLaterals }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .noLaterals }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .lNoObstruentLaterals }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .lNoObstruentLaterals }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .lNoObstruentLaterals }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .lNoObstruentLaterals }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .lNoObstruentLaterals }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .lAndLateralObstruent }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .lNoObstruentLaterals }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noLaterals }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .lNoObstruentLaterals }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .lNoObstruentLaterals }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .lNoObstruentLaterals }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .lNoObstruentLaterals }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .lNoObstruentLaterals }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .lNoObstruentLaterals }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .lNoObstruentLaterals }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .lNoObstruentLaterals }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noLaterals }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noLaterals }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .lNoObstruentLaterals }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .noLaterals }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noLaterals }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .noLaterals }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .lAndLateralObstruent }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .lNoObstruentLaterals }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .lNoObstruentLaterals }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .noLaterals }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .noLaterals }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .lAndLateralObstruent }
  , { walsCode := "som", language := "Somali", iso := "som", value := .lNoObstruentLaterals }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .lNoObstruentLaterals }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .lNoObstruentLaterals }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .lNoObstruentLaterals }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .lAndLateralObstruent }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .lNoObstruentLaterals }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noLaterals }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .lNoObstruentLaterals }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .lNoObstruentLaterals }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .lNoObstruentLaterals }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .lNoObstruentLaterals }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .lNoObstruentLaterals }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noLaterals }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .lNoObstruentLaterals }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .lNoObstruentLaterals }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .lNoObstruentLaterals }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .lNoObstruentLaterals }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .lNoObstruentLaterals }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .lNoObstruentLaterals }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .lNoObstruentLaterals }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .lAndLateralObstruent }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .lNoObstruentLaterals }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .lNoObstruentLaterals }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .lNoObstruentLaterals }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .lNoObstruentLaterals }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .lAndLateralObstruent }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .lNoObstruentLaterals }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .lNoObstruentLaterals }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .lNoObstruentLaterals }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .noLaterals }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noLButLateralObstruents }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .lNoObstruentLaterals }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .lNoObstruentLaterals }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .lAndLateralObstruent }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .lNoObstruentLaterals }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .lNoObstruentLaterals }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noLButLateralObstruents }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .lNoObstruentLaterals }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .lNoObstruentLaterals }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .lNoObstruentLaterals }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .lNoObstruentLaterals }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .lAndLateralObstruent }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .lAndLateralObstruent }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .lAndLateralObstruent }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .noLaterals }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .lAndLateralObstruent }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .lNoObstruentLaterals }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .lNoObstruentLaterals }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .lNoObstruentLaterals }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .lNoObstruentLaterals }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .lNoObstruentLaterals }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .lNoObstruentLaterals }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .lNoObstruentLaterals }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .lNoObstruentLaterals }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .lNoObstruentLaterals }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .lNoObstruentLaterals }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noLaterals }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noLaterals }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .lNoObstruentLaterals }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .lNoObstruentLaterals }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .lNoObstruentLaterals }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .noLaterals }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .lNoObstruentLaterals }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .noLaterals }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noLaterals }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .noLaterals }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .lNoObstruentLaterals }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .lNoObstruentLaterals }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .lNoObstruentLaterals }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noLaterals }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .lNoObstruentLaterals }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .lNoObstruentLaterals }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .lNoObstruentLaterals }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noLaterals }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .lNoObstruentLaterals }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .lNoObstruentLaterals }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .lAndLateralObstruent }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .lAndLateralObstruent }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .lNoObstruentLaterals }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .lNoObstruentLaterals }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .lNoObstruentLaterals }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noLaterals }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .lNoObstruentLaterals }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .lNoObstruentLaterals }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .lNoObstruentLaterals }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .lNoObstruentLaterals }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .noLaterals }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .noLaterals }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .lNoObstruentLaterals }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .lNoObstruentLaterals }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .lNoObstruentLaterals }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .lNoObstruentLaterals }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .lNoObstruentLaterals }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .lNoObstruentLaterals }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .lNoObstruentLaterals }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .lAndLateralObstruent }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .lNoObstruentLaterals }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .lNoObstruentLaterals }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .lNoObstruentLaterals }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .lNoObstruentLaterals }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .lAndLateralObstruent }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .lateralsButNoLNoObstruentLaterals }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .lNoObstruentLaterals }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .lAndLateralObstruent }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .lAndLateralObstruent }
  ]

/-- Complete WALS 8A dataset (567 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 567 := by native_decide

theorem count_noLaterals :
    (allData.filter (·.value == .noLaterals)).length = 95 := by native_decide
theorem count_lNoObstruentLaterals :
    (allData.filter (·.value == .lNoObstruentLaterals)).length = 388 := by native_decide
theorem count_lateralsButNoLNoObstruentLaterals :
    (allData.filter (·.value == .lateralsButNoLNoObstruentLaterals)).length = 29 := by native_decide
theorem count_lAndLateralObstruent :
    (allData.filter (·.value == .lAndLateralObstruent)).length = 47 := by native_decide
theorem count_noLButLateralObstruents :
    (allData.filter (·.value == .noLButLateralObstruents)).length = 8 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F8A
