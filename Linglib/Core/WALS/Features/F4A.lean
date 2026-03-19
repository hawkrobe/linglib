import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 4A: Voicing in Plosives and Fricatives
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 4A`.

Chapter 4, 567 languages.
-/

namespace Core.WALS.F4A

/-- WALS 4A values. -/
inductive VoicingInPlosivesAndFricatives where
  | noVoicingContrast  -- No voicing contrast (182 languages)
  | inPlosivesAlone  -- In plosives alone (189 languages)
  | inFricativesAlone  -- In fricatives alone (38 languages)
  | inBothPlosivesAndFricatives  -- In both plosives and fricatives (158 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint VoicingInPlosivesAndFricatives) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .inPlosivesAlone }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .inPlosivesAlone }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noVoicingContrast }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .inBothPlosivesAndFricatives }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .noVoicingContrast }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .noVoicingContrast }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .noVoicingContrast }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .inPlosivesAlone }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .inBothPlosivesAndFricatives }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .inFricativesAlone }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noVoicingContrast }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .inBothPlosivesAndFricatives }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .inPlosivesAlone }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .inBothPlosivesAndFricatives }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .inPlosivesAlone }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .inPlosivesAlone }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noVoicingContrast }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .inBothPlosivesAndFricatives }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .inFricativesAlone }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .inBothPlosivesAndFricatives }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .noVoicingContrast }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .inPlosivesAlone }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .inPlosivesAlone }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .inBothPlosivesAndFricatives }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .inFricativesAlone }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .noVoicingContrast }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .inPlosivesAlone }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .noVoicingContrast }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .inFricativesAlone }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .noVoicingContrast }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noVoicingContrast }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .noVoicingContrast }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .inBothPlosivesAndFricatives }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .inPlosivesAlone }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .inBothPlosivesAndFricatives }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .inFricativesAlone }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noVoicingContrast }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noVoicingContrast }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .inFricativesAlone }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .inBothPlosivesAndFricatives }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .inFricativesAlone }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .inBothPlosivesAndFricatives }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .noVoicingContrast }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .inPlosivesAlone }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .inFricativesAlone }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .inPlosivesAlone }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .inBothPlosivesAndFricatives }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .noVoicingContrast }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .noVoicingContrast }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .inPlosivesAlone }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .inPlosivesAlone }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .inPlosivesAlone }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .inFricativesAlone }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .inPlosivesAlone }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .noVoicingContrast }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .inPlosivesAlone }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .noVoicingContrast }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .inBothPlosivesAndFricatives }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .inPlosivesAlone }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .noVoicingContrast }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .inBothPlosivesAndFricatives }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .inPlosivesAlone }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .noVoicingContrast }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .inBothPlosivesAndFricatives }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .inBothPlosivesAndFricatives }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .noVoicingContrast }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .inPlosivesAlone }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noVoicingContrast }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noVoicingContrast }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .inPlosivesAlone }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noVoicingContrast }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noVoicingContrast }
  , { walsCode := "car", language := "Carib", iso := "car", value := .inPlosivesAlone }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .inBothPlosivesAndFricatives }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .inPlosivesAlone }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .inPlosivesAlone }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .noVoicingContrast }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .inPlosivesAlone }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .inPlosivesAlone }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .noVoicingContrast }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .noVoicingContrast }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .inPlosivesAlone }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .inBothPlosivesAndFricatives }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .inPlosivesAlone }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .inFricativesAlone }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .inFricativesAlone }
  , { walsCode := "cve", language := "Chuave", iso := "cjv", value := .inPlosivesAlone }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noVoicingContrast }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .inBothPlosivesAndFricatives }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .noVoicingContrast }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .inBothPlosivesAndFricatives }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noVoicingContrast }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .inPlosivesAlone }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noVoicingContrast }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .inPlosivesAlone }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .noVoicingContrast }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .inPlosivesAlone }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .inBothPlosivesAndFricatives }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .inBothPlosivesAndFricatives }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .inPlosivesAlone }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .inBothPlosivesAndFricatives }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .inBothPlosivesAndFricatives }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noVoicingContrast }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .inPlosivesAlone }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .inPlosivesAlone }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .inFricativesAlone }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .inPlosivesAlone }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .inPlosivesAlone }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noVoicingContrast }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .inBothPlosivesAndFricatives }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noVoicingContrast }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .inPlosivesAlone }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noVoicingContrast }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .inBothPlosivesAndFricatives }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .inBothPlosivesAndFricatives }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .inPlosivesAlone }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noVoicingContrast }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .inPlosivesAlone }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .inPlosivesAlone }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noVoicingContrast }
  , { walsCode := "eng", language := "English", iso := "eng", value := .inBothPlosivesAndFricatives }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .inPlosivesAlone }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .inPlosivesAlone }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .inPlosivesAlone }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .inBothPlosivesAndFricatives }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .inPlosivesAlone }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .noVoicingContrast }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .inBothPlosivesAndFricatives }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noVoicingContrast }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .inBothPlosivesAndFricatives }
  , { walsCode := "fre", language := "French", iso := "fra", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .inBothPlosivesAndFricatives }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .inPlosivesAlone }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .noVoicingContrast }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .inFricativesAlone }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .noVoicingContrast }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .inPlosivesAlone }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noVoicingContrast }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .inBothPlosivesAndFricatives }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .inFricativesAlone }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ger", language := "German", iso := "deu", value := .inBothPlosivesAndFricatives }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .noVoicingContrast }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noVoicingContrast }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .inPlosivesAlone }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .inPlosivesAlone }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .inBothPlosivesAndFricatives }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .inFricativesAlone }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .inBothPlosivesAndFricatives }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .noVoicingContrast }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .inFricativesAlone }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .inBothPlosivesAndFricatives }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .inPlosivesAlone }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .noVoicingContrast }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .noVoicingContrast }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noVoicingContrast }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .inBothPlosivesAndFricatives }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noVoicingContrast }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .inPlosivesAlone }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .inBothPlosivesAndFricatives }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .inPlosivesAlone }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noVoicingContrast }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .noVoicingContrast }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noVoicingContrast }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .inPlosivesAlone }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .inBothPlosivesAndFricatives }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .inBothPlosivesAndFricatives }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .inBothPlosivesAndFricatives }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .noVoicingContrast }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .inBothPlosivesAndFricatives }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .inPlosivesAlone }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .inPlosivesAlone }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .inPlosivesAlone }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noVoicingContrast }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .inBothPlosivesAndFricatives }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .inPlosivesAlone }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .inBothPlosivesAndFricatives }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .inPlosivesAlone }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .inPlosivesAlone }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noVoicingContrast }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .inBothPlosivesAndFricatives }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .inFricativesAlone }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .inPlosivesAlone }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .inPlosivesAlone }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .noVoicingContrast }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noVoicingContrast }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .inBothPlosivesAndFricatives }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .inPlosivesAlone }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .noVoicingContrast }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .noVoicingContrast }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .noVoicingContrast }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .inPlosivesAlone }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .inPlosivesAlone }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noVoicingContrast }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .noVoicingContrast }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .noVoicingContrast }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .noVoicingContrast }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .noVoicingContrast }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .inPlosivesAlone }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .inPlosivesAlone }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .inFricativesAlone }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noVoicingContrast }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .inPlosivesAlone }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .inPlosivesAlone }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .inPlosivesAlone }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noVoicingContrast }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .inPlosivesAlone }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .inPlosivesAlone }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .inPlosivesAlone }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noVoicingContrast }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .noVoicingContrast }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .inPlosivesAlone }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .inPlosivesAlone }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .noVoicingContrast }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .noVoicingContrast }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .inPlosivesAlone }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .inPlosivesAlone }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .inBothPlosivesAndFricatives }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noVoicingContrast }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .noVoicingContrast }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .inPlosivesAlone }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .inPlosivesAlone }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .inPlosivesAlone }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .inPlosivesAlone }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noVoicingContrast }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .inBothPlosivesAndFricatives }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .inPlosivesAlone }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .inPlosivesAlone }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .inPlosivesAlone }
  , { walsCode := "kgi", language := "Konyagi", iso := "cou", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noVoicingContrast }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .noVoicingContrast }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .inPlosivesAlone }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .inPlosivesAlone }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .inPlosivesAlone }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .inPlosivesAlone }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .inPlosivesAlone }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noVoicingContrast }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noVoicingContrast }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .inPlosivesAlone }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .inPlosivesAlone }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .inPlosivesAlone }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .inBothPlosivesAndFricatives }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .inBothPlosivesAndFricatives }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .inPlosivesAlone }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .noVoicingContrast }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .noVoicingContrast }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .inPlosivesAlone }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .inFricativesAlone }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .inBothPlosivesAndFricatives }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .inBothPlosivesAndFricatives }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .inBothPlosivesAndFricatives }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .inFricativesAlone }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .noVoicingContrast }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .inBothPlosivesAndFricatives }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .inPlosivesAlone }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .inBothPlosivesAndFricatives }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .inPlosivesAlone }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .inBothPlosivesAndFricatives }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .noVoicingContrast }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .inBothPlosivesAndFricatives }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .inBothPlosivesAndFricatives }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .inBothPlosivesAndFricatives }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .inPlosivesAlone }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .inBothPlosivesAndFricatives }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .noVoicingContrast }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .inPlosivesAlone }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .inPlosivesAlone }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noVoicingContrast }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .inFricativesAlone }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .inPlosivesAlone }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .noVoicingContrast }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noVoicingContrast }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .inPlosivesAlone }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noVoicingContrast }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .inPlosivesAlone }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .inPlosivesAlone }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .inFricativesAlone }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noVoicingContrast }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noVoicingContrast }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noVoicingContrast }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .inPlosivesAlone }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noVoicingContrast }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .inFricativesAlone }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noVoicingContrast }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noVoicingContrast }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noVoicingContrast }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .noVoicingContrast }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noVoicingContrast }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .noVoicingContrast }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .inFricativesAlone }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .noVoicingContrast }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .inPlosivesAlone }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .inPlosivesAlone }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .noVoicingContrast }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noVoicingContrast }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .inPlosivesAlone }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .inFricativesAlone }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .noVoicingContrast }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .inPlosivesAlone }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .noVoicingContrast }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .inBothPlosivesAndFricatives }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .inPlosivesAlone }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .inPlosivesAlone }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .inPlosivesAlone }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .noVoicingContrast }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noVoicingContrast }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noVoicingContrast }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noVoicingContrast }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .inPlosivesAlone }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .noVoicingContrast }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .noVoicingContrast }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .inPlosivesAlone }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noVoicingContrast }
  , { walsCode := "nbk", language := "Natügu", iso := "ntu", value := .noVoicingContrast }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .inFricativesAlone }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .inPlosivesAlone }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .inPlosivesAlone }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .inBothPlosivesAndFricatives }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .inPlosivesAlone }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .inPlosivesAlone }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .noVoicingContrast }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .inPlosivesAlone }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noVoicingContrast }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .inBothPlosivesAndFricatives }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .inPlosivesAlone }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .noVoicingContrast }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .inFricativesAlone }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .inBothPlosivesAndFricatives }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .inPlosivesAlone }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .inPlosivesAlone }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .inPlosivesAlone }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .noVoicingContrast }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noVoicingContrast }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .noVoicingContrast }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .inPlosivesAlone }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .noVoicingContrast }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .inPlosivesAlone }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .inPlosivesAlone }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .inPlosivesAlone }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .inBothPlosivesAndFricatives }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noVoicingContrast }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noVoicingContrast }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .inBothPlosivesAndFricatives }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .inBothPlosivesAndFricatives }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .inBothPlosivesAndFricatives }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noVoicingContrast }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .noVoicingContrast }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .inBothPlosivesAndFricatives }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .noVoicingContrast }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .inBothPlosivesAndFricatives }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .inBothPlosivesAndFricatives }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noVoicingContrast }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .inBothPlosivesAndFricatives }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .inBothPlosivesAndFricatives }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .inPlosivesAlone }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .inBothPlosivesAndFricatives }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .inBothPlosivesAndFricatives }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .inPlosivesAlone }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noVoicingContrast }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .inFricativesAlone }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noVoicingContrast }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .inBothPlosivesAndFricatives }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .inPlosivesAlone }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .inPlosivesAlone }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .noVoicingContrast }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .noVoicingContrast }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noVoicingContrast }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .inFricativesAlone }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .inPlosivesAlone }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .inPlosivesAlone }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noVoicingContrast }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .inPlosivesAlone }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .inBothPlosivesAndFricatives }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .noVoicingContrast }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .noVoicingContrast }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .inBothPlosivesAndFricatives }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .inBothPlosivesAndFricatives }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .inBothPlosivesAndFricatives }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .inPlosivesAlone }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .inPlosivesAlone }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .inPlosivesAlone }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .inBothPlosivesAndFricatives }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noVoicingContrast }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .inFricativesAlone }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .noVoicingContrast }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .noVoicingContrast }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .noVoicingContrast }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .noVoicingContrast }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .noVoicingContrast }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .inPlosivesAlone }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .inBothPlosivesAndFricatives }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noVoicingContrast }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .inPlosivesAlone }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .noVoicingContrast }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .noVoicingContrast }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noVoicingContrast }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .noVoicingContrast }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .noVoicingContrast }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .inBothPlosivesAndFricatives }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .inPlosivesAlone }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .noVoicingContrast }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .inPlosivesAlone }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .inFricativesAlone }
  , { walsCode := "som", language := "Somali", iso := "som", value := .inPlosivesAlone }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .inBothPlosivesAndFricatives }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .inPlosivesAlone }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .inFricativesAlone }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .noVoicingContrast }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .inPlosivesAlone }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .inPlosivesAlone }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .inBothPlosivesAndFricatives }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .inBothPlosivesAndFricatives }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .inBothPlosivesAndFricatives }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .inBothPlosivesAndFricatives }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .inPlosivesAlone }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .inPlosivesAlone }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .inPlosivesAlone }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .inPlosivesAlone }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .noVoicingContrast }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .inBothPlosivesAndFricatives }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .inBothPlosivesAndFricatives }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .inBothPlosivesAndFricatives }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .inPlosivesAlone }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .inPlosivesAlone }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .inPlosivesAlone }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .inPlosivesAlone }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .inPlosivesAlone }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .inPlosivesAlone }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .inBothPlosivesAndFricatives }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .inPlosivesAlone }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .inPlosivesAlone }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .inPlosivesAlone }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .inPlosivesAlone }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .inPlosivesAlone }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .inBothPlosivesAndFricatives }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .inPlosivesAlone }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .inPlosivesAlone }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noVoicingContrast }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .inPlosivesAlone }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .noVoicingContrast }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .noVoicingContrast }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .noVoicingContrast }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noVoicingContrast }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .inPlosivesAlone }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .noVoicingContrast }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .inPlosivesAlone }
  ]

private def allData_1 : List (Datapoint VoicingInPlosivesAndFricatives) :=
  [ { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .inPlosivesAlone }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .inFricativesAlone }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .inBothPlosivesAndFricatives }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .inBothPlosivesAndFricatives }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .noVoicingContrast }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .inPlosivesAlone }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .inPlosivesAlone }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .inBothPlosivesAndFricatives }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .inPlosivesAlone }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .inPlosivesAlone }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .inFricativesAlone }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .inPlosivesAlone }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noVoicingContrast }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noVoicingContrast }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .inPlosivesAlone }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .inBothPlosivesAndFricatives }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .inFricativesAlone }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .noVoicingContrast }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .inPlosivesAlone }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noVoicingContrast }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .noVoicingContrast }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .inPlosivesAlone }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .inPlosivesAlone }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .inPlosivesAlone }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noVoicingContrast }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .noVoicingContrast }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noVoicingContrast }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noVoicingContrast }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .noVoicingContrast }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .inPlosivesAlone }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .noVoicingContrast }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .noVoicingContrast }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .noVoicingContrast }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .noVoicingContrast }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .inPlosivesAlone }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noVoicingContrast }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .inPlosivesAlone }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .inPlosivesAlone }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .inFricativesAlone }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .inPlosivesAlone }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noVoicingContrast }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .inBothPlosivesAndFricatives }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .inPlosivesAlone }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .noVoicingContrast }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .inPlosivesAlone }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .inPlosivesAlone }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .inPlosivesAlone }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .inPlosivesAlone }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .inPlosivesAlone }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .noVoicingContrast }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .noVoicingContrast }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .inBothPlosivesAndFricatives }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noVoicingContrast }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noVoicingContrast }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .inPlosivesAlone }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .noVoicingContrast }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .inPlosivesAlone }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .noVoicingContrast }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .inPlosivesAlone }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .inPlosivesAlone }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .inBothPlosivesAndFricatives }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .inFricativesAlone }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .noVoicingContrast }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .inBothPlosivesAndFricatives }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noVoicingContrast }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .inFricativesAlone }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .noVoicingContrast }
  ]

/-- Complete WALS 4A dataset (567 languages). -/
def allData : List (Datapoint VoicingInPlosivesAndFricatives) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 567 := by native_decide

theorem count_noVoicingContrast :
    (allData.filter (·.value == .noVoicingContrast)).length = 182 := by native_decide
theorem count_inPlosivesAlone :
    (allData.filter (·.value == .inPlosivesAlone)).length = 189 := by native_decide
theorem count_inFricativesAlone :
    (allData.filter (·.value == .inFricativesAlone)).length = 38 := by native_decide
theorem count_inBothPlosivesAndFricatives :
    (allData.filter (·.value == .inBothPlosivesAndFricatives)).length = 158 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F4A
