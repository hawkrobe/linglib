import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 7A: Glottalized Consonants
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 7A`.

Chapter 7, 567 languages.
-/

namespace Core.WALS.F7A

/-- WALS 7A values. -/
inductive GlottalizedConsonants where
  | noGlottalizedConsonants  -- No glottalized consonants (409 languages)
  | ejectivesOnly  -- Ejectives only (58 languages)
  | implosivesOnly  -- Implosives only (55 languages)
  | glottalizedResonantsOnly  -- Glottalized resonants only (4 languages)
  | ejectivesAndImplosives  -- Ejectives and implosives (14 languages)
  | ejectivesAndGlottalizedResonants  -- Ejectives and glottalized resonants (20 languages)
  | implosivesAndGlottalizedResonants  -- Implosives and glottalized resonants (4 languages)
  | ejectivesImplosivesAndGlottalizedResonants  -- Ejectives, implosives, and glottalized resonants (3 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint GlottalizedConsonants) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .ejectivesOnly }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .noGlottalizedConsonants }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .ejectivesOnly }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .noGlottalizedConsonants }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .noGlottalizedConsonants }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noGlottalizedConsonants }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .noGlottalizedConsonants }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .ejectivesOnly }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .noGlottalizedConsonants }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .noGlottalizedConsonants }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .implosivesOnly }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .noGlottalizedConsonants }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .noGlottalizedConsonants }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .noGlottalizedConsonants }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noGlottalizedConsonants }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .noGlottalizedConsonants }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .noGlottalizedConsonants }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .noGlottalizedConsonants }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .noGlottalizedConsonants }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .noGlottalizedConsonants }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .noGlottalizedConsonants }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .ejectivesOnly }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .noGlottalizedConsonants }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .noGlottalizedConsonants }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .noGlottalizedConsonants }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .noGlottalizedConsonants }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .noGlottalizedConsonants }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .implosivesOnly }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .noGlottalizedConsonants }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .noGlottalizedConsonants }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noGlottalizedConsonants }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .noGlottalizedConsonants }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .noGlottalizedConsonants }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noGlottalizedConsonants }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .noGlottalizedConsonants }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .ejectivesOnly }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .ejectivesOnly }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .noGlottalizedConsonants }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .noGlottalizedConsonants }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .noGlottalizedConsonants }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .ejectivesOnly }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .noGlottalizedConsonants }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .noGlottalizedConsonants }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .ejectivesOnly }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .noGlottalizedConsonants }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .implosivesOnly }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .noGlottalizedConsonants }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .noGlottalizedConsonants }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .noGlottalizedConsonants }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .noGlottalizedConsonants }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .noGlottalizedConsonants }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .noGlottalizedConsonants }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .noGlottalizedConsonants }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .noGlottalizedConsonants }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .noGlottalizedConsonants }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .noGlottalizedConsonants }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .noGlottalizedConsonants }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .noGlottalizedConsonants }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .noGlottalizedConsonants }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noGlottalizedConsonants }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .ejectivesOnly }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .noGlottalizedConsonants }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .noGlottalizedConsonants }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .ejectivesOnly }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .noGlottalizedConsonants }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .noGlottalizedConsonants }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .noGlottalizedConsonants }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .noGlottalizedConsonants }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .noGlottalizedConsonants }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .noGlottalizedConsonants }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .implosivesOnly }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .noGlottalizedConsonants }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .noGlottalizedConsonants }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .noGlottalizedConsonants }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .noGlottalizedConsonants }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .noGlottalizedConsonants }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noGlottalizedConsonants }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noGlottalizedConsonants }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .implosivesOnly }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .noGlottalizedConsonants }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .ejectivesOnly }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noGlottalizedConsonants }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .noGlottalizedConsonants }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .noGlottalizedConsonants }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .noGlottalizedConsonants }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .noGlottalizedConsonants }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noGlottalizedConsonants }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noGlottalizedConsonants }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .noGlottalizedConsonants }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .noGlottalizedConsonants }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .implosivesOnly }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .noGlottalizedConsonants }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .noGlottalizedConsonants }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .ejectivesOnly }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .noGlottalizedConsonants }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .noGlottalizedConsonants }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .glottalizedResonantsOnly }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .noGlottalizedConsonants }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .glottalizedResonantsOnly }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .ejectivesOnly }
  , { walsCode := "cve", language := "Chuave", iso := "cjv", value := .noGlottalizedConsonants }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noGlottalizedConsonants }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noGlottalizedConsonants }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .noGlottalizedConsonants }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .noGlottalizedConsonants }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .noGlottalizedConsonants }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .noGlottalizedConsonants }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .ejectivesOnly }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .noGlottalizedConsonants }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noGlottalizedConsonants }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .noGlottalizedConsonants }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .noGlottalizedConsonants }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .noGlottalizedConsonants }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .noGlottalizedConsonants }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .ejectivesAndImplosives }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .implosivesOnly }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .implosivesOnly }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .implosivesOnly }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noGlottalizedConsonants }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .noGlottalizedConsonants }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .ejectivesAndImplosives }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noGlottalizedConsonants }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noGlottalizedConsonants }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noGlottalizedConsonants }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noGlottalizedConsonants }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .ejectivesOnly }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .noGlottalizedConsonants }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .noGlottalizedConsonants }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .noGlottalizedConsonants }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .implosivesOnly }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .noGlottalizedConsonants }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .noGlottalizedConsonants }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .noGlottalizedConsonants }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .noGlottalizedConsonants }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .noGlottalizedConsonants }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .noGlottalizedConsonants }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noGlottalizedConsonants }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noGlottalizedConsonants }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .noGlottalizedConsonants }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .noGlottalizedConsonants }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .noGlottalizedConsonants }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .noGlottalizedConsonants }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .ejectivesOnly }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .noGlottalizedConsonants }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .noGlottalizedConsonants }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noGlottalizedConsonants }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .noGlottalizedConsonants }
  , { walsCode := "fre", language := "French", iso := "fra", value := .noGlottalizedConsonants }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .noGlottalizedConsonants }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .noGlottalizedConsonants }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .noGlottalizedConsonants }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .implosivesOnly }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .noGlottalizedConsonants }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noGlottalizedConsonants }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .noGlottalizedConsonants }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .implosivesOnly }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .noGlottalizedConsonants }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .ejectivesOnly }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noGlottalizedConsonants }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .noGlottalizedConsonants }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .noGlottalizedConsonants }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .noGlottalizedConsonants }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .noGlottalizedConsonants }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .noGlottalizedConsonants }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noGlottalizedConsonants }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .noGlottalizedConsonants }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .noGlottalizedConsonants }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .noGlottalizedConsonants }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .implosivesOnly }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .noGlottalizedConsonants }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .ejectivesOnly }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .noGlottalizedConsonants }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .ejectivesAndImplosives }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .noGlottalizedConsonants }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .ejectivesAndImplosives }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .noGlottalizedConsonants }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .noGlottalizedConsonants }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .noGlottalizedConsonants }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noGlottalizedConsonants }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .noGlottalizedConsonants }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .noGlottalizedConsonants }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .ejectivesOnly }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .noGlottalizedConsonants }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .noGlottalizedConsonants }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .noGlottalizedConsonants }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .ejectivesOnly }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .ejectivesOnly }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .noGlottalizedConsonants }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .noGlottalizedConsonants }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noGlottalizedConsonants }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .noGlottalizedConsonants }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .noGlottalizedConsonants }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .ejectivesAndImplosives }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .noGlottalizedConsonants }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .noGlottalizedConsonants }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .noGlottalizedConsonants }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .noGlottalizedConsonants }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .ejectivesOnly }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .noGlottalizedConsonants }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .ejectivesAndImplosives }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noGlottalizedConsonants }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .noGlottalizedConsonants }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .noGlottalizedConsonants }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .ejectivesOnly }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .ejectivesOnly }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .noGlottalizedConsonants }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .noGlottalizedConsonants }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .ejectivesOnly }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .noGlottalizedConsonants }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .noGlottalizedConsonants }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .ejectivesOnly }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .noGlottalizedConsonants }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .implosivesOnly }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .noGlottalizedConsonants }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .noGlottalizedConsonants }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .noGlottalizedConsonants }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .ejectivesOnly }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .ejectivesAndImplosives }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .ejectivesOnly }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .implosivesOnly }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .noGlottalizedConsonants }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .noGlottalizedConsonants }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .noGlottalizedConsonants }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .noGlottalizedConsonants }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .implosivesOnly }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .noGlottalizedConsonants }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noGlottalizedConsonants }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .implosivesOnly }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .noGlottalizedConsonants }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .noGlottalizedConsonants }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noGlottalizedConsonants }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .noGlottalizedConsonants }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noGlottalizedConsonants }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .noGlottalizedConsonants }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .ejectivesOnly }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .implosivesOnly }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .noGlottalizedConsonants }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .noGlottalizedConsonants }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .noGlottalizedConsonants }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .noGlottalizedConsonants }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .noGlottalizedConsonants }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .noGlottalizedConsonants }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .implosivesOnly }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .implosivesAndGlottalizedResonants }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noGlottalizedConsonants }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .ejectivesOnly }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .noGlottalizedConsonants }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .noGlottalizedConsonants }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .implosivesOnly }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .noGlottalizedConsonants }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .noGlottalizedConsonants }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .noGlottalizedConsonants }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .noGlottalizedConsonants }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .implosivesOnly }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .noGlottalizedConsonants }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .noGlottalizedConsonants }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .ejectivesAndImplosives }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .noGlottalizedConsonants }
  , { walsCode := "kgi", language := "Konyagi", iso := "cou", value := .implosivesOnly }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .ejectivesOnly }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .noGlottalizedConsonants }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .noGlottalizedConsonants }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .noGlottalizedConsonants }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .ejectivesAndImplosives }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .noGlottalizedConsonants }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noGlottalizedConsonants }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .noGlottalizedConsonants }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .noGlottalizedConsonants }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .implosivesOnly }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .implosivesOnly }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .noGlottalizedConsonants }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .ejectivesAndImplosives }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .noGlottalizedConsonants }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noGlottalizedConsonants }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .noGlottalizedConsonants }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .noGlottalizedConsonants }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .noGlottalizedConsonants }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .noGlottalizedConsonants }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .noGlottalizedConsonants }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noGlottalizedConsonants }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .noGlottalizedConsonants }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .ejectivesOnly }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .ejectivesOnly }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .implosivesOnly }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .implosivesOnly }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noGlottalizedConsonants }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .noGlottalizedConsonants }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .noGlottalizedConsonants }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .noGlottalizedConsonants }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .noGlottalizedConsonants }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .noGlottalizedConsonants }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .ejectivesOnly }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .noGlottalizedConsonants }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .implosivesOnly }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .implosivesAndGlottalizedResonants }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .noGlottalizedConsonants }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .noGlottalizedConsonants }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .ejectivesImplosivesAndGlottalizedResonants }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .noGlottalizedConsonants }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .noGlottalizedConsonants }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .noGlottalizedConsonants }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .noGlottalizedConsonants }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .implosivesOnly }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noGlottalizedConsonants }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .ejectivesAndImplosives }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .ejectivesOnly }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .noGlottalizedConsonants }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .noGlottalizedConsonants }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .noGlottalizedConsonants }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .noGlottalizedConsonants }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .noGlottalizedConsonants }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .noGlottalizedConsonants }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .noGlottalizedConsonants }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noGlottalizedConsonants }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .noGlottalizedConsonants }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .noGlottalizedConsonants }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noGlottalizedConsonants }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .implosivesOnly }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .noGlottalizedConsonants }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noGlottalizedConsonants }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .noGlottalizedConsonants }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noGlottalizedConsonants }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .noGlottalizedConsonants }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .noGlottalizedConsonants }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .noGlottalizedConsonants }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .ejectivesImplosivesAndGlottalizedResonants }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .noGlottalizedConsonants }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .implosivesOnly }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .noGlottalizedConsonants }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .implosivesOnly }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .noGlottalizedConsonants }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .noGlottalizedConsonants }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .noGlottalizedConsonants }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .noGlottalizedConsonants }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .noGlottalizedConsonants }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noGlottalizedConsonants }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .noGlottalizedConsonants }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .noGlottalizedConsonants }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .noGlottalizedConsonants }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .noGlottalizedConsonants }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .implosivesOnly }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .noGlottalizedConsonants }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .implosivesOnly }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .noGlottalizedConsonants }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .implosivesOnly }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .noGlottalizedConsonants }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .noGlottalizedConsonants }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noGlottalizedConsonants }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .noGlottalizedConsonants }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .ejectivesImplosivesAndGlottalizedResonants }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .noGlottalizedConsonants }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .noGlottalizedConsonants }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .noGlottalizedConsonants }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .noGlottalizedConsonants }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .noGlottalizedConsonants }
  , { walsCode := "nbk", language := "Natügu", iso := "ntu", value := .noGlottalizedConsonants }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .ejectivesOnly }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .noGlottalizedConsonants }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .implosivesOnly }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noGlottalizedConsonants }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .noGlottalizedConsonants }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .noGlottalizedConsonants }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .noGlottalizedConsonants }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .noGlottalizedConsonants }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .noGlottalizedConsonants }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .implosivesOnly }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .noGlottalizedConsonants }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .implosivesOnly }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .noGlottalizedConsonants }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .ejectivesOnly }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .noGlottalizedConsonants }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .noGlottalizedConsonants }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .noGlottalizedConsonants }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .noGlottalizedConsonants }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .noGlottalizedConsonants }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .implosivesOnly }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .noGlottalizedConsonants }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .noGlottalizedConsonants }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .implosivesOnly }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .noGlottalizedConsonants }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .noGlottalizedConsonants }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .noGlottalizedConsonants }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .noGlottalizedConsonants }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .implosivesOnly }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .noGlottalizedConsonants }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .noGlottalizedConsonants }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .noGlottalizedConsonants }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .ejectivesAndImplosives }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .noGlottalizedConsonants }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noGlottalizedConsonants }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .implosivesOnly }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noGlottalizedConsonants }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .noGlottalizedConsonants }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .noGlottalizedConsonants }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noGlottalizedConsonants }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .noGlottalizedConsonants }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .implosivesOnly }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .noGlottalizedConsonants }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .noGlottalizedConsonants }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .noGlottalizedConsonants }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .implosivesOnly }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .noGlottalizedConsonants }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .noGlottalizedConsonants }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .noGlottalizedConsonants }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noGlottalizedConsonants }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .noGlottalizedConsonants }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .ejectivesOnly }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .noGlottalizedConsonants }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .noGlottalizedConsonants }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .noGlottalizedConsonants }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .ejectivesOnly }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .ejectivesOnly }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .ejectivesOnly }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .noGlottalizedConsonants }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .noGlottalizedConsonants }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .noGlottalizedConsonants }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noGlottalizedConsonants }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .noGlottalizedConsonants }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .noGlottalizedConsonants }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .noGlottalizedConsonants }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .noGlottalizedConsonants }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .noGlottalizedConsonants }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .ejectivesOnly }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .noGlottalizedConsonants }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .noGlottalizedConsonants }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .ejectivesOnly }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .implosivesOnly }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noGlottalizedConsonants }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .noGlottalizedConsonants }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .noGlottalizedConsonants }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .implosivesAndGlottalizedResonants }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .noGlottalizedConsonants }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .ejectivesOnly }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .noGlottalizedConsonants }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .glottalizedResonantsOnly }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .noGlottalizedConsonants }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .noGlottalizedConsonants }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .noGlottalizedConsonants }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .noGlottalizedConsonants }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .ejectivesOnly }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .noGlottalizedConsonants }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .noGlottalizedConsonants }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .implosivesOnly }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .noGlottalizedConsonants }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .ejectivesOnly }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .noGlottalizedConsonants }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "som", language := "Somali", iso := "som", value := .noGlottalizedConsonants }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .noGlottalizedConsonants }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noGlottalizedConsonants }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .implosivesOnly }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noGlottalizedConsonants }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .implosivesAndGlottalizedResonants }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .noGlottalizedConsonants }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .noGlottalizedConsonants }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .noGlottalizedConsonants }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noGlottalizedConsonants }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .noGlottalizedConsonants }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .noGlottalizedConsonants }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .implosivesOnly }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .noGlottalizedConsonants }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .noGlottalizedConsonants }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .implosivesOnly }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .noGlottalizedConsonants }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .noGlottalizedConsonants }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .ejectivesOnly }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .noGlottalizedConsonants }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .noGlottalizedConsonants }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .noGlottalizedConsonants }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .noGlottalizedConsonants }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .implosivesOnly }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .noGlottalizedConsonants }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .noGlottalizedConsonants }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .noGlottalizedConsonants }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .noGlottalizedConsonants }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .noGlottalizedConsonants }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .ejectivesOnly }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .noGlottalizedConsonants }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .ejectivesOnly }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .noGlottalizedConsonants }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .noGlottalizedConsonants }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .ejectivesOnly }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .noGlottalizedConsonants }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .ejectivesOnly }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noGlottalizedConsonants }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .noGlottalizedConsonants }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .noGlottalizedConsonants }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .ejectivesOnly }
  ]

private def allData_1 : List (Datapoint GlottalizedConsonants) :=
  [ { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .implosivesOnly }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .ejectivesOnly }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .noGlottalizedConsonants }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .implosivesOnly }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .noGlottalizedConsonants }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noGlottalizedConsonants }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .noGlottalizedConsonants }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .noGlottalizedConsonants }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .ejectivesOnly }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .noGlottalizedConsonants }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noGlottalizedConsonants }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .noGlottalizedConsonants }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .noGlottalizedConsonants }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noGlottalizedConsonants }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .noGlottalizedConsonants }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .implosivesOnly }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .noGlottalizedConsonants }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .noGlottalizedConsonants }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .noGlottalizedConsonants }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .noGlottalizedConsonants }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noGlottalizedConsonants }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .implosivesOnly }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noGlottalizedConsonants }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .noGlottalizedConsonants }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .noGlottalizedConsonants }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .glottalizedResonantsOnly }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .noGlottalizedConsonants }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noGlottalizedConsonants }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .noGlottalizedConsonants }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .noGlottalizedConsonants }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .ejectivesOnly }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .noGlottalizedConsonants }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .noGlottalizedConsonants }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .noGlottalizedConsonants }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .noGlottalizedConsonants }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .implosivesOnly }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .noGlottalizedConsonants }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .noGlottalizedConsonants }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .ejectivesOnly }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .noGlottalizedConsonants }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .noGlottalizedConsonants }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .noGlottalizedConsonants }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .noGlottalizedConsonants }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .noGlottalizedConsonants }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .noGlottalizedConsonants }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .noGlottalizedConsonants }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .ejectivesOnly }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noGlottalizedConsonants }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .noGlottalizedConsonants }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noGlottalizedConsonants }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .ejectivesAndImplosives }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .noGlottalizedConsonants }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noGlottalizedConsonants }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .noGlottalizedConsonants }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .implosivesOnly }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .noGlottalizedConsonants }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .ejectivesAndGlottalizedResonants }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .noGlottalizedConsonants }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noGlottalizedConsonants }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .ejectivesAndImplosives }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .ejectivesOnly }
  ]

/-- Complete WALS 7A dataset (567 languages). -/
def allData : List (Datapoint GlottalizedConsonants) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 567 := by native_decide

theorem count_noGlottalizedConsonants :
    (allData.filter (·.value == .noGlottalizedConsonants)).length = 409 := by native_decide
theorem count_ejectivesOnly :
    (allData.filter (·.value == .ejectivesOnly)).length = 58 := by native_decide
theorem count_implosivesOnly :
    (allData.filter (·.value == .implosivesOnly)).length = 55 := by native_decide
theorem count_glottalizedResonantsOnly :
    (allData.filter (·.value == .glottalizedResonantsOnly)).length = 4 := by native_decide
theorem count_ejectivesAndImplosives :
    (allData.filter (·.value == .ejectivesAndImplosives)).length = 14 := by native_decide
theorem count_ejectivesAndGlottalizedResonants :
    (allData.filter (·.value == .ejectivesAndGlottalizedResonants)).length = 20 := by native_decide
theorem count_implosivesAndGlottalizedResonants :
    (allData.filter (·.value == .implosivesAndGlottalizedResonants)).length = 4 := by native_decide
theorem count_ejectivesImplosivesAndGlottalizedResonants :
    (allData.filter (·.value == .ejectivesImplosivesAndGlottalizedResonants)).length = 3 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F7A
