import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 19A: Presence of Uncommon Consonants
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 19A`.

Chapter 19, 567 languages.
-/

namespace Core.WALS.F19A

/-- WALS 19A values. -/
inductive PresenceOfUncommonConsonants where
  | none  -- None (449 languages)
  | clicks  -- Clicks (9 languages)
  | labialVelars  -- Labial-velars (45 languages)
  | pharyngeals  -- Pharyngeals (21 languages)
  | thSounds  -- 'Th' sounds (40 languages)
  | clicksPharyngealsAndTh  -- Clicks, pharyngeals, and 'th' (1 languages)
  | pharyngealsAndTh  -- Pharyngeals and "th" (2 languages)
  deriving DecidableEq, BEq, Repr

private def allData_0 : List (Datapoint PresenceOfUncommonConsonants) :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .clicks }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .clicks }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .none }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .pharyngeals }
  , { walsCode := "acm", language := "Achumawi", iso := "acv", value := .none }
  , { walsCode := "ach", language := "Aché", iso := "guq", value := .none }
  , { walsCode := "aco", language := "Acoma", iso := "kjq", value := .thSounds }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .none }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .labialVelars }
  , { walsCode := "aht", language := "Ahtna", iso := "aht", value := .none }
  , { walsCode := "aik", language := "Aikaná", iso := "tba", value := .none }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .none }
  , { walsCode := "aiz", language := "Aizi", iso := "ahp", value := .labialVelars }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .none }
  , { walsCode := "akw", language := "Akawaio", iso := "ake", value := .none }
  , { walsCode := "abm", language := "Alabama", iso := "akz", value := .none }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .none }
  , { walsCode := "alw", language := "Alawa", iso := "alh", value := .none }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .thSounds }
  , { walsCode := "aea", language := "Aleut (Eastern)", iso := "ale", value := .thSounds }
  , { walsCode := "ald", language := "Alladian", iso := "ald", value := .labialVelars }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .thSounds }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .labialVelars }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .none }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .labialVelars }
  , { walsCode := "amu", language := "Amuesha", iso := "ame", value := .none }
  , { walsCode := "amz", language := "Amuzgo", iso := "amu", value := .none }
  , { walsCode := "adk", language := "Andoke", iso := "ano", value := .none }
  , { walsCode := "ant", language := "Angaataha", iso := "agm", value := .none }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .none }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .none }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .none }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .none }
  , { walsCode := "arb", language := "Arabela", iso := "arl", value := .none }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .pharyngeals }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .none }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .none }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .pharyngeals }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .none }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .none }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .none }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .pharyngeals }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .pharyngeals }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .none }
  , { walsCode := "awn", language := "Awngi", iso := "awn", value := .none }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .none }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .none }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .none }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .none }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .none }
  , { walsCode := "bki", language := "Bakairí", iso := "bkq", value := .none }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .none }
  , { walsCode := "byu", language := "Bandjalang (Yugumbir)", iso := "bdy", value := .none }
  , { walsCode := "brd", language := "Bardi", iso := "bcj", value := .none }
  , { walsCode := "brb", language := "Bariba", iso := "bba", value := .labialVelars }
  , { walsCode := "bsk", language := "Bashkir", iso := "bak", value := .thSounds }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .none }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .none }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .none }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .none }
  , { walsCode := "bee", language := "Beembe", iso := "beq", value := .none }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .none }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .none }
  , { walsCode := "ben", language := "Bengali", iso := "ben", value := .none }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .pharyngeals }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .thSounds }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .labialVelars }
  , { walsCode := "bis", language := "Bisa", iso := "bib", value := .none }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .labialVelars }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .none }
  , { walsCode := "brr", language := "Bororo", iso := "bor", value := .none }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .none }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .pharyngeals }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .none }
  , { walsCode := "bri", language := "Bribri", iso := "bzd", value := .none }
  , { walsCode := "brw", language := "Bru (Western)", iso := "brv", value := .none }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .none }
  , { walsCode := "bua", language := "Burarra", iso := "bvr", value := .none }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .thSounds }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .none }
  , { walsCode := "bet", language := "Bété", iso := "bev", value := .labialVelars }
  , { walsCode := "cac", language := "Cacua", iso := "cbv", value := .none }
  , { walsCode := "cad", language := "Caddo", iso := "cad", value := .none }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .none }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .none }
  , { walsCode := "cam", language := "Camsá", iso := "kbh", value := .none }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .none }
  , { walsCode := "cnt", language := "Cantonese", iso := "yue", value := .none }
  , { walsCode := "car", language := "Carib", iso := "car", value := .none }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .none }
  , { walsCode := "cay", language := "Cayapa", iso := "cbi", value := .none }
  , { walsCode := "cyv", language := "Cayuvava", iso := "cyb", value := .none }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .none }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .none }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .none }
  , { walsCode := "chl", language := "Chehalis (Upper)", iso := "cjh", value := .none }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .none }
  , { walsCode := "cck", language := "Chickasaw", iso := "cic", value := .none }
  , { walsCode := "cti", language := "Chin (Tiddim)", iso := "ctd", value := .none }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .none }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .thSounds }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .thSounds }
  , { walsCode := "cve", language := "Chuave", iso := "cjv", value := .none }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .none }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .none }
  , { walsCode := "cil", language := "CiLuba", iso := "lua", value := .none }
  , { walsCode := "ccp", language := "Cocopa", iso := "coc", value := .none }
  , { walsCode := "cof", language := "Cofán", iso := "con", value := .none }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .none }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .none }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .none }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .thSounds }
  , { walsCode := "dad", language := "Dadibi", iso := "mps", value := .none }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .none }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .labialVelars }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .none }
  , { walsCode := "dah", language := "Dahalo", iso := "dal", value := .clicksPharyngealsAndTh }
  , { walsCode := "ddf", language := "Daju (Dar Fur)", iso := "daj", value := .none }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .labialVelars }
  , { walsCode := "dnw", language := "Dangaléat (Western)", iso := "daa", value := .none }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .none }
  , { walsCode := "dar", language := "Darai", iso := "dry", value := .none }
  , { walsCode := "det", language := "Deti", iso := "shg", value := .clicks }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .none }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .none }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .none }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .none }
  , { walsCode := "diz", language := "Dizi", iso := "mdx", value := .none }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .none }
  , { walsCode := "der", language := "Dla (Proper)", iso := "kbv", value := .none }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .none }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .labialVelars }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .thSounds }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .none }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .none }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .labialVelars }
  , { walsCode := "eja", language := "Ejagham", iso := "etu", value := .labialVelars }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .none }
  , { walsCode := "eng", language := "English", iso := "eng", value := .thSounds }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .none }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .none }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .none }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .labialVelars }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .labialVelars }
  , { walsCode := "eya", language := "Eyak", iso := "eya", value := .none }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .none }
  , { walsCode := "fef", language := "Fe'fe'", iso := "fmp", value := .none }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .thSounds }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .none }
  , { walsCode := "fre", language := "French", iso := "fra", value := .none }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .none }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .none }
  , { walsCode := "fuz", language := "Fuzhou", iso := "cdo", value := .none }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .none }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .none }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .none }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .none }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .labialVelars }
  , { walsCode := "gla", language := "Gelao", iso := "gqu", value := .none }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .none }
  , { walsCode := "ger", language := "German", iso := "deu", value := .none }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .none }
  , { walsCode := "goo", language := "Gooniyandi", iso := "gni", value := .none }
  , { walsCode := "gan", language := "Great Andamanese", iso := "apq", value := .none }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .labialVelars }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .thSounds }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .none }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .none }
  , { walsCode := "gmb", language := "Guambiano", iso := "gum", value := .none }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .none }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .labialVelars }
  , { walsCode := "ga", language := "Gã", iso := "gaa", value := .labialVelars }
  , { walsCode := "had", language := "Hadza", iso := "hts", value := .clicks }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .none }
  , { walsCode := "hak", language := "Hakka", iso := "hak", value := .none }
  , { walsCode := "hmr", language := "Hamer", iso := "amf", value := .none }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .none }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .none }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .none }
  , { walsCode := "hba", language := "Hebrew (Modern Ashkenazic)", iso := "heb", value := .none }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .none }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .none }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .none }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .none }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .thSounds }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .thSounds }
  , { walsCode := "hum", language := "Huitoto (Murui)", iso := "huu", value := .thSounds }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .none }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .pharyngeals }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .none }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .thSounds }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .none }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .labialVelars }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .none }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .labialVelars }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .none }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .none }
  , { walsCode := "imo", language := "Imonda", iso := "imn", value := .none }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .none }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .thSounds }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .pharyngeals }
  , { walsCode := "irx", language := "Iranxe", iso := "irn", value := .none }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .pharyngeals }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .none }
  , { walsCode := "ird", language := "Irish (Donegal)", iso := "gle", value := .none }
  , { walsCode := "iso", language := "Isoko", iso := "iso", value := .labialVelars }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .none }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .none }
  , { walsCode := "iva", language := "Ivatan", iso := "ivb", value := .none }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .none }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .none }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .none }
  , { walsCode := "jpr", language := "Japreria", iso := "jru", value := .none }
  , { walsCode := "jaq", language := "Jaqaru", iso := "jqr", value := .none }
  , { walsCode := "jav", language := "Javanese", iso := "jav", value := .none }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .none }
  , { walsCode := "jeh", language := "Jeh", iso := "jeh", value := .none }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .none }
  , { walsCode := "jiv", language := "Jivaro", iso := "jiv", value := .none }
  , { walsCode := "jom", language := "Jomang", iso := "tlo", value := .none }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .clicks }
  , { walsCode := "kek", language := "K'ekchí", iso := "kek", value := .none }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .pharyngealsAndTh }
  , { walsCode := "kad", language := "Kadugli", iso := "xtc", value := .none }
  , { walsCode := "kng", language := "Kaingang", iso := "kgp", value := .none }
  , { walsCode := "kly", language := "Kala Lagaw Ya", iso := "mwp", value := .none }
  , { walsCode := "kal", language := "Kalami", iso := "gwc", value := .none }
  , { walsCode := "kgu", language := "Kalkatungu", iso := "ktg", value := .none }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .none }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .none }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .none }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .thSounds }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .none }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .none }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .none }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .none }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .none }
  , { walsCode := "ked", language := "Kedang", iso := "ksx", value := .none }
  , { walsCode := "kef", language := "Kefa", iso := "kbr", value := .none }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .none }
  , { walsCode := "ket", language := "Ket", iso := "ket", value := .none }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .none }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .none }
  , { walsCode := "kty", language := "Khanty", iso := "kca", value := .none }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .none }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .none }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .none }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .none }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .none }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .none }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .none }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .none }
  , { walsCode := "kss", language := "Kisi (Southern)", iso := "kss", value := .labialVelars }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .none }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .none }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .labialVelars }
  , { walsCode := "koa", language := "Koasati", iso := "cku", value := .none }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .none }
  , { walsCode := "koh", language := "Kohumono", iso := "bcs", value := .labialVelars }
  , { walsCode := "koi", language := "Koiari", iso := "kbk", value := .none }
  , { walsCode := "kzy", language := "Komi-Zyrian", iso := "kpv", value := .none }
  , { walsCode := "kom", language := "Komo", iso := "xom", value := .none }
  , { walsCode := "kkn", language := "Konkani", iso := "knn", value := .none }
  , { walsCode := "kgi", language := "Konyagi", iso := "cou", value := .none }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .none }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .none }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .none }
  , { walsCode := "kot", language := "Kota", iso := "kfe", value := .none }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .labialVelars }
  , { walsCode := "koy", language := "Koya", iso := "kff", value := .none }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .none }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .none }
  , { walsCode := "kpa", language := "Kpan", iso := "kpk", value := .labialVelars }
  , { walsCode := "kpe", language := "Kpelle", iso := "xpe", value := .labialVelars }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .none }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .none }
  , { walsCode := "kul", language := "Kullo", iso := "dwr", value := .none }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .none }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .none }
  , { walsCode := "kmp", language := "Kunimaipa", iso := "kup", value := .none }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .pharyngeals }
  , { walsCode := "kur", language := "Kurukh", iso := "kru", value := .none }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .none }
  , { walsCode := "kwa", language := "Kwaio", iso := "kwd", value := .none }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .none }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .none }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .none }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .none }
  , { walsCode := "lak", language := "Lak", iso := "lbe", value := .pharyngeals }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .none }
  , { walsCode := "lkk", language := "Lakkia", iso := "lbc", value := .thSounds }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .none }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .none }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .none }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .none }
  , { walsCode := "llm", language := "Lelemi", iso := "lef", value := .labialVelars }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .none }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .none }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .none }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .none }
  , { walsCode := "lua", language := "Lua", iso := "nie", value := .none }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .labialVelars }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .none }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .none }
  , { walsCode := "lus", language := "Lushootseed", iso := "lut", value := .none }
  , { walsCode := "kkv", language := "Lusi", iso := "khl", value := .none }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .none }
  , { walsCode := "lu", language := "Lü", iso := "khb", value := .none }
  , { walsCode := "mya", language := "Ma'ya", iso := "slz", value := .none }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .none }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .none }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .none }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .none }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .none }
  , { walsCode := "mlk", language := "Malakmalak", iso := "mpb", value := .none }
  , { walsCode := "mla", language := "Mambila", iso := "", value := .none }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .none }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .none }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .none }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .none }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .none }
  , { walsCode := "map", language := "Mapudungun", iso := "arn", value := .thSounds }
  , { walsCode := "mrn", language := "Maranao", iso := "mrw", value := .none }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .none }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .none }
  , { walsCode := "mme", language := "Mari (Meadow)", iso := "mhr", value := .thSounds }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .thSounds }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .none }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .none }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .none }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .none }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .none }
  , { walsCode := "maz", language := "Mazahua", iso := "maz", value := .none }
  , { walsCode := "mzc", language := "Mazatec (Chiquihuitlán)", iso := "maq", value := .none }
  , { walsCode := "mba", language := "Mba", iso := "mfc", value := .labialVelars }
  , { walsCode := "mbb", language := "Mbabaram", iso := "vmb", value := .none }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .labialVelars }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .none }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .none }
  , { walsCode := "hok", language := "Min (Southern)", iso := "nan", value := .none }
  , { walsCode := "mss", language := "Miwok (Southern Sierra)", iso := "skd", value := .none }
  , { walsCode := "mtp", language := "Mixe (Totontepec)", iso := "mto", value := .none }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .thSounds }
  , { walsCode := "mxm", language := "Mixtec (Molinos)", iso := "mig", value := .thSounds }
  , { walsCode := "mog", language := "Moghol", iso := "mhj", value := .none }
  , { walsCode := "mor", language := "Mor", iso := "mhz", value := .none }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .thSounds }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .none }
  , { walsCode := "mui", language := "Muinane", iso := "bmr", value := .none }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .labialVelars }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .none }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .thSounds }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .none }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .none }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .none }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .clicks }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .none }
  , { walsCode := "nai", language := "Nanai", iso := "gld", value := .none }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .none }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .none }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .none }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .none }
  , { walsCode := "nbk", language := "Natügu", iso := "ntu", value := .none }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .none }
  , { walsCode := "nax", language := "Naxi", iso := "nxq", value := .none }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .none }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .none }
  , { walsCode := "ntu", language := "Nenets", iso := "yrk", value := .pharyngealsAndTh }
  , { walsCode := "nap", language := "Neo-Aramaic (Persian Azerbaijan)", iso := "trg", value := .none }
  , { walsCode := "nep", language := "Nepali", iso := "npi", value := .none }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .none }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .none }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .thSounds }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .labialVelars }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .thSounds }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .none }
  , { walsCode := "nim", language := "Nimboran", iso := "nir", value := .none }
  , { walsCode := "chu", language := "Nivacle", iso := "cag", value := .none }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .none }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .none }
  , { walsCode := "nob", language := "Nobiin", iso := "fia", value := .none }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .none }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .none }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .none }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .none }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .pharyngeals }
  , { walsCode := "nkt", language := "Nyah Kur (Tha Pong)", iso := "cbn", value := .none }
  , { walsCode := "nyg", language := "Nyangi", iso := "nyp", value := .none }
  , { walsCode := "nyi", language := "Nyimang", iso := "nyi", value := .none }
  , { walsCode := "nis", language := "Nyishi", iso := "njz", value := .none }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .none }
  , { walsCode := "oca", language := "Ocaina", iso := "oca", value := .none }
  , { walsCode := "ogb", language := "Ogbia", iso := "ogb", value := .labialVelars }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .none }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .none }
  , { walsCode := "orm", language := "Ormuri", iso := "oru", value := .none }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .none }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .thSounds }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .none }
  , { walsCode := "pac", language := "Pacoh", iso := "pac", value := .none }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .none }
  , { walsCode := "pnr", language := "Panare", iso := "pbh", value := .none }
  , { walsCode := "puk", language := "Parauk", iso := "prk", value := .none }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .none }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .none }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .none }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .none }
  , { walsCode := "pec", language := "Pech", iso := "pay", value := .none }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .none }
  , { walsCode := "phl", language := "Phlong", iso := "pww", value := .none }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .none }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .none }
  , { walsCode := "poa", language := "Po-Ai", iso := "fwa", value := .none }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .none }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .none }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .none }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .none }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .none }
  , { walsCode := "bng", language := "Qaqet", iso := "byx", value := .none }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .none }
  , { walsCode := "qco", language := "Quechua (Cochabamba)", iso := "quh", value := .thSounds }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .none }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .none }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .none }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .none }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .none }
  , { walsCode := "rsc", language := "Romansch (Scharans)", iso := "roh", value := .none }
  , { walsCode := "ror", language := "Roro", iso := "rro", value := .none }
  , { walsCode := "rtk", language := "Rotokas", iso := "roo", value := .thSounds }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .thSounds }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .none }
  , { walsCode := "rut", language := "Rutul", iso := "rut", value := .pharyngeals }
  , { walsCode := "sab", language := "Sa'ban", iso := "snv", value := .none }
  , { walsCode := "scs", language := "Saami (Central-South)", iso := "sma", value := .none }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .clicks }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .labialVelars }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .none }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .none }
  , { walsCode := "seb", language := "Sebei", iso := "kpz", value := .none }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .none }
  , { walsCode := "slp", language := "Selepet", iso := "spl", value := .none }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .none }
  , { walsCode := "skp", language := "Selkup", iso := "sel", value := .none }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .none }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .labialVelars }
  , { walsCode := "snc", language := "Seneca", iso := "see", value := .none }
  , { walsCode := "snt", language := "Sentani", iso := "set", value := .none }
  , { walsCode := "sha", language := "Shan", iso := "shn", value := .none }
  , { walsCode := "shs", language := "Shasta", iso := "sht", value := .none }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .none }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .none }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .none }
  , { walsCode := "sdh", language := "Sindhi", iso := "snd", value := .none }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .none }
  , { walsCode := "sin", language := "Siona", iso := "snn", value := .none }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .none }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .none }
  , { walsCode := "som", language := "Somali", iso := "som", value := .pharyngeals }
  , { walsCode := "soq", language := "Soqotri", iso := "sqt", value := .pharyngeals }
  , { walsCode := "sor", language := "Sora", iso := "srb", value := .none }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .thSounds }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .pharyngeals }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .none }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .none }
  , { walsCode := "sui", language := "Sui", iso := "swi", value := .none }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .none }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .thSounds }
  , { walsCode := "sba", language := "Sáliba (in Colombia)", iso := "slc", value := .none }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .none }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .thSounds }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .none }
  , { walsCode := "tma", language := "Tama", iso := "tma", value := .pharyngeals }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .none }
  , { walsCode := "tmp", language := "Tampulma", iso := "tpm", value := .labialVelars }
  , { walsCode := "tok", language := "Tarok", iso := "yer", value := .labialVelars }
  , { walsCode := "tas", language := "Tashlhiyt", iso := "shi", value := .pharyngeals }
  , { walsCode := "tsg", language := "Tausug", iso := "tsg", value := .none }
  , { walsCode := "teh", language := "Tehuelche", iso := "teh", value := .none }
  , { walsCode := "tks", language := "Teke (Southern)", iso := "kkw", value := .none }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .none }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .none }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .labialVelars }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .none }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .none }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .none }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .none }
  , { walsCode := "tic", language := "Ticuna", iso := "tca", value := .none }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .none }
  , { walsCode := "tgr", language := "Tigré", iso := "tig", value := .pharyngeals }
  , { walsCode := "try", language := "Tiruray", iso := "tiy", value := .none }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .none }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .none }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .none }
  , { walsCode := "tli", language := "Tlingit", iso := "tli", value := .none }
  , { walsCode := "toa", language := "Toaripi", iso := "tqo", value := .none }
  , { walsCode := "tol", language := "Tol", iso := "jic", value := .none }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .none }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .thSounds }
  , { walsCode := "tpa", language := "Totonac (Papantla)", iso := "top", value := .none }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .none }
  ]

private def allData_1 : List (Datapoint PresenceOfUncommonConsonants) :=
  [ { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .none }
  , { walsCode := "tso", language := "Tsou", iso := "tsu", value := .none }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .pharyngeals }
  , { walsCode := "tug", language := "Tuareg (Ahaggar)", iso := "thv", value := .none }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .none }
  , { walsCode := "tul", language := "Tulu", iso := "tcy", value := .none }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .none }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .none }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .none }
  , { walsCode := "tza", language := "Tzeltal (Aguacatenango)", iso := "tzh", value := .none }
  , { walsCode := "umb", language := "UMbundu", iso := "umb", value := .none }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .none }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .none }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .none }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .none }
  , { walsCode := "uzn", language := "Uzbek (Northern)", iso := "uzn", value := .none }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .none }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .none }
  , { walsCode := "bno", language := "Waimaha", iso := "bao", value := .none }
  , { walsCode := "wam", language := "Wambaya", iso := "wmb", value := .none }
  , { walsCode := "wnt", language := "Wantoat", iso := "wnc", value := .none }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .none }
  , { walsCode := "wps", language := "Wapishana", iso := "wap", value := .none }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .none }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .none }
  , { walsCode := "wry", language := "Waray (in Australia)", iso := "wrz", value := .none }
  , { walsCode := "wrd", language := "Wardaman", iso := "wrr", value := .none }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .none }
  , { walsCode := "wrs", language := "Waris", iso := "wrs", value := .none }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .none }
  , { walsCode := "wdo", language := "Western Desert (Ooldea)", iso := "pjt", value := .none }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .none }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .none }
  , { walsCode := "wmu", language := "Wik Munkan", iso := "wim", value := .none }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .none }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .none }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .none }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .none }
  , { walsCode := "wuc", language := "Wu", iso := "wuu", value := .none }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .none }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .none }
  , { walsCode := "ykt", language := "Yakut", iso := "sah", value := .none }
  , { walsCode := "yan", language := "Yana", iso := "ynn", value := .none }
  , { walsCode := "yny", language := "Yanyuwa", iso := "jao", value := .none }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .thSounds }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .none }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .none }
  , { walsCode := "yaw", language := "Yawa", iso := "yva", value := .none }
  , { walsCode := "yay", language := "Yay", iso := "pcc", value := .thSounds }
  , { walsCode := "yel", language := "Yelî Dnye", iso := "yle", value := .labialVelars }
  , { walsCode := "yes", language := "Yessan-Mayo", iso := "yss", value := .none }
  , { walsCode := "yey", language := "Yeyi", iso := "yey", value := .clicks }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .none }
  , { walsCode := "yim", language := "Yimas", iso := "yee", value := .none }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .labialVelars }
  , { walsCode := "yct", language := "Yucatec", iso := "yua", value := .none }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .none }
  , { walsCode := "ycn", language := "Yucuna", iso := "ycn", value := .none }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .none }
  , { walsCode := "ytu", language := "Yukaghir (Tundra)", iso := "ykg", value := .none }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .labialVelars }
  , { walsCode := "yus", language := "Yupik (Siberian)", iso := "ess", value := .none }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .none }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .labialVelars }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .none }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .clicks }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .none }
  ]

/-- Complete WALS 19A dataset (567 languages). -/
def allData : List (Datapoint PresenceOfUncommonConsonants) := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 567 := by native_decide

theorem count_none :
    (allData.filter (·.value == .none)).length = 449 := by native_decide
theorem count_clicks :
    (allData.filter (·.value == .clicks)).length = 9 := by native_decide
theorem count_labialVelars :
    (allData.filter (·.value == .labialVelars)).length = 45 := by native_decide
theorem count_pharyngeals :
    (allData.filter (·.value == .pharyngeals)).length = 21 := by native_decide
theorem count_thSounds :
    (allData.filter (·.value == .thSounds)).length = 40 := by native_decide
theorem count_clicksPharyngealsAndTh :
    (allData.filter (·.value == .clicksPharyngealsAndTh)).length = 1 := by native_decide
theorem count_pharyngealsAndTh :
    (allData.filter (·.value == .pharyngealsAndTh)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F19A
