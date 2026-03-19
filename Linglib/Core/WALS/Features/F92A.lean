/-!
# WALS Feature 92A: Position of Polar Question Particles
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 92A`.

Chapter 92, 884 languages.
-/

namespace Core.WALS.F92A

/-- WALS 92A values. -/
inductive PositionOfPolarQuestionParticles where
  | initial  -- Initial (129 languages)
  | final  -- Final (314 languages)
  | secondPosition  -- Second position (52 languages)
  | otherPosition  -- Other position (8 languages)
  | inEitherOfTwoPositions  -- In either of two positions (26 languages)
  | noQuestionParticle  -- No question particle (355 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 92A datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PositionOfPolarQuestionParticles
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .initial }
  , { walsCode := "ani", language := "//Ani", iso := "hnh", value := .final }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .noQuestionParticle }
  , { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .noQuestionParticle }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .final }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .inEitherOfTwoPositions }
  , { walsCode := "acn", language := "Achang", iso := "acn", value := .final }
  , { walsCode := "acu", language := "Achuar", iso := "acu", value := .noQuestionParticle }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .final }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .noQuestionParticle }
  , { walsCode := "aga", language := "Agarabi", iso := "agd", value := .noQuestionParticle }
  , { walsCode := "agc", language := "Agta (Central)", iso := "agt", value := .initial }
  , { walsCode := "agd", language := "Agta (Dupaningan)", iso := "duo", value := .secondPosition }
  , { walsCode := "ain", language := "Ainu", iso := "ain", value := .final }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .final }
  , { walsCode := "akn", language := "Akan", iso := "aka", value := .inEitherOfTwoPositions }
  , { walsCode := "akh", language := "Akha", iso := "ahk", value := .final }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .initial }
  , { walsCode := "ala", language := "Alamblak", iso := "amp", value := .noQuestionParticle }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .initial }
  , { walsCode := "amc", language := "Amahuaca", iso := "amc", value := .secondPosition }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .inEitherOfTwoPositions }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .noQuestionParticle }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .final }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .final }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .final }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .final }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .final }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .final }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .noQuestionParticle }
  , { walsCode := "ano", language := "Anong", iso := "nun", value := .noQuestionParticle }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .final }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .final }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .noQuestionParticle }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .noQuestionParticle }
  , { walsCode := "apt", language := "Apatani", iso := "apt", value := .final }
  , { walsCode := "api", language := "Apinayé", iso := "apn", value := .initial }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .noQuestionParticle }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .initial }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .noQuestionParticle }
  , { walsCode := "ams", language := "Arabic (Modern Standard)", iso := "arb", value := .initial }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .initial }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .final }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .noQuestionParticle }
  , { walsCode := "aab", language := "Arapesh (Abu)", iso := "aah", value := .final }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .final }
  , { walsCode := "arc", language := "Archi", iso := "aqc", value := .noQuestionParticle }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .noQuestionParticle }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .noQuestionParticle }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .noQuestionParticle }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .final }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .secondPosition }
  , { walsCode := "asm", language := "Asmat", iso := "cns", value := .final }
  , { walsCode := "ass", language := "Assamese", iso := "asm", value := .noQuestionParticle }
  , { walsCode := "ata", language := "Atayal", iso := "tay", value := .final }
  , { walsCode := "ath", language := "Athpare", iso := "aph", value := .noQuestionParticle }
  , { walsCode := "ava", language := "Avar", iso := "ava", value := .secondPosition }
  , { walsCode := "avk", language := "Avikam", iso := "avi", value := .final }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .final }
  , { walsCode := "awt", language := "Awtuw", iso := "kmn", value := .final }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .final }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .noQuestionParticle }
  , { walsCode := "aze", language := "Azerbaijani", iso := "", value := .final }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .final }
  , { walsCode := "bdm", language := "Badimaya", iso := "bia", value := .noQuestionParticle }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .noQuestionParticle }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .final }
  , { walsCode := "bai", language := "Bai", iso := "bca", value := .final }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .secondPosition }
  , { walsCode := "bkn", language := "Bakundu", iso := "bdu", value := .final }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .noQuestionParticle }
  , { walsCode := "bam", language := "Bambara", iso := "bam", value := .final }
  , { walsCode := "bnj", language := "Bandjalang", iso := "bdy", value := .initial }
  , { walsCode := "bgz", language := "Banggi", iso := "bdg", value := .noQuestionParticle }
  , { walsCode := "bao", language := "Bao'an", iso := "peh", value := .noQuestionParticle }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .noQuestionParticle }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .noQuestionParticle }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .initial }
  , { walsCode := "bae", language := "Baré", iso := "bae", value := .noQuestionParticle }
  , { walsCode := "bsq", language := "Basque", iso := "eus", value := .otherPosition }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .secondPosition }
  , { walsCode := "baw", language := "Bawm", iso := "bgr", value := .final }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .noQuestionParticle }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .final }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .noQuestionParticle }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .initial }
  , { walsCode := "bem", language := "Bemba", iso := "bem", value := .inEitherOfTwoPositions }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .initial }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .initial }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .initial }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .noQuestionParticle }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .final }
  , { walsCode := "bti", language := "Betoi", iso := "", value := .noQuestionParticle }
  , { walsCode := "bho", language := "Bhojpuri", iso := "bho", value := .initial }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .noQuestionParticle }
  , { walsCode := "bln", language := "Bilin", iso := "byn", value := .noQuestionParticle }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .final }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .noQuestionParticle }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .noQuestionParticle }
  , { walsCode := "bbw", language := "Bininj Gun-Wok", iso := "gup", value := .initial }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .noQuestionParticle }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .final }
  , { walsCode := "biu", language := "Bisu", iso := "", value := .noQuestionParticle }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .noQuestionParticle }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .final }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .noQuestionParticle }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .final }
  , { walsCode := "bon", language := "Bongu", iso := "bpu", value := .final }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .initial }
  , { walsCode := "bra", language := "Brao", iso := "brb", value := .final }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .initial }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .final }
  , { walsCode := "bgn", language := "Bugun", iso := "bgg", value := .final }
  , { walsCode := "bnu", language := "Bularnu", iso := "", value := .initial }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .secondPosition }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .noQuestionParticle }
  , { walsCode := "ghr", language := "Bunan", iso := "bfu", value := .final }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .noQuestionParticle }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .noQuestionParticle }
  , { walsCode := "bur", language := "Burushaski", iso := "bsk", value := .noQuestionParticle }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .final }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .noQuestionParticle }
  , { walsCode := "bya", language := "Byansi", iso := "bee", value := .initial }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .noQuestionParticle }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .noQuestionParticle }
  , { walsCode := "can", language := "Candoshi", iso := "cbu", value := .noQuestionParticle }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .initial }
  , { walsCode := "crp", language := "Carapana", iso := "cbc", value := .noQuestionParticle }
  , { walsCode := "car", language := "Carib", iso := "car", value := .noQuestionParticle }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .noQuestionParticle }
  , { walsCode := "cga", language := "Chaga", iso := "old", value := .final }
  , { walsCode := "chh", language := "Chaha", iso := "sgw", value := .final }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .noQuestionParticle }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .final }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .initial }
  , { walsCode := "chg", language := "Chang", iso := "nbc", value := .final }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .final }
  , { walsCode := "chc", language := "Chechen", iso := "che", value := .noQuestionParticle }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .secondPosition }
  , { walsCode := "che", language := "Cherokee", iso := "chr", value := .secondPosition }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .initial }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .noQuestionParticle }
  , { walsCode := "cmr", language := "Chin (Mara)", iso := "mrh", value := .final }
  , { walsCode := "chs", language := "Chin (Siyin)", iso := "csy", value := .final }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .initial }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .initial }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .noQuestionParticle }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .initial }
  , { walsCode := "cpy", language := "Chipaya", iso := "cap", value := .noQuestionParticle }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .final }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .final }
  , { walsCode := "cct", language := "Choctaw", iso := "cho", value := .final }
  , { walsCode := "chx", language := "Chontal (Huamelultec Oaxaca)", iso := "clo", value := .initial }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .noQuestionParticle }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .final }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .noQuestionParticle }
  , { walsCode := "cba", language := "Chumash (Barbareño)", iso := "boi", value := .noQuestionParticle }
  , { walsCode := "chv", language := "Chuvash", iso := "chv", value := .noQuestionParticle }
  , { walsCode := "coa", language := "Coahuilteco", iso := "xcw", value := .noQuestionParticle }
  , { walsCode := "coc", language := "Cocama", iso := "cod", value := .secondPosition }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .secondPosition }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .final }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .initial }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .initial }
  , { walsCode := "cre", language := "Cree (Plains)", iso := "crk", value := .secondPosition }
  , { walsCode := "cea", language := "Cree (Swampy)", iso := "csw", value := .secondPosition }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .noQuestionParticle }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .noQuestionParticle }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .noQuestionParticle }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .initial }
  , { walsCode := "dgr", language := "Dagur", iso := "dta", value := .final }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .final }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .noQuestionParticle }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .noQuestionParticle }
  , { walsCode := "drm", language := "Darma", iso := "drd", value := .initial }
  , { walsCode := "des", language := "Desano", iso := "des", value := .noQuestionParticle }
  , { walsCode := "deu", language := "Deuri", iso := "der", value := .noQuestionParticle }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .noQuestionParticle }
  , { walsCode := "dhi", language := "Dhivehi", iso := "div", value := .final }
  , { walsCode := "die", language := "Diegueño (Mesa Grande)", iso := "dih", value := .noQuestionParticle }
  , { walsCode := "dim", language := "Dime", iso := "dim", value := .noQuestionParticle }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .noQuestionParticle }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .noQuestionParticle }
  , { walsCode := "diy", language := "Diyari", iso := "dif", value := .noQuestionParticle }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .noQuestionParticle }
  , { walsCode := "djp", language := "Djapu", iso := "dwu", value := .initial }
  , { walsCode := "dji", language := "Djingili", iso := "jig", value := .initial }
  , { walsCode := "dlm", language := "Dla (Menggwa)", iso := "kbv", value := .noQuestionParticle }
  , { walsCode := "dmk", language := "Domaaki", iso := "dmk", value := .final }
  , { walsCode := "don", language := "Dong (Southern)", iso := "kmc", value := .final }
  , { walsCode := "dds", language := "Donno So", iso := "dds", value := .final }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .final }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .initial }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .final }
  , { walsCode := "dul", language := "Dulong", iso := "duu", value := .final }
  , { walsCode := "dum", language := "Dumo", iso := "vam", value := .final }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .final }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .noQuestionParticle }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .secondPosition }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .inEitherOfTwoPositions }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .noQuestionParticle }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .initial }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .final }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .noQuestionParticle }
  , { walsCode := "ora", language := "Emai", iso := "ema", value := .noQuestionParticle }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .noQuestionParticle }
  , { walsCode := "ene", language := "Enets", iso := "", value := .noQuestionParticle }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .final }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .noQuestionParticle }
  , { walsCode := "eng", language := "English", iso := "eng", value := .noQuestionParticle }
  , { walsCode := "epe", language := "Epena Pedee", iso := "sja", value := .noQuestionParticle }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .initial }
  , { walsCode := "ese", language := "Ese Ejja", iso := "ese", value := .initial }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .inEitherOfTwoPositions }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .initial }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .final }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .final }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .initial }
  , { walsCode := "fas", language := "Fasu", iso := "faa", value := .noQuestionParticle }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .noQuestionParticle }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .secondPosition }
  , { walsCode := "foe", language := "Foe", iso := "foi", value := .noQuestionParticle }
  , { walsCode := "pdp", language := "Folopa", iso := "ppo", value := .noQuestionParticle }
  , { walsCode := "fre", language := "French", iso := "fra", value := .initial }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .noQuestionParticle }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .final }
  , { walsCode := "ful", language := "Fulniô", iso := "fun", value := .noQuestionParticle }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .final }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .final }
  , { walsCode := "gds", language := "Gadsup", iso := "gaj", value := .noQuestionParticle }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .noQuestionParticle }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .noQuestionParticle }
  , { walsCode := "gal", language := "Galo", iso := "adl", value := .noQuestionParticle }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .final }
  , { walsCode := "gar", language := "Garo", iso := "grt", value := .noQuestionParticle }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .inEitherOfTwoPositions }
  , { walsCode := "gav", language := "Gavião", iso := "gvo", value := .initial }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .final }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .final }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .noQuestionParticle }
  , { walsCode := "ger", language := "German", iso := "deu", value := .noQuestionParticle }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .noQuestionParticle }
  , { walsCode := "git", language := "Gitksan", iso := "git", value := .final }
  , { walsCode := "goa", language := "Goajiro", iso := "guc", value := .initial }
  , { walsCode := "goe", language := "Goemai", iso := "ank", value := .final }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .initial }
  , { walsCode := "gln", language := "Golin", iso := "gvf", value := .noQuestionParticle }
  , { walsCode := "gon", language := "Gondi", iso := "gno", value := .final }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .initial }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .initial }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .noQuestionParticle }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .noQuestionParticle }
  , { walsCode := "grj", language := "Guarijío", iso := "var", value := .noQuestionParticle }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .final }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .final }
  , { walsCode := "guj", language := "Gujarati", iso := "guj", value := .noQuestionParticle }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .final }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .noQuestionParticle }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .noQuestionParticle }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .noQuestionParticle }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .noQuestionParticle }
  , { walsCode := "guw", language := "Gungbe", iso := "guw", value := .final }
  , { walsCode := "gur", language := "Gurung", iso := "", value := .final }
  , { walsCode := "gdb", language := "Gutob", iso := "gbj", value := .noQuestionParticle }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .final }
  , { walsCode := "gyc", language := "Gyarong (Cogtse)", iso := "jya", value := .noQuestionParticle }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .secondPosition }
  , { walsCode := "ham", language := "Hamtai", iso := "hmt", value := .final }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .final }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .final }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .noQuestionParticle }
  , { walsCode := "hay", language := "Hayu", iso := "vay", value := .noQuestionParticle }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .final }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .initial }
  , { walsCode := "hin", language := "Hindi", iso := "hin", value := .initial }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .noQuestionParticle }
  , { walsCode := "hma", language := "Hmar", iso := "hmr", value := .final }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .otherPosition }
  , { walsCode := "ho", language := "Ho", iso := "hoc", value := .final }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .noQuestionParticle }
  , { walsCode := "hop", language := "Hopi", iso := "hop", value := .initial }
  , { walsCode := "hua", language := "Hua", iso := "ygr", value := .noQuestionParticle }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .noQuestionParticle }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .initial }
  , { walsCode := "hmi", language := "Huitoto (Minica)", iso := "hto", value := .noQuestionParticle }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .inEitherOfTwoPositions }
  , { walsCode := "hzb", language := "Hunzib", iso := "huz", value := .noQuestionParticle }
  , { walsCode := "hpd", language := "Hup", iso := "jup", value := .noQuestionParticle }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .initial }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .initial }
  , { walsCode := "idu", language := "Idu", iso := "clk", value := .noQuestionParticle }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .initial }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .final }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .noQuestionParticle }
  , { walsCode := "ige", language := "Igede", iso := "ige", value := .final }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .noQuestionParticle }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .final }
  , { walsCode := "ika", language := "Ika", iso := "arh", value := .final }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .final }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .inEitherOfTwoPositions }
  , { walsCode := "ing", language := "Ingush", iso := "inh", value := .noQuestionParticle }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .noQuestionParticle }
  , { walsCode := "irr", language := "Irarutu", iso := "irh", value := .noQuestionParticle }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .initial }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .noQuestionParticle }
  , { walsCode := "ito", language := "Itonama", iso := "ito", value := .noQuestionParticle }
  , { walsCode := "iwa", language := "Iwaidja", iso := "ibd", value := .inEitherOfTwoPositions }
  , { walsCode := "iwm", language := "Iwam", iso := "iwm", value := .final }
  , { walsCode := "jar", language := "Izere", iso := "izr", value := .final }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .final }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .final }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .noQuestionParticle }
  , { walsCode := "jms", language := "Jamsay", iso := "djm", value := .final }
  , { walsCode := "jpn", language := "Japanese", iso := "jpn", value := .final }
  , { walsCode := "jng", language := "Jingpho", iso := "kac", value := .final }
  , { walsCode := "jug", language := "Jugli", iso := "nst", value := .noQuestionParticle }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .final }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .noQuestionParticle }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .secondPosition }
  , { walsCode := "kab", language := "Kabardian", iso := "kbd", value := .noQuestionParticle }
  , { walsCode := "kby", language := "Kabiyé", iso := "kbp", value := .final }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .noQuestionParticle }
  , { walsCode := "kdz", language := "Kadazan", iso := "kzj", value := .secondPosition }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .noQuestionParticle }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .noQuestionParticle }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .noQuestionParticle }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .noQuestionParticle }
  , { walsCode := "kba", language := "Kamba", iso := "kam", value := .noQuestionParticle }
  , { walsCode := "kmr", language := "Kamoro", iso := "kgq", value := .noQuestionParticle }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .noQuestionParticle }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .final }
  , { walsCode := "knd", language := "Kannada", iso := "kan", value := .final }
  , { walsCode := "kno", language := "Kanoê", iso := "kxo", value := .final }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .noQuestionParticle }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .final }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .noQuestionParticle }
  , { walsCode := "krj", language := "Karadjeri", iso := "gbd", value := .initial }
  , { walsCode := "kkp", language := "Karakalpak", iso := "kaa", value := .noQuestionParticle }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .final }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .final }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .final }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .final }
  , { walsCode := "kaa", language := "Karó (Arára)", iso := "arr", value := .final }
  , { walsCode := "ksm", language := "Kasem", iso := "xsm", value := .final }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .final }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .noQuestionParticle }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .secondPosition }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .final }
  , { walsCode := "kyp", language := "Kayapó", iso := "txu", value := .initial }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .noQuestionParticle }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .final }
  , { walsCode := "kem", language := "Kemant", iso := "ahg", value := .noQuestionParticle }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .final }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .final }
  , { walsCode := "ksa", language := "Keresan (Santa Ana)", iso := "kee", value := .initial }
  , { walsCode := "kew", language := "Kewa", iso := "kew", value := .final }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .final }
  , { walsCode := "kha", language := "Khalkha", iso := "khk", value := .final }
  , { walsCode := "kmh", language := "Kham", iso := "kjl", value := .noQuestionParticle }
  , { walsCode := "khr", language := "Kharia", iso := "khr", value := .final }
  , { walsCode := "khi", language := "Khinalug", iso := "kjj", value := .noQuestionParticle }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .final }
  , { walsCode := "kmu", language := "Khmu'", iso := "kjg", value := .final }
  , { walsCode := "khn", language := "Khün", iso := "kkh", value := .final }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .noQuestionParticle }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .noQuestionParticle }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .noQuestionParticle }
  , { walsCode := "kil", language := "Kiluba", iso := "lub", value := .final }
  , { walsCode := "kim", language := "Kimaghama", iso := "kig", value := .final }
  , { walsCode := "knn", language := "Kinnauri", iso := "kfk", value := .noQuestionParticle }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .initial }
  , { walsCode := "kgz", language := "Kirghiz", iso := "kir", value := .final }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noQuestionParticle }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .inEitherOfTwoPositions }
  , { walsCode := "kob", language := "Kobon", iso := "kpw", value := .final }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .noQuestionParticle }
  , { walsCode := "kmo", language := "Koiali (Mountain)", iso := "kpx", value := .secondPosition }
  , { walsCode := "kta", language := "Koita", iso := "kqi", value := .final }
  , { walsCode := "kok", language := "Kokborok", iso := "trp", value := .noQuestionParticle }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .noQuestionParticle }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .final }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .noQuestionParticle }
  , { walsCode := "knw", language := "Konkow", iso := "mjd", value := .noQuestionParticle }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .noQuestionParticle }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .final }
  , { walsCode := "kor", language := "Korean", iso := "kor", value := .noQuestionParticle }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .noQuestionParticle }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .final }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .final }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .initial }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .noQuestionParticle }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .inEitherOfTwoPositions }
  , { walsCode := "kqq", language := "Krenak", iso := "kqq", value := .noQuestionParticle }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .final }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .noQuestionParticle }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .noQuestionParticle }
  , { walsCode := "kya", language := "Kuku-Yalanji", iso := "gvn", value := .initial }
  , { walsCode := "kmn", language := "Kuman", iso := "kue", value := .noQuestionParticle }
  , { walsCode := "kum", language := "Kumauni", iso := "kfy", value := .inEitherOfTwoPositions }
  , { walsCode := "kun", language := "Kuna", iso := "kvn", value := .noQuestionParticle }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .noQuestionParticle }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .noQuestionParticle }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .initial }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .noQuestionParticle }
  , { walsCode := "kuu", language := "Kuuku Ya'u", iso := "kuy", value := .noQuestionParticle }
  , { walsCode := "kuv", language := "Kuvi", iso := "kxv", value := .final }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .final }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .noQuestionParticle }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .secondPosition }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .final }
  , { walsCode := "kyk", language := "Kyaka", iso := "kyc", value := .noQuestionParticle }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .inEitherOfTwoPositions }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .noQuestionParticle }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .final }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .noQuestionParticle }
  , { walsCode := "lag", language := "Lagwan", iso := "kot", value := .final }
  , { walsCode := "lah", language := "Lahu", iso := "lhu", value := .final }
  , { walsCode := "lai", language := "Lai", iso := "cnh", value := .final }
  , { walsCode := "lkt", language := "Lakhota", iso := "lkt", value := .final }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .final }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .noQuestionParticle }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .final }
  , { walsCode := "lmn", language := "Lamani", iso := "lmn", value := .final }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .initial }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .noQuestionParticle }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .final }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .initial }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .final }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .final }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .final }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .secondPosition }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .final }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .final }
  , { walsCode := "lez", language := "Lezgian", iso := "lez", value := .noQuestionParticle }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .noQuestionParticle }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .final }
  , { walsCode := "lin", language := "Lingala", iso := "lin", value := .noQuestionParticle }
  , { walsCode := "lis", language := "Lisu", iso := "lis", value := .noQuestionParticle }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .initial }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .final }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .noQuestionParticle }
  , { walsCode := "ldo", language := "Londo", iso := "bdu", value := .final }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .noQuestionParticle }
  , { walsCode := "lot", language := "Lotha", iso := "njh", value := .noQuestionParticle }
  , { walsCode := "loz", language := "Lozi", iso := "loz", value := .inEitherOfTwoPositions }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .final }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .secondPosition }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .noQuestionParticle }
  , { walsCode := "lun", language := "Lungchang", iso := "nst", value := .final }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .noQuestionParticle }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .final }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .initial }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .noQuestionParticle }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .noQuestionParticle }
  , { walsCode := "mae", language := "Mae", iso := "mmw", value := .final }
  , { walsCode := "mne", language := "Maidu (Northeast)", iso := "nmu", value := .noQuestionParticle }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .final }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .final }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .secondPosition }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .inEitherOfTwoPositions }
  , { walsCode := "mym", language := "Malayalam", iso := "mal", value := .final }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .noQuestionParticle }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .secondPosition }
  , { walsCode := "mmi", language := "Mambai", iso := "mcs", value := .final }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .noQuestionParticle }
  , { walsCode := "mnc", language := "Manchu", iso := "mnc", value := .noQuestionParticle }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .noQuestionParticle }
  , { walsCode := "mnd", language := "Mandarin", iso := "cmn", value := .final }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .final }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .final }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .noQuestionParticle }
  , { walsCode := "mgg", language := "Mangghuer", iso := "mjg", value := .noQuestionParticle }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .final }
  , { walsCode := "man", language := "Mano", iso := "mev", value := .noQuestionParticle }
  , { walsCode := "mns", language := "Mansi", iso := "mns", value := .initial }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .noQuestionParticle }
  , { walsCode := "mra", language := "Mara", iso := "mec", value := .noQuestionParticle }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .noQuestionParticle }
  , { walsCode := "mhi", language := "Marathi", iso := "mar", value := .final }
  , { walsCode := "mny", language := "Margany", iso := "zmc", value := .initial }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .final }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .noQuestionParticle }
  , { walsCode := "mrd", language := "Marind", iso := "mrz", value := .final }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .initial }
  , { walsCode := "mrt", language := "Martuthunira", iso := "vma", value := .noQuestionParticle }
  , { walsCode := "mru", language := "Maru", iso := "mhx", value := .final }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .final }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .noQuestionParticle }
  , { walsCode := "mtt", language := "Massachusett", iso := "wam", value := .noQuestionParticle }
  , { walsCode := "mts", language := "Matis", iso := "mpq", value := .noQuestionParticle }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .final }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .initial }
  , { walsCode := "max", language := "Maxakalí", iso := "mbl", value := .initial }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .final }
  , { walsCode := "mzh", language := "Mazatec (Huautla)", iso := "mau", value := .initial }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .final }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .final }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .otherPosition }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .final }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .final }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "mee", language := "Me'en", iso := "mym", value := .final }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .noQuestionParticle }
  , { walsCode := "mei", language := "Meithei", iso := "mni", value := .final }
  , { walsCode := "mek", language := "Mekens", iso := "skf", value := .final }
  , { walsCode := "mke", language := "Mekeo", iso := "mek", value := .final }
  , { walsCode := "mde", language := "Mende", iso := "men", value := .noQuestionParticle }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .noQuestionParticle }
  , { walsCode := "mey", language := "Menya", iso := "mcr", value := .final }
  , { walsCode := "mer", language := "Meryam Mir", iso := "ulk", value := .noQuestionParticle }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .final }
  , { walsCode := "mpt", language := "Mian", iso := "mpt", value := .final }
  , { walsCode := "mie", language := "Mien", iso := "ium", value := .final }
  , { walsCode := "mik", language := "Mikir", iso := "mjw", value := .noQuestionParticle }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .final }
  , { walsCode := "msg", language := "Mising", iso := "mrg", value := .noQuestionParticle }
  , { walsCode := "mis", language := "Miskito", iso := "miq", value := .final }
  , { walsCode := "mxx", language := "Mixe (Ayutla)", iso := "mxp", value := .final }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .inEitherOfTwoPositions }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .noQuestionParticle }
  , { walsCode := "mxj", language := "Mixtec (Jicaltepec)", iso := "mio", value := .final }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .initial }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .final }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .final }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .final }
  , { walsCode := "miz", language := "Mizo", iso := "lus", value := .final }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .initial }
  , { walsCode := "mon", language := "Mon", iso := "mnw", value := .final }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .final }
  , { walsCode := "mni", language := "Moni", iso := "mnz", value := .noQuestionParticle }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .secondPosition }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .final }
  , { walsCode := "mri", language := "Moraori", iso := "mok", value := .final }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .initial }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .final }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .secondPosition }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .final }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .noQuestionParticle }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .final }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .final }
  , { walsCode := "msc", language := "Muisca", iso := "chb", value := .noQuestionParticle }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .final }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .noQuestionParticle }
  , { walsCode := "mun", language := "Mundari", iso := "unr", value := .final }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .final }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .final }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .noQuestionParticle }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .final }
  , { walsCode := "mrw", language := "Muruwari", iso := "zmu", value := .initial }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .final }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .final }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .initial }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .noQuestionParticle }
  , { walsCode := "nab", language := "Nabak", iso := "naf", value := .noQuestionParticle }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .noQuestionParticle }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .noQuestionParticle }
  , { walsCode := "nma", language := "Naga (Mao)", iso := "nbi", value := .final }
  , { walsCode := "ngt", language := "Naga (Tangkhul)", iso := "nmf", value := .noQuestionParticle }
  , { walsCode := "nze", language := "Naga (Zeme)", iso := "nzm", value := .final }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .final }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .noQuestionParticle }
  , { walsCode := "kho", language := "Nama", iso := "naq", value := .secondPosition }
  , { walsCode := "nmb", language := "Nambikuára (Southern)", iso := "nab", value := .noQuestionParticle }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .final }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .initial }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .final }
  , { walsCode := "nnk", language := "Nankina", iso := "nnk", value := .noQuestionParticle }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .noQuestionParticle }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .secondPosition }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .inEitherOfTwoPositions }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .final }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .final }
  , { walsCode := "ndj", language := "Ndjébbana", iso := "djj", value := .noQuestionParticle }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .noQuestionParticle }
  , { walsCode := "nnd", language := "Nend", iso := "anh", value := .noQuestionParticle }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .noQuestionParticle }
  , { walsCode := "nev", language := "Nevome", iso := "pia", value := .initial }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .final }
  , { walsCode := "new", language := "Newari (Kathmandu)", iso := "new", value := .final }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .final }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .initial }
  , { walsCode := "ngd", language := "Ngad'a", iso := "nxg", value := .noQuestionParticle }
  , { walsCode := "nkb", language := "Ngalkbun", iso := "ngk", value := .initial }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .final }
  , { walsCode := "nga", language := "Nganasan", iso := "nio", value := .noQuestionParticle }
  , { walsCode := "ngn", language := "Ngandi", iso := "nid", value := .initial }
  , { walsCode := "ngk", language := "Ngankikurungkurr", iso := "nam", value := .noQuestionParticle }
  , { walsCode := "nbm", language := "Ngbaka (Ma'bo)", iso := "nbm", value := .final }
  , { walsCode := "ngb", language := "Ngbaka (Minagende)", iso := "nga", value := .final }
  , { walsCode := "ndi", language := "Ngbandi", iso := "ngb", value := .noQuestionParticle }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .inEitherOfTwoPositions }
  , { walsCode := "ngi", language := "Ngiyambaa", iso := "wyb", value := .secondPosition }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .noQuestionParticle }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .noQuestionParticle }
  , { walsCode := "nha", language := "Nhanda", iso := "nha", value := .noQuestionParticle }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .initial }
  , { walsCode := "nsg", language := "Nisgha", iso := "ncg", value := .final }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .noQuestionParticle }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .otherPosition }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .final }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .final }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .final }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .final }
  , { walsCode := "noc", language := "Nocte", iso := "njb", value := .noQuestionParticle }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .final }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .final }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .noQuestionParticle }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .noQuestionParticle }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .noQuestionParticle }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .final }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .inEitherOfTwoPositions }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .inEitherOfTwoPositions }
  , { walsCode := "nyk", language := "Nyamkad", iso := "tpq", value := .noQuestionParticle }
  , { walsCode := "nyu", language := "Nyulnyul", iso := "nyv", value := .initial }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .initial }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .initial }
  , { walsCode := "ocu", language := "Ocuilteco", iso := "ocu", value := .initial }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .final }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .secondPosition }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .final }
  , { walsCode := "omh", language := "Omaha", iso := "oma", value := .final }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .secondPosition }
  , { walsCode := "ong", language := "Onge", iso := "oon", value := .initial }
  , { walsCode := "oya", language := "Oriya", iso := "ory", value := .final }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .final }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .noQuestionParticle }
  , { walsCode := "osa", language := "Osage", iso := "osa", value := .noQuestionParticle }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .initial }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .noQuestionParticle }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .noQuestionParticle }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .secondPosition }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .noQuestionParticle }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .noQuestionParticle }
  , { walsCode := "plk", language := "Palikur", iso := "plu", value := .initial }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .initial }
  , { walsCode := "pan", language := "Panjabi", iso := "pan", value := .initial }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .noQuestionParticle }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .noQuestionParticle }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .noQuestionParticle }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .noQuestionParticle }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .final }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .initial }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .initial }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .noQuestionParticle }
  , { walsCode := "prh", language := "Pirahã", iso := "myp", value := .final }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .final }
  , { walsCode := "ppi", language := "Pitta Pitta", iso := "pit", value := .noQuestionParticle }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .final }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .noQuestionParticle }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .final }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .initial }
  , { walsCode := "pme", language := "Pomo (Eastern)", iso := "peb", value := .noQuestionParticle }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .noQuestionParticle }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .noQuestionParticle }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .initial }
  , { walsCode := "puq", language := "Puquina", iso := "puq", value := .noQuestionParticle }
  , { walsCode := "prk", language := "Purki", iso := "prx", value := .noQuestionParticle }
  , { walsCode := "pae", language := "Páez", iso := "pbb", value := .noQuestionParticle }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .noQuestionParticle }
  , { walsCode := "qaw", language := "Qawasqar", iso := "alc", value := .noQuestionParticle }
  , { walsCode := "qia", language := "Qiang", iso := "", value := .noQuestionParticle }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .noQuestionParticle }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .final }
  , { walsCode := "qui", language := "Quileute", iso := "qui", value := .noQuestionParticle }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .initial }
  , { walsCode := "raw", language := "Rawang", iso := "raw", value := .final }
  , { walsCode := "rem", language := "Remo", iso := "bfw", value := .noQuestionParticle }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .initial }
  , { walsCode := "ret", language := "Retuarã", iso := "tnc", value := .initial }
  , { walsCode := "rit", language := "Ritharngu", iso := "rit", value := .final }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .initial }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .noQuestionParticle }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .final }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .initial }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .noQuestionParticle }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .noQuestionParticle }
  , { walsCode := "rum", language := "Rumu", iso := "klq", value := .final }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .noQuestionParticle }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .noQuestionParticle }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .secondPosition }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .noQuestionParticle }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .final }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .noQuestionParticle }
  , { walsCode := "syu", language := "Salt-Yui", iso := "sll", value := .noQuestionParticle }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .final }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .initial }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .final }
  , { walsCode := "sta", language := "Santa", iso := "sce", value := .noQuestionParticle }
  , { walsCode := "stl", language := "Santali", iso := "sat", value := .noQuestionParticle }
  , { walsCode := "snm", language := "Sanuma", iso := "xsu", value := .noQuestionParticle }
  , { walsCode := "sap", language := "Sapuan", iso := "spu", value := .final }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .noQuestionParticle }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .initial }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .noQuestionParticle }
  , { walsCode := "svs", language := "Savosavo", iso := "svs", value := .noQuestionParticle }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .otherPosition }
  , { walsCode := "sem", language := "Sema", iso := "nsm", value := .final }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .noQuestionParticle }
  , { walsCode := "smn", language := "Seminole", iso := "mus", value := .noQuestionParticle }
  , { walsCode := "scr", language := "Serbian-Croatian", iso := "hbs", value := .inEitherOfTwoPositions }
  , { walsCode := "ser", language := "Seri", iso := "sei", value := .final }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .noQuestionParticle }
  , { walsCode := "shh", language := "Sharanahua", iso := "mcd", value := .final }
  , { walsCode := "skw", language := "Shekhawati", iso := "swv", value := .noQuestionParticle }
  , { walsCode := "she", language := "Sherpa", iso := "xsr", value := .final }
  , { walsCode := "shl", language := "Shilluk", iso := "shk", value := .noQuestionParticle }
  , { walsCode := "sna", language := "Shina", iso := "scl", value := .noQuestionParticle }
  , { walsCode := "shk", language := "Shipibo-Konibo", iso := "shp", value := .secondPosition }
  , { walsCode := "shi", language := "Shiriana", iso := "shb", value := .final }
  , { walsCode := "ryu", language := "Shuri", iso := "ryu", value := .noQuestionParticle }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .inEitherOfTwoPositions }
  , { walsCode := "sia", language := "Siane", iso := "snp", value := .noQuestionParticle }
  , { walsCode := "sid", language := "Sidaama", iso := "sid", value := .noQuestionParticle }
  , { walsCode := "skk", language := "Sikkimese", iso := "sip", value := .final }
  , { walsCode := "sng", language := "Sinaugoro", iso := "snc", value := .final }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .final }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .initial }
  , { walsCode := "srn", language := "Sirionó", iso := "srq", value := .final }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .final }
  , { walsCode := "sko", language := "Skou", iso := "skv", value := .final }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .initial }
  , { walsCode := "so", language := "So", iso := "teu", value := .final }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .final }
  , { walsCode := "som", language := "Somali", iso := "som", value := .otherPosition }
  , { walsCode := "snn", language := "Soninke", iso := "snk", value := .final }
  , { walsCode := "son", language := "Sonsorol-Tobi", iso := "sov", value := .initial }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .noQuestionParticle }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .noQuestionParticle }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .secondPosition }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .final }
  , { walsCode := "sti", language := "Stieng", iso := "", value := .final }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .noQuestionParticle }
  , { walsCode := "sue", language := "Suena", iso := "sue", value := .noQuestionParticle }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .noQuestionParticle }
  , { walsCode := "slg", language := "Sulung", iso := "suv", value := .final }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .initial }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .final }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .initial }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .final }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .noQuestionParticle }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .noQuestionParticle }
  , { walsCode := "tbw", language := "Tabwa", iso := "tap", value := .noQuestionParticle }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .initial }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .secondPosition }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .secondPosition }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .noQuestionParticle }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .final }
  , { walsCode := "tkl", language := "Takelma", iso := "tkm", value := .secondPosition }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .final }
  , { walsCode := "tam", language := "Tamang (Eastern)", iso := "taj", value := .final }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .initial }
  , { walsCode := "tml", language := "Tamil", iso := "tam", value := .noQuestionParticle }
  , { walsCode := "tbx", language := "Tangbe", iso := "skj", value := .noQuestionParticle }
  , { walsCode := "tao", language := "Tarao", iso := "tro", value := .final }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .noQuestionParticle }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .final }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .otherPosition }
  , { walsCode := "tel", language := "Telugu", iso := "tel", value := .noQuestionParticle }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .final }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .noQuestionParticle }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .final }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .noQuestionParticle }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .initial }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .secondPosition }
  , { walsCode := "tps", language := "Tepehuan (Southeastern)", iso := "stp", value := .noQuestionParticle }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .final }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .final }
  , { walsCode := "tet", language := "Tetela", iso := "tll", value := .final }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .final }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .final }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .inEitherOfTwoPositions }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .noQuestionParticle }
  , { walsCode := "tib", language := "Tibetan (Standard Spoken)", iso := "bod", value := .final }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .noQuestionParticle }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .final }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .final }
  , { walsCode := "tni", language := "Tinani", iso := "lbf", value := .noQuestionParticle }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .otherPosition }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .noQuestionParticle }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .final }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .initial }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .noQuestionParticle }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .noQuestionParticle }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .noQuestionParticle }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .initial }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .noQuestionParticle }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .initial }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .final }
  , { walsCode := "tsf", language := "Tsafiki", iso := "cof", value := .noQuestionParticle }
  , { walsCode := "tsz", language := "Tsez", iso := "ddo", value := .noQuestionParticle }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .final }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .noQuestionParticle }
  , { walsCode := "tsn", language := "Tsonga", iso := "tso", value := .inEitherOfTwoPositions }
  , { walsCode := "ttu", language := "Tsova-Tush", iso := "bbl", value := .secondPosition }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .noQuestionParticle }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .final }
  , { walsCode := "tuc", language := "Tucano", iso := "tuo", value := .noQuestionParticle }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .final }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .final }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .noQuestionParticle }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .final }
  , { walsCode := "tur", language := "Turkish", iso := "tur", value := .final }
  , { walsCode := "tus", language := "Tuscarora", iso := "tus", value := .secondPosition }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .noQuestionParticle }
  , { walsCode := "tvt", language := "Tutsa", iso := "tvt", value := .final }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .noQuestionParticle }
  , { walsCode := "tuv", language := "Tuvan", iso := "tyv", value := .final }
  , { walsCode := "tuy", language := "Tuyuca", iso := "tue", value := .noQuestionParticle }
  , { walsCode := "tzo", language := "Tzotzil", iso := "tzo", value := .initial }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .initial }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .secondPosition }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .noQuestionParticle }
  , { walsCode := "udh", language := "Udihe", iso := "ude", value := .noQuestionParticle }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .initial }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .final }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .noQuestionParticle }
  , { walsCode := "una", language := "Una", iso := "mtg", value := .noQuestionParticle }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .final }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .final }
  , { walsCode := "urd", language := "Urdu", iso := "urd", value := .initial }
  , { walsCode := "urk", language := "Urubú-Kaapor", iso := "urb", value := .final }
  , { walsCode := "usa", language := "Usan", iso := "wnu", value := .noQuestionParticle }
  , { walsCode := "usr", language := "Usarufa", iso := "usa", value := .noQuestionParticle }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .secondPosition }
  , { walsCode := "uzb", language := "Uzbek", iso := "", value := .noQuestionParticle }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .final }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .noQuestionParticle }
  , { walsCode := "wwa", language := "Waama", iso := "wwa", value := .final }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .final }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .noQuestionParticle }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .final }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .noQuestionParticle }
  , { walsCode := "wap", language := "Wappo", iso := "wao", value := .noQuestionParticle }
  , { walsCode := "wra", language := "Warao", iso := "wba", value := .noQuestionParticle }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .noQuestionParticle }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .noQuestionParticle }
  , { walsCode := "wrl", language := "Warlpiri", iso := "wbp", value := .secondPosition }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .noQuestionParticle }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .noQuestionParticle }
  , { walsCode := "was", language := "Washo", iso := "was", value := .final }
  , { walsCode := "wtm", language := "Watam", iso := "wax", value := .noQuestionParticle }
  , { walsCode := "wth", language := "Wathawurrung", iso := "wth", value := .initial }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .secondPosition }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .initial }
  , { walsCode := "wem", language := "Wembawemba", iso := "xww", value := .noQuestionParticle }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .noQuestionParticle }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .initial }
  , { walsCode := "wn", language := "Wik Ngathana", iso := "wig", value := .final }
  , { walsCode := "wik", language := "Wikchamni", iso := "yok", value := .initial }
  , { walsCode := "wiy", language := "Wiyot", iso := "wiy", value := .secondPosition }
  , { walsCode := "wly", language := "Wolaytta", iso := "wal", value := .noQuestionParticle }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .noQuestionParticle }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .initial }
  , { walsCode := "xas", language := "Xasonga", iso := "kao", value := .inEitherOfTwoPositions }
  , { walsCode := "xav", language := "Xavánte", iso := "xav", value := .initial }
  , { walsCode := "ygr", language := "Yagaria", iso := "ygr", value := .final }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .secondPosition }
  , { walsCode := "yal", language := "Yale (Kosarek)", iso := "kkl", value := .noQuestionParticle }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .noQuestionParticle }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .initial }
  , { walsCode := "yar", language := "Yareba", iso := "yrb", value := .final }
  , { walsCode := "ywl", language := "Yawelmani", iso := "yok", value := .initial }
  , { walsCode := "yid", language := "Yidiny", iso := "yii", value := .noQuestionParticle }
  , { walsCode := "yin", language := "Yindjibarndi", iso := "yij", value := .final }
  , { walsCode := "yng", language := "Yingkarta", iso := "yia", value := .noQuestionParticle }
  , { walsCode := "yok", language := "Yokuts (Yaudanchi)", iso := "yok", value := .initial }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .noQuestionParticle }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .secondPosition }
  , { walsCode := "yko", language := "Yukaghir (Kolyma)", iso := "yux", value := .noQuestionParticle }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .initial }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .final }
  , { walsCode := "ypk", language := "Yup'ik (Central)", iso := "esu", value := .secondPosition }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .secondPosition }
  , { walsCode := "yuw", language := "Yuwaalaraay", iso := "kld", value := .initial }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .final }
  , { walsCode := "zap", language := "Zapotec (Mitla)", iso := "zaw", value := .initial }
  , { walsCode := "zya", language := "Zapotec (Yatzachi)", iso := "zav", value := .initial }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .noQuestionParticle }
  , { walsCode := "zay", language := "Zayse", iso := "zay", value := .noQuestionParticle }
  , { walsCode := "zaz", language := "Zazaki", iso := "diq", value := .noQuestionParticle }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .final }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .noQuestionParticle }
  , { walsCode := "zqc", language := "Zoque (Copainalá)", iso := "zoc", value := .noQuestionParticle }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .final }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .secondPosition }
  ]

/-- Complete WALS 92A dataset (884 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 884 := by native_decide

theorem count_initial :
    (allData.filter (·.value == .initial)).length = 129 := by native_decide
theorem count_final :
    (allData.filter (·.value == .final)).length = 314 := by native_decide
theorem count_secondPosition :
    (allData.filter (·.value == .secondPosition)).length = 52 := by native_decide
theorem count_otherPosition :
    (allData.filter (·.value == .otherPosition)).length = 8 := by native_decide
theorem count_inEitherOfTwoPositions :
    (allData.filter (·.value == .inEitherOfTwoPositions)).length = 26 := by native_decide
theorem count_noQuestionParticle :
    (allData.filter (·.value == .noQuestionParticle)).length = 355 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F92A
