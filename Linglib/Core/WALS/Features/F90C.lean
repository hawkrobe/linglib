/-!
# WALS Feature 90C: Postnominal relative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 90C`.

Chapter 90, 620 languages.
-/

namespace Core.WALS.F90C

/-- WALS 90C values. -/
inductive PostnominalRelativeClauses where
  | nounRelativeClauseDominant  -- Noun-Relative clause (NRel) dominant (579 languages)
  | nrelOrReln  -- NRel or RelN (31 languages)
  | nrelOrInternallyHeaded  -- NRel or internally-headed (8 languages)
  | nrelOrCorrelative  -- NRel or correlative (2 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 90C datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : PostnominalRelativeClauses
  deriving Repr, BEq, DecidableEq

private def allData_0 : List Datapoint :=
  [ { walsCode := "xoo", language := "!Xóõ", iso := "nmn", value := .nounRelativeClauseDominant }
  , { walsCode := "huc", language := "=|Hoan", iso := "huc", value := .nounRelativeClauseDominant }
  , { walsCode := "aar", language := "Aari", iso := "aiw", value := .nounRelativeClauseDominant }
  , { walsCode := "abi", language := "Abipón", iso := "axb", value := .nounRelativeClauseDominant }
  , { walsCode := "abv", language := "Abui", iso := "abz", value := .nounRelativeClauseDominant }
  , { walsCode := "abu", language := "Abun", iso := "kgr", value := .nounRelativeClauseDominant }
  , { walsCode := "ace", language := "Acehnese", iso := "ace", value := .nounRelativeClauseDominant }
  , { walsCode := "acg", language := "Achagua", iso := "aca", value := .nounRelativeClauseDominant }
  , { walsCode := "acl", language := "Acholi", iso := "ach", value := .nounRelativeClauseDominant }
  , { walsCode := "adi", language := "Adioukrou", iso := "adj", value := .nounRelativeClauseDominant }
  , { walsCode := "adz", language := "Adzera", iso := "adz", value := .nounRelativeClauseDominant }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .nounRelativeClauseDominant }
  , { walsCode := "all", language := "Ala'ala", iso := "nrz", value := .nounRelativeClauseDominant }
  , { walsCode := "alb", language := "Albanian", iso := "sqi", value := .nounRelativeClauseDominant }
  , { walsCode := "aly", language := "Alyawarra", iso := "aly", value := .nounRelativeClauseDominant }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .nounRelativeClauseDominant }
  , { walsCode := "amq", language := "Ambai", iso := "amk", value := .nounRelativeClauseDominant }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .nounRelativeClauseDominant }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .nounRelativeClauseDominant }
  , { walsCode := "anj", language := "Anejom", iso := "aty", value := .nounRelativeClauseDominant }
  , { walsCode := "agm", language := "Angami", iso := "njm", value := .nounRelativeClauseDominant }
  , { walsCode := "anc", language := "Angas", iso := "anc", value := .nounRelativeClauseDominant }
  , { walsCode := "ang", language := "Anggor", iso := "agg", value := .nounRelativeClauseDominant }
  , { walsCode := "anu", language := "Anufo", iso := "cko", value := .nounRelativeClauseDominant }
  , { walsCode := "any", language := "Anywa", iso := "anu", value := .nounRelativeClauseDominant }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .nounRelativeClauseDominant }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .nounRelativeClauseDominant }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .nounRelativeClauseDominant }
  , { walsCode := "arg", language := "Arabic (Gulf)", iso := "afb", value := .nounRelativeClauseDominant }
  , { walsCode := "arq", language := "Arabic (Iraqi)", iso := "acm", value := .nounRelativeClauseDominant }
  , { walsCode := "arj", language := "Arabic (Kuwaiti)", iso := "afb", value := .nounRelativeClauseDominant }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .nounRelativeClauseDominant }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .nounRelativeClauseDominant }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .nounRelativeClauseDominant }
  , { walsCode := "abo", language := "Arbore", iso := "arv", value := .nounRelativeClauseDominant }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .nrelOrReln }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .nounRelativeClauseDominant }
  , { walsCode := "alk", language := "Arop-Lokep", iso := "apr", value := .nounRelativeClauseDominant }
  , { walsCode := "aro", language := "Arosi", iso := "aia", value := .nounRelativeClauseDominant }
  , { walsCode := "amp", language := "Arrernte (Mparntwe)", iso := "aer", value := .nounRelativeClauseDominant }
  , { walsCode := "awe", language := "Arrernte (Western)", iso := "are", value := .nounRelativeClauseDominant }
  , { walsCode := "azi", language := "Azari (Iranian)", iso := "azb", value := .nrelOrReln }
  , { walsCode := "bbl", language := "Babole", iso := "bvx", value := .nounRelativeClauseDominant }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .nounRelativeClauseDominant }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .nounRelativeClauseDominant }
  , { walsCode := "bag", language := "Bagirmi", iso := "bmi", value := .nounRelativeClauseDominant }
  , { walsCode := "bgr", language := "Bagiro", iso := "fuu", value := .nounRelativeClauseDominant }
  , { walsCode := "baj", language := "Bajau (Sama)", iso := "bdl", value := .nounRelativeClauseDominant }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .nounRelativeClauseDominant }
  , { walsCode := "bka", language := "Baka (in South Sudan)", iso := "bdh", value := .nounRelativeClauseDominant }
  , { walsCode := "bku", language := "Bakueri", iso := "bri", value := .nounRelativeClauseDominant }
  , { walsCode := "bvi", language := "Bali-Vitu", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "baa", language := "Barai", iso := "bbb", value := .nounRelativeClauseDominant }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .nounRelativeClauseDominant }
  , { walsCode := "brs", language := "Barasano", iso := "bsn", value := .nounRelativeClauseDominant }
  , { walsCode := "bar", language := "Bari", iso := "bfa", value := .nounRelativeClauseDominant }
  , { walsCode := "brp", language := "Barupu", iso := "bpe", value := .nounRelativeClauseDominant }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .nounRelativeClauseDominant }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .nounRelativeClauseDominant }
  , { walsCode := "bto", language := "Batak (Toba)", iso := "bbc", value := .nounRelativeClauseDominant }
  , { walsCode := "baq", language := "Baure", iso := "brg", value := .nounRelativeClauseDominant }
  , { walsCode := "bej", language := "Beja", iso := "bej", value := .nounRelativeClauseDominant }
  , { walsCode := "bco", language := "Bella Coola", iso := "blc", value := .nounRelativeClauseDominant }
  , { walsCode := "blr", language := "Belorussian", iso := "bel", value := .nounRelativeClauseDominant }
  , { walsCode := "bfg", language := "Berber (Figuig)", iso := "grr", value := .nounRelativeClauseDominant }
  , { walsCode := "bma", language := "Berber (Middle Atlas)", iso := "tzm", value := .nounRelativeClauseDominant }
  , { walsCode := "brf", language := "Berber (Rif)", iso := "rif", value := .nounRelativeClauseDominant }
  , { walsCode := "zag", language := "Beria", iso := "zag", value := .nounRelativeClauseDominant }
  , { walsCode := "ber", language := "Berta", iso := "wti", value := .nounRelativeClauseDominant }
  , { walsCode := "bik", language := "Biak", iso := "bhw", value := .nounRelativeClauseDominant }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .nounRelativeClauseDominant }
  , { walsCode := "bil", language := "Bilua", iso := "blb", value := .nrelOrReln }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .nounRelativeClauseDominant }
  , { walsCode := "bni", language := "Bini", iso := "bin", value := .nounRelativeClauseDominant }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .nounRelativeClauseDominant }
  , { walsCode := "bir", language := "Birom", iso := "bom", value := .nounRelativeClauseDominant }
  , { walsCode := "bla", language := "Blackfoot", iso := "bla", value := .nrelOrReln }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .nounRelativeClauseDominant }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .nrelOrReln }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .nounRelativeClauseDominant }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .nounRelativeClauseDominant }
  , { walsCode := "brh", language := "Brahui", iso := "brh", value := .nounRelativeClauseDominant }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .nounRelativeClauseDominant }
  , { walsCode := "bud", language := "Buduma", iso := "bdm", value := .nounRelativeClauseDominant }
  , { walsCode := "bug", language := "Bugis", iso := "bug", value := .nounRelativeClauseDominant }
  , { walsCode := "bul", language := "Bulgarian", iso := "bul", value := .nounRelativeClauseDominant }
  , { walsCode := "bum", language := "Buma", iso := "tkw", value := .nounRelativeClauseDominant }
  , { walsCode := "buu", language := "Buru", iso := "mhs", value := .nounRelativeClauseDominant }
  , { walsCode := "brn", language := "Burunge", iso := "bds", value := .nounRelativeClauseDominant }
  , { walsCode := "bus", language := "Busa", iso := "bqp", value := .nounRelativeClauseDominant }
  , { walsCode := "bsh", language := "Bushoong", iso := "buf", value := .nounRelativeClauseDominant }
  , { walsCode := "cah", language := "Cahuilla", iso := "chl", value := .nounRelativeClauseDominant }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .nounRelativeClauseDominant }
  , { walsCode := "cax", language := "Campa (Axininca)", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "cnm", language := "Canamarí", iso := "knm", value := .nounRelativeClauseDominant }
  , { walsCode := "cnl", language := "Canela", iso := "ram", value := .nrelOrInternallyHeaded }
  , { walsCode := "cde", language := "Carib (De'kwana)", iso := "mch", value := .nounRelativeClauseDominant }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .nounRelativeClauseDominant }
  , { walsCode := "cav", language := "Cavineña", iso := "cav", value := .nounRelativeClauseDominant }
  , { walsCode := "ceb", language := "Cebuano", iso := "ceb", value := .nounRelativeClauseDominant }
  , { walsCode := "cld", language := "Chaldean (Modern)", iso := "cld", value := .nounRelativeClauseDominant }
  , { walsCode := "chw", language := "Cham (Western)", iso := "cja", value := .nounRelativeClauseDominant }
  , { walsCode := "cha", language := "Chamorro", iso := "cha", value := .nounRelativeClauseDominant }
  , { walsCode := "cso", language := "Chatino (Sierra Occidental)", iso := "ctp", value := .nounRelativeClauseDominant }
  , { walsCode := "cya", language := "Chatino (Yaitepec)", iso := "ctp", value := .nounRelativeClauseDominant }
  , { walsCode := "cmh", language := "Chemehuevi", iso := "ute", value := .nounRelativeClauseDominant }
  , { walsCode := "cic", language := "Chichewa", iso := "nya", value := .nounRelativeClauseDominant }
  , { walsCode := "ccm", language := "Chinantec (Comaltepec)", iso := "cco", value := .nounRelativeClauseDominant }
  , { walsCode := "cle", language := "Chinantec (Lealao)", iso := "cle", value := .nounRelativeClauseDominant }
  , { walsCode := "cpl", language := "Chinantec (Palantla)", iso := "cpa", value := .nounRelativeClauseDominant }
  , { walsCode := "chq", language := "Chinantec (Quiotepec)", iso := "chq", value := .nounRelativeClauseDominant }
  , { walsCode := "chp", language := "Chipewyan", iso := "chp", value := .nounRelativeClauseDominant }
  , { walsCode := "ctm", language := "Chitimacha", iso := "ctm", value := .nounRelativeClauseDominant }
  , { walsCode := "cmy", language := "Chontal Maya", iso := "chf", value := .nounRelativeClauseDominant }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .nounRelativeClauseDominant }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .nounRelativeClauseDominant }
  , { walsCode := "chk", language := "Chukchi", iso := "ckt", value := .nrelOrReln }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .nounRelativeClauseDominant }
  , { walsCode := "coo", language := "Coos (Hanis)", iso := "csz", value := .nounRelativeClauseDominant }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .nounRelativeClauseDominant }
  , { walsCode := "cor", language := "Cora", iso := "crn", value := .nounRelativeClauseDominant }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .nounRelativeClauseDominant }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .nounRelativeClauseDominant }
  , { walsCode := "cze", language := "Czech", iso := "ces", value := .nounRelativeClauseDominant }
  , { walsCode := "cem", language := "Cèmuhî", iso := "cam", value := .nounRelativeClauseDominant }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .nounRelativeClauseDominant }
  , { walsCode := "dag", language := "Daga", iso := "dgz", value := .nounRelativeClauseDominant }
  , { walsCode := "dan", language := "Dan", iso := "dnj", value := .nounRelativeClauseDominant }
  , { walsCode := "dni", language := "Dani (Lower Grand Valley)", iso := "dni", value := .nounRelativeClauseDominant }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .nounRelativeClauseDominant }
  , { walsCode := "day", language := "Day", iso := "dai", value := .nounRelativeClauseDominant }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .nounRelativeClauseDominant }
  , { walsCode := "des", language := "Desano", iso := "des", value := .nounRelativeClauseDominant }
  , { walsCode := "did", language := "Didinga", iso := "did", value := .nounRelativeClauseDominant }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .nounRelativeClauseDominant }
  , { walsCode := "dio", language := "Diola-Fogny", iso := "dyo", value := .nounRelativeClauseDominant }
  , { walsCode := "djm", language := "Djambarrpuyngu", iso := "djr", value := .nounRelativeClauseDominant }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .nounRelativeClauseDominant }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .nounRelativeClauseDominant }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .nounRelativeClauseDominant }
  , { walsCode := "duk", language := "Duka", iso := "dud", value := .nounRelativeClauseDominant }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .nounRelativeClauseDominant }
  , { walsCode := "dyi", language := "Dyirbal", iso := "dbl", value := .nounRelativeClauseDominant }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .nounRelativeClauseDominant }
  , { walsCode := "efi", language := "Efik", iso := "efi", value := .nounRelativeClauseDominant }
  , { walsCode := "emb", language := "Emberá (Northern)", iso := "emp", value := .nounRelativeClauseDominant }
  , { walsCode := "egn", language := "Engenni", iso := "enn", value := .nounRelativeClauseDominant }
  , { walsCode := "eno", language := "Enggano", iso := "eno", value := .nounRelativeClauseDominant }
  , { walsCode := "eng", language := "English", iso := "eng", value := .nounRelativeClauseDominant }
  , { walsCode := "err", language := "Erromangan", iso := "erg", value := .nounRelativeClauseDominant }
  , { walsCode := "est", language := "Estonian", iso := "ekk", value := .nounRelativeClauseDominant }
  , { walsCode := "eud", language := "Eudeve", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .nounRelativeClauseDominant }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .nounRelativeClauseDominant }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .nounRelativeClauseDominant }
  , { walsCode := "fin", language := "Finnish", iso := "fin", value := .nounRelativeClauseDominant }
  , { walsCode := "fon", language := "Fongbe", iso := "fon", value := .nounRelativeClauseDominant }
  , { walsCode := "fre", language := "French", iso := "fra", value := .nounRelativeClauseDominant }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .nounRelativeClauseDominant }
  , { walsCode := "fua", language := "Fulfulde (Adamawa)", iso := "fub", value := .nounRelativeClauseDominant }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .nounRelativeClauseDominant }
  , { walsCode := "fut", language := "Futuna-Aniwa", iso := "fut", value := .nounRelativeClauseDominant }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .nounRelativeClauseDominant }
  , { walsCode := "gnd", language := "Ga'anda", iso := "gqa", value := .nounRelativeClauseDominant }
  , { walsCode := "gae", language := "Gaelic (Scots)", iso := "gla", value := .nounRelativeClauseDominant }
  , { walsCode := "gah", language := "Gahuku", iso := "gah", value := .nrelOrReln }
  , { walsCode := "gap", language := "Gapapaiwa", iso := "pwg", value := .nounRelativeClauseDominant }
  , { walsCode := "grf", language := "Garífuna", iso := "cab", value := .nounRelativeClauseDominant }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .nounRelativeClauseDominant }
  , { walsCode := "gel", language := "Gela", iso := "nlg", value := .nounRelativeClauseDominant }
  , { walsCode := "geo", language := "Georgian", iso := "kat", value := .nounRelativeClauseDominant }
  , { walsCode := "ger", language := "German", iso := "deu", value := .nounRelativeClauseDominant }
  , { walsCode := "gim", language := "Gimira", iso := "bcq", value := .nrelOrReln }
  , { walsCode := "god", language := "Godoberi", iso := "gdo", value := .nrelOrReln }
  , { walsCode := "gok", language := "Gokana", iso := "gkn", value := .nounRelativeClauseDominant }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .nounRelativeClauseDominant }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .nounRelativeClauseDominant }
  , { walsCode := "grw", language := "Greenlandic (West)", iso := "kal", value := .nounRelativeClauseDominant }
  , { walsCode := "ghb", language := "Guahibo", iso := "guh", value := .nounRelativeClauseDominant }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .nounRelativeClauseDominant }
  , { walsCode := "gul", language := "Gula (in Central African Republic)", iso := "kcm", value := .nounRelativeClauseDominant }
  , { walsCode := "gmw", language := "Gumawana", iso := "gvs", value := .nrelOrInternallyHeaded }
  , { walsCode := "gum", language := "Gumbaynggir", iso := "kgs", value := .nounRelativeClauseDominant }
  , { walsCode := "gmz", language := "Gumuz", iso := "guk", value := .nounRelativeClauseDominant }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .nounRelativeClauseDominant }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .nounRelativeClauseDominant }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .nounRelativeClauseDominant }
  , { walsCode := "hat", language := "Hatam", iso := "had", value := .nounRelativeClauseDominant }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .nounRelativeClauseDominant }
  , { walsCode := "haw", language := "Hawaiian", iso := "haw", value := .nounRelativeClauseDominant }
  , { walsCode := "hwr", language := "Hawrami", iso := "hac", value := .nounRelativeClauseDominant }
  , { walsCode := "hya", language := "Haya", iso := "hay", value := .nounRelativeClauseDominant }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .nounRelativeClauseDominant }
  , { walsCode := "heb", language := "Hebrew (Modern)", iso := "heb", value := .nounRelativeClauseDominant }
  , { walsCode := "hei", language := "Heiltsuk", iso := "hei", value := .nounRelativeClauseDominant }
  , { walsCode := "hid", language := "Hidatsa", iso := "hid", value := .nounRelativeClauseDominant }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .nounRelativeClauseDominant }
  , { walsCode := "hmo", language := "Hmong Njua", iso := "hnj", value := .nounRelativeClauseDominant }
  , { walsCode := "hoa", language := "Hoava", iso := "hoa", value := .nounRelativeClauseDominant }
  , { walsCode := "hol", language := "Holoholo", iso := "hoo", value := .nounRelativeClauseDominant }
  , { walsCode := "htc", language := "Huastec", iso := "hus", value := .nounRelativeClauseDominant }
  , { walsCode := "hve", language := "Huave (San Mateo del Mar)", iso := "huv", value := .nounRelativeClauseDominant }
  , { walsCode := "hui", language := "Huichol", iso := "hch", value := .nounRelativeClauseDominant }
  , { walsCode := "hnd", language := "Hunde", iso := "hke", value := .nounRelativeClauseDominant }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .nrelOrReln }
  , { walsCode := "hup", language := "Hupa", iso := "hup", value := .nounRelativeClauseDominant }
  , { walsCode := "isa", language := "I'saka", iso := "ksi", value := .nounRelativeClauseDominant }
  , { walsCode := "iaa", language := "Iaai", iso := "iai", value := .nounRelativeClauseDominant }
  , { walsCode := "iau", language := "Iau", iso := "tmu", value := .nounRelativeClauseDominant }
  , { walsCode := "iba", language := "Iban", iso := "iba", value := .nounRelativeClauseDominant }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .nounRelativeClauseDominant }
  , { walsCode := "idn", language := "Iduna", iso := "viv", value := .nounRelativeClauseDominant }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .nounRelativeClauseDominant }
  , { walsCode := "ifu", language := "Ifugao (Batad)", iso := "ifb", value := .nounRelativeClauseDominant }
  , { walsCode := "igb", language := "Igbo", iso := "ibo", value := .nounRelativeClauseDominant }
  , { walsCode := "ign", language := "Ignaciano", iso := "ign", value := .nounRelativeClauseDominant }
  , { walsCode := "ik", language := "Ik", iso := "ikx", value := .nounRelativeClauseDominant }
  , { walsCode := "ila", language := "Ila", iso := "ilb", value := .nounRelativeClauseDominant }
  , { walsCode := "ind", language := "Indonesian", iso := "ind", value := .nounRelativeClauseDominant }
  , { walsCode := "igs", language := "Ingessana", iso := "tbi", value := .nounRelativeClauseDominant }
  , { walsCode := "irq", language := "Iraqw", iso := "irk", value := .nounRelativeClauseDominant }
  , { walsCode := "iri", language := "Irish", iso := "gle", value := .nounRelativeClauseDominant }
  , { walsCode := "ita", language := "Italian", iso := "ita", value := .nounRelativeClauseDominant }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .nounRelativeClauseDominant }
  , { walsCode := "jab", language := "Jabêm", iso := "jae", value := .nounRelativeClauseDominant }
  , { walsCode := "jak", language := "Jakaltek", iso := "jac", value := .nounRelativeClauseDominant }
  , { walsCode := "jeb", language := "Jebero", iso := "jeb", value := .nounRelativeClauseDominant }
  , { walsCode := "juk", language := "Jukun", iso := "jbu", value := .nounRelativeClauseDominant }
  , { walsCode := "jmo", language := "Jur Mödö", iso := "bex", value := .nounRelativeClauseDominant }
  , { walsCode := "juh", language := "Ju|'hoan", iso := "ktz", value := .nounRelativeClauseDominant }
  , { walsCode := "kbt", language := "Kabatei", iso := "xkp", value := .nounRelativeClauseDominant }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .nounRelativeClauseDominant }
  , { walsCode := "kgr", language := "Kagulu", iso := "kki", value := .nounRelativeClauseDominant }
  , { walsCode := "krr", language := "Kairiru", iso := "kxa", value := .nounRelativeClauseDominant }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .nounRelativeClauseDominant }
  , { walsCode := "kmz", language := "Kamasau", iso := "kms", value := .nrelOrReln }
  , { walsCode := "kam", language := "Kambera", iso := "xbr", value := .nounRelativeClauseDominant }
  , { walsCode := "kan", language := "Kana", iso := "ogo", value := .nounRelativeClauseDominant }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .nounRelativeClauseDominant }
  , { walsCode := "knr", language := "Kanuri", iso := "knc", value := .nounRelativeClauseDominant }
  , { walsCode := "kyo", language := "Kanyok", iso := "kny", value := .nounRelativeClauseDominant }
  , { walsCode := "kpm", language := "Kapampangan", iso := "pam", value := .nounRelativeClauseDominant }
  , { walsCode := "kar", language := "Kara (in Central African Republic)", iso := "kah", value := .nounRelativeClauseDominant }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .nounRelativeClauseDominant }
  , { walsCode := "kpw", language := "Karen (Pwo)", iso := "kjp", value := .nounRelativeClauseDominant }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .nounRelativeClauseDominant }
  , { walsCode := "kmj", language := "Karimojong", iso := "kdj", value := .nounRelativeClauseDominant }
  , { walsCode := "kas", language := "Kashmiri", iso := "kas", value := .nrelOrCorrelative }
  , { walsCode := "ktc", language := "Katcha", iso := "xtc", value := .nounRelativeClauseDominant }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .nounRelativeClauseDominant }
  , { walsCode := "kau", language := "Kaulong", iso := "pss", value := .nounRelativeClauseDominant }
  , { walsCode := "kws", language := "Kawaiisu", iso := "xaw", value := .nounRelativeClauseDominant }
  , { walsCode := "kyl", language := "Kayah Li (Eastern)", iso := "eky", value := .nounRelativeClauseDominant }
  , { walsCode := "kay", language := "Kayardild", iso := "gyd", value := .nounRelativeClauseDominant }
  , { walsCode := "kel", language := "Kele", iso := "sbc", value := .nounRelativeClauseDominant }
  , { walsCode := "ken", language := "Kenga", iso := "kyq", value := .nounRelativeClauseDominant }
  , { walsCode := "ker", language := "Kera", iso := "ker", value := .nounRelativeClauseDominant }
  , { walsCode := "kte", language := "Kete", iso := "kcv", value := .nounRelativeClauseDominant }
  , { walsCode := "khl", language := "Khalaj", iso := "klj", value := .nounRelativeClauseDominant }
  , { walsCode := "knz", language := "Kham (Tibetan) (Nangchen)", iso := "khg", value := .nounRelativeClauseDominant }
  , { walsCode := "khs", language := "Khasi", iso := "kha", value := .nounRelativeClauseDominant }
  , { walsCode := "khm", language := "Khmer", iso := "khm", value := .nounRelativeClauseDominant }
  , { walsCode := "kik", language := "Kikuyu", iso := "kik", value := .nounRelativeClauseDominant }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .nounRelativeClauseDominant }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .nounRelativeClauseDominant }
  , { walsCode := "kri", language := "Kipea", iso := "kzw", value := .nounRelativeClauseDominant }
  , { walsCode := "krb", language := "Kiribati", iso := "gil", value := .nounRelativeClauseDominant }
  , { walsCode := "kir", language := "Kirma", iso := "cme", value := .nounRelativeClauseDominant }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .nounRelativeClauseDominant }
  , { walsCode := "klm", language := "Klamath", iso := "kla", value := .nounRelativeClauseDominant }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .nounRelativeClauseDominant }
  , { walsCode := "kkt", language := "Kokota", iso := "kkk", value := .nounRelativeClauseDominant }
  , { walsCode := "klr", language := "Koluri", iso := "shm", value := .nounRelativeClauseDominant }
  , { walsCode := "xbi", language := "Kombio", iso := "xbi", value := .nounRelativeClauseDominant }
  , { walsCode := "kni", language := "Konni", iso := "kma", value := .nounRelativeClauseDominant }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .nrelOrReln }
  , { walsCode := "kje", language := "Koreguaje", iso := "coe", value := .nounRelativeClauseDominant }
  , { walsCode := "kfe", language := "Koromfe", iso := "kfz", value := .nounRelativeClauseDominant }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .nrelOrReln }
  , { walsCode := "kos", language := "Kosraean", iso := "kos", value := .nounRelativeClauseDominant }
  , { walsCode := "kch", language := "Koyra Chiini", iso := "khq", value := .nounRelativeClauseDominant }
  , { walsCode := "kse", language := "Koyraboro Senni", iso := "ses", value := .nounRelativeClauseDominant }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .nounRelativeClauseDominant }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .nounRelativeClauseDominant }
  , { walsCode := "knc", language := "Kugu Nganhcara", iso := "uwa", value := .nounRelativeClauseDominant }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .nrelOrReln }
  , { walsCode := "knm", language := "Kunama", iso := "kun", value := .nounRelativeClauseDominant }
  , { walsCode := "kuo", language := "Kuot", iso := "kto", value := .nounRelativeClauseDominant }
  , { walsCode := "krd", language := "Kurdish (Central)", iso := "ckb", value := .nounRelativeClauseDominant }
  , { walsCode := "thy", language := "Kuuk Thaayorre", iso := "thd", value := .nounRelativeClauseDominant }
  , { walsCode := "kwn", language := "Kwangali", iso := "kwn", value := .nounRelativeClauseDominant }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .nounRelativeClauseDominant }
  , { walsCode := "kgy", language := "Kyirong", iso := "kgy", value := .nrelOrReln }
  , { walsCode := "kyq", language := "Kyuquot", iso := "nuk", value := .nounRelativeClauseDominant }
  , { walsCode := "lab", language := "Labu", iso := "lbu", value := .nounRelativeClauseDominant }
  , { walsCode := "lal", language := "Lalo", iso := "ywt", value := .nrelOrReln }
  , { walsCode := "lmh", language := "Lamaholot", iso := "slp", value := .nounRelativeClauseDominant }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .nounRelativeClauseDominant }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .nounRelativeClauseDominant }
  , { walsCode := "lmp", language := "Lampung", iso := "ljp", value := .nounRelativeClauseDominant }
  , { walsCode := "lan", language := "Lango", iso := "laj", value := .nounRelativeClauseDominant }
  , { walsCode := "lao", language := "Lao", iso := "lao", value := .nounRelativeClauseDominant }
  , { walsCode := "lat", language := "Latvian", iso := "lav", value := .nounRelativeClauseDominant }
  , { walsCode := "leg", language := "Lega", iso := "lea", value := .nounRelativeClauseDominant }
  , { walsCode := "lel", language := "Lele", iso := "lln", value := .nounRelativeClauseDominant }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .nounRelativeClauseDominant }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .nrelOrReln }
  , { walsCode := "let", language := "Leti", iso := "lti", value := .nounRelativeClauseDominant }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .nounRelativeClauseDominant }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .nounRelativeClauseDominant }
  , { walsCode := "lit", language := "Lithuanian", iso := "lit", value := .nounRelativeClauseDominant }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .nounRelativeClauseDominant }
  , { walsCode := "ara", language := "Lokono", iso := "arw", value := .nrelOrReln }
  , { walsCode := "lgu", language := "Longgu", iso := "lgu", value := .nounRelativeClauseDominant }
  , { walsCode := "lon", language := "Loniu", iso := "los", value := .nounRelativeClauseDominant }
  , { walsCode := "lda", language := "Luganda", iso := "lug", value := .nounRelativeClauseDominant }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .nounRelativeClauseDominant }
  , { walsCode := "lui", language := "Luiseño", iso := "lui", value := .nounRelativeClauseDominant }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .nounRelativeClauseDominant }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .nounRelativeClauseDominant }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .nounRelativeClauseDominant }
  , { walsCode := "myn", language := "Ma'anyan", iso := "mhy", value := .nounRelativeClauseDominant }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .nounRelativeClauseDominant }
  , { walsCode := "maa", language := "Maasai", iso := "mas", value := .nounRelativeClauseDominant }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .nounRelativeClauseDominant }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .nrelOrReln }
  , { walsCode := "mpr", language := "Maipure", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "mai", language := "Maithili", iso := "mai", value := .nrelOrCorrelative }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .nounRelativeClauseDominant }
  , { walsCode := "mak", language := "Makah", iso := "myh", value := .nrelOrReln }
  , { walsCode := "mkj", language := "Makasae", iso := "mkz", value := .nounRelativeClauseDominant }
  , { walsCode := "mal", language := "Malagasy", iso := "plt", value := .nounRelativeClauseDominant }
  , { walsCode := "mlu", language := "Maleu", iso := "mgl", value := .nounRelativeClauseDominant }
  , { walsCode := "mlg", language := "Malgwa", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "mam", language := "Mam", iso := "mam", value := .nounRelativeClauseDominant }
  , { walsCode := "mmn", language := "Mamanwa", iso := "mmn", value := .nounRelativeClauseDominant }
  , { walsCode := "mds", language := "Manadonese", iso := "xmm", value := .nounRelativeClauseDominant }
  , { walsCode := "mnm", language := "Manam", iso := "mva", value := .nounRelativeClauseDominant }
  , { walsCode := "mmb", language := "Mangap-Mbula", iso := "mna", value := .nounRelativeClauseDominant }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .nounRelativeClauseDominant }
  , { walsCode := "mng", language := "Manggarai", iso := "mqy", value := .nounRelativeClauseDominant }
  , { walsCode := "mgq", language := "Mango", iso := "mge", value := .nounRelativeClauseDominant }
  , { walsCode := "maw", language := "Maninka (Western)", iso := "mlq", value := .nounRelativeClauseDominant }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .nounRelativeClauseDominant }
  , { walsCode := "mrg", language := "Margi", iso := "mrt", value := .nounRelativeClauseDominant }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .nrelOrInternallyHeaded }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "mas", language := "Masa", iso := "mcn", value := .nounRelativeClauseDominant }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .nounRelativeClauseDominant }
  , { walsCode := "msl", language := "Masalit", iso := "mls", value := .nounRelativeClauseDominant }
  , { walsCode := "mau", language := "Maung", iso := "mph", value := .nounRelativeClauseDominant }
  , { walsCode := "may", language := "Maybrat", iso := "ayz", value := .nounRelativeClauseDominant }
  , { walsCode := "myg", language := "Mayogo", iso := "mdm", value := .nounRelativeClauseDominant }
  , { walsCode := "mbr", language := "Mbara", iso := "mpk", value := .nounRelativeClauseDominant }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .nounRelativeClauseDominant }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .nounRelativeClauseDominant }
  , { walsCode := "mbm", language := "Mbum", iso := "mdd", value := .nounRelativeClauseDominant }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .nounRelativeClauseDominant }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .nounRelativeClauseDominant }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .nounRelativeClauseDominant }
  , { walsCode := "mea", language := "Meyah", iso := "mej", value := .nounRelativeClauseDominant }
  , { walsCode := "hna", language := "Mina", iso := "hna", value := .nounRelativeClauseDominant }
  , { walsCode := "min", language := "Minangkabau", iso := "min", value := .nounRelativeClauseDominant }
  , { walsCode := "mco", language := "Mixe (Coatlán)", iso := "mco", value := .nounRelativeClauseDominant }
  , { walsCode := "mxc", language := "Mixtec (Chalcatongo)", iso := "mig", value := .nounRelativeClauseDominant }
  , { walsCode := "mxo", language := "Mixtec (Ocotepec)", iso := "mie", value := .nounRelativeClauseDominant }
  , { walsCode := "mxp", language := "Mixtec (Peñoles)", iso := "mil", value := .nounRelativeClauseDominant }
  , { walsCode := "mxy", language := "Mixtec (Yosondúa)", iso := "mpm", value := .nounRelativeClauseDominant }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .nounRelativeClauseDominant }
  , { walsCode := "mcv", language := "Mocoví", iso := "moc", value := .nounRelativeClauseDominant }
  , { walsCode := "mof", language := "Mofu-Gudur", iso := "mif", value := .nounRelativeClauseDominant }
  , { walsCode := "mok", language := "Mokilese", iso := "mkj", value := .nounRelativeClauseDominant }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .nounRelativeClauseDominant }
  , { walsCode := "mgo", language := "Mongo", iso := "lol", value := .nounRelativeClauseDominant }
  , { walsCode := "mno", language := "Mono (in United States)", iso := "mnr", value := .nounRelativeClauseDominant }
  , { walsCode := "moa", language := "Mono-Alu", iso := "mte", value := .nounRelativeClauseDominant }
  , { walsCode := "mro", language := "Moro", iso := "mor", value := .nounRelativeClauseDominant }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .nounRelativeClauseDominant }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .nounRelativeClauseDominant }
  , { walsCode := "mot", language := "Motuna", iso := "siw", value := .nounRelativeClauseDominant }
  , { walsCode := "mpu", language := "Mpur", iso := "akc", value := .nounRelativeClauseDominant }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .nounRelativeClauseDominant }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .nounRelativeClauseDominant }
  , { walsCode := "mna", language := "Muna", iso := "mnb", value := .nounRelativeClauseDominant }
  , { walsCode := "mdg", language := "Mundang", iso := "mua", value := .nounRelativeClauseDominant }
  , { walsCode := "mud", language := "Mundani", iso := "mnf", value := .nounRelativeClauseDominant }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .nounRelativeClauseDominant }
  , { walsCode := "mrl", language := "Murle", iso := "mur", value := .nounRelativeClauseDominant }
  , { walsCode := "mpa", language := "Murrinh-Patha", iso := "mwf", value := .nrelOrInternallyHeaded }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .nounRelativeClauseDominant }
  , { walsCode := "mgu", language := "Musgu", iso := "mug", value := .nounRelativeClauseDominant }
  , { walsCode := "msm", language := "Musom", iso := "msu", value := .nounRelativeClauseDominant }
  , { walsCode := "mus", language := "Mussau", iso := "emi", value := .nounRelativeClauseDominant }
  , { walsCode := "mut", language := "Mutsun", iso := "css", value := .nounRelativeClauseDominant }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .nounRelativeClauseDominant }
  , { walsCode := "ndr", language := "Nadroga", iso := "wyy", value := .nounRelativeClauseDominant }
  , { walsCode := "nhh", language := "Nahuatl (Huasteca)", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "nhm", language := "Nahuatl (Michoacán)", iso := "ncl", value := .nounRelativeClauseDominant }
  , { walsCode := "nhn", language := "Nahuatl (North Puebla)", iso := "ncj", value := .nrelOrReln }
  , { walsCode := "nht", language := "Nahuatl (Tetelcingo)", iso := "nhg", value := .nounRelativeClauseDominant }
  , { walsCode := "bio", language := "Nai", iso := "bio", value := .nounRelativeClauseDominant }
  , { walsCode := "nal", language := "Nalik", iso := "nal", value := .nounRelativeClauseDominant }
  , { walsCode := "nam", language := "Namia", iso := "nnm", value := .nrelOrReln }
  , { walsCode := "nan", language := "Nandi", iso := "niq", value := .nounRelativeClauseDominant }
  , { walsCode := "nrg", language := "Nanerge", iso := "sen", value := .nounRelativeClauseDominant }
  , { walsCode := "nar", language := "Nara (in Ethiopia)", iso := "nrb", value := .nounRelativeClauseDominant }
  , { walsCode := "nat", language := "Natchez", iso := "ncz", value := .nounRelativeClauseDominant }
  , { walsCode := "ncm", language := "Ncàm", iso := "bud", value := .nounRelativeClauseDominant }
  , { walsCode := "ndo", language := "Ndonga", iso := "ndo", value := .nounRelativeClauseDominant }
  , { walsCode := "ndt", language := "Ndut", iso := "ndv", value := .nounRelativeClauseDominant }
  , { walsCode := "ndy", language := "Ndyuka", iso := "djk", value := .nounRelativeClauseDominant }
  , { walsCode := "neh", language := "Nehan", iso := "nsn", value := .nounRelativeClauseDominant }
  , { walsCode := "naj", language := "Neo-Aramaic (Arbel Jewish)", iso := "aij", value := .nounRelativeClauseDominant }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .nounRelativeClauseDominant }
  , { walsCode := "nez", language := "Nez Perce", iso := "nez", value := .nounRelativeClauseDominant }
  , { walsCode := "ngl", language := "Ngalakan", iso := "nig", value := .nounRelativeClauseDominant }
  , { walsCode := "ngm", language := "Ngambay", iso := "sba", value := .nounRelativeClauseDominant }
  , { walsCode := "ngz", language := "Ngizim", iso := "ngi", value := .nounRelativeClauseDominant }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .nounRelativeClauseDominant }
  , { walsCode := "nia", language := "Nias", iso := "nia", value := .nounRelativeClauseDominant }
  , { walsCode := "nif", language := "Niuafo'ou", iso := "num", value := .nounRelativeClauseDominant }
  , { walsCode := "niu", language := "Niuean", iso := "niu", value := .nounRelativeClauseDominant }
  , { walsCode := "nkn", language := "Nkonya", iso := "nko", value := .nounRelativeClauseDominant }
  , { walsCode := "nko", language := "Nkore-Kiga", iso := "cgg", value := .nounRelativeClauseDominant }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .nounRelativeClauseDominant }
  , { walsCode := "noo", language := "Noon", iso := "snf", value := .nounRelativeClauseDominant }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .nounRelativeClauseDominant }
  , { walsCode := "nua", language := "Nuaulu", iso := "nxl", value := .nounRelativeClauseDominant }
  , { walsCode := "nbd", language := "Nubian (Dongolese)", iso := "dgl", value := .nounRelativeClauseDominant }
  , { walsCode := "nku", language := "Nubian (Kunuz)", iso := "xnz", value := .nounRelativeClauseDominant }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .nounRelativeClauseDominant }
  , { walsCode := "nun", language := "Nung (in Vietnam)", iso := "nut", value := .nounRelativeClauseDominant }
  , { walsCode := "nug", language := "Nunggubuyu", iso := "nuy", value := .nounRelativeClauseDominant }
  , { walsCode := "nup", language := "Nupe", iso := "nup", value := .nounRelativeClauseDominant }
  , { walsCode := "nza", language := "Nzakara", iso := "nzk", value := .nounRelativeClauseDominant }
  , { walsCode := "ood", language := "O'odham", iso := "ood", value := .nounRelativeClauseDominant }
  , { walsCode := "obo", language := "Obolo", iso := "ann", value := .nounRelativeClauseDominant }
  , { walsCode := "obg", language := "Ogbronuagum", iso := "ogu", value := .nounRelativeClauseDominant }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "olo", language := "Olo", iso := "ong", value := .nounRelativeClauseDominant }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .nounRelativeClauseDominant }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .nounRelativeClauseDominant }
  , { walsCode := "otm", language := "Otomí (Mezquital)", iso := "ote", value := .nounRelativeClauseDominant }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .nounRelativeClauseDominant }
  , { walsCode := "pms", language := "Paamese", iso := "pma", value := .nounRelativeClauseDominant }
  , { walsCode := "pno", language := "Paiute (Northern)", iso := "pao", value := .nounRelativeClauseDominant }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .nounRelativeClauseDominant }
  , { walsCode := "pal", language := "Palauan", iso := "pau", value := .nounRelativeClauseDominant }
  , { walsCode := "plg", language := "Palaung", iso := "pll", value := .nounRelativeClauseDominant }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .nounRelativeClauseDominant }
  , { walsCode := "pre", language := "Pare", iso := "asa", value := .nounRelativeClauseDominant }
  , { walsCode := "psh", language := "Pashto", iso := "pst", value := .nounRelativeClauseDominant }
  , { walsCode := "pat", language := "Patep", iso := "ptp", value := .nounRelativeClauseDominant }
  , { walsCode := "ptt", language := "Pattani", iso := "lae", value := .nounRelativeClauseDominant }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .nounRelativeClauseDominant }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .nounRelativeClauseDominant }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .nounRelativeClauseDominant }
  , { walsCode := "prs", language := "Persian", iso := "pes", value := .nounRelativeClauseDominant }
  , { walsCode := "pga", language := "Pilagá", iso := "plg", value := .nounRelativeClauseDominant }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .nounRelativeClauseDominant }
  , { walsCode := "pip", language := "Pipil", iso := "ppl", value := .nounRelativeClauseDominant }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .nrelOrInternallyHeaded }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .nounRelativeClauseDominant }
  , { walsCode := "poh", language := "Pohnpeian", iso := "pon", value := .nounRelativeClauseDominant }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .nounRelativeClauseDominant }
  , { walsCode := "pol", language := "Polish", iso := "pol", value := .nounRelativeClauseDominant }
  , { walsCode := "psw", language := "Port Sandwich", iso := "psw", value := .nounRelativeClauseDominant }
  , { walsCode := "por", language := "Portuguese", iso := "por", value := .nounRelativeClauseDominant }
  , { walsCode := "pul", language := "Puluwat", iso := "puw", value := .nounRelativeClauseDominant }
  , { walsCode := "pur", language := "Purépecha", iso := "tsz", value := .nounRelativeClauseDominant }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .nounRelativeClauseDominant }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .nounRelativeClauseDominant }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .nounRelativeClauseDominant }
  , { walsCode := "res", language := "Resígaro", iso := "rgr", value := .nrelOrInternallyHeaded }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .nounRelativeClauseDominant }
  , { walsCode := "rom", language := "Romanian", iso := "ron", value := .nounRelativeClauseDominant }
  , { walsCode := "rsu", language := "Romansch (Sursilvan)", iso := "roh", value := .nounRelativeClauseDominant }
  , { walsCode := "ron", language := "Ron", iso := "cla", value := .nounRelativeClauseDominant }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .nounRelativeClauseDominant }
  , { walsCode := "rov", language := "Roviana", iso := "rug", value := .nounRelativeClauseDominant }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .nrelOrReln }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .nounRelativeClauseDominant }
  , { walsCode := "rny", language := "Runyankore", iso := "nyn", value := .nounRelativeClauseDominant }
  , { walsCode := "rus", language := "Russian", iso := "rus", value := .nounRelativeClauseDominant }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .nounRelativeClauseDominant }
  , { walsCode := "sak", language := "Sakao", iso := "sku", value := .nounRelativeClauseDominant }
  , { walsCode := "slb", language := "Saliba (in Papua New Guinea)", iso := "sbe", value := .nounRelativeClauseDominant }
  , { walsCode := "sle", language := "Samba Leko", iso := "ndi", value := .nounRelativeClauseDominant }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .nounRelativeClauseDominant }
  , { walsCode := "sdw", language := "Sandawe", iso := "sad", value := .nounRelativeClauseDominant }
  , { walsCode := "san", language := "Sango", iso := "sag", value := .nounRelativeClauseDominant }
  , { walsCode := "sgu", language := "Sangu", iso := "snq", value := .nounRelativeClauseDominant }
  , { walsCode := "src", language := "Sarcee", iso := "srs", value := .nounRelativeClauseDominant }
  , { walsCode := "srd", language := "Sardinian", iso := "sro", value := .nounRelativeClauseDominant }
  , { walsCode := "sed", language := "Sedang", iso := "sed", value := .nounRelativeClauseDominant }
  , { walsCode := "see", language := "Seediq", iso := "trv", value := .nounRelativeClauseDominant }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .nounRelativeClauseDominant }
  , { walsCode := "ses", language := "Sesotho", iso := "sot", value := .nounRelativeClauseDominant }
  , { walsCode := "shb", language := "Shabo", iso := "sbf", value := .nounRelativeClauseDominant }
  , { walsCode := "sht", language := "Shatt", iso := "shj", value := .nounRelativeClauseDominant }
  ]

private def allData_1 : List Datapoint :=
  [ { walsCode := "shn", language := "Shona", iso := "sna", value := .nounRelativeClauseDominant }
  , { walsCode := "sir", language := "Siar", iso := "sjr", value := .nounRelativeClauseDominant }
  , { walsCode := "skr", language := "Sikaritai", iso := "tty", value := .nounRelativeClauseDominant }
  , { walsCode := "snh", language := "Sinhala", iso := "sin", value := .nounRelativeClauseDominant }
  , { walsCode := "sio", language := "Sio", iso := "xsi", value := .nounRelativeClauseDominant }
  , { walsCode := "qum", language := "Sipakapense", iso := "qum", value := .nounRelativeClauseDominant }
  , { walsCode := "sro", language := "Siroi", iso := "ssd", value := .nounRelativeClauseDominant }
  , { walsCode := "sis", language := "Sisiqa", iso := "baa", value := .nounRelativeClauseDominant }
  , { walsCode := "sla", language := "Slave", iso := "den", value := .nrelOrInternallyHeaded }
  , { walsCode := "so", language := "So", iso := "teu", value := .nounRelativeClauseDominant }
  , { walsCode := "sob", language := "Sobei", iso := "sob", value := .nounRelativeClauseDominant }
  , { walsCode := "som", language := "Somali", iso := "som", value := .nounRelativeClauseDominant }
  , { walsCode := "sgb", language := "Sougb", iso := "mnx", value := .nounRelativeClauseDominant }
  , { walsCode := "sea", language := "Southeast Ambrym", iso := "tvk", value := .nounRelativeClauseDominant }
  , { walsCode := "spa", language := "Spanish", iso := "spa", value := .nounRelativeClauseDominant }
  , { walsCode := "squ", language := "Squamish", iso := "squ", value := .nrelOrReln }
  , { walsCode := "sre", language := "Sre", iso := "kpm", value := .nounRelativeClauseDominant }
  , { walsCode := "sud", language := "Sudest", iso := "tgo", value := .nounRelativeClauseDominant }
  , { walsCode := "sul", language := "Sulka", iso := "sua", value := .nounRelativeClauseDominant }
  , { walsCode := "sun", language := "Sundanese", iso := "sun", value := .nounRelativeClauseDominant }
  , { walsCode := "swa", language := "Swahili", iso := "swh", value := .nounRelativeClauseDominant }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .nounRelativeClauseDominant }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .nounRelativeClauseDominant }
  , { walsCode := "tab", language := "Taba", iso := "mky", value := .nounRelativeClauseDominant }
  , { walsCode := "tag", language := "Tagalog", iso := "tgl", value := .nounRelativeClauseDominant }
  , { walsCode := "tah", language := "Tahitian", iso := "tah", value := .nounRelativeClauseDominant }
  , { walsCode := "taf", language := "Taiof", iso := "sps", value := .nounRelativeClauseDominant }
  , { walsCode := "taj", language := "Tajik", iso := "tgk", value := .nounRelativeClauseDominant }
  , { walsCode := "tak", language := "Takia", iso := "tbc", value := .nounRelativeClauseDominant }
  , { walsCode := "tls", language := "Talysh (Southern)", iso := "shm", value := .nounRelativeClauseDominant }
  , { walsCode := "tmm", language := "Tamabo", iso := "mla", value := .nounRelativeClauseDominant }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .nounRelativeClauseDominant }
  , { walsCode := "tpt", language := "Tapieté", iso := "tpj", value := .nounRelativeClauseDominant }
  , { walsCode := "tce", language := "Tarahumara (Central)", iso := "tar", value := .nounRelativeClauseDominant }
  , { walsCode := "twe", language := "Tarahumara (Western)", iso := "tac", value := .nrelOrReln }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .nounRelativeClauseDominant }
  , { walsCode := "tat", language := "Tatana'", iso := "txx", value := .nounRelativeClauseDominant }
  , { walsCode := "tau", language := "Tauya", iso := "tya", value := .nrelOrReln }
  , { walsCode := "taw", language := "Tawala", iso := "tbo", value := .nounRelativeClauseDominant }
  , { walsCode := "tbo", language := "Tboli", iso := "tbl", value := .nounRelativeClauseDominant }
  , { walsCode := "tmr", language := "Temiar", iso := "tea", value := .nounRelativeClauseDominant }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .nounRelativeClauseDominant }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .nounRelativeClauseDominant }
  , { walsCode := "tny", language := "Tenyer", iso := "kza", value := .nounRelativeClauseDominant }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .nounRelativeClauseDominant }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .nounRelativeClauseDominant }
  , { walsCode := "tep", language := "Tepehua (Tlachichilco)", iso := "tpt", value := .nounRelativeClauseDominant }
  , { walsCode := "tpn", language := "Tepehuan (Northern)", iso := "ntp", value := .nounRelativeClauseDominant }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .nounRelativeClauseDominant }
  , { walsCode := "trb", language := "Teribe", iso := "tfr", value := .nounRelativeClauseDominant }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .nounRelativeClauseDominant }
  , { walsCode := "ttn", language := "Tetun", iso := "tet", value := .nounRelativeClauseDominant }
  , { walsCode := "ttd", language := "Tetun Dili", iso := "tet", value := .nounRelativeClauseDominant }
  , { walsCode := "tha", language := "Thai", iso := "tha", value := .nounRelativeClauseDominant }
  , { walsCode := "tdr", language := "Tibetan (Drokpa)", iso := "bod", value := .nrelOrReln }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .nounRelativeClauseDominant }
  , { walsCode := "tgk", language := "Tigak", iso := "tgc", value := .nounRelativeClauseDominant }
  , { walsCode := "tim", language := "Timugon", iso := "tih", value := .nounRelativeClauseDominant }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .nounRelativeClauseDominant }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .nounRelativeClauseDominant }
  , { walsCode := "tiw", language := "Tiwi", iso := "tiw", value := .nounRelativeClauseDominant }
  , { walsCode := "tlp", language := "Tlapanec", iso := "tcf", value := .nounRelativeClauseDominant }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .nounRelativeClauseDominant }
  , { walsCode := "tke", language := "Tokelauan", iso := "tkl", value := .nounRelativeClauseDominant }
  , { walsCode := "tla", language := "Tolai", iso := "ksd", value := .nounRelativeClauseDominant }
  , { walsCode := "tno", language := "Tondano", iso := "tdn", value := .nounRelativeClauseDominant }
  , { walsCode := "toz", language := "Tonga (in Zambia)", iso := "toi", value := .nounRelativeClauseDominant }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .nounRelativeClauseDominant }
  , { walsCode := "txj", language := "Totonac (Xicotepec de Juárez)", iso := "too", value := .nounRelativeClauseDominant }
  , { walsCode := "tri", language := "Trique (Copala)", iso := "trc", value := .nounRelativeClauseDominant }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .nounRelativeClauseDominant }
  , { walsCode := "tai", language := "Tuareg (Air)", iso := "thz", value := .nounRelativeClauseDominant }
  , { walsCode := "tbu", language := "Tubu", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "tgn", language := "Tugun", iso := "tzn", value := .nounRelativeClauseDominant }
  , { walsCode := "tuk", language := "Tukang Besi", iso := "", value := .nrelOrInternallyHeaded }
  , { walsCode := "tnn", language := "Tunen", iso := "tvu", value := .nounRelativeClauseDominant }
  , { walsCode := "tnk", language := "Tungak", iso := "lcm", value := .nounRelativeClauseDominant }
  , { walsCode := "tun", language := "Tunica", iso := "tun", value := .nounRelativeClauseDominant }
  , { walsCode := "tna", language := "Turkana", iso := "tuv", value := .nounRelativeClauseDominant }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .nounRelativeClauseDominant }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .nounRelativeClauseDominant }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .nrelOrReln }
  , { walsCode := "ukr", language := "Ukrainian", iso := "ukr", value := .nounRelativeClauseDominant }
  , { walsCode := "uld", language := "Uldeme", iso := "udl", value := .nounRelativeClauseDominant }
  , { walsCode := "uli", language := "Ulithian", iso := "uli", value := .nounRelativeClauseDominant }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .nounRelativeClauseDominant }
  , { walsCode := "url", language := "Urak Lawoi'", iso := "urk", value := .nounRelativeClauseDominant }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .nounRelativeClauseDominant }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .nounRelativeClauseDominant }
  , { walsCode := "vaf", language := "Vafsi", iso := "vaf", value := .nounRelativeClauseDominant }
  , { walsCode := "vie", language := "Vietnamese", iso := "vie", value := .nounRelativeClauseDominant }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .nounRelativeClauseDominant }
  , { walsCode := "wah", language := "Wahgi", iso := "", value := .nounRelativeClauseDominant }
  , { walsCode := "wak", language := "Wakhi", iso := "wbl", value := .nounRelativeClauseDominant }
  , { walsCode := "wal", language := "Walman", iso := "van", value := .nounRelativeClauseDominant }
  , { walsCode := "wao", language := "Waorani", iso := "auc", value := .nrelOrReln }
  , { walsCode := "war", language := "Wari'", iso := "pav", value := .nounRelativeClauseDominant }
  , { walsCode := "wrg", language := "Warrgamay", iso := "wgy", value := .nrelOrReln }
  , { walsCode := "wel", language := "Welsh", iso := "cym", value := .nounRelativeClauseDominant }
  , { walsCode := "wma", language := "West Makian", iso := "mqs", value := .nounRelativeClauseDominant }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .nounRelativeClauseDominant }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .nounRelativeClauseDominant }
  , { walsCode := "wol", language := "Woleaian", iso := "woe", value := .nounRelativeClauseDominant }
  , { walsCode := "wlo", language := "Wolio", iso := "wlo", value := .nounRelativeClauseDominant }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .nounRelativeClauseDominant }
  , { walsCode := "xho", language := "Xhosa", iso := "xho", value := .nounRelativeClauseDominant }
  , { walsCode := "yag", language := "Yagua", iso := "yad", value := .nounRelativeClauseDominant }
  , { walsCode := "yap", language := "Yapese", iso := "yap", value := .nounRelativeClauseDominant }
  , { walsCode := "yaq", language := "Yaqui", iso := "yaq", value := .nounRelativeClauseDominant }
  , { walsCode := "yor", language := "Yoruba", iso := "yor", value := .nounRelativeClauseDominant }
  , { walsCode := "yuc", language := "Yuchi", iso := "yuc", value := .nounRelativeClauseDominant }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .nounRelativeClauseDominant }
  , { walsCode := "yul", language := "Yulu", iso := "yul", value := .nounRelativeClauseDominant }
  , { walsCode := "yur", language := "Yurok", iso := "yur", value := .nrelOrReln }
  , { walsCode := "zai", language := "Zapotec (Isthmus)", iso := "zai", value := .nounRelativeClauseDominant }
  , { walsCode := "zzo", language := "Zapotec (Zoogocho)", iso := "zpq", value := .nounRelativeClauseDominant }
  , { walsCode := "zhn", language := "Zhuang (Northern)", iso := "zgb", value := .nounRelativeClauseDominant }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .nounRelativeClauseDominant }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .nounRelativeClauseDominant }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .nounRelativeClauseDominant }
  ]

/-- Complete WALS 90C dataset (620 languages). -/
def allData : List Datapoint := allData_0 ++ allData_1

-- Count verification
theorem total_count : allData.length = 620 := by native_decide

theorem count_nounRelativeClauseDominant :
    (allData.filter (·.value == .nounRelativeClauseDominant)).length = 579 := by native_decide
theorem count_nrelOrReln :
    (allData.filter (·.value == .nrelOrReln)).length = 31 := by native_decide
theorem count_nrelOrInternallyHeaded :
    (allData.filter (·.value == .nrelOrInternallyHeaded)).length = 8 := by native_decide
theorem count_nrelOrCorrelative :
    (allData.filter (·.value == .nrelOrCorrelative)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F90C
