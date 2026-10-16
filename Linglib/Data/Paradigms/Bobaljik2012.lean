module

public import Linglib.Data.Paradigms.Schema

/-!
# `Bobaljik2012`: paradigm data

Auto-generated from `Linglib/Data/Paradigms/Bobaljik2012.json` by `scripts/gen_paradigms.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in
`namespace Bobaljik2012.Paradigms`.
-/

@[expose] public section

namespace Bobaljik2012.Paradigms

open Data.Paradigms

/-- The positive cell, `Degree=Pos`. -/
def positive : UD.MorphFeatures := { degree := ↑UD.Degree.Pos }

/-- The comparative cell, `Degree=Cmp`. -/
def comparative : UD.MorphFeatures := { degree := ↑UD.Degree.Cmp }

/-- The superlative cell, `Degree=Sup`. -/
def superlative : UD.MorphFeatures := { degree := ↑UD.Degree.Sup }

def eng_good : Lexeme :=
  { id := "eng_good", languageId := "stan1293", label := "good", meaning := "good" }

def swe_good : Lexeme :=
  { id := "swe_good", languageId := "swed1254", label := "bra", meaning := "good" }

def got_good : Lexeme :=
  { id := "got_good", languageId := "goth1244", label := "gôd", meaning := "good" }

def cim_good : Lexeme :=
  { id := "cim_good", languageId := "tred1238", label := "guot", meaning := "good" }

def ces_good : Lexeme :=
  { id := "ces_good", languageId := "czec1258", label := "dobrý", meaning := "good" }

def hbs_good : Lexeme :=
  { id := "hbs_good", languageId := "sout1528", label := "dobar", meaning := "good" }

def sorb_good : Lexeme :=
  { id := "sorb_good", languageId := "sorb1249", label := "dobry", meaning := "good" }

def ukr_good_dobr : Lexeme :=
  { id := "ukr_good_dobr", languageId := "ukra1253", label := "dobryj", meaning := "good" }

def ukr_good_harn : Lexeme :=
  { id := "ukr_good_harn", languageId := "ukra1253", label := "harnyj", meaning := "good" }

def rus_good : Lexeme :=
  { id := "rus_good", languageId := "russ1263", label := "xorošij", meaning := "good" }

def lat_good : Lexeme :=
  { id := "lat_good", languageId := "lati1261", label := "bonus", meaning := "good" }

def cym_good : Lexeme :=
  { id := "cym_good", languageId := "wels1247", label := "da", meaning := "good" }

def sga_good : Lexeme :=
  { id := "sga_good", languageId := "oldi1246", label := "maith", meaning := "good" }

def bre_good : Lexeme :=
  { id := "bre_good", languageId := "bret1244", label := "mat", meaning := "good" }

def grc_good : Lexeme :=
  { id := "grc_good", languageId := "anci1242", label := "agathós", meaning := "good" }

def san_good : Lexeme :=
  { id := "san_good", languageId := "sans1269", label := "praśásyas", meaning := "good" }

def kho_good : Lexeme :=
  { id := "kho_good", languageId := "khot1251", label := "śśära", meaning := "good" }

def pal_good : Lexeme :=
  { id := "pal_good", languageId := "pahl1241", label := "xōb", meaning := "good" }

def fas_good : Lexeme :=
  { id := "fas_good", languageId := "west2369", label := "xub", meaning := "good" }

def eus_good : Lexeme :=
  { id := "eus_good", languageId := "basq1248", label := "on", meaning := "good" }

def fin_good : Lexeme :=
  { id := "fin_good", languageId := "finn1318", label := "hyvä", meaning := "good" }

def sjd_good : Lexeme :=
  { id := "sjd_good", languageId := "kild1236", label := "š’ig’", meaning := "good" }

def kat_good : Lexeme :=
  { id := "kat_good", languageId := "nucl1302", label := "k’argii", meaning := "good" }

def sva_good : Lexeme :=
  { id := "sva_good", languageId := "svan1243", label := "ezär", meaning := "good" }

def chr_good : Lexeme :=
  { id := "chr_good", languageId := "cher1273", label := "osda", meaning := "good" }

def eng_bad : Lexeme :=
  { id := "eng_bad", languageId := "stan1293", label := "bad", meaning := "bad" }

def goh_bad : Lexeme :=
  { id := "goh_bad", languageId := "oldh1241", label := "ubil", meaning := "bad" }

def non_bad_vandr : Lexeme :=
  { id := "non_bad_vandr", languageId := "oldn1244", label := "vándr", meaning := "bad" }

def non_bad_illr : Lexeme :=
  { id := "non_bad_illr", languageId := "oldn1244", label := "íllr", meaning := "bad" }

def dan_bad : Lexeme :=
  { id := "dan_bad", languageId := "dani1285", label := "slem", meaning := "bad" }

def fao_bad : Lexeme :=
  { id := "fao_bad", languageId := "faro1244", label := "ringur", meaning := "bad" }

def swe_bad : Lexeme :=
  { id := "swe_bad", languageId := "swed1254", label := "dålig", meaning := "bad" }

def yid_bad : Lexeme :=
  { id := "yid_bad", languageId := "east2295", label := "šlext", meaning := "bad" }

def pol_bad : Lexeme :=
  { id := "pol_bad", languageId := "poli1260", label := "zły", meaning := "bad" }

def ces_bad : Lexeme :=
  { id := "ces_bad", languageId := "czec1258", label := "špatný", meaning := "bad" }

def ukr_bad : Lexeme :=
  { id := "ukr_bad", languageId := "ukra1253", label := "pohanyj", meaning := "bad" }

def bel_bad_drenn : Lexeme :=
  { id := "bel_bad_drenn", languageId := "bela1254", label := "drènny", meaning := "bad" }

def bel_bad_blah : Lexeme :=
  { id := "bel_bad_blah", languageId := "bela1254", label := "blahi", meaning := "bad" }

def hbs_bad : Lexeme :=
  { id := "hbs_bad", languageId := "sout1528", label := "loš", meaning := "bad" }

def rus_bad : Lexeme :=
  { id := "rus_bad", languageId := "russ1263", label := "ploxoj", meaning := "bad" }

def lat_bad : Lexeme :=
  { id := "lat_bad", languageId := "lati1261", label := "malus", meaning := "bad" }

def sga_bad : Lexeme :=
  { id := "sga_bad", languageId := "oldi1246", label := "olc", meaning := "bad" }

def cym_bad : Lexeme :=
  { id := "cym_bad", languageId := "wels1247", label := "drwg", meaning := "bad" }

def bre_bad : Lexeme :=
  { id := "bre_bad", languageId := "bret1244", label := "fall", meaning := "bad" }

def grc_bad : Lexeme :=
  { id := "grc_bad", languageId := "anci1242", label := "kakós", meaning := "bad" }

def got_big : Lexeme :=
  { id := "got_big", languageId := "goth1244", label := "mikils", meaning := "big" }

def ces_big : Lexeme :=
  { id := "ces_big", languageId := "czec1258", label := "velký", meaning := "big" }

def ukr_big : Lexeme :=
  { id := "ukr_big", languageId := "ukra1253", label := "velykyj", meaning := "big" }

def pol_big : Lexeme :=
  { id := "pol_big", languageId := "poli1260", label := "duży", meaning := "big" }

def cym_big : Lexeme :=
  { id := "cym_big", languageId := "wels1247", label := "mawr", meaning := "big" }

def pal_big : Lexeme :=
  { id := "pal_big", languageId := "pahl1241", label := "wazurg", meaning := "big" }

def sva_big : Lexeme :=
  { id := "sva_big", languageId := "svan1243", label := "d͜zɣəd", meaning := "big" }

def got_small : Lexeme :=
  { id := "got_small", languageId := "goth1244", label := "leitils", meaning := "small" }

def ang_small : Lexeme :=
  { id := "ang_small", languageId := "olde1238", label := "lýtel", meaning := "small" }

def dan_small : Lexeme :=
  { id := "dan_small", languageId := "dani1285", label := "små", meaning := "small" }

def hbs_small : Lexeme :=
  { id := "hbs_small", languageId := "sout1528", label := "mali", meaning := "small" }

def lat_small : Lexeme :=
  { id := "lat_small", languageId := "lati1261", label := "parvus", meaning := "small" }

def cym_small : Lexeme :=
  { id := "cym_small", languageId := "wels1247", label := "bach", meaning := "small" }

def grc_small : Lexeme :=
  { id := "grc_small", languageId := "anci1242", label := "mikrós", meaning := "small" }

def pal_small : Lexeme :=
  { id := "pal_small", languageId := "pahl1241", label := "kōdag", meaning := "small" }

def non_old : Lexeme :=
  { id := "non_old", languageId := "oldn1244", label := "gamall", meaning := "old" }

def cym_near : Lexeme :=
  { id := "cym_near", languageId := "wels1247", label := "agos", meaning := "near" }

def cym_strong : Lexeme :=
  { id := "cym_strong", languageId := "wels1247", label := "cryf", meaning := "strong" }

def eng_good_positive : Form :=
  { id := "eng_good_positive", lexeme := eng_good, cell := positive, form := "good",
    analysed := "good", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_good_comparative : Form :=
  { id := "eng_good_comparative", lexeme := eng_good, cell := comparative, form := "better",
    analysed := "bett-er", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_good_superlative : Form :=
  { id := "eng_good_superlative", lexeme := eng_good, cell := superlative, form := "best",
    analysed := "be-st", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_good_positive : Form :=
  { id := "swe_good_positive", lexeme := swe_good, cell := positive, form := "bra",
    analysed := "bra", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_good_comparative : Form :=
  { id := "swe_good_comparative", lexeme := swe_good, cell := comparative, form := "bättre",
    analysed := "bätt-re", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_good_superlative : Form :=
  { id := "swe_good_superlative", lexeme := swe_good, cell := superlative, form := "bäst",
    analysed := "bä-st", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_good_positive : Form :=
  { id := "got_good_positive", lexeme := got_good, cell := positive, form := "gôd",
    analysed := "gôd", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_good_comparative : Form :=
  { id := "got_good_comparative", lexeme := got_good, cell := comparative, form := "sêlra",
    analysed := "sêl-ra", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_good_superlative : Form :=
  { id := "got_good_superlative", lexeme := got_good, cell := superlative, form := "sêlost",
    analysed := "sêl-ost", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cim_good_positive : Form :=
  { id := "cim_good_positive", lexeme := cim_good, cell := positive, form := "guot",
    analysed := "guot", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cim_good_comparative : Form :=
  { id := "cim_good_comparative", lexeme := cim_good, cell := comparative, form := "ƀegur",
    analysed := "ƀeg-ur", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cim_good_superlative : Form :=
  { id := "cim_good_superlative", lexeme := cim_good, cell := superlative, form := "ƀegurste",
    analysed := "ƀeg-ur-ste", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_good_positive : Form :=
  { id := "ces_good_positive", lexeme := ces_good, cell := positive, form := "dobrý",
    analysed := "dobr-ý", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_good_comparative : Form :=
  { id := "ces_good_comparative", lexeme := ces_good, cell := comparative, form := "lepší",
    analysed := "lep-ší", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_good_superlative : Form :=
  { id := "ces_good_superlative", lexeme := ces_good, cell := superlative, form := "nejlepší",
    analysed := "nej-lep-ší", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_good_positive : Form :=
  { id := "hbs_good_positive", lexeme := hbs_good, cell := positive, form := "dobar",
    analysed := "dobar", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_good_comparative : Form :=
  { id := "hbs_good_comparative", lexeme := hbs_good, cell := comparative, form := "bolji",
    analysed := "bol-ji", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_good_superlative : Form :=
  { id := "hbs_good_superlative", lexeme := hbs_good, cell := superlative, form := "najbolji",
    analysed := "naj-bol-ji", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sorb_good_positive : Form :=
  { id := "sorb_good_positive", lexeme := sorb_good, cell := positive, form := "dobry",
    analysed := "dobr-y", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sorb_good_comparative : Form :=
  { id := "sorb_good_comparative", lexeme := sorb_good, cell := comparative, form := "redliši",
    analysed := "redl-iši", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_dobr_positive : Form :=
  { id := "ukr_good_dobr_positive", lexeme := ukr_good_dobr, cell := positive, form := "dobryj",
    analysed := "dobr-yj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_dobr_comparative : Form :=
  { id := "ukr_good_dobr_comparative", lexeme := ukr_good_dobr, cell := comparative, form := "kraščyj",
    analysed := "krašč-yj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_dobr_superlative : Form :=
  { id := "ukr_good_dobr_superlative", lexeme := ukr_good_dobr, cell := superlative, form := "najkraščyj",
    analysed := "naj-krašč-yj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_harn_positive : Form :=
  { id := "ukr_good_harn_positive", lexeme := ukr_good_harn, cell := positive, form := "harnyj",
    analysed := "harn-yj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_harn_comparative : Form :=
  { id := "ukr_good_harn_comparative", lexeme := ukr_good_harn, cell := comparative, form := "kraščyj",
    analysed := "krašč-yj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_harn_superlative : Form :=
  { id := "ukr_good_harn_superlative", lexeme := ukr_good_harn, cell := superlative, form := "najkraščyj",
    analysed := "naj-krašč-yj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_good_positive : Form :=
  { id := "rus_good_positive", lexeme := rus_good, cell := positive, form := "xorošij",
    analysed := "xoroš-ij", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_good_comparative : Form :=
  { id := "rus_good_comparative", lexeme := rus_good, cell := comparative, form := "lučše",
    analysed := "luč-še", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_good_superlative : Form :=
  { id := "rus_good_superlative", lexeme := rus_good, cell := superlative, form := "nailučšij",
    analysed := "nai-luč-š-ij", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_good_positive : Form :=
  { id := "lat_good_positive", lexeme := lat_good, cell := positive, form := "bonus",
    analysed := "bon-us", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_good_comparative : Form :=
  { id := "lat_good_comparative", lexeme := lat_good, cell := comparative, form := "melior",
    analysed := "mel-ior", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_good_superlative : Form :=
  { id := "lat_good_superlative", lexeme := lat_good, cell := superlative, form := "optimus",
    analysed := "opt-imus", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_good_positive : Form :=
  { id := "cym_good_positive", lexeme := cym_good, cell := positive, form := "da",
    analysed := "da", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_good_comparative : Form :=
  { id := "cym_good_comparative", lexeme := cym_good, cell := comparative, form := "gwell",
    analysed := "gwell", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_good_superlative : Form :=
  { id := "cym_good_superlative", lexeme := cym_good, cell := superlative, form := "gorau",
    analysed := "gor-au", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_good_positive : Form :=
  { id := "sga_good_positive", lexeme := sga_good, cell := positive, form := "maith",
    analysed := "maith", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_good_comparative : Form :=
  { id := "sga_good_comparative", lexeme := sga_good, cell := comparative, form := "ferr",
    analysed := "ferr", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_good_superlative : Form :=
  { id := "sga_good_superlative", lexeme := sga_good, cell := superlative, form := "dech",
    analysed := "dech", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_good_positive : Form :=
  { id := "bre_good_positive", lexeme := bre_good, cell := positive, form := "mat",
    analysed := "mat", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_good_comparative : Form :=
  { id := "bre_good_comparative", lexeme := bre_good, cell := comparative, form := "gwell(oc’h)",
    analysed := "gwell-(oc’h)", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_good_superlative : Form :=
  { id := "bre_good_superlative", lexeme := bre_good, cell := superlative, form := "gwellañ",
    analysed := "gwell-añ", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_positive : Form :=
  { id := "grc_good_positive", lexeme := grc_good, cell := positive, form := "agathós",
    analysed := "agath-ós", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative : Form :=
  { id := "grc_good_comparative", lexeme := grc_good, cell := comparative, form := "ameínōn",
    analysed := "ameín-ōn", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative : Form :=
  { id := "grc_good_superlative", lexeme := grc_good, cell := superlative, form := "(phéristos)",
    analysed := "(phér-ist-os)", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative_2 : Form :=
  { id := "grc_good_comparative_2", lexeme := grc_good, cell := comparative, form := "areíōn",
    analysed := "areí-ōn", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative_2 : Form :=
  { id := "grc_good_superlative_2", lexeme := grc_good, cell := superlative, form := "áristos",
    analysed := "ár-ist-os", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative_3 : Form :=
  { id := "grc_good_comparative_3", lexeme := grc_good, cell := comparative, form := "beltíōn",
    analysed := "belt-íōn", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative_3 : Form :=
  { id := "grc_good_superlative_3", lexeme := grc_good, cell := superlative, form := "béltistos",
    analysed := "bélt-ist-os", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative_4 : Form :=
  { id := "grc_good_comparative_4", lexeme := grc_good, cell := comparative, form := "kreíssōn",
    analysed := "kreíss-ōn", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative_4 : Form :=
  { id := "grc_good_superlative_4", lexeme := grc_good, cell := superlative, form := "krátistos",
    analysed := "krát-ist-os", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative_5 : Form :=
  { id := "grc_good_comparative_5", lexeme := grc_good, cell := comparative, form := "lóïon",
    analysed := "ló-ïon", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative_5 : Form :=
  { id := "grc_good_superlative_5", lexeme := grc_good, cell := superlative, form := "lõistos",
    analysed := "lõ-ist-os", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_positive : Form :=
  { id := "san_good_positive", lexeme := san_good, cell := positive, form := "praśásyas",
    analysed := "pra-śásya-s", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_comparative : Form :=
  { id := "san_good_comparative", lexeme := san_good, cell := comparative, form := "śréyān",
    analysed := "śré-yān", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_superlative : Form :=
  { id := "san_good_superlative", lexeme := san_good, cell := superlative, form := "śréṣṭhas",
    analysed := "śré-ṣṭhas", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_comparative_2 : Form :=
  { id := "san_good_comparative_2", lexeme := san_good, cell := comparative, form := "jyāyān",
    analysed := "jyā-yān", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_superlative_2 : Form :=
  { id := "san_good_superlative_2", lexeme := san_good, cell := superlative, form := "jyēṣṭhas",
    analysed := "jyē-ṣṭhas", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kho_good_positive : Form :=
  { id := "kho_good_positive", lexeme := kho_good, cell := positive, form := "śśära",
    analysed := "śśära-", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kho_good_comparative : Form :=
  { id := "kho_good_comparative", lexeme := kho_good, cell := comparative, form := "hastara",
    analysed := "has-tara", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kho_good_superlative : Form :=
  { id := "kho_good_superlative", lexeme := kho_good, cell := superlative, form := "hastama",
    analysed := "has-tama", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_good_positive : Form :=
  { id := "pal_good_positive", lexeme := pal_good, cell := positive, form := "xōb",
    analysed := "xōb", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_good_comparative : Form :=
  { id := "pal_good_comparative", lexeme := pal_good, cell := comparative, form := "weh/wahīy",
    analysed := "weh/wah-īy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_good_superlative : Form :=
  { id := "pal_good_superlative", lexeme := pal_good, cell := superlative, form := "pahlom",
    analysed := "pahl-om", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_good_superlative_2 : Form :=
  { id := "pal_good_superlative_2", lexeme := pal_good, cell := superlative, form := "pāšom",
    analysed := "pāš-om", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fas_good_positive : Form :=
  { id := "fas_good_positive", lexeme := fas_good, cell := positive, form := "xub",
    analysed := "xub", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fas_good_comparative : Form :=
  { id := "fas_good_comparative", lexeme := fas_good, cell := comparative, form := "behtær",
    analysed := "beh-tær", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fas_good_superlative : Form :=
  { id := "fas_good_superlative", lexeme := fas_good, cell := superlative, form := "behtærin",
    analysed := "beh-tær-in", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eus_good_positive : Form :=
  { id := "eus_good_positive", lexeme := eus_good, cell := positive, form := "on",
    analysed := "on", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eus_good_comparative : Form :=
  { id := "eus_good_comparative", lexeme := eus_good, cell := comparative, form := "hobe",
    analysed := "hobe", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eus_good_superlative : Form :=
  { id := "eus_good_superlative", lexeme := eus_good, cell := superlative, form := "hoberen",
    analysed := "hobe-ren", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eus_good_superlative_2 : Form :=
  { id := "eus_good_superlative_2", lexeme := eus_good, cell := superlative, form := "onen",
    analysed := "on-en", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fin_good_positive : Form :=
  { id := "fin_good_positive", lexeme := fin_good, cell := positive, form := "hyvä",
    analysed := "hyvä", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fin_good_comparative : Form :=
  { id := "fin_good_comparative", lexeme := fin_good, cell := comparative, form := "parempi",
    analysed := "pare-mpi", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fin_good_superlative : Form :=
  { id := "fin_good_superlative", lexeme := fin_good, cell := superlative, form := "parhain",
    analysed := "parha-i-n", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sjd_good_positive : Form :=
  { id := "sjd_good_positive", lexeme := sjd_good, cell := positive, form := "š’ig’",
    analysed := "š’ig’", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sjd_good_comparative : Form :=
  { id := "sjd_good_comparative", lexeme := sjd_good, cell := comparative, form := "pɛr’amp",
    analysed := "pɛr’a-mp", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sjd_good_superlative : Form :=
  { id := "sjd_good_superlative", lexeme := sjd_good, cell := superlative, form := "pɛr’mus",
    analysed := "pɛr’-mus", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_positive : Form :=
  { id := "kat_good_positive", lexeme := kat_good, cell := positive, form := "k’argii",
    analysed := "k’argi-i", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_comparative : Form :=
  { id := "kat_good_comparative", lexeme := kat_good, cell := comparative, form := "umǰobesi",
    analysed := "u-mǰob-es-i", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_superlative : Form :=
  { id := "kat_good_superlative", lexeme := kat_good, cell := superlative, form := "saumǰobeso",
    analysed := "sa-u-mǰob-es-o", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_comparative_2 : Form :=
  { id := "kat_good_comparative_2", lexeme := kat_good, cell := comparative, form := "uk’etesi",
    analysed := "u-k’et-es-i", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_superlative_2 : Form :=
  { id := "kat_good_superlative_2", lexeme := kat_good, cell := superlative, form := "sauk’eteso",
    analysed := "sa-u-k’et-es-o", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_good_positive : Form :=
  { id := "sva_good_positive", lexeme := sva_good, cell := positive, form := "ezär",
    analysed := "ezär", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_good_comparative : Form :=
  { id := "sva_good_comparative", lexeme := sva_good, cell := comparative, form := "xoča",
    analysed := "xo-č-a", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_good_comparative_2 : Form :=
  { id := "sva_good_comparative_2", lexeme := sva_good, cell := comparative, form := "xočēl",
    analysed := "xo-č-ēl", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_good_superlative : Form :=
  { id := "sva_good_superlative", lexeme := sva_good, cell := superlative, form := "mačēne",
    analysed := "ma-č-ēne", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def chr_good_positive : Form :=
  { id := "chr_good_positive", lexeme := chr_good, cell := positive, form := "osda",
    analysed := "osda", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def chr_good_comparative : Form :=
  { id := "chr_good_comparative", lexeme := chr_good, cell := comparative, form := "dajehla",
    analysed := "dajehla", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def chr_good_superlative : Form :=
  { id := "chr_good_superlative", lexeme := chr_good, cell := superlative, form := "widajehlʌ̃ʔi",
    analysed := "wi-dajehl-ʌ̃ʔi", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_bad_positive : Form :=
  { id := "eng_bad_positive", lexeme := eng_bad, cell := positive, form := "bad",
    analysed := "bad", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_bad_comparative : Form :=
  { id := "eng_bad_comparative", lexeme := eng_bad, cell := comparative, form := "worse",
    analysed := "worse", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_bad_superlative : Form :=
  { id := "eng_bad_superlative", lexeme := eng_bad, cell := superlative, form := "worst",
    analysed := "wors-t", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def goh_bad_positive : Form :=
  { id := "goh_bad_positive", lexeme := goh_bad, cell := positive, form := "ubil",
    analysed := "ubil", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def goh_bad_comparative : Form :=
  { id := "goh_bad_comparative", lexeme := goh_bad, cell := comparative, form := "wirsiro",
    analysed := "wirsi-ro", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def goh_bad_superlative : Form :=
  { id := "goh_bad_superlative", lexeme := goh_bad, cell := superlative, form := "wirsisto",
    analysed := "wirsi-sto", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_vandr_positive : Form :=
  { id := "non_bad_vandr_positive", lexeme := non_bad_vandr, cell := positive, form := "vándr",
    analysed := "vándr", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_vandr_comparative : Form :=
  { id := "non_bad_vandr_comparative", lexeme := non_bad_vandr, cell := comparative, form := "verre",
    analysed := "ver-re", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_vandr_superlative : Form :=
  { id := "non_bad_vandr_superlative", lexeme := non_bad_vandr, cell := superlative, form := "verstr",
    analysed := "ver-str", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_illr_positive : Form :=
  { id := "non_bad_illr_positive", lexeme := non_bad_illr, cell := positive, form := "íllr",
    analysed := "íllr", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_illr_comparative : Form :=
  { id := "non_bad_illr_comparative", lexeme := non_bad_illr, cell := comparative, form := "verre",
    analysed := "ver-re", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_illr_superlative : Form :=
  { id := "non_bad_illr_superlative", lexeme := non_bad_illr, cell := superlative, form := "verstr",
    analysed := "ver-str", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_bad_positive : Form :=
  { id := "dan_bad_positive", lexeme := dan_bad, cell := positive, form := "slem",
    analysed := "slem", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_bad_comparative : Form :=
  { id := "dan_bad_comparative", lexeme := dan_bad, cell := comparative, form := "værre",
    analysed := "vær-re", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_bad_superlative : Form :=
  { id := "dan_bad_superlative", lexeme := dan_bad, cell := superlative, form := "værst",
    analysed := "vær-st", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fao_bad_positive : Form :=
  { id := "fao_bad_positive", lexeme := fao_bad, cell := positive, form := "ringur",
    analysed := "ringur", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fao_bad_comparative : Form :=
  { id := "fao_bad_comparative", lexeme := fao_bad, cell := comparative, form := "verri",
    analysed := "ver-ri", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fao_bad_superlative : Form :=
  { id := "fao_bad_superlative", lexeme := fao_bad, cell := superlative, form := "verstur",
    analysed := "ver-st-ur", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_positive : Form :=
  { id := "swe_bad_positive", lexeme := swe_bad, cell := positive, form := "dålig",
    analysed := "dålig", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_comparative : Form :=
  { id := "swe_bad_comparative", lexeme := swe_bad, cell := comparative, form := "värre",
    analysed := "vär-re", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_superlative : Form :=
  { id := "swe_bad_superlative", lexeme := swe_bad, cell := superlative, form := "värst",
    analysed := "vär-st", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_comparative_2 : Form :=
  { id := "swe_bad_comparative_2", lexeme := swe_bad, cell := comparative, form := "sämre",
    analysed := "säm-re", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_superlative_2 : Form :=
  { id := "swe_bad_superlative_2", lexeme := swe_bad, cell := superlative, form := "sämst",
    analysed := "säm-st", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def yid_bad_positive : Form :=
  { id := "yid_bad_positive", lexeme := yid_bad, cell := positive, form := "šlext",
    analysed := "šlext", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def yid_bad_comparative : Form :=
  { id := "yid_bad_comparative", lexeme := yid_bad, cell := comparative, form := "erger",
    analysed := "erg-er", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def yid_bad_superlative : Form :=
  { id := "yid_bad_superlative", lexeme := yid_bad, cell := superlative, form := "ergst",
    analysed := "erg-st", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_bad_positive : Form :=
  { id := "pol_bad_positive", lexeme := pol_bad, cell := positive, form := "zły",
    analysed := "zł-y", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_bad_comparative : Form :=
  { id := "pol_bad_comparative", lexeme := pol_bad, cell := comparative, form := "gorszy",
    analysed := "gor-szy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_bad_superlative : Form :=
  { id := "pol_bad_superlative", lexeme := pol_bad, cell := superlative, form := "najgorszy",
    analysed := "naj-gor-szy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_bad_positive : Form :=
  { id := "ces_bad_positive", lexeme := ces_bad, cell := positive, form := "špatný",
    analysed := "špatn-ý", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_bad_comparative : Form :=
  { id := "ces_bad_comparative", lexeme := ces_bad, cell := comparative, form := "horší",
    analysed := "hor-ší", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_bad_superlative : Form :=
  { id := "ces_bad_superlative", lexeme := ces_bad, cell := superlative, form := "nejhorší",
    analysed := "nej-hor-ší", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_bad_positive : Form :=
  { id := "ukr_bad_positive", lexeme := ukr_bad, cell := positive, form := "pohanyj",
    analysed := "pohan-yj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_bad_comparative : Form :=
  { id := "ukr_bad_comparative", lexeme := ukr_bad, cell := comparative, form := "hiršyj",
    analysed := "hir-šyj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_bad_superlative : Form :=
  { id := "ukr_bad_superlative", lexeme := ukr_bad, cell := superlative, form := "najhiršyj",
    analysed := "naj-hir-šyj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_drenn_positive : Form :=
  { id := "bel_bad_drenn_positive", lexeme := bel_bad_drenn, cell := positive, form := "drènny",
    analysed := "drènn-y", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_drenn_comparative : Form :=
  { id := "bel_bad_drenn_comparative", lexeme := bel_bad_drenn, cell := comparative, form := "horšy",
    analysed := "hor-šy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_drenn_superlative : Form :=
  { id := "bel_bad_drenn_superlative", lexeme := bel_bad_drenn, cell := superlative, form := "najhoršy",
    analysed := "naj-hor-šy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_blah_positive : Form :=
  { id := "bel_bad_blah_positive", lexeme := bel_bad_blah, cell := positive, form := "blahi",
    analysed := "blah-i", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_blah_comparative : Form :=
  { id := "bel_bad_blah_comparative", lexeme := bel_bad_blah, cell := comparative, form := "horšy",
    analysed := "hor-šy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_blah_superlative : Form :=
  { id := "bel_bad_blah_superlative", lexeme := bel_bad_blah, cell := superlative, form := "najhoršy",
    analysed := "naj-hor-šy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_bad_positive : Form :=
  { id := "hbs_bad_positive", lexeme := hbs_bad, cell := positive, form := "loš",
    analysed := "loš", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_bad_comparative : Form :=
  { id := "hbs_bad_comparative", lexeme := hbs_bad, cell := comparative, form := "gori",
    analysed := "gor-i", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_bad_superlative : Form :=
  { id := "hbs_bad_superlative", lexeme := hbs_bad, cell := superlative, form := "najgori",
    analysed := "naj-gor-i", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_bad_positive : Form :=
  { id := "rus_bad_positive", lexeme := rus_bad, cell := positive, form := "ploxoj",
    analysed := "plox-oj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_bad_comparative : Form :=
  { id := "rus_bad_comparative", lexeme := rus_bad, cell := comparative, form := "xuže",
    analysed := "xuž-e", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_bad_superlative : Form :=
  { id := "rus_bad_superlative", lexeme := rus_bad, cell := superlative, form := "naixudšij",
    analysed := "nai-xud-š-ij", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_bad_positive : Form :=
  { id := "lat_bad_positive", lexeme := lat_bad, cell := positive, form := "malus",
    analysed := "malus", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_bad_comparative : Form :=
  { id := "lat_bad_comparative", lexeme := lat_bad, cell := comparative, form := "pējor",
    analysed := "pēj-or", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_bad_superlative : Form :=
  { id := "lat_bad_superlative", lexeme := lat_bad, cell := superlative, form := "pessimus",
    analysed := "pe-ssimus", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_bad_positive : Form :=
  { id := "sga_bad_positive", lexeme := sga_bad, cell := positive, form := "olc",
    analysed := "olc", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_bad_comparative : Form :=
  { id := "sga_bad_comparative", lexeme := sga_bad, cell := comparative, form := "messa",
    analysed := "messa", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_bad_superlative : Form :=
  { id := "sga_bad_superlative", lexeme := sga_bad, cell := superlative, form := "messam",
    analysed := "messa-m", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_bad_positive : Form :=
  { id := "cym_bad_positive", lexeme := cym_bad, cell := positive, form := "drwg",
    analysed := "drwg", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_bad_comparative : Form :=
  { id := "cym_bad_comparative", lexeme := cym_bad, cell := comparative, form := "gwaeth",
    analysed := "gwaeth", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_bad_superlative : Form :=
  { id := "cym_bad_superlative", lexeme := cym_bad, cell := superlative, form := "gwaethaf",
    analysed := "gwaeth-af", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_bad_positive : Form :=
  { id := "bre_bad_positive", lexeme := bre_bad, cell := positive, form := "fall",
    analysed := "fall", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_bad_comparative : Form :=
  { id := "bre_bad_comparative", lexeme := bre_bad, cell := comparative, form := "gwash(oc’h)",
    analysed := "gwash-(oc’h)", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_bad_superlative : Form :=
  { id := "bre_bad_superlative", lexeme := bre_bad, cell := superlative, form := "gwashañ",
    analysed := "gwash-añ", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_positive : Form :=
  { id := "grc_bad_positive", lexeme := grc_bad, cell := positive, form := "kakós",
    analysed := "kak-ós", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_comparative : Form :=
  { id := "grc_bad_comparative", lexeme := grc_bad, cell := comparative, form := "cheírōn",
    analysed := "cheír-ōn", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_superlative : Form :=
  { id := "grc_bad_superlative", lexeme := grc_bad, cell := superlative, form := "cheíristos",
    analysed := "cheír-ist-os", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_comparative_2 : Form :=
  { id := "grc_bad_comparative_2", lexeme := grc_bad, cell := comparative, form := "héssōn",
    analysed := "héssōn", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_superlative_2 : Form :=
  { id := "grc_bad_superlative_2", lexeme := grc_bad, cell := superlative, form := "hékistos",
    analysed := "hék-ist-os", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_big_positive : Form :=
  { id := "got_big_positive", lexeme := got_big, cell := positive, form := "mikils",
    analysed := "mikil-s", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_big_comparative : Form :=
  { id := "got_big_comparative", lexeme := got_big, cell := comparative, form := "maiza",
    analysed := "mai-za", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_big_superlative : Form :=
  { id := "got_big_superlative", lexeme := got_big, cell := superlative, form := "maists",
    analysed := "mai-sts", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_big_positive : Form :=
  { id := "ces_big_positive", lexeme := ces_big, cell := positive, form := "velký",
    analysed := "velk-ý", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_big_comparative : Form :=
  { id := "ces_big_comparative", lexeme := ces_big, cell := comparative, form := "větší",
    analysed := "vět-ší", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_big_superlative : Form :=
  { id := "ces_big_superlative", lexeme := ces_big, cell := superlative, form := "největší",
    analysed := "nej-vět-ší", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_big_positive : Form :=
  { id := "ukr_big_positive", lexeme := ukr_big, cell := positive, form := "velykyj",
    analysed := "velyk-yj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_big_comparative : Form :=
  { id := "ukr_big_comparative", lexeme := ukr_big, cell := comparative, form := "bil’šyj",
    analysed := "bil’-šyj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_big_superlative : Form :=
  { id := "ukr_big_superlative", lexeme := ukr_big, cell := superlative, form := "najbil’šyj",
    analysed := "naj-bil’-šyj", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_big_positive : Form :=
  { id := "pol_big_positive", lexeme := pol_big, cell := positive, form := "duży",
    analysed := "duż-y", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_big_comparative : Form :=
  { id := "pol_big_comparative", lexeme := pol_big, cell := comparative, form := "większy",
    analysed := "więk-szy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_big_superlative : Form :=
  { id := "pol_big_superlative", lexeme := pol_big, cell := superlative, form := "największy",
    analysed := "naj-więk-szy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_big_positive : Form :=
  { id := "cym_big_positive", lexeme := cym_big, cell := positive, form := "mawr",
    analysed := "mawr", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_big_comparative : Form :=
  { id := "cym_big_comparative", lexeme := cym_big, cell := comparative, form := "mwy",
    analysed := "mwy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_big_superlative : Form :=
  { id := "cym_big_superlative", lexeme := cym_big, cell := superlative, form := "mwyaf",
    analysed := "mwy-af", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_big_positive : Form :=
  { id := "pal_big_positive", lexeme := pal_big, cell := positive, form := "wazurg",
    analysed := "wazurg", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_big_comparative : Form :=
  { id := "pal_big_comparative", lexeme := pal_big, cell := comparative, form := "meh/mahīy",
    analysed := "meh/mah-īy", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_big_superlative : Form :=
  { id := "pal_big_superlative", lexeme := pal_big, cell := superlative, form := "mahist",
    analysed := "mah-ist", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_big_positive : Form :=
  { id := "sva_big_positive", lexeme := sva_big, cell := positive, form := "d͜zɣəd",
    analysed := "d͜zɣəd", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_big_comparative : Form :=
  { id := "sva_big_comparative", lexeme := sva_big, cell := comparative, form := "xoša",
    analysed := "xo-š-a", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_big_comparative_2 : Form :=
  { id := "sva_big_comparative_2", lexeme := sva_big, cell := comparative, form := "xošēl",
    analysed := "xo-š-ēl", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_big_superlative : Form :=
  { id := "sva_big_superlative", lexeme := sva_big, cell := superlative, form := "mašēne",
    analysed := "ma-š-ēne", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_small_positive : Form :=
  { id := "got_small_positive", lexeme := got_small, cell := positive, form := "leitils",
    analysed := "leitils", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_small_comparative : Form :=
  { id := "got_small_comparative", lexeme := got_small, cell := comparative, form := "minniza",
    analysed := "minn-iza", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_small_superlative : Form :=
  { id := "got_small_superlative", lexeme := got_small, cell := superlative, form := "minnists",
    analysed := "minn-ists", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ang_small_positive : Form :=
  { id := "ang_small_positive", lexeme := ang_small, cell := positive, form := "lýtel",
    analysed := "lýtel", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ang_small_comparative : Form :=
  { id := "ang_small_comparative", lexeme := ang_small, cell := comparative, form := "læssa",
    analysed := "læssa", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ang_small_superlative : Form :=
  { id := "ang_small_superlative", lexeme := ang_small, cell := superlative, form := "læst",
    analysed := "læ-st", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_small_positive : Form :=
  { id := "dan_small_positive", lexeme := dan_small, cell := positive, form := "små",
    analysed := "små", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_small_comparative : Form :=
  { id := "dan_small_comparative", lexeme := dan_small, cell := comparative, form := "mindre",
    analysed := "mind-re", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_small_superlative : Form :=
  { id := "dan_small_superlative", lexeme := dan_small, cell := superlative, form := "mindst",
    analysed := "mind-st", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_small_positive : Form :=
  { id := "hbs_small_positive", lexeme := hbs_small, cell := positive, form := "mali",
    analysed := "mali", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_small_positive_2 : Form :=
  { id := "hbs_small_positive_2", lexeme := hbs_small, cell := positive, form := "malen",
    analysed := "malen", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_small_comparative : Form :=
  { id := "hbs_small_comparative", lexeme := hbs_small, cell := comparative, form := "manji",
    analysed := "man-ji", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_small_superlative : Form :=
  { id := "hbs_small_superlative", lexeme := hbs_small, cell := superlative, form := "najmanji",
    analysed := "naj-man-ji", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_small_positive : Form :=
  { id := "lat_small_positive", lexeme := lat_small, cell := positive, form := "parvus",
    analysed := "parvus", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_small_positive_2 : Form :=
  { id := "lat_small_positive_2", lexeme := lat_small, cell := positive, form := "paulum",
    analysed := "paulum", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_small_comparative : Form :=
  { id := "lat_small_comparative", lexeme := lat_small, cell := comparative, form := "minor",
    analysed := "min-or", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_small_superlative : Form :=
  { id := "lat_small_superlative", lexeme := lat_small, cell := superlative, form := "minimus",
    analysed := "min-imus", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_small_positive : Form :=
  { id := "cym_small_positive", lexeme := cym_small, cell := positive, form := "bach",
    analysed := "bach", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_small_comparative : Form :=
  { id := "cym_small_comparative", lexeme := cym_small, cell := comparative, form := "llai",
    analysed := "llai", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_small_superlative : Form :=
  { id := "cym_small_superlative", lexeme := cym_small, cell := superlative, form := "lleiaf",
    analysed := "llei-af", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_positive : Form :=
  { id := "grc_small_positive", lexeme := grc_small, cell := positive, form := "mikrós",
    analysed := "mikr-ós", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_comparative : Form :=
  { id := "grc_small_comparative", lexeme := grc_small, cell := comparative, form := "meíōn",
    analysed := "meí-ōn", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_superlative : Form :=
  { id := "grc_small_superlative", lexeme := grc_small, cell := superlative, form := "meĩstos",
    analysed := "meĩ-st-os", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_comparative_2 : Form :=
  { id := "grc_small_comparative_2", lexeme := grc_small, cell := comparative, form := "elássōn",
    analysed := "eláss-ōn", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_superlative_2 : Form :=
  { id := "grc_small_superlative_2", lexeme := grc_small, cell := superlative, form := "elachistos",
    analysed := "elach-ist-os", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_small_positive : Form :=
  { id := "pal_small_positive", lexeme := pal_small, cell := positive, form := "kōdag",
    analysed := "kōdag", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_small_comparative : Form :=
  { id := "pal_small_comparative", lexeme := pal_small, cell := comparative, form := "keh",
    analysed := "keh", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_small_superlative : Form :=
  { id := "pal_small_superlative", lexeme := pal_small, cell := superlative, form := "kasišts",
    analysed := "kas-išts", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_old_positive : Form :=
  { id := "non_old_positive", lexeme := non_old, cell := positive, form := "gamall",
    analysed := "gamall", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_old_comparative : Form :=
  { id := "non_old_comparative", lexeme := non_old, cell := comparative, form := "ellre",
    analysed := "ell-re", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_old_superlative : Form :=
  { id := "non_old_superlative", lexeme := non_old, cell := superlative, form := "ellztr",
    analysed := "ell-ztr", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_near_positive : Form :=
  { id := "cym_near_positive", lexeme := cym_near, cell := positive, form := "agos",
    analysed := "agos", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_near_comparative : Form :=
  { id := "cym_near_comparative", lexeme := cym_near, cell := comparative, form := "nes",
    analysed := "nes", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_near_superlative : Form :=
  { id := "cym_near_superlative", lexeme := cym_near, cell := superlative, form := "nesaf",
    analysed := "nes-af", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_strong_positive : Form :=
  { id := "cym_strong_positive", lexeme := cym_strong, cell := positive, form := "cryf",
    analysed := "cryf", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_strong_comparative : Form :=
  { id := "cym_strong_comparative", lexeme := cym_strong, cell := comparative, form := "trech",
    analysed := "trech", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_strong_superlative : Form :=
  { id := "cym_strong_superlative", lexeme := cym_strong, cell := superlative, form := "trechaf",
    analysed := "trech-af", source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_good.roots : RootClasses :=
  { id := "eng_good", lexeme := eng_good, forms := [eng_good_positive, eng_good_comparative, eng_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def swe_good.roots : RootClasses :=
  { id := "swe_good", lexeme := swe_good, forms := [swe_good_positive, swe_good_comparative, swe_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def got_good.roots : RootClasses :=
  { id := "got_good", lexeme := got_good, forms := [got_good_positive, got_good_comparative, got_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cim_good.roots : RootClasses :=
  { id := "cim_good", lexeme := cim_good, forms := [cim_good_positive, cim_good_comparative, cim_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ces_good.roots : RootClasses :=
  { id := "ces_good", lexeme := ces_good, forms := [ces_good_positive, ces_good_comparative, ces_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def hbs_good.roots : RootClasses :=
  { id := "hbs_good", lexeme := hbs_good, forms := [hbs_good_positive, hbs_good_comparative, hbs_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sorb_good.roots : RootClasses :=
  { id := "sorb_good", lexeme := sorb_good, forms := [sorb_good_positive, sorb_good_comparative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "Table 4.1, note a"⟩
    ] }

def ukr_good_dobr.roots : RootClasses :=
  { id := "ukr_good_dobr", lexeme := ukr_good_dobr, forms := [ukr_good_dobr_positive, ukr_good_dobr_comparative, ukr_good_dobr_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ukr_good_harn.roots : RootClasses :=
  { id := "ukr_good_harn", lexeme := ukr_good_harn, forms := [ukr_good_harn_positive, ukr_good_harn_comparative, ukr_good_harn_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def rus_good.roots : RootClasses :=
  { id := "rus_good", lexeme := rus_good, forms := [rus_good_positive, rus_good_comparative, rus_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def lat_good.roots : RootClasses :=
  { id := "lat_good", lexeme := lat_good, forms := [lat_good_positive, lat_good_comparative, lat_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "(31a)"⟩
    ] }

def cym_good.roots : RootClasses :=
  { id := "cym_good", lexeme := cym_good, forms := [cym_good_positive, cym_good_comparative, cym_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "(31b)"⟩
    ] }

def sga_good.roots : RootClasses :=
  { id := "sga_good", lexeme := sga_good, forms := [sga_good_positive, sga_good_comparative, sga_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "(31c)"⟩
    ] }

def bre_good.roots : RootClasses :=
  { id := "bre_good", lexeme := bre_good, forms := [bre_good_positive, bre_good_comparative, bre_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_good_amein.roots : RootClasses :=
  { id := "grc_good_amein", lexeme := grc_good, forms := [grc_good_positive, grc_good_comparative, grc_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "p. 112"⟩
    ] }

def grc_good_arei.roots : RootClasses :=
  { id := "grc_good_arei", lexeme := grc_good, forms := [grc_good_positive, grc_good_comparative_2, grc_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_good_belt.roots : RootClasses :=
  { id := "grc_good_belt", lexeme := grc_good, forms := [grc_good_positive, grc_good_comparative_3, grc_good_superlative_3],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_good_kreiss.roots : RootClasses :=
  { id := "grc_good_kreiss", lexeme := grc_good, forms := [grc_good_positive, grc_good_comparative_4, grc_good_superlative_4],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_good_lo.roots : RootClasses :=
  { id := "grc_good_lo", lexeme := grc_good, forms := [grc_good_positive, grc_good_comparative_5, grc_good_superlative_5],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def san_good_sre.roots : RootClasses :=
  { id := "san_good_sre", lexeme := san_good, forms := [san_good_positive, san_good_comparative, san_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def san_good_jya.roots : RootClasses :=
  { id := "san_good_jya", lexeme := san_good, forms := [san_good_positive, san_good_comparative_2, san_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def kho_good.roots : RootClasses :=
  { id := "kho_good", lexeme := kho_good, forms := [kho_good_positive, kho_good_comparative, kho_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pal_good.roots : RootClasses :=
  { id := "pal_good", lexeme := pal_good, forms := [pal_good_positive, pal_good_comparative, pal_good_superlative, pal_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "(31d)"⟩
    ] }

def fas_good.roots : RootClasses :=
  { id := "fas_good", lexeme := fas_good, forms := [fas_good_positive, fas_good_comparative, fas_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def eus_good_hobe.roots : RootClasses :=
  { id := "eus_good_hobe", lexeme := eus_good, forms := [eus_good_positive, eus_good_comparative, eus_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def eus_good_on.roots : RootClasses :=
  { id := "eus_good_on", lexeme := eus_good, forms := [eus_good_positive, eus_good_comparative, eus_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 0)],
    source := [
      ⟨"bobaljik-2012", "(143)"⟩
    ] }

def fin_good.roots : RootClasses :=
  { id := "fin_good", lexeme := fin_good, forms := [fin_good_positive, fin_good_comparative, fin_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sjd_good.roots : RootClasses :=
  { id := "sjd_good", lexeme := sjd_good, forms := [sjd_good_positive, sjd_good_comparative, sjd_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def kat_good_mjob.roots : RootClasses :=
  { id := "kat_good_mjob", lexeme := kat_good, forms := [kat_good_positive, kat_good_comparative, kat_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def kat_good_ket.roots : RootClasses :=
  { id := "kat_good_ket", lexeme := kat_good, forms := [kat_good_positive, kat_good_comparative_2, kat_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sva_good.roots : RootClasses :=
  { id := "sva_good", lexeme := sva_good, forms := [sva_good_positive, sva_good_comparative, sva_good_comparative_2, sva_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def chr_good.roots : RootClasses :=
  { id := "chr_good", lexeme := chr_good, forms := [chr_good_positive, chr_good_comparative, chr_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def eng_bad.roots : RootClasses :=
  { id := "eng_bad", lexeme := eng_bad, forms := [eng_bad_positive, eng_bad_comparative, eng_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def goh_bad.roots : RootClasses :=
  { id := "goh_bad", lexeme := goh_bad, forms := [goh_bad_positive, goh_bad_comparative, goh_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def non_bad_vandr.roots : RootClasses :=
  { id := "non_bad_vandr", lexeme := non_bad_vandr, forms := [non_bad_vandr_positive, non_bad_vandr_comparative, non_bad_vandr_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def non_bad_illr.roots : RootClasses :=
  { id := "non_bad_illr", lexeme := non_bad_illr, forms := [non_bad_illr_positive, non_bad_illr_comparative, non_bad_illr_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def dan_bad.roots : RootClasses :=
  { id := "dan_bad", lexeme := dan_bad, forms := [dan_bad_positive, dan_bad_comparative, dan_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def fao_bad.roots : RootClasses :=
  { id := "fao_bad", lexeme := fao_bad, forms := [fao_bad_positive, fao_bad_comparative, fao_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def swe_bad_var.roots : RootClasses :=
  { id := "swe_bad_var", lexeme := swe_bad, forms := [swe_bad_positive, swe_bad_comparative, swe_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def swe_bad_sam.roots : RootClasses :=
  { id := "swe_bad_sam", lexeme := swe_bad, forms := [swe_bad_positive, swe_bad_comparative_2, swe_bad_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def yid_bad.roots : RootClasses :=
  { id := "yid_bad", lexeme := yid_bad, forms := [yid_bad_positive, yid_bad_comparative, yid_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pol_bad.roots : RootClasses :=
  { id := "pol_bad", lexeme := pol_bad, forms := [pol_bad_positive, pol_bad_comparative, pol_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ces_bad.roots : RootClasses :=
  { id := "ces_bad", lexeme := ces_bad, forms := [ces_bad_positive, ces_bad_comparative, ces_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ukr_bad.roots : RootClasses :=
  { id := "ukr_bad", lexeme := ukr_bad, forms := [ukr_bad_positive, ukr_bad_comparative, ukr_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def bel_bad_drenn.roots : RootClasses :=
  { id := "bel_bad_drenn", lexeme := bel_bad_drenn, forms := [bel_bad_drenn_positive, bel_bad_drenn_comparative, bel_bad_drenn_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def bel_bad_blah.roots : RootClasses :=
  { id := "bel_bad_blah", lexeme := bel_bad_blah, forms := [bel_bad_blah_positive, bel_bad_blah_comparative, bel_bad_blah_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def hbs_bad.roots : RootClasses :=
  { id := "hbs_bad", lexeme := hbs_bad, forms := [hbs_bad_positive, hbs_bad_comparative, hbs_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def rus_bad.roots : RootClasses :=
  { id := "rus_bad", lexeme := rus_bad, forms := [rus_bad_positive, rus_bad_comparative, rus_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def lat_bad.roots : RootClasses :=
  { id := "lat_bad", lexeme := lat_bad, forms := [lat_bad_positive, lat_bad_comparative, lat_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sga_bad.roots : RootClasses :=
  { id := "sga_bad", lexeme := sga_bad, forms := [sga_bad_positive, sga_bad_comparative, sga_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_bad.roots : RootClasses :=
  { id := "cym_bad", lexeme := cym_bad, forms := [cym_bad_positive, cym_bad_comparative, cym_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def bre_bad.roots : RootClasses :=
  { id := "bre_bad", lexeme := bre_bad, forms := [bre_bad_positive, bre_bad_comparative, bre_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_bad_cheir.roots : RootClasses :=
  { id := "grc_bad_cheir", lexeme := grc_bad, forms := [grc_bad_positive, grc_bad_comparative, grc_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_bad_hess.roots : RootClasses :=
  { id := "grc_bad_hess", lexeme := grc_bad, forms := [grc_bad_positive, grc_bad_comparative_2, grc_bad_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def got_big.roots : RootClasses :=
  { id := "got_big", lexeme := got_big, forms := [got_big_positive, got_big_comparative, got_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ces_big.roots : RootClasses :=
  { id := "ces_big", lexeme := ces_big, forms := [ces_big_positive, ces_big_comparative, ces_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ukr_big.roots : RootClasses :=
  { id := "ukr_big", lexeme := ukr_big, forms := [ukr_big_positive, ukr_big_comparative, ukr_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pol_big.roots : RootClasses :=
  { id := "pol_big", lexeme := pol_big, forms := [pol_big_positive, pol_big_comparative, pol_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_big.roots : RootClasses :=
  { id := "cym_big", lexeme := cym_big, forms := [cym_big_positive, cym_big_comparative, cym_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pal_big.roots : RootClasses :=
  { id := "pal_big", lexeme := pal_big, forms := [pal_big_positive, pal_big_comparative, pal_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sva_big.roots : RootClasses :=
  { id := "sva_big", lexeme := sva_big, forms := [sva_big_positive, sva_big_comparative, sva_big_comparative_2, sva_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def got_small.roots : RootClasses :=
  { id := "got_small", lexeme := got_small, forms := [got_small_positive, got_small_comparative, got_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ang_small.roots : RootClasses :=
  { id := "ang_small", lexeme := ang_small, forms := [ang_small_positive, ang_small_comparative, ang_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def dan_small.roots : RootClasses :=
  { id := "dan_small", lexeme := dan_small, forms := [dan_small_positive, dan_small_comparative, dan_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def hbs_small.roots : RootClasses :=
  { id := "hbs_small", lexeme := hbs_small, forms := [hbs_small_positive, hbs_small_positive_2, hbs_small_comparative, hbs_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def lat_small.roots : RootClasses :=
  { id := "lat_small", lexeme := lat_small, forms := [lat_small_positive, lat_small_positive_2, lat_small_comparative, lat_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_small.roots : RootClasses :=
  { id := "cym_small", lexeme := cym_small, forms := [cym_small_positive, cym_small_comparative, cym_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_small_mei.roots : RootClasses :=
  { id := "grc_small_mei", lexeme := grc_small, forms := [grc_small_positive, grc_small_comparative, grc_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_small_elass.roots : RootClasses :=
  { id := "grc_small_elass", lexeme := grc_small, forms := [grc_small_positive, grc_small_comparative_2, grc_small_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pal_small.roots : RootClasses :=
  { id := "pal_small", lexeme := pal_small, forms := [pal_small_positive, pal_small_comparative, pal_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def non_old.roots : RootClasses :=
  { id := "non_old", lexeme := non_old, forms := [non_old_positive, non_old_comparative, non_old_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_near.roots : RootClasses :=
  { id := "cym_near", lexeme := cym_near, forms := [cym_near_positive, cym_near_comparative, cym_near_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_strong.roots : RootClasses :=
  { id := "cym_strong", lexeme := cym_strong, forms := [cym_strong_positive, cym_strong_comparative, cym_strong_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [eng_good, swe_good, got_good, cim_good, ces_good, hbs_good, sorb_good, ukr_good_dobr, ukr_good_harn, rus_good, lat_good, cym_good, sga_good, bre_good, grc_good, san_good, kho_good, pal_good, fas_good, eus_good, fin_good, sjd_good, kat_good, sva_good, chr_good, eng_bad, goh_bad, non_bad_vandr, non_bad_illr, dan_bad, fao_bad, swe_bad, yid_bad, pol_bad, ces_bad, ukr_bad, bel_bad_drenn, bel_bad_blah, hbs_bad, rus_bad, lat_bad, sga_bad, cym_bad, bre_bad, grc_bad, got_big, ces_big, ukr_big, pol_big, cym_big, pal_big, sva_big, got_small, ang_small, dan_small, hbs_small, lat_small, cym_small, grc_small, pal_small, non_old, cym_near, cym_strong]

/-- Every form of the data. -/
def forms : List Form := [eng_good_positive, eng_good_comparative, eng_good_superlative, swe_good_positive, swe_good_comparative, swe_good_superlative, got_good_positive, got_good_comparative, got_good_superlative, cim_good_positive, cim_good_comparative, cim_good_superlative, ces_good_positive, ces_good_comparative, ces_good_superlative, hbs_good_positive, hbs_good_comparative, hbs_good_superlative, sorb_good_positive, sorb_good_comparative, ukr_good_dobr_positive, ukr_good_dobr_comparative, ukr_good_dobr_superlative, ukr_good_harn_positive, ukr_good_harn_comparative, ukr_good_harn_superlative, rus_good_positive, rus_good_comparative, rus_good_superlative, lat_good_positive, lat_good_comparative, lat_good_superlative, cym_good_positive, cym_good_comparative, cym_good_superlative, sga_good_positive, sga_good_comparative, sga_good_superlative, bre_good_positive, bre_good_comparative, bre_good_superlative, grc_good_positive, grc_good_comparative, grc_good_superlative, grc_good_comparative_2, grc_good_superlative_2, grc_good_comparative_3, grc_good_superlative_3, grc_good_comparative_4, grc_good_superlative_4, grc_good_comparative_5, grc_good_superlative_5, san_good_positive, san_good_comparative, san_good_superlative, san_good_comparative_2, san_good_superlative_2, kho_good_positive, kho_good_comparative, kho_good_superlative, pal_good_positive, pal_good_comparative, pal_good_superlative, pal_good_superlative_2, fas_good_positive, fas_good_comparative, fas_good_superlative, eus_good_positive, eus_good_comparative, eus_good_superlative, eus_good_superlative_2, fin_good_positive, fin_good_comparative, fin_good_superlative, sjd_good_positive, sjd_good_comparative, sjd_good_superlative, kat_good_positive, kat_good_comparative, kat_good_superlative, kat_good_comparative_2, kat_good_superlative_2, sva_good_positive, sva_good_comparative, sva_good_comparative_2, sva_good_superlative, chr_good_positive, chr_good_comparative, chr_good_superlative, eng_bad_positive, eng_bad_comparative, eng_bad_superlative, goh_bad_positive, goh_bad_comparative, goh_bad_superlative, non_bad_vandr_positive, non_bad_vandr_comparative, non_bad_vandr_superlative, non_bad_illr_positive, non_bad_illr_comparative, non_bad_illr_superlative, dan_bad_positive, dan_bad_comparative, dan_bad_superlative, fao_bad_positive, fao_bad_comparative, fao_bad_superlative, swe_bad_positive, swe_bad_comparative, swe_bad_superlative, swe_bad_comparative_2, swe_bad_superlative_2, yid_bad_positive, yid_bad_comparative, yid_bad_superlative, pol_bad_positive, pol_bad_comparative, pol_bad_superlative, ces_bad_positive, ces_bad_comparative, ces_bad_superlative, ukr_bad_positive, ukr_bad_comparative, ukr_bad_superlative, bel_bad_drenn_positive, bel_bad_drenn_comparative, bel_bad_drenn_superlative, bel_bad_blah_positive, bel_bad_blah_comparative, bel_bad_blah_superlative, hbs_bad_positive, hbs_bad_comparative, hbs_bad_superlative, rus_bad_positive, rus_bad_comparative, rus_bad_superlative, lat_bad_positive, lat_bad_comparative, lat_bad_superlative, sga_bad_positive, sga_bad_comparative, sga_bad_superlative, cym_bad_positive, cym_bad_comparative, cym_bad_superlative, bre_bad_positive, bre_bad_comparative, bre_bad_superlative, grc_bad_positive, grc_bad_comparative, grc_bad_superlative, grc_bad_comparative_2, grc_bad_superlative_2, got_big_positive, got_big_comparative, got_big_superlative, ces_big_positive, ces_big_comparative, ces_big_superlative, ukr_big_positive, ukr_big_comparative, ukr_big_superlative, pol_big_positive, pol_big_comparative, pol_big_superlative, cym_big_positive, cym_big_comparative, cym_big_superlative, pal_big_positive, pal_big_comparative, pal_big_superlative, sva_big_positive, sva_big_comparative, sva_big_comparative_2, sva_big_superlative, got_small_positive, got_small_comparative, got_small_superlative, ang_small_positive, ang_small_comparative, ang_small_superlative, dan_small_positive, dan_small_comparative, dan_small_superlative, hbs_small_positive, hbs_small_positive_2, hbs_small_comparative, hbs_small_superlative, lat_small_positive, lat_small_positive_2, lat_small_comparative, lat_small_superlative, cym_small_positive, cym_small_comparative, cym_small_superlative, grc_small_positive, grc_small_comparative, grc_small_superlative, grc_small_comparative_2, grc_small_superlative_2, pal_small_positive, pal_small_comparative, pal_small_superlative, non_old_positive, non_old_comparative, non_old_superlative, cym_near_positive, cym_near_comparative, cym_near_superlative, cym_strong_positive, cym_strong_comparative, cym_strong_superlative]

/-- Every root-class judgment of the data. -/
def rootClasses : List RootClasses := [eng_good.roots, swe_good.roots, got_good.roots, cim_good.roots, ces_good.roots, hbs_good.roots, sorb_good.roots, ukr_good_dobr.roots, ukr_good_harn.roots, rus_good.roots, lat_good.roots, cym_good.roots, sga_good.roots, bre_good.roots, grc_good_amein.roots, grc_good_arei.roots, grc_good_belt.roots, grc_good_kreiss.roots, grc_good_lo.roots, san_good_sre.roots, san_good_jya.roots, kho_good.roots, pal_good.roots, fas_good.roots, eus_good_hobe.roots, eus_good_on.roots, fin_good.roots, sjd_good.roots, kat_good_mjob.roots, kat_good_ket.roots, sva_good.roots, chr_good.roots, eng_bad.roots, goh_bad.roots, non_bad_vandr.roots, non_bad_illr.roots, dan_bad.roots, fao_bad.roots, swe_bad_var.roots, swe_bad_sam.roots, yid_bad.roots, pol_bad.roots, ces_bad.roots, ukr_bad.roots, bel_bad_drenn.roots, bel_bad_blah.roots, hbs_bad.roots, rus_bad.roots, lat_bad.roots, sga_bad.roots, cym_bad.roots, bre_bad.roots, grc_bad_cheir.roots, grc_bad_hess.roots, got_big.roots, ces_big.roots, ukr_big.roots, pol_big.roots, cym_big.roots, pal_big.roots, sva_big.roots, got_small.roots, ang_small.roots, dan_small.roots, hbs_small.roots, lat_small.roots, cym_small.roots, grc_small_mei.roots, grc_small_elass.roots, pal_small.roots, non_old.roots, cym_near.roots, cym_strong.roots]

end Bobaljik2012.Paradigms
