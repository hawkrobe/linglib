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

def eng_many : Lexeme :=
  { id := "eng_many", languageId := "stan1293", label := "many", meaning := "many, much" }

def eng_much : Lexeme :=
  { id := "eng_much", languageId := "stan1293", label := "much", meaning := "many, much" }

def eng_lot : Lexeme :=
  { id := "eng_lot", languageId := "stan1293", label := "(a) lot", meaning := "many, much" }

def deu_many : Lexeme :=
  { id := "deu_many", languageId := "stan1295", label := "viel", meaning := "many, much" }

def fao_many : Lexeme :=
  { id := "fao_many", languageId := "faro1244", label := "nógvur", meaning := "many, much" }

def afr_many_party : Lexeme :=
  { id := "afr_many_party", languageId := "afri1274", label := "party", meaning := "many, much" }

def afr_many_baie : Lexeme :=
  { id := "afr_many_baie", languageId := "afri1274", label := "baie", meaning := "many, much" }

def yid_many : Lexeme :=
  { id := "yid_many", languageId := "east2295", label := "sakh", meaning := "many, much" }

def dan_many : Lexeme :=
  { id := "dan_many", languageId := "dani1285", label := "mange", meaning := "many, much" }

def ces_many : Lexeme :=
  { id := "ces_many", languageId := "czec1258", label := "mnoho", meaning := "many, much" }

def rus_many : Lexeme :=
  { id := "rus_many", languageId := "russ1263", label := "mnogo", meaning := "many, much" }

def bul_many : Lexeme :=
  { id := "bul_many", languageId := "bulg1262", label := "mnogo", meaning := "many, much" }

def pol_many : Lexeme :=
  { id := "pol_many", languageId := "poli1260", label := "wiele", meaning := "many, much" }

def hbs_many : Lexeme :=
  { id := "hbs_many", languageId := "sout1528", label := "puno", meaning := "many, much" }

def ukr_many_bahato : Lexeme :=
  { id := "ukr_many_bahato", languageId := "ukra1253", label := "baháto", meaning := "many, much" }

def ukr_many_duze : Lexeme :=
  { id := "ukr_many_duze", languageId := "ukra1253", label := "dúže", meaning := "many, much" }

def lav_many : Lexeme :=
  { id := "lav_many", languageId := "latv1249", label := "daudz", meaning := "many, much" }

def lat_many : Lexeme :=
  { id := "lat_many", languageId := "lati1261", label := "mult", meaning := "many, much" }

def bre_many : Lexeme :=
  { id := "bre_many", languageId := "bret1244", label := "kalz", meaning := "many, much" }

def cym_many : Lexeme :=
  { id := "cym_many", languageId := "wels1247", label := "llawer", meaning := "many, much" }

def grc_many : Lexeme :=
  { id := "grc_many", languageId := "anci1242", label := "polús", meaning := "many, much" }

def hye_many : Lexeme :=
  { id := "hye_many", languageId := "nucl1235", label := "šaterë", meaning := "many, much" }

def fas_many_xele : Lexeme :=
  { id := "fas_many_xele", languageId := "west2369", label := "xele", meaning := "many, much" }

def fas_many_ziad : Lexeme :=
  { id := "fas_many_ziad", languageId := "west2369", label := "ziad", meaning := "many, much" }

def eus_many : Lexeme :=
  { id := "eus_many", languageId := "basq1248", label := "asko", meaning := "many, much" }

def fin_many_monet : Lexeme :=
  { id := "fin_many_monet", languageId := "finn1318", label := "monet", meaning := "many, much" }

def fin_many_paljon : Lexeme :=
  { id := "fin_many_paljon", languageId := "finn1318", label := "paljon", meaning := "many, much" }

def krl_many : Lexeme :=
  { id := "krl_many", languageId := "kare1335", label := "äijä", meaning := "many, much" }

def hun_many : Lexeme :=
  { id := "hun_many", languageId := "hung1274", label := "sok", meaning := "many, much" }

def kat_many : Lexeme :=
  { id := "kat_many", languageId := "nucl1302", label := "bevri", meaning := "many, much" }

def kbd_many : Lexeme :=
  { id := "kbd_many", languageId := "kaba1278", label := "kwad", meaning := "many, much" }

def eng_few : Lexeme :=
  { id := "eng_few", languageId := "stan1293", label := "(a) little", meaning := "few" }

def afr_few : Lexeme :=
  { id := "afr_few", languageId := "afri1274", label := "weinig", meaning := "few" }

def fry_few : Lexeme :=
  { id := "fry_few", languageId := "west2354", label := "(en) bytsje", meaning := "few" }

def ukr_few : Lexeme :=
  { id := "ukr_few", languageId := "ukra1253", label := "troxi", meaning := "few" }

def lat_few : Lexeme :=
  { id := "lat_few", languageId := "lati1261", label := "paucus", meaning := "few" }

def grc_few : Lexeme :=
  { id := "grc_few", languageId := "anci1242", label := "olígos", meaning := "few" }

def krl_many_onego : Lexeme :=
  { id := "krl_many_onego", languageId := "kare1335", label := "äijy", meaning := "many, much" }

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

def eng_many_positive : Form :=
  { id := "eng_many_positive", lexeme := eng_many, cell := positive, form := "many",
    analysed := "many", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_many_comparative : Form :=
  { id := "eng_many_comparative", lexeme := eng_many, cell := comparative, form := "more",
    analysed := "mo-re", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_many_superlative : Form :=
  { id := "eng_many_superlative", lexeme := eng_many, cell := superlative, form := "most",
    analysed := "mo-st", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_much_positive : Form :=
  { id := "eng_much_positive", lexeme := eng_much, cell := positive, form := "much",
    analysed := "much", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_much_comparative : Form :=
  { id := "eng_much_comparative", lexeme := eng_much, cell := comparative, form := "more",
    analysed := "mo-re", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_much_superlative : Form :=
  { id := "eng_much_superlative", lexeme := eng_much, cell := superlative, form := "most",
    analysed := "mo-st", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_lot_positive : Form :=
  { id := "eng_lot_positive", lexeme := eng_lot, cell := positive, form := "(a) lot",
    analysed := "(a) lot", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_lot_comparative : Form :=
  { id := "eng_lot_comparative", lexeme := eng_lot, cell := comparative, form := "more",
    analysed := "mo-re", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_lot_superlative : Form :=
  { id := "eng_lot_superlative", lexeme := eng_lot, cell := superlative, form := "most",
    analysed := "mo-st", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def deu_many_positive : Form :=
  { id := "deu_many_positive", lexeme := deu_many, cell := positive, form := "viel",
    analysed := "viel", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def deu_many_comparative : Form :=
  { id := "deu_many_comparative", lexeme := deu_many, cell := comparative, form := "mehr",
    analysed := "me-hr", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def deu_many_superlative : Form :=
  { id := "deu_many_superlative", lexeme := deu_many, cell := superlative, form := "meist",
    analysed := "mei-st", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fao_many_positive : Form :=
  { id := "fao_many_positive", lexeme := fao_many, cell := positive, form := "nógvur",
    analysed := "nógv-ur", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fao_many_comparative : Form :=
  { id := "fao_many_comparative", lexeme := fao_many, cell := comparative, form := "meiri",
    analysed := "mei-ri", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fao_many_superlative : Form :=
  { id := "fao_many_superlative", lexeme := fao_many, cell := superlative, form := "mestur",
    analysed := "me-st-ur", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_party_positive : Form :=
  { id := "afr_many_party_positive", lexeme := afr_many_party, cell := positive, form := "party",
    analysed := "party", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_party_comparative : Form :=
  { id := "afr_many_party_comparative", lexeme := afr_many_party, cell := comparative, form := "meer",
    analysed := "me-er", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_party_superlative : Form :=
  { id := "afr_many_party_superlative", lexeme := afr_many_party, cell := superlative, form := "meeste",
    analysed := "mee-ste", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_baie_positive : Form :=
  { id := "afr_many_baie_positive", lexeme := afr_many_baie, cell := positive, form := "baie",
    analysed := "baie", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_baie_comparative : Form :=
  { id := "afr_many_baie_comparative", lexeme := afr_many_baie, cell := comparative, form := "meer",
    analysed := "me-er", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_baie_superlative : Form :=
  { id := "afr_many_baie_superlative", lexeme := afr_many_baie, cell := superlative, form := "meeste",
    analysed := "mee-ste", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def yid_many_positive : Form :=
  { id := "yid_many_positive", lexeme := yid_many, cell := positive, form := "sakh",
    analysed := "sakh", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def yid_many_comparative : Form :=
  { id := "yid_many_comparative", lexeme := yid_many, cell := comparative, form := "mer",
    analysed := "me-r", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def yid_many_superlative : Form :=
  { id := "yid_many_superlative", lexeme := yid_many, cell := superlative, form := "merste",
    analysed := "me-r-ste", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def dan_many_positive : Form :=
  { id := "dan_many_positive", lexeme := dan_many, cell := positive, form := "mange",
    analysed := "mange", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def dan_many_comparative : Form :=
  { id := "dan_many_comparative", lexeme := dan_many, cell := comparative, form := "flere",
    analysed := "fle-re", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def dan_many_superlative : Form :=
  { id := "dan_many_superlative", lexeme := dan_many, cell := superlative, form := "flest",
    analysed := "fle-st", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ces_many_positive : Form :=
  { id := "ces_many_positive", lexeme := ces_many, cell := positive, form := "mnoho",
    analysed := "mnoho", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ces_many_comparative : Form :=
  { id := "ces_many_comparative", lexeme := ces_many, cell := comparative, form := "více",
    analysed := "víc-e", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ces_many_superlative : Form :=
  { id := "ces_many_superlative", lexeme := ces_many, cell := superlative, form := "nejvíce",
    analysed := "nej-víc-e", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def rus_many_positive : Form :=
  { id := "rus_many_positive", lexeme := rus_many, cell := positive, form := "mnogo",
    analysed := "mnogo", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def rus_many_comparative : Form :=
  { id := "rus_many_comparative", lexeme := rus_many, cell := comparative, form := "bol’še",
    analysed := "bol’š-e", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def rus_many_superlative : Form :=
  { id := "rus_many_superlative", lexeme := rus_many, cell := superlative, form := "najbo’lšij",
    analysed := "naj-bo’lš-ij", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bul_many_positive : Form :=
  { id := "bul_many_positive", lexeme := bul_many, cell := positive, form := "mnogo",
    analysed := "mnogo", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bul_many_comparative : Form :=
  { id := "bul_many_comparative", lexeme := bul_many, cell := comparative, form := "poveče",
    analysed := "po-več-e", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bul_many_superlative : Form :=
  { id := "bul_many_superlative", lexeme := bul_many, cell := superlative, form := "najmnogo",
    analysed := "naj-mnogo", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def pol_many_positive : Form :=
  { id := "pol_many_positive", lexeme := pol_many, cell := positive, form := "wiele",
    analysed := "wiele", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def pol_many_comparative : Form :=
  { id := "pol_many_comparative", lexeme := pol_many, cell := comparative, form := "więcej",
    analysed := "więc-ej", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def pol_many_superlative : Form :=
  { id := "pol_many_superlative", lexeme := pol_many, cell := superlative, form := "najwięcej",
    analysed := "naj-więc-ej", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hbs_many_positive : Form :=
  { id := "hbs_many_positive", lexeme := hbs_many, cell := positive, form := "puno",
    analysed := "puno", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hbs_many_comparative : Form :=
  { id := "hbs_many_comparative", lexeme := hbs_many, cell := comparative, form := "veće",
    analysed := "već-e", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hbs_many_superlative : Form :=
  { id := "hbs_many_superlative", lexeme := hbs_many, cell := superlative, form := "najveće",
    analysed := "naj-već-e", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_bahato_positive : Form :=
  { id := "ukr_many_bahato_positive", lexeme := ukr_many_bahato, cell := positive, form := "baháto",
    analysed := "baháto", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_bahato_comparative : Form :=
  { id := "ukr_many_bahato_comparative", lexeme := ukr_many_bahato, cell := comparative, form := "bil’šyj",
    analysed := "bil’-šyj", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_bahato_superlative : Form :=
  { id := "ukr_many_bahato_superlative", lexeme := ukr_many_bahato, cell := superlative, form := "najbil’šyj",
    analysed := "naj-bil’-šyj", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_duze_positive : Form :=
  { id := "ukr_many_duze_positive", lexeme := ukr_many_duze, cell := positive, form := "dúže",
    analysed := "dúže", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_duze_comparative : Form :=
  { id := "ukr_many_duze_comparative", lexeme := ukr_many_duze, cell := comparative, form := "bil’šyj",
    analysed := "bil’-šyj", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_duze_superlative : Form :=
  { id := "ukr_many_duze_superlative", lexeme := ukr_many_duze, cell := superlative, form := "najbil’šyj",
    analysed := "naj-bil’-šyj", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lav_many_positive : Form :=
  { id := "lav_many_positive", lexeme := lav_many, cell := positive, form := "daudz",
    analysed := "daudz", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lav_many_comparative : Form :=
  { id := "lav_many_comparative", lexeme := lav_many, cell := comparative, form := "vairâk",
    analysed := "vair-âk", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lav_many_superlative : Form :=
  { id := "lav_many_superlative", lexeme := lav_many, cell := superlative, form := "visvairâk",
    analysed := "vis-vair-âk", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_many_positive : Form :=
  { id := "lat_many_positive", lexeme := lat_many, cell := positive, form := "mult",
    analysed := "mult-", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_many_comparative : Form :=
  { id := "lat_many_comparative", lexeme := lat_many, cell := comparative, form := "plūs",
    analysed := "plū-s", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_many_superlative : Form :=
  { id := "lat_many_superlative", lexeme := lat_many, cell := superlative, form := "plūrimus",
    analysed := "plūr-imu-s", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bre_many_positive : Form :=
  { id := "bre_many_positive", lexeme := bre_many, cell := positive, form := "kalz",
    analysed := "kalz", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bre_many_comparative : Form :=
  { id := "bre_many_comparative", lexeme := bre_many, cell := comparative, form := "mui(oc’h)",
    analysed := "mui-(oc’h)", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bre_many_superlative : Form :=
  { id := "bre_many_superlative", lexeme := bre_many, cell := superlative, form := "muiañ",
    analysed := "mui-añ", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def cym_many_positive : Form :=
  { id := "cym_many_positive", lexeme := cym_many, cell := positive, form := "llawer",
    analysed := "llawer", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def cym_many_comparative : Form :=
  { id := "cym_many_comparative", lexeme := cym_many, cell := comparative, form := "mwy",
    analysed := "mwy", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def cym_many_superlative : Form :=
  { id := "cym_many_superlative", lexeme := cym_many, cell := superlative, form := "mwyaf",
    analysed := "mwy-af", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_many_positive : Form :=
  { id := "grc_many_positive", lexeme := grc_many, cell := positive, form := "polús",
    analysed := "pol-ús", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_many_comparative : Form :=
  { id := "grc_many_comparative", lexeme := grc_many, cell := comparative, form := "pleíōn",
    analysed := "ple-íōn", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_many_superlative : Form :=
  { id := "grc_many_superlative", lexeme := grc_many, cell := superlative, form := "pleĩstos",
    analysed := "ple-ĩst-os", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hye_many_positive : Form :=
  { id := "hye_many_positive", lexeme := hye_many, cell := positive, form := "šaterë",
    analysed := "šat-erë", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hye_many_comparative : Form :=
  { id := "hye_many_comparative", lexeme := hye_many, cell := comparative, form := "aveli",
    analysed := "aveli", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hye_many_superlative : Form :=
  { id := "hye_many_superlative", lexeme := hye_many, cell := superlative, form := "amenašat",
    analysed := "amena-šat", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_xele_positive : Form :=
  { id := "fas_many_xele_positive", lexeme := fas_many_xele, cell := positive, form := "xele",
    analysed := "xele", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_xele_comparative : Form :=
  { id := "fas_many_xele_comparative", lexeme := fas_many_xele, cell := comparative, form := "beš(tar)",
    analysed := "beš-(tar)", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_xele_superlative : Form :=
  { id := "fas_many_xele_superlative", lexeme := fas_many_xele, cell := superlative, form := "beštarin",
    analysed := "beš-tar-in", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_ziad_positive : Form :=
  { id := "fas_many_ziad_positive", lexeme := fas_many_ziad, cell := positive, form := "ziad",
    analysed := "ziad", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_ziad_comparative : Form :=
  { id := "fas_many_ziad_comparative", lexeme := fas_many_ziad, cell := comparative, form := "beš(tar)",
    analysed := "beš-(tar)", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_ziad_superlative : Form :=
  { id := "fas_many_ziad_superlative", lexeme := fas_many_ziad, cell := superlative, form := "beštarin",
    analysed := "beš-tar-in", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eus_many_positive : Form :=
  { id := "eus_many_positive", lexeme := eus_many, cell := positive, form := "asko",
    analysed := "asko", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eus_many_comparative : Form :=
  { id := "eus_many_comparative", lexeme := eus_many, cell := comparative, form := "gehiago",
    analysed := "gehi-ago", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eus_many_superlative : Form :=
  { id := "eus_many_superlative", lexeme := eus_many, cell := superlative, form := "gehien",
    analysed := "gehi-en", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_monet_positive : Form :=
  { id := "fin_many_monet_positive", lexeme := fin_many_monet, cell := positive, form := "monet",
    analysed := "monet", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_monet_comparative : Form :=
  { id := "fin_many_monet_comparative", lexeme := fin_many_monet, cell := comparative, form := "useammat",
    analysed := "usea-mmat", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_monet_superlative : Form :=
  { id := "fin_many_monet_superlative", lexeme := fin_many_monet, cell := superlative, form := "useimmat",
    analysed := "use-i-mmat", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_paljon_positive : Form :=
  { id := "fin_many_paljon_positive", lexeme := fin_many_paljon, cell := positive, form := "paljon",
    analysed := "paljon", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_paljon_comparative : Form :=
  { id := "fin_many_paljon_comparative", lexeme := fin_many_paljon, cell := comparative, form := "enemmän",
    analysed := "ene-mmän", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_paljon_superlative : Form :=
  { id := "fin_many_paljon_superlative", lexeme := fin_many_paljon, cell := superlative, form := "eniten",
    analysed := "en-iten", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def krl_many_positive : Form :=
  { id := "krl_many_positive", lexeme := krl_many, cell := positive, form := "äijä",
    analysed := "äijä", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def krl_many_comparative : Form :=
  { id := "krl_many_comparative", lexeme := krl_many, cell := comparative, form := "enämpi",
    analysed := "enä-mpi", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def krl_many_superlative : Form :=
  { id := "krl_many_superlative", lexeme := krl_many, cell := superlative, form := "äijin",
    analysed := "äij-in", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hun_many_positive : Form :=
  { id := "hun_many_positive", lexeme := hun_many, cell := positive, form := "sok",
    analysed := "sok", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hun_many_comparative : Form :=
  { id := "hun_many_comparative", lexeme := hun_many, cell := comparative, form := "több",
    analysed := "tö-bb", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hun_many_superlative : Form :=
  { id := "hun_many_superlative", lexeme := hun_many, cell := superlative, form := "legtöbb",
    analysed := "leg-tö-bb", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kat_many_positive : Form :=
  { id := "kat_many_positive", lexeme := kat_many, cell := positive, form := "bevri",
    analysed := "bevri", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kat_many_comparative : Form :=
  { id := "kat_many_comparative", lexeme := kat_many, cell := comparative, form := "met’i",
    analysed := "met’-i", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kat_many_superlative : Form :=
  { id := "kat_many_superlative", lexeme := kat_many, cell := superlative, form := "umet’esi",
    analysed := "u-met’-es-i", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kbd_many_positive : Form :=
  { id := "kbd_many_positive", lexeme := kbd_many, cell := positive, form := "kwad",
    analysed := "kwad", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kbd_many_positive_2 : Form :=
  { id := "kbd_many_positive_2", lexeme := kbd_many, cell := positive, form := "ba",
    analysed := "ba", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kbd_many_comparative : Form :=
  { id := "kbd_many_comparative", lexeme := kbd_many, cell := comparative, form := "nax",
    analysed := "nax", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kbd_many_superlative : Form :=
  { id := "kbd_many_superlative", lexeme := kbd_many, cell := superlative, form := "naxdeda",
    analysed := "nax-deda", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_few_positive : Form :=
  { id := "eng_few_positive", lexeme := eng_few, cell := positive, form := "(a) little",
    analysed := "(a) little", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_few_comparative : Form :=
  { id := "eng_few_comparative", lexeme := eng_few, cell := comparative, form := "less",
    analysed := "less", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_few_superlative : Form :=
  { id := "eng_few_superlative", lexeme := eng_few, cell := superlative, form := "least",
    analysed := "leas-t", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_few_positive : Form :=
  { id := "afr_few_positive", lexeme := afr_few, cell := positive, form := "weinig",
    analysed := "weinig", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_few_comparative : Form :=
  { id := "afr_few_comparative", lexeme := afr_few, cell := comparative, form := "minder",
    analysed := "mind-er", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_few_superlative : Form :=
  { id := "afr_few_superlative", lexeme := afr_few, cell := superlative, form := "mindste",
    analysed := "mind-ste", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fry_few_positive : Form :=
  { id := "fry_few_positive", lexeme := fry_few, cell := positive, form := "(en) bytsje",
    analysed := "(en) bytsje", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fry_few_comparative : Form :=
  { id := "fry_few_comparative", lexeme := fry_few, cell := comparative, form := "minder",
    analysed := "mind-er", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fry_few_superlative : Form :=
  { id := "fry_few_superlative", lexeme := fry_few, cell := superlative, form := "minst",
    analysed := "minst", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_few_positive : Form :=
  { id := "ukr_few_positive", lexeme := ukr_few, cell := positive, form := "troxi",
    analysed := "troxi", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_few_comparative : Form :=
  { id := "ukr_few_comparative", lexeme := ukr_few, cell := comparative, form := "menše",
    analysed := "men-še", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_few_superlative : Form :=
  { id := "ukr_few_superlative", lexeme := ukr_few, cell := superlative, form := "najmenšij",
    analysed := "naj-men-šij", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_few_positive : Form :=
  { id := "lat_few_positive", lexeme := lat_few, cell := positive, form := "paucus",
    analysed := "paucus", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_few_comparative : Form :=
  { id := "lat_few_comparative", lexeme := lat_few, cell := comparative, form := "minor",
    analysed := "min-or", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_few_superlative : Form :=
  { id := "lat_few_superlative", lexeme := lat_few, cell := superlative, form := "minimus",
    analysed := "min-imus", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_positive : Form :=
  { id := "grc_few_positive", lexeme := grc_few, cell := positive, form := "olígos",
    analysed := "olíg-os", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_comparative : Form :=
  { id := "grc_few_comparative", lexeme := grc_few, cell := comparative, form := "héssōn",
    analysed := "héss-ōn", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_superlative : Form :=
  { id := "grc_few_superlative", lexeme := grc_few, cell := superlative, form := "hékistos",
    analysed := "hék-ist-os", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_comparative_2 : Form :=
  { id := "grc_few_comparative_2", lexeme := grc_few, cell := comparative, form := "meíōn",
    analysed := "meí-ōn", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_superlative_2 : Form :=
  { id := "grc_few_superlative_2", lexeme := grc_few, cell := superlative, form := "meĩstos",
    analysed := "meĩ-st-os", source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def krl_many_onego_positive : Form :=
  { id := "krl_many_onego_positive", lexeme := krl_many_onego, cell := positive, form := "äijy",
    analysed := "äijy", source := [
      ⟨"bobaljik-2012", "(170)"⟩
    ] }

def krl_many_onego_comparative : Form :=
  { id := "krl_many_onego_comparative", lexeme := krl_many_onego, cell := comparative, form := "enämbi",
    analysed := "enä-mbi", source := [
      ⟨"bobaljik-2012", "(170)"⟩
    ] }

def krl_many_onego_superlative : Form :=
  { id := "krl_many_onego_superlative", lexeme := krl_many_onego, cell := superlative, form := "enin",
    analysed := "en-in", source := [
      ⟨"bobaljik-2012", "(170)"⟩
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

def eng_many.roots : RootClasses :=
  { id := "eng_many", lexeme := eng_many, forms := [eng_many_positive, eng_many_comparative, eng_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def eng_much.roots : RootClasses :=
  { id := "eng_much", lexeme := eng_much, forms := [eng_much_positive, eng_much_comparative, eng_much_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def eng_lot.roots : RootClasses :=
  { id := "eng_lot", lexeme := eng_lot, forms := [eng_lot_positive, eng_lot_comparative, eng_lot_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def deu_many.roots : RootClasses :=
  { id := "deu_many", lexeme := deu_many, forms := [deu_many_positive, deu_many_comparative, deu_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fao_many.roots : RootClasses :=
  { id := "fao_many", lexeme := fao_many, forms := [fao_many_positive, fao_many_comparative, fao_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def afr_many_party.roots : RootClasses :=
  { id := "afr_many_party", lexeme := afr_many_party, forms := [afr_many_party_positive, afr_many_party_comparative, afr_many_party_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def afr_many_baie.roots : RootClasses :=
  { id := "afr_many_baie", lexeme := afr_many_baie, forms := [afr_many_baie_positive, afr_many_baie_comparative, afr_many_baie_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def yid_many.roots : RootClasses :=
  { id := "yid_many", lexeme := yid_many, forms := [yid_many_positive, yid_many_comparative, yid_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def dan_many.roots : RootClasses :=
  { id := "dan_many", lexeme := dan_many, forms := [dan_many_positive, dan_many_comparative, dan_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def ces_many.roots : RootClasses :=
  { id := "ces_many", lexeme := ces_many, forms := [ces_many_positive, ces_many_comparative, ces_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def rus_many.roots : RootClasses :=
  { id := "rus_many", lexeme := rus_many, forms := [rus_many_positive, rus_many_comparative, rus_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def bul_many.roots : RootClasses :=
  { id := "bul_many", lexeme := bul_many, forms := [bul_many_positive, bul_many_comparative, bul_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 0)],
    source := [
      ⟨"bobaljik-2012", "(165c)"⟩
    ] }

def pol_many.roots : RootClasses :=
  { id := "pol_many", lexeme := pol_many, forms := [pol_many_positive, pol_many_comparative, pol_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def hbs_many.roots : RootClasses :=
  { id := "hbs_many", lexeme := hbs_many, forms := [hbs_many_positive, hbs_many_comparative, hbs_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def ukr_many_bahato.roots : RootClasses :=
  { id := "ukr_many_bahato", lexeme := ukr_many_bahato, forms := [ukr_many_bahato_positive, ukr_many_bahato_comparative, ukr_many_bahato_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def ukr_many_duze.roots : RootClasses :=
  { id := "ukr_many_duze", lexeme := ukr_many_duze, forms := [ukr_many_duze_positive, ukr_many_duze_comparative, ukr_many_duze_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def lav_many.roots : RootClasses :=
  { id := "lav_many", lexeme := lav_many, forms := [lav_many_positive, lav_many_comparative, lav_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def lat_many.roots : RootClasses :=
  { id := "lat_many", lexeme := lat_many, forms := [lat_many_positive, lat_many_comparative, lat_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def bre_many.roots : RootClasses :=
  { id := "bre_many", lexeme := bre_many, forms := [bre_many_positive, bre_many_comparative, bre_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def cym_many.roots : RootClasses :=
  { id := "cym_many", lexeme := cym_many, forms := [cym_many_positive, cym_many_comparative, cym_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def grc_many.roots : RootClasses :=
  { id := "grc_many", lexeme := grc_many, forms := [grc_many_positive, grc_many_comparative, grc_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def hye_many.roots : RootClasses :=
  { id := "hye_many", lexeme := hye_many, forms := [hye_many_positive, hye_many_comparative, hye_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 0)],
    source := [
      ⟨"bobaljik-2012", "(165b)"⟩
    ] }

def fas_many_xele.roots : RootClasses :=
  { id := "fas_many_xele", lexeme := fas_many_xele, forms := [fas_many_xele_positive, fas_many_xele_comparative, fas_many_xele_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fas_many_ziad.roots : RootClasses :=
  { id := "fas_many_ziad", lexeme := fas_many_ziad, forms := [fas_many_ziad_positive, fas_many_ziad_comparative, fas_many_ziad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def eus_many.roots : RootClasses :=
  { id := "eus_many", lexeme := eus_many, forms := [eus_many_positive, eus_many_comparative, eus_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fin_many_monet.roots : RootClasses :=
  { id := "fin_many_monet", lexeme := fin_many_monet, forms := [fin_many_monet_positive, fin_many_monet_comparative, fin_many_monet_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fin_many_paljon.roots : RootClasses :=
  { id := "fin_many_paljon", lexeme := fin_many_paljon, forms := [fin_many_paljon_positive, fin_many_paljon_comparative, fin_many_paljon_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def krl_many.roots : RootClasses :=
  { id := "krl_many", lexeme := krl_many, forms := [krl_many_positive, krl_many_comparative, krl_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 0)],
    source := [
      ⟨"bobaljik-2012", "(165a)"⟩
    ] }

def hun_many.roots : RootClasses :=
  { id := "hun_many", lexeme := hun_many, forms := [hun_many_positive, hun_many_comparative, hun_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def kat_many.roots : RootClasses :=
  { id := "kat_many", lexeme := kat_many, forms := [kat_many_positive, kat_many_comparative, kat_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def kbd_many.roots : RootClasses :=
  { id := "kbd_many", lexeme := kbd_many, forms := [kbd_many_positive, kbd_many_positive_2, kbd_many_comparative, kbd_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def eng_few.roots : RootClasses :=
  { id := "eng_few", lexeme := eng_few, forms := [eng_few_positive, eng_few_comparative, eng_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def afr_few.roots : RootClasses :=
  { id := "afr_few", lexeme := afr_few, forms := [afr_few_positive, afr_few_comparative, afr_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fry_few.roots : RootClasses :=
  { id := "fry_few", lexeme := fry_few, forms := [fry_few_positive, fry_few_comparative, fry_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def ukr_few.roots : RootClasses :=
  { id := "ukr_few", lexeme := ukr_few, forms := [ukr_few_positive, ukr_few_comparative, ukr_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def lat_few.roots : RootClasses :=
  { id := "lat_few", lexeme := lat_few, forms := [lat_few_positive, lat_few_comparative, lat_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def grc_few_hess.roots : RootClasses :=
  { id := "grc_few_hess", lexeme := grc_few, forms := [grc_few_positive, grc_few_comparative, grc_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def grc_few_mei.roots : RootClasses :=
  { id := "grc_few_mei", lexeme := grc_few, forms := [grc_few_positive, grc_few_comparative_2, grc_few_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def krl_many_onego.roots : RootClasses :=
  { id := "krl_many_onego", lexeme := krl_many_onego, forms := [krl_many_onego_positive, krl_many_onego_comparative, krl_many_onego_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "(170)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [eng_good, swe_good, got_good, cim_good, ces_good, hbs_good, sorb_good, ukr_good_dobr, ukr_good_harn, rus_good, lat_good, cym_good, sga_good, bre_good, grc_good, san_good, kho_good, pal_good, fas_good, eus_good, fin_good, sjd_good, kat_good, sva_good, chr_good, eng_bad, goh_bad, non_bad_vandr, non_bad_illr, dan_bad, fao_bad, swe_bad, yid_bad, pol_bad, ces_bad, ukr_bad, bel_bad_drenn, bel_bad_blah, hbs_bad, rus_bad, lat_bad, sga_bad, cym_bad, bre_bad, grc_bad, got_big, ces_big, ukr_big, pol_big, cym_big, pal_big, sva_big, got_small, ang_small, dan_small, hbs_small, lat_small, cym_small, grc_small, pal_small, non_old, cym_near, cym_strong, eng_many, eng_much, eng_lot, deu_many, fao_many, afr_many_party, afr_many_baie, yid_many, dan_many, ces_many, rus_many, bul_many, pol_many, hbs_many, ukr_many_bahato, ukr_many_duze, lav_many, lat_many, bre_many, cym_many, grc_many, hye_many, fas_many_xele, fas_many_ziad, eus_many, fin_many_monet, fin_many_paljon, krl_many, hun_many, kat_many, kbd_many, eng_few, afr_few, fry_few, ukr_few, lat_few, grc_few, krl_many_onego]

/-- Every form of the data. -/
def forms : List Form := [eng_good_positive, eng_good_comparative, eng_good_superlative, swe_good_positive, swe_good_comparative, swe_good_superlative, got_good_positive, got_good_comparative, got_good_superlative, cim_good_positive, cim_good_comparative, cim_good_superlative, ces_good_positive, ces_good_comparative, ces_good_superlative, hbs_good_positive, hbs_good_comparative, hbs_good_superlative, sorb_good_positive, sorb_good_comparative, ukr_good_dobr_positive, ukr_good_dobr_comparative, ukr_good_dobr_superlative, ukr_good_harn_positive, ukr_good_harn_comparative, ukr_good_harn_superlative, rus_good_positive, rus_good_comparative, rus_good_superlative, lat_good_positive, lat_good_comparative, lat_good_superlative, cym_good_positive, cym_good_comparative, cym_good_superlative, sga_good_positive, sga_good_comparative, sga_good_superlative, bre_good_positive, bre_good_comparative, bre_good_superlative, grc_good_positive, grc_good_comparative, grc_good_superlative, grc_good_comparative_2, grc_good_superlative_2, grc_good_comparative_3, grc_good_superlative_3, grc_good_comparative_4, grc_good_superlative_4, grc_good_comparative_5, grc_good_superlative_5, san_good_positive, san_good_comparative, san_good_superlative, san_good_comparative_2, san_good_superlative_2, kho_good_positive, kho_good_comparative, kho_good_superlative, pal_good_positive, pal_good_comparative, pal_good_superlative, pal_good_superlative_2, fas_good_positive, fas_good_comparative, fas_good_superlative, eus_good_positive, eus_good_comparative, eus_good_superlative, eus_good_superlative_2, fin_good_positive, fin_good_comparative, fin_good_superlative, sjd_good_positive, sjd_good_comparative, sjd_good_superlative, kat_good_positive, kat_good_comparative, kat_good_superlative, kat_good_comparative_2, kat_good_superlative_2, sva_good_positive, sva_good_comparative, sva_good_comparative_2, sva_good_superlative, chr_good_positive, chr_good_comparative, chr_good_superlative, eng_bad_positive, eng_bad_comparative, eng_bad_superlative, goh_bad_positive, goh_bad_comparative, goh_bad_superlative, non_bad_vandr_positive, non_bad_vandr_comparative, non_bad_vandr_superlative, non_bad_illr_positive, non_bad_illr_comparative, non_bad_illr_superlative, dan_bad_positive, dan_bad_comparative, dan_bad_superlative, fao_bad_positive, fao_bad_comparative, fao_bad_superlative, swe_bad_positive, swe_bad_comparative, swe_bad_superlative, swe_bad_comparative_2, swe_bad_superlative_2, yid_bad_positive, yid_bad_comparative, yid_bad_superlative, pol_bad_positive, pol_bad_comparative, pol_bad_superlative, ces_bad_positive, ces_bad_comparative, ces_bad_superlative, ukr_bad_positive, ukr_bad_comparative, ukr_bad_superlative, bel_bad_drenn_positive, bel_bad_drenn_comparative, bel_bad_drenn_superlative, bel_bad_blah_positive, bel_bad_blah_comparative, bel_bad_blah_superlative, hbs_bad_positive, hbs_bad_comparative, hbs_bad_superlative, rus_bad_positive, rus_bad_comparative, rus_bad_superlative, lat_bad_positive, lat_bad_comparative, lat_bad_superlative, sga_bad_positive, sga_bad_comparative, sga_bad_superlative, cym_bad_positive, cym_bad_comparative, cym_bad_superlative, bre_bad_positive, bre_bad_comparative, bre_bad_superlative, grc_bad_positive, grc_bad_comparative, grc_bad_superlative, grc_bad_comparative_2, grc_bad_superlative_2, got_big_positive, got_big_comparative, got_big_superlative, ces_big_positive, ces_big_comparative, ces_big_superlative, ukr_big_positive, ukr_big_comparative, ukr_big_superlative, pol_big_positive, pol_big_comparative, pol_big_superlative, cym_big_positive, cym_big_comparative, cym_big_superlative, pal_big_positive, pal_big_comparative, pal_big_superlative, sva_big_positive, sva_big_comparative, sva_big_comparative_2, sva_big_superlative, got_small_positive, got_small_comparative, got_small_superlative, ang_small_positive, ang_small_comparative, ang_small_superlative, dan_small_positive, dan_small_comparative, dan_small_superlative, hbs_small_positive, hbs_small_positive_2, hbs_small_comparative, hbs_small_superlative, lat_small_positive, lat_small_positive_2, lat_small_comparative, lat_small_superlative, cym_small_positive, cym_small_comparative, cym_small_superlative, grc_small_positive, grc_small_comparative, grc_small_superlative, grc_small_comparative_2, grc_small_superlative_2, pal_small_positive, pal_small_comparative, pal_small_superlative, non_old_positive, non_old_comparative, non_old_superlative, cym_near_positive, cym_near_comparative, cym_near_superlative, cym_strong_positive, cym_strong_comparative, cym_strong_superlative, eng_many_positive, eng_many_comparative, eng_many_superlative, eng_much_positive, eng_much_comparative, eng_much_superlative, eng_lot_positive, eng_lot_comparative, eng_lot_superlative, deu_many_positive, deu_many_comparative, deu_many_superlative, fao_many_positive, fao_many_comparative, fao_many_superlative, afr_many_party_positive, afr_many_party_comparative, afr_many_party_superlative, afr_many_baie_positive, afr_many_baie_comparative, afr_many_baie_superlative, yid_many_positive, yid_many_comparative, yid_many_superlative, dan_many_positive, dan_many_comparative, dan_many_superlative, ces_many_positive, ces_many_comparative, ces_many_superlative, rus_many_positive, rus_many_comparative, rus_many_superlative, bul_many_positive, bul_many_comparative, bul_many_superlative, pol_many_positive, pol_many_comparative, pol_many_superlative, hbs_many_positive, hbs_many_comparative, hbs_many_superlative, ukr_many_bahato_positive, ukr_many_bahato_comparative, ukr_many_bahato_superlative, ukr_many_duze_positive, ukr_many_duze_comparative, ukr_many_duze_superlative, lav_many_positive, lav_many_comparative, lav_many_superlative, lat_many_positive, lat_many_comparative, lat_many_superlative, bre_many_positive, bre_many_comparative, bre_many_superlative, cym_many_positive, cym_many_comparative, cym_many_superlative, grc_many_positive, grc_many_comparative, grc_many_superlative, hye_many_positive, hye_many_comparative, hye_many_superlative, fas_many_xele_positive, fas_many_xele_comparative, fas_many_xele_superlative, fas_many_ziad_positive, fas_many_ziad_comparative, fas_many_ziad_superlative, eus_many_positive, eus_many_comparative, eus_many_superlative, fin_many_monet_positive, fin_many_monet_comparative, fin_many_monet_superlative, fin_many_paljon_positive, fin_many_paljon_comparative, fin_many_paljon_superlative, krl_many_positive, krl_many_comparative, krl_many_superlative, hun_many_positive, hun_many_comparative, hun_many_superlative, kat_many_positive, kat_many_comparative, kat_many_superlative, kbd_many_positive, kbd_many_positive_2, kbd_many_comparative, kbd_many_superlative, eng_few_positive, eng_few_comparative, eng_few_superlative, afr_few_positive, afr_few_comparative, afr_few_superlative, fry_few_positive, fry_few_comparative, fry_few_superlative, ukr_few_positive, ukr_few_comparative, ukr_few_superlative, lat_few_positive, lat_few_comparative, lat_few_superlative, grc_few_positive, grc_few_comparative, grc_few_superlative, grc_few_comparative_2, grc_few_superlative_2, krl_many_onego_positive, krl_many_onego_comparative, krl_many_onego_superlative]

/-- Every root-class judgment of the data. -/
def rootClasses : List RootClasses := [eng_good.roots, swe_good.roots, got_good.roots, cim_good.roots, ces_good.roots, hbs_good.roots, sorb_good.roots, ukr_good_dobr.roots, ukr_good_harn.roots, rus_good.roots, lat_good.roots, cym_good.roots, sga_good.roots, bre_good.roots, grc_good_amein.roots, grc_good_arei.roots, grc_good_belt.roots, grc_good_kreiss.roots, grc_good_lo.roots, san_good_sre.roots, san_good_jya.roots, kho_good.roots, pal_good.roots, fas_good.roots, eus_good_hobe.roots, eus_good_on.roots, fin_good.roots, sjd_good.roots, kat_good_mjob.roots, kat_good_ket.roots, sva_good.roots, chr_good.roots, eng_bad.roots, goh_bad.roots, non_bad_vandr.roots, non_bad_illr.roots, dan_bad.roots, fao_bad.roots, swe_bad_var.roots, swe_bad_sam.roots, yid_bad.roots, pol_bad.roots, ces_bad.roots, ukr_bad.roots, bel_bad_drenn.roots, bel_bad_blah.roots, hbs_bad.roots, rus_bad.roots, lat_bad.roots, sga_bad.roots, cym_bad.roots, bre_bad.roots, grc_bad_cheir.roots, grc_bad_hess.roots, got_big.roots, ces_big.roots, ukr_big.roots, pol_big.roots, cym_big.roots, pal_big.roots, sva_big.roots, got_small.roots, ang_small.roots, dan_small.roots, hbs_small.roots, lat_small.roots, cym_small.roots, grc_small_mei.roots, grc_small_elass.roots, pal_small.roots, non_old.roots, cym_near.roots, cym_strong.roots, eng_many.roots, eng_much.roots, eng_lot.roots, deu_many.roots, fao_many.roots, afr_many_party.roots, afr_many_baie.roots, yid_many.roots, dan_many.roots, ces_many.roots, rus_many.roots, bul_many.roots, pol_many.roots, hbs_many.roots, ukr_many_bahato.roots, ukr_many_duze.roots, lav_many.roots, lat_many.roots, bre_many.roots, cym_many.roots, grc_many.roots, hye_many.roots, fas_many_xele.roots, fas_many_ziad.roots, eus_many.roots, fin_many_monet.roots, fin_many_paljon.roots, krl_many.roots, hun_many.roots, kat_many.roots, kbd_many.roots, eng_few.roots, afr_few.roots, fry_few.roots, ukr_few.roots, lat_few.roots, grc_few_hess.roots, grc_few_mei.roots, krl_many_onego.roots]

end Bobaljik2012.Paradigms
