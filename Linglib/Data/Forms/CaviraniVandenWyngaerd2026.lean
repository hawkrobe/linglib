module

public import Linglib.Data.Forms.Schema

/-!
# `CaviraniVandenWyngaerd2026` — CLDF form data

Auto-generated from `Linglib/Data/Forms/CaviraniVandenWyngaerd2026.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace CaviraniVandenWyngaerd2026.Forms`.
-/

@[expose] public section

namespace CaviraniVandenWyngaerd2026.Forms

open Data.Forms

def louka : Form :=
  { id := "caviranivandenwyngaerd2026_louka"
    languageId := "czec1258"
    parameterId := "meadow"
    form := "louka"
    segments := ["lou", "k", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def louce : Form :=
  { id := "caviranivandenwyngaerd2026_louce"
    languageId := "czec1258"
    parameterId := "meadow_locdat"
    form := "louce"
    segments := ["lou", "c", "e"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "k")] }

def liga : Form :=
  { id := "caviranivandenwyngaerd2026_liga"
    languageId := "czec1258"
    parameterId := "league"
    form := "liga"
    segments := ["li", "g", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def lize : Form :=
  { id := "caviranivandenwyngaerd2026_lize"
    languageId := "czec1258"
    parameterId := "league_locdat"
    form := "lize"
    segments := ["li", "z", "e"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "g")] }

def strecha : Form :=
  { id := "caviranivandenwyngaerd2026_strecha"
    languageId := "czec1258"
    parameterId := "roof"
    form := "střecha"
    segments := ["stře", "ch", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def strese : Form :=
  { id := "caviranivandenwyngaerd2026_strese"
    languageId := "czec1258"
    parameterId := "roof_locdat"
    form := "střeše"
    segments := ["stře", "š", "e"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "x")] }

def kniha : Form :=
  { id := "caviranivandenwyngaerd2026_kniha"
    languageId := "czec1258"
    parameterId := "book"
    form := "kniha"
    segments := ["kni", "h", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def knize : Form :=
  { id := "caviranivandenwyngaerd2026_knize"
    languageId := "czec1258"
    parameterId := "book_locdat"
    form := "knize"
    segments := ["kni", "z", "e"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "ɦ")] }

def mata : Form :=
  { id := "caviranivandenwyngaerd2026_mata"
    languageId := "czec1258"
    parameterId := "mint"
    form := "máta"
    segments := ["má", "t", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def mate : Form :=
  { id := "caviranivandenwyngaerd2026_mate"
    languageId := "czec1258"
    parameterId := "mint_locdat"
    form := "mátě"
    segments := ["má", "t", "ě"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "t")] }

def vlada : Form :=
  { id := "caviranivandenwyngaerd2026_vlada"
    languageId := "czec1258"
    parameterId := "government"
    form := "vláda"
    segments := ["vlá", "d", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def vlade : Form :=
  { id := "caviranivandenwyngaerd2026_vlade"
    languageId := "czec1258"
    parameterId := "government_locdat"
    form := "vládě"
    segments := ["vlá", "d", "ě"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "d")] }

def bystrica : Form :=
  { id := "caviranivandenwyngaerd2026_bystrica"
    languageId := "czec1258"
    parameterId := "bystrica"
    form := "Bystrica"
    segments := ["Bystri", "c", "a"]
    comment := "parenthesised in the table"
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def bystrice : Form :=
  { id := "caviranivandenwyngaerd2026_bystrice"
    languageId := "czec1258"
    parameterId := "bystrica_locdat"
    form := "Bystrice"
    segments := ["Bystri", "c", "e"]
    comment := "parenthesised in the table"
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "ʦ")] }

def misa : Form :=
  { id := "caviranivandenwyngaerd2026_misa"
    languageId := "czec1258"
    parameterId := "bowl"
    form := "mísa"
    segments := ["mí", "s", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def mise : Form :=
  { id := "caviranivandenwyngaerd2026_mise"
    languageId := "czec1258"
    parameterId := "bowl_locdat"
    form := "míse"
    segments := ["mí", "s", "e"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "s")] }

def koza : Form :=
  { id := "caviranivandenwyngaerd2026_koza"
    languageId := "czec1258"
    parameterId := "goat"
    form := "koza"
    segments := ["ko", "z", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def koze : Form :=
  { id := "caviranivandenwyngaerd2026_koze"
    languageId := "czec1258"
    parameterId := "goat_locdat"
    form := "koze"
    segments := ["ko", "z", "e"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "z")] }

def vina : Form :=
  { id := "caviranivandenwyngaerd2026_vina"
    languageId := "czec1258"
    parameterId := "guilt"
    form := "vina"
    segments := ["vi", "n", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def vine : Form :=
  { id := "caviranivandenwyngaerd2026_vine"
    languageId := "czec1258"
    parameterId := "guilt_locdat"
    form := "vině"
    segments := ["vi", "n", "ě"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "n")] }

def sestra : Form :=
  { id := "caviranivandenwyngaerd2026_sestra"
    languageId := "czec1258"
    parameterId := "sister"
    form := "sestra"
    segments := ["sest", "r", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def sestre : Form :=
  { id := "caviranivandenwyngaerd2026_sestre"
    languageId := "czec1258"
    parameterId := "sister_locdat"
    form := "sestře"
    segments := ["sest", "ř", "e"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "r")] }

def vila : Form :=
  { id := "caviranivandenwyngaerd2026_vila"
    languageId := "czec1258"
    parameterId := "fairy"
    form := "víla"
    segments := ["ví", "l", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def vile : Form :=
  { id := "caviranivandenwyngaerd2026_vile"
    languageId := "czec1258"
    parameterId := "fairy_locdat"
    form := "víle"
    segments := ["ví", "l", "e"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "l")] }

def stoupa : Form :=
  { id := "caviranivandenwyngaerd2026_stoupa"
    languageId := "czec1258"
    parameterId := "rise"
    form := "stoupa"
    segments := ["stou", "p", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def stoupe : Form :=
  { id := "caviranivandenwyngaerd2026_stoupe"
    languageId := "czec1258"
    parameterId := "rise_locdat"
    form := "stoupě"
    segments := ["stou", "p", "ě"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "p")] }

def ryba : Form :=
  { id := "caviranivandenwyngaerd2026_ryba"
    languageId := "czec1258"
    parameterId := "fish"
    form := "ryba"
    segments := ["ry", "b", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def rybe : Form :=
  { id := "caviranivandenwyngaerd2026_rybe"
    languageId := "czec1258"
    parameterId := "fish_locdat"
    form := "rybě"
    segments := ["ry", "b", "ě"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "b")] }

def karafa : Form :=
  { id := "caviranivandenwyngaerd2026_karafa"
    languageId := "czec1258"
    parameterId := "decanter"
    form := "karafa"
    segments := ["kara", "f", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def karafe : Form :=
  { id := "caviranivandenwyngaerd2026_karafe"
    languageId := "czec1258"
    parameterId := "decanter_locdat"
    form := "karafě"
    segments := ["kara", "f", "ě"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "f")] }

def hlava : Form :=
  { id := "caviranivandenwyngaerd2026_hlava"
    languageId := "czec1258"
    parameterId := "head"
    form := "hlava"
    segments := ["hla", "v", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def hlave : Form :=
  { id := "caviranivandenwyngaerd2026_hlave"
    languageId := "czec1258"
    parameterId := "head_locdat"
    form := "hlavě"
    segments := ["hla", "v", "ě"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "v")] }

def zima : Form :=
  { id := "caviranivandenwyngaerd2026_zima"
    languageId := "czec1258"
    parameterId := "winter"
    form := "zima"
    segments := ["zi", "m", "a"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zime : Form :=
  { id := "caviranivandenwyngaerd2026_zime"
    languageId := "czec1258"
    parameterId := "winter_locdat"
    form := "zimě"
    segments := ["zi", "m", "ě"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "m")] }

def zatknout : Form :=
  { id := "caviranivandenwyngaerd2026_zatknout"
    languageId := "czec1258"
    parameterId := "arrested_base"
    form := "zatknout"
    segments := ["zat", "k", "nout"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zatcen : Form :=
  { id := "caviranivandenwyngaerd2026_zatcen"
    languageId := "czec1258"
    parameterId := "arrested"
    form := "zatčen"
    segments := ["zat", "č", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "k")] }

def olga : Form :=
  { id := "caviranivandenwyngaerd2026_olga"
    languageId := "czec1258"
    parameterId := "olga"
    form := "Olga"
    segments := ["Ol", "g", "a"]
    comment := "parenthesised in the table"
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def olzin : Form :=
  { id := "caviranivandenwyngaerd2026_olzin"
    languageId := "czec1258"
    parameterId := "olga_poss"
    form := "Olžin"
    segments := ["Ol", "ž", "in"]
    comment := "parenthesised in the table"
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "g")] }

def nadchnout : Form :=
  { id := "caviranivandenwyngaerd2026_nadchnout"
    languageId := "czec1258"
    parameterId := "excited_base"
    form := "nadchnout"
    segments := ["nad", "ch", "nout"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def nadsen : Form :=
  { id := "caviranivandenwyngaerd2026_nadsen"
    languageId := "czec1258"
    parameterId := "excited"
    form := "nadšen"
    segments := ["nad", "š", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "x")] }

def tahnout : Form :=
  { id := "caviranivandenwyngaerd2026_tahnout"
    languageId := "czec1258"
    parameterId := "pulled_base"
    form := "táhnout"
    segments := ["tá", "h", "nout"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def tazen : Form :=
  { id := "caviranivandenwyngaerd2026_tazen"
    languageId := "czec1258"
    parameterId := "pulled"
    form := "tažen"
    segments := ["ta", "ž", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "ɦ")] }

def nutit : Form :=
  { id := "caviranivandenwyngaerd2026_nutit"
    languageId := "czec1258"
    parameterId := "forced_base"
    form := "nutit"
    segments := ["nu", "t", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def nucen : Form :=
  { id := "caviranivandenwyngaerd2026_nucen"
    languageId := "czec1258"
    parameterId := "forced"
    form := "nucen"
    segments := ["nu", "c", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "t")] }

def uklidit : Form :=
  { id := "caviranivandenwyngaerd2026_uklidit"
    languageId := "czec1258"
    parameterId := "cleaned_up_base"
    form := "uklidit"
    segments := ["ukli", "d", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def uklizen : Form :=
  { id := "caviranivandenwyngaerd2026_uklizen"
    languageId := "czec1258"
    parameterId := "cleaned_up"
    form := "uklizen"
    segments := ["ukli", "z", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "d")] }

def peci : Form :=
  { id := "caviranivandenwyngaerd2026_peci"
    languageId := "czec1258"
    parameterId := "baked_base"
    form := "péci"
    segments := ["pé", "c", "i"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def pecen : Form :=
  { id := "caviranivandenwyngaerd2026_pecen"
    languageId := "czec1258"
    parameterId := "baked"
    form := "pečen"
    segments := ["pe", "č", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "ʦ")] }

def hlasit : Form :=
  { id := "caviranivandenwyngaerd2026_hlasit"
    languageId := "czec1258"
    parameterId := "reported_base"
    form := "hlásit"
    segments := ["hlá", "s", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def hlasen : Form :=
  { id := "caviranivandenwyngaerd2026_hlasen"
    languageId := "czec1258"
    parameterId := "reported"
    form := "hlášen"
    segments := ["hlá", "š", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "s")] }

def ohrozit : Form :=
  { id := "caviranivandenwyngaerd2026_ohrozit"
    languageId := "czec1258"
    parameterId := "endangered_base"
    form := "ohrozit"
    segments := ["ohro", "z", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def ohrozen : Form :=
  { id := "caviranivandenwyngaerd2026_ohrozen"
    languageId := "czec1258"
    parameterId := "endangered"
    form := "ohrožen"
    segments := ["ohro", "ž", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "z")] }

def ranit : Form :=
  { id := "caviranivandenwyngaerd2026_ranit"
    languageId := "czec1258"
    parameterId := "wounded_base"
    form := "ranit"
    segments := ["ra", "n", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def ranen : Form :=
  { id := "caviranivandenwyngaerd2026_ranen"
    languageId := "czec1258"
    parameterId := "wounded"
    form := "raněn"
    segments := ["ra", "n", "ěn"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "n")] }

def vera : Form :=
  { id := "caviranivandenwyngaerd2026_vera"
    languageId := "czec1258"
    parameterId := "vera"
    form := "Věra"
    segments := ["Vě", "r", "a"]
    comment := "parenthesised in the table"
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def verin : Form :=
  { id := "caviranivandenwyngaerd2026_verin"
    languageId := "czec1258"
    parameterId := "vera_poss"
    form := "Věřin"
    segments := ["Vě", "ř", "in"]
    comment := "parenthesised in the table"
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "r")] }

def zvolit : Form :=
  { id := "caviranivandenwyngaerd2026_zvolit"
    languageId := "czec1258"
    parameterId := "elected_base"
    form := "zvolit"
    segments := ["zvo", "l", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zvolen : Form :=
  { id := "caviranivandenwyngaerd2026_zvolen"
    languageId := "czec1258"
    parameterId := "elected"
    form := "zvolen"
    segments := ["zvo", "l", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "l")] }

def zatopit : Form :=
  { id := "caviranivandenwyngaerd2026_zatopit"
    languageId := "czec1258"
    parameterId := "flooded_base"
    form := "zatopit"
    segments := ["zato", "p", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zatopen : Form :=
  { id := "caviranivandenwyngaerd2026_zatopen"
    languageId := "czec1258"
    parameterId := "flooded"
    form := "zatopen"
    segments := ["zato", "p", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "p")] }

def rozzlobit : Form :=
  { id := "caviranivandenwyngaerd2026_rozzlobit"
    languageId := "czec1258"
    parameterId := "angered_base"
    form := "rozzlobit"
    segments := ["rozzlo", "b", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def rozzloben : Form :=
  { id := "caviranivandenwyngaerd2026_rozzloben"
    languageId := "czec1258"
    parameterId := "angered"
    form := "rozzloben"
    segments := ["rozzlo", "b", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "b")] }

def trefit : Form :=
  { id := "caviranivandenwyngaerd2026_trefit"
    languageId := "czec1258"
    parameterId := "hit_base"
    form := "trefit"
    segments := ["tre", "f", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def trefen : Form :=
  { id := "caviranivandenwyngaerd2026_trefen"
    languageId := "czec1258"
    parameterId := "hit"
    form := "trefen"
    segments := ["tre", "f", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "f")] }

def obarvit : Form :=
  { id := "caviranivandenwyngaerd2026_obarvit"
    languageId := "czec1258"
    parameterId := "dyed_base"
    form := "obarvit"
    segments := ["obar", "v", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def obarven : Form :=
  { id := "caviranivandenwyngaerd2026_obarven"
    languageId := "czec1258"
    parameterId := "dyed"
    form := "obarven"
    segments := ["obar", "v", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "v")] }

def zlomit : Form :=
  { id := "caviranivandenwyngaerd2026_zlomit"
    languageId := "czec1258"
    parameterId := "broken_base"
    form := "zlomit"
    segments := ["zlo", "m", "it"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zlomen : Form :=
  { id := "caviranivandenwyngaerd2026_zlomen"
    languageId := "czec1258"
    parameterId := "broken"
    form := "zlomen"
    segments := ["zlo", "m", "en"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ]
    columns := [("Base", "m")] }

def divoky : Form :=
  { id := "caviranivandenwyngaerd2026_divoky"
    languageId := "czec1258"
    parameterId := "wild"
    form := "divoký"
    segments := ["divo", "k", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def divocejsi : Form :=
  { id := "caviranivandenwyngaerd2026_divocejsi"
    languageId := "czec1258"
    parameterId := "wild_cmpr"
    form := "divočejší"
    segments := ["divo", "č", "ejší"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "k")] }

def plachy : Form :=
  { id := "caviranivandenwyngaerd2026_plachy"
    languageId := "czec1258"
    parameterId := "timid"
    form := "plachý"
    segments := ["pla", "ch", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def plasejsi : Form :=
  { id := "caviranivandenwyngaerd2026_plasejsi"
    languageId := "czec1258"
    parameterId := "timid_cmpr"
    form := "plašejší"
    segments := ["pla", "š", "ejší"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "x")] }

def strohy : Form :=
  { id := "caviranivandenwyngaerd2026_strohy"
    languageId := "czec1258"
    parameterId := "austere"
    form := "strohý"
    segments := ["stro", "h", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def strozejsi : Form :=
  { id := "caviranivandenwyngaerd2026_strozejsi"
    languageId := "czec1258"
    parameterId := "austere_cmpr"
    form := "strožejší"
    segments := ["stro", "ž", "ejší"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "ɦ")] }

def kulaty : Form :=
  { id := "caviranivandenwyngaerd2026_kulaty"
    languageId := "czec1258"
    parameterId := "round"
    form := "kulatý"
    segments := ["kula", "t", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def kulatejsi : Form :=
  { id := "caviranivandenwyngaerd2026_kulatejsi"
    languageId := "czec1258"
    parameterId := "round_cmpr"
    form := "kulatější"
    segments := ["kula", "t", "ější"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "t")] }

def hrdy : Form :=
  { id := "caviranivandenwyngaerd2026_hrdy"
    languageId := "czec1258"
    parameterId := "proud"
    form := "hrdý"
    segments := ["hr", "d", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def hrdejsi : Form :=
  { id := "caviranivandenwyngaerd2026_hrdejsi"
    languageId := "czec1258"
    parameterId := "proud_cmpr"
    form := "hrdější"
    segments := ["hr", "d", "ější"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "d")] }

def domaci : Form :=
  { id := "caviranivandenwyngaerd2026_domaci"
    languageId := "czec1258"
    parameterId := "homemade"
    form := "domácí"
    segments := ["domá", "c", "í"]
    comment := "base parenthesised in the table"
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def domacejsi : Form :=
  { id := "caviranivandenwyngaerd2026_domacejsi"
    languageId := "czec1258"
    parameterId := "homemade_cmpr"
    form := "domácejší"
    segments := ["domá", "c", "ejší"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "ʦ")] }

def lysy : Form :=
  { id := "caviranivandenwyngaerd2026_lysy"
    languageId := "czec1258"
    parameterId := "bald"
    form := "lysý"
    segments := ["ly", "s", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def lysejsi : Form :=
  { id := "caviranivandenwyngaerd2026_lysejsi"
    languageId := "czec1258"
    parameterId := "bald_cmpr"
    form := "lysejší"
    segments := ["ly", "s", "ejší"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "s")] }

def drzy : Form :=
  { id := "caviranivandenwyngaerd2026_drzy"
    languageId := "czec1258"
    parameterId := "cheeky"
    form := "drzý"
    segments := ["dr", "z", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def drzejsi : Form :=
  { id := "caviranivandenwyngaerd2026_drzejsi"
    languageId := "czec1258"
    parameterId := "cheeky_cmpr"
    form := "drzejší"
    segments := ["dr", "z", "ejší"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "z")] }

def levny : Form :=
  { id := "caviranivandenwyngaerd2026_levny"
    languageId := "czec1258"
    parameterId := "cheap"
    form := "levný"
    segments := ["lev", "n", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩,
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def levnejsi : Form :=
  { id := "caviranivandenwyngaerd2026_levnejsi"
    languageId := "czec1258"
    parameterId := "cheap_cmpr"
    form := "levnější"
    segments := ["lev", "n", "ější"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "n")] }

def bujary : Form :=
  { id := "caviranivandenwyngaerd2026_bujary"
    languageId := "czec1258"
    parameterId := "merry"
    form := "bujarý"
    segments := ["buja", "r", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def bujarejsi : Form :=
  { id := "caviranivandenwyngaerd2026_bujarejsi"
    languageId := "czec1258"
    parameterId := "merry_cmpr"
    form := "bujařejší"
    segments := ["buja", "ř", "ejší"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "r")] }

def rychly : Form :=
  { id := "caviranivandenwyngaerd2026_rychly"
    languageId := "czec1258"
    parameterId := "fast"
    form := "rychlý"
    segments := ["rych", "l", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩,
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def rychlejsi : Form :=
  { id := "caviranivandenwyngaerd2026_rychlejsi"
    languageId := "czec1258"
    parameterId := "fast_cmpr"
    form := "rychlejší"
    segments := ["rych", "l", "ejší"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "l")] }

def hloupy : Form :=
  { id := "caviranivandenwyngaerd2026_hloupy"
    languageId := "czec1258"
    parameterId := "stupid"
    form := "hloupý"
    segments := ["hlou", "p", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def hloupejsi : Form :=
  { id := "caviranivandenwyngaerd2026_hloupejsi"
    languageId := "czec1258"
    parameterId := "stupid_cmpr"
    form := "hloupější"
    segments := ["hlou", "p", "ější"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "p")] }

def blby : Form :=
  { id := "caviranivandenwyngaerd2026_blby"
    languageId := "czec1258"
    parameterId := "stupid"
    form := "blbý"
    segments := ["bl", "b", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def blbejsi : Form :=
  { id := "caviranivandenwyngaerd2026_blbejsi"
    languageId := "czec1258"
    parameterId := "stupid_cmpr"
    form := "blbější"
    segments := ["bl", "b", "ější"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "b")] }

def hravy : Form :=
  { id := "caviranivandenwyngaerd2026_hravy"
    languageId := "czec1258"
    parameterId := "playful"
    form := "hravý"
    segments := ["hra", "v", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def hravejsi : Form :=
  { id := "caviranivandenwyngaerd2026_hravejsi"
    languageId := "czec1258"
    parameterId := "playful_cmpr"
    form := "hravější"
    segments := ["hra", "v", "ější"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "v")] }

def lakomy : Form :=
  { id := "caviranivandenwyngaerd2026_lakomy"
    languageId := "czec1258"
    parameterId := "stingy"
    form := "lakomý"
    segments := ["lako", "m", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def lakomejsi : Form :=
  { id := "caviranivandenwyngaerd2026_lakomejsi"
    languageId := "czec1258"
    parameterId := "stingy_cmpr"
    form := "lakomější"
    segments := ["lako", "m", "ější"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ]
    columns := [("Base", "m")] }

def trpky : Form :=
  { id := "caviranivandenwyngaerd2026_trpky"
    languageId := "czec1258"
    parameterId := "bitter"
    form := "trpký"
    segments := ["trp", "k", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def ztrpcil : Form :=
  { id := "caviranivandenwyngaerd2026_ztrpcil"
    languageId := "czec1258"
    parameterId := "bitter_caus"
    form := "ztrpčil"
    segments := ["ztrp", "č", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "k")] }

def tichy : Form :=
  { id := "caviranivandenwyngaerd2026_tichy"
    languageId := "czec1258"
    parameterId := "silent"
    form := "tichý"
    segments := ["ti", "ch", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def tisil : Form :=
  { id := "caviranivandenwyngaerd2026_tisil"
    languageId := "czec1258"
    parameterId := "silent_caus"
    form := "tišil"
    segments := ["ti", "š", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "x")] }

def drahy : Form :=
  { id := "caviranivandenwyngaerd2026_drahy"
    languageId := "czec1258"
    parameterId := "expensive"
    form := "drahý"
    segments := ["dra", "h", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zdrazil : Form :=
  { id := "caviranivandenwyngaerd2026_zdrazil"
    languageId := "czec1258"
    parameterId := "expensive_caus"
    form := "zdražil"
    segments := ["zdra", "ž", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "ɦ")] }

def nejisty : Form :=
  { id := "caviranivandenwyngaerd2026_nejisty"
    languageId := "czec1258"
    parameterId := "unsure"
    form := "nejistý"
    segments := ["nejis", "t", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def znejistil : Form :=
  { id := "caviranivandenwyngaerd2026_znejistil"
    languageId := "czec1258"
    parameterId := "unsure_caus"
    form := "znejistil"
    segments := ["znejis", "t", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "t")] }

def hnedy : Form :=
  { id := "caviranivandenwyngaerd2026_hnedy"
    languageId := "czec1258"
    parameterId := "brown"
    form := "hnědý"
    segments := ["hně", "d", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zahnedil : Form :=
  { id := "caviranivandenwyngaerd2026_zahnedil"
    languageId := "czec1258"
    parameterId := "brown_caus"
    form := "zahnědil"
    segments := ["zahně", "d", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "d")] }

def kosy : Form :=
  { id := "caviranivandenwyngaerd2026_kosy"
    languageId := "czec1258"
    parameterId := "slanting"
    form := "kosý"
    segments := ["ko", "s", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zkosil : Form :=
  { id := "caviranivandenwyngaerd2026_zkosil"
    languageId := "czec1258"
    parameterId := "slanting_caus"
    form := "zkosil"
    segments := ["zko", "s", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "s")] }

def mraz : Form :=
  { id := "caviranivandenwyngaerd2026_mraz"
    languageId := "czec1258"
    parameterId := "frost"
    form := "mráz"
    segments := ["mrá", "z"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zmrazil : Form :=
  { id := "caviranivandenwyngaerd2026_zmrazil"
    languageId := "czec1258"
    parameterId := "frost_caus"
    form := "zmrazil"
    segments := ["zmra", "z", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "z")] }

def zlevnil : Form :=
  { id := "caviranivandenwyngaerd2026_zlevnil"
    languageId := "czec1258"
    parameterId := "cheap_caus"
    form := "zlevnil"
    segments := ["zlev", "n", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "n")] }

def moudry : Form :=
  { id := "caviranivandenwyngaerd2026_moudry"
    languageId := "czec1258"
    parameterId := "wise"
    form := "moudrý"
    segments := ["moud", "r", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zmoudril : Form :=
  { id := "caviranivandenwyngaerd2026_zmoudril"
    languageId := "czec1258"
    parameterId := "wise_caus"
    form := "zmoudřil"
    segments := ["zmoud", "ř", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "r")] }

def zrychlil : Form :=
  { id := "caviranivandenwyngaerd2026_zrychlil"
    languageId := "czec1258"
    parameterId := "fast_caus"
    form := "zrychlil"
    segments := ["zrych", "l", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "l")] }

def tupy : Form :=
  { id := "caviranivandenwyngaerd2026_tupy"
    languageId := "czec1258"
    parameterId := "blunt"
    form := "tupý"
    segments := ["tu", "p", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def tupil : Form :=
  { id := "caviranivandenwyngaerd2026_tupil"
    languageId := "czec1258"
    parameterId := "blunt_caus"
    form := "tupil"
    segments := ["tu", "p", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "p")] }

def chaby : Form :=
  { id := "caviranivandenwyngaerd2026_chaby"
    languageId := "czec1258"
    parameterId := "weak"
    form := "chabý"
    segments := ["cha", "b", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def ochabil : Form :=
  { id := "caviranivandenwyngaerd2026_ochabil"
    languageId := "czec1258"
    parameterId := "weak_caus"
    form := "ochabil"
    segments := ["ocha", "b", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "b")] }

def osklivy : Form :=
  { id := "caviranivandenwyngaerd2026_osklivy"
    languageId := "czec1258"
    parameterId := "ugly"
    form := "ošklivý"
    segments := ["oškli", "v", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zosklivil : Form :=
  { id := "caviranivandenwyngaerd2026_zosklivil"
    languageId := "czec1258"
    parameterId := "ugly_caus"
    form := "zošklivil"
    segments := ["zoškli", "v", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "v")] }

def chromy : Form :=
  { id := "caviranivandenwyngaerd2026_chromy"
    languageId := "czec1258"
    parameterId := "lame"
    form := "chromý"
    segments := ["chro", "m", "ý"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def ochromil : Form :=
  { id := "caviranivandenwyngaerd2026_ochromil"
    languageId := "czec1258"
    parameterId := "lame_caus"
    form := "ochromil"
    segments := ["ochro", "m", "il"]
    comment := ""
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "m")] }

def all : List Form := [louka, louce, liga, lize, strecha, strese, kniha, knize, mata, mate, vlada, vlade, bystrica, bystrice, misa, mise, koza, koze, vina, vine, sestra, sestre, vila, vile, stoupa, stoupe, ryba, rybe, karafa, karafe, hlava, hlave, zima, zime, zatknout, zatcen, olga, olzin, nadchnout, nadsen, tahnout, tazen, nutit, nucen, uklidit, uklizen, peci, pecen, hlasit, hlasen, ohrozit, ohrozen, ranit, ranen, vera, verin, zvolit, zvolen, zatopit, zatopen, rozzlobit, rozzloben, trefit, trefen, obarvit, obarven, zlomit, zlomen, divoky, divocejsi, plachy, plasejsi, strohy, strozejsi, kulaty, kulatejsi, hrdy, hrdejsi, domaci, domacejsi, lysy, lysejsi, drzy, drzejsi, levny, levnejsi, bujary, bujarejsi, rychly, rychlejsi, hloupy, hloupejsi, blby, blbejsi, hravy, hravejsi, lakomy, lakomejsi, trpky, ztrpcil, tichy, tisil, drahy, zdrazil, nejisty, znejistil, hnedy, zahnedil, kosy, zkosil, mraz, zmrazil, zlevnil, moudry, zmoudril, zrychlil, tupy, tupil, chaby, ochabil, osklivy, zosklivil, chromy, ochromil]

def parameters : List Parameter := [
  { id := "meadow", name := "meadow", description := "" },
  { id := "meadow_locdat", name := "meadow (LOC/DAT.F.SG)", description := "" },
  { id := "league", name := "league", description := "" },
  { id := "league_locdat", name := "league (LOC/DAT.F.SG)", description := "" },
  { id := "roof", name := "roof", description := "" },
  { id := "roof_locdat", name := "roof (LOC/DAT.F.SG)", description := "" },
  { id := "book", name := "book", description := "" },
  { id := "book_locdat", name := "book (LOC/DAT.F.SG)", description := "" },
  { id := "mint", name := "mint", description := "" },
  { id := "mint_locdat", name := "mint (LOC/DAT.F.SG)", description := "" },
  { id := "government", name := "government", description := "" },
  { id := "government_locdat", name := "government (LOC/DAT.F.SG)", description := "" },
  { id := "bystrica", name := "Bystrica", description := "" },
  { id := "bystrica_locdat", name := "Bystrica (LOC/DAT.F.SG)", description := "" },
  { id := "bowl", name := "bowl", description := "" },
  { id := "bowl_locdat", name := "bowl (LOC/DAT.F.SG)", description := "" },
  { id := "goat", name := "goat", description := "" },
  { id := "goat_locdat", name := "goat (LOC/DAT.F.SG)", description := "" },
  { id := "guilt", name := "guilt", description := "" },
  { id := "guilt_locdat", name := "guilt (LOC/DAT.F.SG)", description := "" },
  { id := "sister", name := "sister", description := "" },
  { id := "sister_locdat", name := "sister (LOC/DAT.F.SG)", description := "" },
  { id := "fairy", name := "fairy", description := "" },
  { id := "fairy_locdat", name := "fairy (LOC/DAT.F.SG)", description := "" },
  { id := "rise", name := "rise", description := "" },
  { id := "rise_locdat", name := "rise (LOC/DAT.F.SG)", description := "" },
  { id := "fish", name := "fish", description := "" },
  { id := "fish_locdat", name := "fish (LOC/DAT.F.SG)", description := "" },
  { id := "decanter", name := "decanter", description := "" },
  { id := "decanter_locdat", name := "decanter (LOC/DAT.F.SG)", description := "" },
  { id := "head", name := "head", description := "" },
  { id := "head_locdat", name := "head (LOC/DAT.F.SG)", description := "" },
  { id := "winter", name := "winter", description := "" },
  { id := "winter_locdat", name := "winter (LOC/DAT.F.SG)", description := "" },
  { id := "arrested_base", name := "base of 'arrested'", description := "" },
  { id := "arrested", name := "arrested", description := "" },
  { id := "olga", name := "Olga", description := "" },
  { id := "olga_poss", name := "of Olga", description := "" },
  { id := "excited_base", name := "base of 'excited'", description := "" },
  { id := "excited", name := "excited", description := "" },
  { id := "pulled_base", name := "base of 'pulled'", description := "" },
  { id := "pulled", name := "pulled", description := "" },
  { id := "forced_base", name := "base of 'forced'", description := "" },
  { id := "forced", name := "forced", description := "" },
  { id := "cleaned_up_base", name := "base of 'cleaned up'", description := "" },
  { id := "cleaned_up", name := "cleaned up", description := "" },
  { id := "baked_base", name := "base of 'baked'", description := "" },
  { id := "baked", name := "baked", description := "" },
  { id := "reported_base", name := "base of 'reported'", description := "" },
  { id := "reported", name := "reported", description := "" },
  { id := "endangered_base", name := "base of 'endangered'", description := "" },
  { id := "endangered", name := "endangered", description := "" },
  { id := "wounded_base", name := "base of 'wounded'", description := "" },
  { id := "wounded", name := "wounded", description := "" },
  { id := "vera", name := "Vera", description := "" },
  { id := "vera_poss", name := "of Vera", description := "" },
  { id := "elected_base", name := "base of 'elected'", description := "" },
  { id := "elected", name := "elected", description := "" },
  { id := "flooded_base", name := "base of 'flooded'", description := "" },
  { id := "flooded", name := "flooded", description := "" },
  { id := "angered_base", name := "base of 'angered'", description := "" },
  { id := "angered", name := "angered", description := "" },
  { id := "hit_base", name := "base of 'hit'", description := "" },
  { id := "hit", name := "hit", description := "" },
  { id := "dyed_base", name := "base of 'dyed'", description := "" },
  { id := "dyed", name := "dyed", description := "" },
  { id := "broken_base", name := "base of 'broken'", description := "" },
  { id := "broken", name := "broken", description := "" },
  { id := "wild", name := "wild", description := "" },
  { id := "wild_cmpr", name := "wild (comparative)", description := "" },
  { id := "timid", name := "timid", description := "" },
  { id := "timid_cmpr", name := "timid (comparative)", description := "" },
  { id := "austere", name := "austere", description := "" },
  { id := "austere_cmpr", name := "austere (comparative)", description := "" },
  { id := "round", name := "round", description := "" },
  { id := "round_cmpr", name := "round (comparative)", description := "" },
  { id := "proud", name := "proud", description := "" },
  { id := "proud_cmpr", name := "proud (comparative)", description := "" },
  { id := "homemade", name := "homemade", description := "" },
  { id := "homemade_cmpr", name := "homemade (comparative)", description := "" },
  { id := "bald", name := "bald", description := "" },
  { id := "bald_cmpr", name := "bald (comparative)", description := "" },
  { id := "cheeky", name := "cheeky", description := "" },
  { id := "cheeky_cmpr", name := "cheeky (comparative)", description := "" },
  { id := "cheap", name := "cheap", description := "" },
  { id := "cheap_cmpr", name := "cheap (comparative)", description := "" },
  { id := "merry", name := "merry", description := "" },
  { id := "merry_cmpr", name := "merry (comparative)", description := "" },
  { id := "fast", name := "fast", description := "" },
  { id := "fast_cmpr", name := "fast (comparative)", description := "" },
  { id := "stupid", name := "stupid", description := "" },
  { id := "stupid_cmpr", name := "stupid (comparative)", description := "" },
  { id := "playful", name := "playful", description := "" },
  { id := "playful_cmpr", name := "playful (comparative)", description := "" },
  { id := "stingy", name := "stingy", description := "" },
  { id := "stingy_cmpr", name := "stingy (comparative)", description := "" },
  { id := "bitter", name := "bitter", description := "" },
  { id := "bitter_caus", name := "bitter (causative)", description := "" },
  { id := "silent", name := "silent", description := "" },
  { id := "silent_caus", name := "silent (causative)", description := "" },
  { id := "expensive", name := "expensive", description := "" },
  { id := "expensive_caus", name := "expensive (causative)", description := "" },
  { id := "unsure", name := "unsure", description := "" },
  { id := "unsure_caus", name := "unsure (causative)", description := "" },
  { id := "brown", name := "brown", description := "" },
  { id := "brown_caus", name := "brown (causative)", description := "" },
  { id := "slanting", name := "slanting", description := "" },
  { id := "slanting_caus", name := "slanting (causative)", description := "" },
  { id := "frost", name := "frost", description := "" },
  { id := "frost_caus", name := "frost (causative)", description := "" },
  { id := "cheap_caus", name := "cheap (causative)", description := "" },
  { id := "wise", name := "wise", description := "" },
  { id := "wise_caus", name := "wise (causative)", description := "" },
  { id := "fast_caus", name := "fast (causative)", description := "" },
  { id := "blunt", name := "blunt", description := "" },
  { id := "blunt_caus", name := "blunt (causative)", description := "" },
  { id := "weak", name := "weak", description := "" },
  { id := "weak_caus", name := "weak (causative)", description := "" },
  { id := "ugly", name := "ugly", description := "" },
  { id := "ugly_caus", name := "ugly (causative)", description := "" },
  { id := "lame", name := "lame", description := "" },
  { id := "lame_caus", name := "lame (causative)", description := "" }
]

def relations : List FormRelation := [
  { id := "caviranivandenwyngaerd2026_louka_louce", formId := "caviranivandenwyngaerd2026_louka", targetId := "caviranivandenwyngaerd2026_louce", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_liga_lize", formId := "caviranivandenwyngaerd2026_liga", targetId := "caviranivandenwyngaerd2026_lize", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_strecha_strese", formId := "caviranivandenwyngaerd2026_strecha", targetId := "caviranivandenwyngaerd2026_strese", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_kniha_knize", formId := "caviranivandenwyngaerd2026_kniha", targetId := "caviranivandenwyngaerd2026_knize", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_mata_mate", formId := "caviranivandenwyngaerd2026_mata", targetId := "caviranivandenwyngaerd2026_mate", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_vlada_vlade", formId := "caviranivandenwyngaerd2026_vlada", targetId := "caviranivandenwyngaerd2026_vlade", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_bystrica_bystrice", formId := "caviranivandenwyngaerd2026_bystrica", targetId := "caviranivandenwyngaerd2026_bystrice", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_misa_mise", formId := "caviranivandenwyngaerd2026_misa", targetId := "caviranivandenwyngaerd2026_mise", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_koza_koze", formId := "caviranivandenwyngaerd2026_koza", targetId := "caviranivandenwyngaerd2026_koze", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_vina_vine", formId := "caviranivandenwyngaerd2026_vina", targetId := "caviranivandenwyngaerd2026_vine", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_sestra_sestre", formId := "caviranivandenwyngaerd2026_sestra", targetId := "caviranivandenwyngaerd2026_sestre", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_vila_vile", formId := "caviranivandenwyngaerd2026_vila", targetId := "caviranivandenwyngaerd2026_vile", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_stoupa_stoupe", formId := "caviranivandenwyngaerd2026_stoupa", targetId := "caviranivandenwyngaerd2026_stoupe", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_ryba_rybe", formId := "caviranivandenwyngaerd2026_ryba", targetId := "caviranivandenwyngaerd2026_rybe", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_karafa_karafe", formId := "caviranivandenwyngaerd2026_karafa", targetId := "caviranivandenwyngaerd2026_karafe", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hlava_hlave", formId := "caviranivandenwyngaerd2026_hlava", targetId := "caviranivandenwyngaerd2026_hlave", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zima_zime", formId := "caviranivandenwyngaerd2026_zima", targetId := "caviranivandenwyngaerd2026_zime", relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zatknout_zatcen", formId := "caviranivandenwyngaerd2026_zatknout", targetId := "caviranivandenwyngaerd2026_zatcen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_olga_olzin", formId := "caviranivandenwyngaerd2026_olga", targetId := "caviranivandenwyngaerd2026_olzin", relation := "possessive", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_nadchnout_nadsen", formId := "caviranivandenwyngaerd2026_nadchnout", targetId := "caviranivandenwyngaerd2026_nadsen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_tahnout_tazen", formId := "caviranivandenwyngaerd2026_tahnout", targetId := "caviranivandenwyngaerd2026_tazen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_nutit_nucen", formId := "caviranivandenwyngaerd2026_nutit", targetId := "caviranivandenwyngaerd2026_nucen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_uklidit_uklizen", formId := "caviranivandenwyngaerd2026_uklidit", targetId := "caviranivandenwyngaerd2026_uklizen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_peci_pecen", formId := "caviranivandenwyngaerd2026_peci", targetId := "caviranivandenwyngaerd2026_pecen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hlasit_hlasen", formId := "caviranivandenwyngaerd2026_hlasit", targetId := "caviranivandenwyngaerd2026_hlasen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_ohrozit_ohrozen", formId := "caviranivandenwyngaerd2026_ohrozit", targetId := "caviranivandenwyngaerd2026_ohrozen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_ranit_ranen", formId := "caviranivandenwyngaerd2026_ranit", targetId := "caviranivandenwyngaerd2026_ranen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_vera_verin", formId := "caviranivandenwyngaerd2026_vera", targetId := "caviranivandenwyngaerd2026_verin", relation := "possessive", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zvolit_zvolen", formId := "caviranivandenwyngaerd2026_zvolit", targetId := "caviranivandenwyngaerd2026_zvolen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zatopit_zatopen", formId := "caviranivandenwyngaerd2026_zatopit", targetId := "caviranivandenwyngaerd2026_zatopen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_rozzlobit_rozzloben", formId := "caviranivandenwyngaerd2026_rozzlobit", targetId := "caviranivandenwyngaerd2026_rozzloben", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_trefit_trefen", formId := "caviranivandenwyngaerd2026_trefit", targetId := "caviranivandenwyngaerd2026_trefen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_obarvit_obarven", formId := "caviranivandenwyngaerd2026_obarvit", targetId := "caviranivandenwyngaerd2026_obarven", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zlomit_zlomen", formId := "caviranivandenwyngaerd2026_zlomit", targetId := "caviranivandenwyngaerd2026_zlomen", relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_divoky_divocejsi", formId := "caviranivandenwyngaerd2026_divoky", targetId := "caviranivandenwyngaerd2026_divocejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_plachy_plasejsi", formId := "caviranivandenwyngaerd2026_plachy", targetId := "caviranivandenwyngaerd2026_plasejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_strohy_strozejsi", formId := "caviranivandenwyngaerd2026_strohy", targetId := "caviranivandenwyngaerd2026_strozejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_kulaty_kulatejsi", formId := "caviranivandenwyngaerd2026_kulaty", targetId := "caviranivandenwyngaerd2026_kulatejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hrdy_hrdejsi", formId := "caviranivandenwyngaerd2026_hrdy", targetId := "caviranivandenwyngaerd2026_hrdejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_domaci_domacejsi", formId := "caviranivandenwyngaerd2026_domaci", targetId := "caviranivandenwyngaerd2026_domacejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_lysy_lysejsi", formId := "caviranivandenwyngaerd2026_lysy", targetId := "caviranivandenwyngaerd2026_lysejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_drzy_drzejsi", formId := "caviranivandenwyngaerd2026_drzy", targetId := "caviranivandenwyngaerd2026_drzejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_levny_levnejsi", formId := "caviranivandenwyngaerd2026_levny", targetId := "caviranivandenwyngaerd2026_levnejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_bujary_bujarejsi", formId := "caviranivandenwyngaerd2026_bujary", targetId := "caviranivandenwyngaerd2026_bujarejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_rychly_rychlejsi", formId := "caviranivandenwyngaerd2026_rychly", targetId := "caviranivandenwyngaerd2026_rychlejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hloupy_hloupejsi", formId := "caviranivandenwyngaerd2026_hloupy", targetId := "caviranivandenwyngaerd2026_hloupejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_blby_blbejsi", formId := "caviranivandenwyngaerd2026_blby", targetId := "caviranivandenwyngaerd2026_blbejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hravy_hravejsi", formId := "caviranivandenwyngaerd2026_hravy", targetId := "caviranivandenwyngaerd2026_hravejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_lakomy_lakomejsi", formId := "caviranivandenwyngaerd2026_lakomy", targetId := "caviranivandenwyngaerd2026_lakomejsi", relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_trpky_ztrpcil", formId := "caviranivandenwyngaerd2026_trpky", targetId := "caviranivandenwyngaerd2026_ztrpcil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_tichy_tisil", formId := "caviranivandenwyngaerd2026_tichy", targetId := "caviranivandenwyngaerd2026_tisil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_drahy_zdrazil", formId := "caviranivandenwyngaerd2026_drahy", targetId := "caviranivandenwyngaerd2026_zdrazil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_nejisty_znejistil", formId := "caviranivandenwyngaerd2026_nejisty", targetId := "caviranivandenwyngaerd2026_znejistil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hnedy_zahnedil", formId := "caviranivandenwyngaerd2026_hnedy", targetId := "caviranivandenwyngaerd2026_zahnedil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_kosy_zkosil", formId := "caviranivandenwyngaerd2026_kosy", targetId := "caviranivandenwyngaerd2026_zkosil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_mraz_zmrazil", formId := "caviranivandenwyngaerd2026_mraz", targetId := "caviranivandenwyngaerd2026_zmrazil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_levny_zlevnil", formId := "caviranivandenwyngaerd2026_levny", targetId := "caviranivandenwyngaerd2026_zlevnil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_moudry_zmoudril", formId := "caviranivandenwyngaerd2026_moudry", targetId := "caviranivandenwyngaerd2026_zmoudril", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_rychly_zrychlil", formId := "caviranivandenwyngaerd2026_rychly", targetId := "caviranivandenwyngaerd2026_zrychlil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_tupy_tupil", formId := "caviranivandenwyngaerd2026_tupy", targetId := "caviranivandenwyngaerd2026_tupil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_chaby_ochabil", formId := "caviranivandenwyngaerd2026_chaby", targetId := "caviranivandenwyngaerd2026_ochabil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_osklivy_zosklivil", formId := "caviranivandenwyngaerd2026_osklivy", targetId := "caviranivandenwyngaerd2026_zosklivil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_chromy_ochromil", formId := "caviranivandenwyngaerd2026_chromy", targetId := "caviranivandenwyngaerd2026_ochromil", relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }
]

/-- The form and the target of each relation, in the order of `relations`. -/
def relationForms : List (Form × Form) := [(louka, louce), (liga, lize), (strecha, strese), (kniha, knize), (mata, mate), (vlada, vlade), (bystrica, bystrice), (misa, mise), (koza, koze), (vina, vine), (sestra, sestre), (vila, vile), (stoupa, stoupe), (ryba, rybe), (karafa, karafe), (hlava, hlave), (zima, zime), (zatknout, zatcen), (olga, olzin), (nadchnout, nadsen), (tahnout, tazen), (nutit, nucen), (uklidit, uklizen), (peci, pecen), (hlasit, hlasen), (ohrozit, ohrozen), (ranit, ranen), (vera, verin), (zvolit, zvolen), (zatopit, zatopen), (rozzlobit, rozzloben), (trefit, trefen), (obarvit, obarven), (zlomit, zlomen), (divoky, divocejsi), (plachy, plasejsi), (strohy, strozejsi), (kulaty, kulatejsi), (hrdy, hrdejsi), (domaci, domacejsi), (lysy, lysejsi), (drzy, drzejsi), (levny, levnejsi), (bujary, bujarejsi), (rychly, rychlejsi), (hloupy, hloupejsi), (blby, blbejsi), (hravy, hravejsi), (lakomy, lakomejsi), (trpky, ztrpcil), (tichy, tisil), (drahy, zdrazil), (nejisty, znejistil), (hnedy, zahnedil), (kosy, zkosil), (mraz, zmrazil), (levny, zlevnil), (moudry, zmoudril), (rychly, zrychlil), (tupy, tupil), (chaby, ochabil), (osklivy, zosklivil), (chromy, ochromil)]

end CaviraniVandenWyngaerd2026.Forms
