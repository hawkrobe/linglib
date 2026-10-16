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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def louce : Form :=
  { id := "caviranivandenwyngaerd2026_louce"
    languageId := "czec1258"
    parameterId := "meadow_locdat"
    form := "louce"
    segments := ["lou", "c", "e"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def lize : Form :=
  { id := "caviranivandenwyngaerd2026_lize"
    languageId := "czec1258"
    parameterId := "league_locdat"
    form := "lize"
    segments := ["li", "z", "e"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def strese : Form :=
  { id := "caviranivandenwyngaerd2026_strese"
    languageId := "czec1258"
    parameterId := "roof_locdat"
    form := "střeše"
    segments := ["stře", "š", "e"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def knize : Form :=
  { id := "caviranivandenwyngaerd2026_knize"
    languageId := "czec1258"
    parameterId := "book_locdat"
    form := "knize"
    segments := ["kni", "z", "e"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def mate : Form :=
  { id := "caviranivandenwyngaerd2026_mate"
    languageId := "czec1258"
    parameterId := "mint_locdat"
    form := "mátě"
    segments := ["má", "t", "ě"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def vlade : Form :=
  { id := "caviranivandenwyngaerd2026_vlade"
    languageId := "czec1258"
    parameterId := "government_locdat"
    form := "vládě"
    segments := ["vlá", "d", "ě"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def bystrice : Form :=
  { id := "caviranivandenwyngaerd2026_bystrice"
    languageId := "czec1258"
    parameterId := "bystrica_locdat"
    form := "Bystrice"
    segments := ["Bystri", "c", "e"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def mise : Form :=
  { id := "caviranivandenwyngaerd2026_mise"
    languageId := "czec1258"
    parameterId := "bowl_locdat"
    form := "míse"
    segments := ["mí", "s", "e"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def koze : Form :=
  { id := "caviranivandenwyngaerd2026_koze"
    languageId := "czec1258"
    parameterId := "goat_locdat"
    form := "koze"
    segments := ["ko", "z", "e"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def vine : Form :=
  { id := "caviranivandenwyngaerd2026_vine"
    languageId := "czec1258"
    parameterId := "guilt_locdat"
    form := "vině"
    segments := ["vi", "n", "ě"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def sestre : Form :=
  { id := "caviranivandenwyngaerd2026_sestre"
    languageId := "czec1258"
    parameterId := "sister_locdat"
    form := "sestře"
    segments := ["sest", "ř", "e"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def vile : Form :=
  { id := "caviranivandenwyngaerd2026_vile"
    languageId := "czec1258"
    parameterId := "fairy_locdat"
    form := "víle"
    segments := ["ví", "l", "e"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def stoupe : Form :=
  { id := "caviranivandenwyngaerd2026_stoupe"
    languageId := "czec1258"
    parameterId := "rise_locdat"
    form := "stoupě"
    segments := ["stou", "p", "ě"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def rybe : Form :=
  { id := "caviranivandenwyngaerd2026_rybe"
    languageId := "czec1258"
    parameterId := "fish_locdat"
    form := "rybě"
    segments := ["ry", "b", "ě"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def karafe : Form :=
  { id := "caviranivandenwyngaerd2026_karafe"
    languageId := "czec1258"
    parameterId := "decanter_locdat"
    form := "karafě"
    segments := ["kara", "f", "ě"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def hlave : Form :=
  { id := "caviranivandenwyngaerd2026_hlave"
    languageId := "czec1258"
    parameterId := "head_locdat"
    form := "hlavě"
    segments := ["hla", "v", "ě"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zime : Form :=
  { id := "caviranivandenwyngaerd2026_zime"
    languageId := "czec1258"
    parameterId := "winter_locdat"
    form := "zimě"
    segments := ["zi", "m", "ě"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zatcen : Form :=
  { id := "caviranivandenwyngaerd2026_zatcen"
    languageId := "czec1258"
    parameterId := "arrested"
    form := "zatčen"
    segments := ["zat", "č", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def olzin : Form :=
  { id := "caviranivandenwyngaerd2026_olzin"
    languageId := "czec1258"
    parameterId := "olga_poss"
    form := "Olžin"
    segments := ["Ol", "ž", "in"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def nadsen : Form :=
  { id := "caviranivandenwyngaerd2026_nadsen"
    languageId := "czec1258"
    parameterId := "excited"
    form := "nadšen"
    segments := ["nad", "š", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def tazen : Form :=
  { id := "caviranivandenwyngaerd2026_tazen"
    languageId := "czec1258"
    parameterId := "pulled"
    form := "tažen"
    segments := ["ta", "ž", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def nucen : Form :=
  { id := "caviranivandenwyngaerd2026_nucen"
    languageId := "czec1258"
    parameterId := "forced"
    form := "nucen"
    segments := ["nu", "c", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def uklizen : Form :=
  { id := "caviranivandenwyngaerd2026_uklizen"
    languageId := "czec1258"
    parameterId := "cleaned_up"
    form := "uklizen"
    segments := ["ukli", "z", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def pecen : Form :=
  { id := "caviranivandenwyngaerd2026_pecen"
    languageId := "czec1258"
    parameterId := "baked"
    form := "pečen"
    segments := ["pe", "č", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def hlasen : Form :=
  { id := "caviranivandenwyngaerd2026_hlasen"
    languageId := "czec1258"
    parameterId := "reported"
    form := "hlášen"
    segments := ["hlá", "š", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def ohrozen : Form :=
  { id := "caviranivandenwyngaerd2026_ohrozen"
    languageId := "czec1258"
    parameterId := "endangered"
    form := "ohrožen"
    segments := ["ohro", "ž", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def ranen : Form :=
  { id := "caviranivandenwyngaerd2026_ranen"
    languageId := "czec1258"
    parameterId := "wounded"
    form := "raněn"
    segments := ["ra", "n", "ěn"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def verin : Form :=
  { id := "caviranivandenwyngaerd2026_verin"
    languageId := "czec1258"
    parameterId := "vera_poss"
    form := "Věřin"
    segments := ["Vě", "ř", "in"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zvolen : Form :=
  { id := "caviranivandenwyngaerd2026_zvolen"
    languageId := "czec1258"
    parameterId := "elected"
    form := "zvolen"
    segments := ["zvo", "l", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zatopen : Form :=
  { id := "caviranivandenwyngaerd2026_zatopen"
    languageId := "czec1258"
    parameterId := "flooded"
    form := "zatopen"
    segments := ["zato", "p", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def rozzloben : Form :=
  { id := "caviranivandenwyngaerd2026_rozzloben"
    languageId := "czec1258"
    parameterId := "angered"
    form := "rozzloben"
    segments := ["rozzlo", "b", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def trefen : Form :=
  { id := "caviranivandenwyngaerd2026_trefen"
    languageId := "czec1258"
    parameterId := "hit"
    form := "trefen"
    segments := ["tre", "f", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def obarven : Form :=
  { id := "caviranivandenwyngaerd2026_obarven"
    languageId := "czec1258"
    parameterId := "dyed"
    form := "obarven"
    segments := ["obar", "v", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] }

def zlomen : Form :=
  { id := "caviranivandenwyngaerd2026_zlomen"
    languageId := "czec1258"
    parameterId := "broken"
    form := "zlomen"
    segments := ["zlo", "m", "en"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def divocejsi : Form :=
  { id := "caviranivandenwyngaerd2026_divocejsi"
    languageId := "czec1258"
    parameterId := "wild_cmpr"
    form := "divočejší"
    segments := ["divo", "č", "ejší"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def plasejsi : Form :=
  { id := "caviranivandenwyngaerd2026_plasejsi"
    languageId := "czec1258"
    parameterId := "timid_cmpr"
    form := "plašejší"
    segments := ["pla", "š", "ejší"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def strozejsi : Form :=
  { id := "caviranivandenwyngaerd2026_strozejsi"
    languageId := "czec1258"
    parameterId := "austere_cmpr"
    form := "strožejší"
    segments := ["stro", "ž", "ejší"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def kulatejsi : Form :=
  { id := "caviranivandenwyngaerd2026_kulatejsi"
    languageId := "czec1258"
    parameterId := "round_cmpr"
    form := "kulatější"
    segments := ["kula", "t", "ější"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def hrdejsi : Form :=
  { id := "caviranivandenwyngaerd2026_hrdejsi"
    languageId := "czec1258"
    parameterId := "proud_cmpr"
    form := "hrdější"
    segments := ["hr", "d", "ější"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def domacejsi : Form :=
  { id := "caviranivandenwyngaerd2026_domacejsi"
    languageId := "czec1258"
    parameterId := "homemade_cmpr"
    form := "domácejší"
    segments := ["domá", "c", "ejší"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def lysejsi : Form :=
  { id := "caviranivandenwyngaerd2026_lysejsi"
    languageId := "czec1258"
    parameterId := "bald_cmpr"
    form := "lysejší"
    segments := ["ly", "s", "ejší"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def drzejsi : Form :=
  { id := "caviranivandenwyngaerd2026_drzejsi"
    languageId := "czec1258"
    parameterId := "cheeky_cmpr"
    form := "drzejší"
    segments := ["dr", "z", "ejší"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def bujarejsi : Form :=
  { id := "caviranivandenwyngaerd2026_bujarejsi"
    languageId := "czec1258"
    parameterId := "merry_cmpr"
    form := "bujařejší"
    segments := ["buja", "ř", "ejší"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def hloupejsi : Form :=
  { id := "caviranivandenwyngaerd2026_hloupejsi"
    languageId := "czec1258"
    parameterId := "stupid_cmpr"
    form := "hloupější"
    segments := ["hlou", "p", "ější"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def blbejsi : Form :=
  { id := "caviranivandenwyngaerd2026_blbejsi"
    languageId := "czec1258"
    parameterId := "stupid_cmpr"
    form := "blbější"
    segments := ["bl", "b", "ější"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def hravejsi : Form :=
  { id := "caviranivandenwyngaerd2026_hravejsi"
    languageId := "czec1258"
    parameterId := "playful_cmpr"
    form := "hravější"
    segments := ["hra", "v", "ější"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] }

def lakomejsi : Form :=
  { id := "caviranivandenwyngaerd2026_lakomejsi"
    languageId := "czec1258"
    parameterId := "stingy_cmpr"
    form := "lakomější"
    segments := ["lako", "m", "ější"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def ztrpcil : Form :=
  { id := "caviranivandenwyngaerd2026_ztrpcil"
    languageId := "czec1258"
    parameterId := "bitter_caus"
    form := "ztrpčil"
    segments := ["ztrp", "č", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def tisil : Form :=
  { id := "caviranivandenwyngaerd2026_tisil"
    languageId := "czec1258"
    parameterId := "silent_caus"
    form := "tišil"
    segments := ["ti", "š", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zdrazil : Form :=
  { id := "caviranivandenwyngaerd2026_zdrazil"
    languageId := "czec1258"
    parameterId := "expensive_caus"
    form := "zdražil"
    segments := ["zdra", "ž", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def znejistil : Form :=
  { id := "caviranivandenwyngaerd2026_znejistil"
    languageId := "czec1258"
    parameterId := "unsure_caus"
    form := "znejistil"
    segments := ["znejis", "t", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zahnedil : Form :=
  { id := "caviranivandenwyngaerd2026_zahnedil"
    languageId := "czec1258"
    parameterId := "brown_caus"
    form := "zahnědil"
    segments := ["zahně", "d", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zkosil : Form :=
  { id := "caviranivandenwyngaerd2026_zkosil"
    languageId := "czec1258"
    parameterId := "slanting_caus"
    form := "zkosil"
    segments := ["zko", "s", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zmrazil : Form :=
  { id := "caviranivandenwyngaerd2026_zmrazil"
    languageId := "czec1258"
    parameterId := "frost_caus"
    form := "zmrazil"
    segments := ["zmra", "z", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zmoudril : Form :=
  { id := "caviranivandenwyngaerd2026_zmoudril"
    languageId := "czec1258"
    parameterId := "wise_caus"
    form := "zmoudřil"
    segments := ["zmoud", "ř", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def tupil : Form :=
  { id := "caviranivandenwyngaerd2026_tupil"
    languageId := "czec1258"
    parameterId := "blunt_caus"
    form := "tupil"
    segments := ["tu", "p", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def ochabil : Form :=
  { id := "caviranivandenwyngaerd2026_ochabil"
    languageId := "czec1258"
    parameterId := "weak_caus"
    form := "ochabil"
    segments := ["ocha", "b", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def zosklivil : Form :=
  { id := "caviranivandenwyngaerd2026_zosklivil"
    languageId := "czec1258"
    parameterId := "ugly_caus"
    form := "zošklivil"
    segments := ["zoškli", "v", "il"]
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
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }

def ochromil : Form :=
  { id := "caviranivandenwyngaerd2026_ochromil"
    languageId := "czec1258"
    parameterId := "lame_caus"
    form := "ochromil"
    segments := ["ochro", "m", "il"]
    source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ]
    columns := [("Base", "m")] }

def all : List Form := [louka, louce, liga, lize, strecha, strese, kniha, knize, mata, mate, vlada, vlade, bystrica, bystrice, misa, mise, koza, koze, vina, vine, sestra, sestre, vila, vile, stoupa, stoupe, ryba, rybe, karafa, karafe, hlava, hlave, zima, zime, zatknout, zatcen, olga, olzin, nadchnout, nadsen, tahnout, tazen, nutit, nucen, uklidit, uklizen, peci, pecen, hlasit, hlasen, ohrozit, ohrozen, ranit, ranen, vera, verin, zvolit, zvolen, zatopit, zatopen, rozzlobit, rozzloben, trefit, trefen, obarvit, obarven, zlomit, zlomen, divoky, divocejsi, plachy, plasejsi, strohy, strozejsi, kulaty, kulatejsi, hrdy, hrdejsi, domaci, domacejsi, lysy, lysejsi, drzy, drzejsi, levny, levnejsi, bujary, bujarejsi, rychly, rychlejsi, hloupy, hloupejsi, blby, blbejsi, hravy, hravejsi, lakomy, lakomejsi, trpky, ztrpcil, tichy, tisil, drahy, zdrazil, nejisty, znejistil, hnedy, zahnedil, kosy, zkosil, mraz, zmrazil, zlevnil, moudry, zmoudril, zrychlil, tupy, tupil, chaby, ochabil, osklivy, zosklivil, chromy, ochromil]

def relations : List FormRelation := [
  { id := "caviranivandenwyngaerd2026_louka_louce", form := louka, target := louce, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_liga_lize", form := liga, target := lize, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_strecha_strese", form := strecha, target := strese, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_kniha_knize", form := kniha, target := knize, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_mata_mate", form := mata, target := mate, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_vlada_vlade", form := vlada, target := vlade, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_bystrica_bystrice", form := bystrica, target := bystrice, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_misa_mise", form := misa, target := mise, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_koza_koze", form := koza, target := koze, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_vina_vine", form := vina, target := vine, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_sestra_sestre", form := sestra, target := sestre, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_vila_vile", form := vila, target := vile, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_stoupa_stoupe", form := stoupa, target := stoupe, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_ryba_rybe", form := ryba, target := rybe, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_karafa_karafe", form := karafa, target := karafe, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hlava_hlave", form := hlava, target := hlave, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zima_zime", form := zima, target := zime, relation := "locDatFSg", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zatknout_zatcen", form := zatknout, target := zatcen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_olga_olzin", form := olga, target := olzin, relation := "possessive", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_nadchnout_nadsen", form := nadchnout, target := nadsen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_tahnout_tazen", form := tahnout, target := tazen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_nutit_nucen", form := nutit, target := nucen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_uklidit_uklizen", form := uklidit, target := uklizen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_peci_pecen", form := peci, target := pecen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hlasit_hlasen", form := hlasit, target := hlasen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_ohrozit_ohrozen", form := ohrozit, target := ohrozen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_ranit_ranen", form := ranit, target := ranen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_vera_verin", form := vera, target := verin, relation := "possessive", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zvolit_zvolen", form := zvolit, target := zvolen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zatopit_zatopen", form := zatopit, target := zatopen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_rozzlobit_rozzloben", form := rozzlobit, target := rozzloben, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_trefit_trefen", form := trefit, target := trefen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_obarvit_obarven", form := obarvit, target := obarven, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_zlomit_zlomen", form := zlomit, target := zlomen, relation := "passPtcp", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 1"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_divoky_divocejsi", form := divoky, target := divocejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_plachy_plasejsi", form := plachy, target := plasejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_strohy_strozejsi", form := strohy, target := strozejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_kulaty_kulatejsi", form := kulaty, target := kulatejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hrdy_hrdejsi", form := hrdy, target := hrdejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_domaci_domacejsi", form := domaci, target := domacejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_lysy_lysejsi", form := lysy, target := lysejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_drzy_drzejsi", form := drzy, target := drzejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_levny_levnejsi", form := levny, target := levnejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_bujary_bujarejsi", form := bujary, target := bujarejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_rychly_rychlejsi", form := rychly, target := rychlejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hloupy_hloupejsi", form := hloupy, target := hloupejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_blby_blbejsi", form := blby, target := blbejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hravy_hravejsi", form := hravy, target := hravejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_lakomy_lakomejsi", form := lakomy, target := lakomejsi, relation := "comparative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 2"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_trpky_ztrpcil", form := trpky, target := ztrpcil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_tichy_tisil", form := tichy, target := tisil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_drahy_zdrazil", form := drahy, target := zdrazil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_nejisty_znejistil", form := nejisty, target := znejistil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_hnedy_zahnedil", form := hnedy, target := zahnedil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_kosy_zkosil", form := kosy, target := zkosil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_mraz_zmrazil", form := mraz, target := zmrazil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_levny_zlevnil", form := levny, target := zlevnil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_moudry_zmoudril", form := moudry, target := zmoudril, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_rychly_zrychlil", form := rychly, target := zrychlil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_tupy_tupil", form := tupy, target := tupil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_chaby_ochabil", form := chaby, target := ochabil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_osklivy_zosklivil", form := osklivy, target := zosklivil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] },
  { id := "caviranivandenwyngaerd2026_chromy_ochromil", form := chromy, target := ochromil, relation := "causative", source := [
      ⟨"cavirani-vandenwyngaerd-2026", "Table 3"⟩
    ] }
]

end CaviraniVandenWyngaerd2026.Forms
