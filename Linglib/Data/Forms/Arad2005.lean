module

public import Linglib.Data.Forms.Schema

/-!
# `Arad2005` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Arad2005.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Arad2005.Forms`.
-/

@[expose] public section

namespace Arad2005.Forms

open Data.Forms

def lamad : Form :=
  { id := "arad2005_lamad"
    languageId := "hebr1245"
    parameterId := "learn"
    form := "lamad"
    segments := ["l", "a", "m", "a", "d"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ]
    columns := [("Root", "lmd"), ("Binyan", "1"), ("Category", "v")] }

def nilmad : Form :=
  { id := "arad2005_nilmad"
    languageId := "hebr1245"
    parameterId := "learn_passive"
    form := "nilmad"
    segments := ["n", "i", "l", "m", "a", "d"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ]
    columns := [("Root", "lmd"), ("Binyan", "2"), ("Category", "v")] }

def siper : Form :=
  { id := "arad2005_siper"
    languageId := "hebr1245"
    parameterId := "tell"
    form := "siper"
    segments := ["s", "i", "p", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ]
    columns := [("Root", "spr"), ("Binyan", "3"), ("Category", "v")] }

def supar : Form :=
  { id := "arad2005_supar"
    languageId := "hebr1245"
    parameterId := "tell_passive"
    form := "supar"
    segments := ["s", "u", "p", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ]
    columns := [("Root", "spr"), ("Binyan", "4"), ("Category", "v")] }

def hiqlit : Form :=
  { id := "arad2005_hiqlit"
    languageId := "hebr1245"
    parameterId := "record"
    form := "hiqlit"
    segments := ["h", "i", "q", "l", "i", "t"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩,
      ⟨"arad-2005", "Ch. 7 (4b)"⟩
    ]
    columns := [("Root", "qlt"), ("Binyan", "5"), ("Category", "v")] }

def huqlat : Form :=
  { id := "arad2005_huqlat"
    languageId := "hebr1245"
    parameterId := "record_passive"
    form := "huqlat"
    segments := ["h", "u", "q", "l", "a", "t"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ]
    columns := [("Root", "qlt"), ("Binyan", "6"), ("Category", "v")] }

def hitpalel : Form :=
  { id := "arad2005_hitpalel"
    languageId := "hebr1245"
    parameterId := "pray"
    form := "hitpalel"
    segments := ["h", "i", "t", "p", "a", "l", "e", "l"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ]
    columns := [("Root", "pll"), ("Binyan", "7"), ("Category", "v")] }

def nipec : Form :=
  { id := "arad2005_nipec"
    languageId := "hebr1245"
    parameterId := "shatter"
    form := "nipec"
    segments := ["n", "i", "p", "e", "c"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6a)"⟩
    ]
    columns := [("Root", "npc"), ("Binyan", "3"), ("Category", "v")] }

def nupac : Form :=
  { id := "arad2005_nupac"
    languageId := "hebr1245"
    parameterId := "shatter_passive"
    form := "nupac"
    segments := ["n", "u", "p", "a", "c"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6a)"⟩
    ]
    columns := [("Root", "npc"), ("Binyan", "4"), ("Category", "v")] }

def xileq : Form :=
  { id := "arad2005_xileq"
    languageId := "hebr1245"
    parameterId := "divide"
    form := "xileq"
    segments := ["x", "i", "l", "e", "q"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6b)"⟩
    ]
    columns := [("Root", "xlq"), ("Binyan", "3"), ("Category", "v")] }

def xulaq : Form :=
  { id := "arad2005_xulaq"
    languageId := "hebr1245"
    parameterId := "divide_passive"
    form := "xulaq"
    segments := ["x", "u", "l", "a", "q"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6b)"⟩
    ]
    columns := [("Root", "xlq"), ("Binyan", "4"), ("Category", "v")] }

def histir : Form :=
  { id := "arad2005_histir"
    languageId := "hebr1245"
    parameterId := "hide"
    form := "histir"
    segments := ["h", "i", "s", "t", "i", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6c)"⟩
    ]
    columns := [("Root", "str"), ("Binyan", "5"), ("Category", "v")] }

def hustar : Form :=
  { id := "arad2005_hustar"
    languageId := "hebr1245"
    parameterId := "hide_passive"
    form := "hustar"
    segments := ["h", "u", "s", "t", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6c)"⟩
    ]
    columns := [("Root", "str"), ("Binyan", "6"), ("Category", "v")] }

def hifqid : Form :=
  { id := "arad2005_hifqid"
    languageId := "hebr1245"
    parameterId := "deposit"
    form := "hifqid"
    segments := ["h", "i", "f", "q", "i", "d"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6d)"⟩
    ]
    columns := [("Root", "pqd"), ("Binyan", "5"), ("Category", "v")] }

def hufqad : Form :=
  { id := "arad2005_hufqad"
    languageId := "hebr1245"
    parameterId := "deposit_passive"
    form := "hufqad"
    segments := ["h", "u", "f", "q", "a", "d"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6d)"⟩
    ]
    columns := [("Root", "pqd"), ("Binyan", "6"), ("Category", "v")] }

def shamar : Form :=
  { id := "arad2005_shamar"
    languageId := "hebr1245"
    parameterId := "guard"
    form := "šamar"
    segments := ["š", "a", "m", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (27)"⟩
    ]
    columns := [("Root", "šmr"), ("Binyan", "1"), ("Category", "v")] }

def tirgem : Form :=
  { id := "arad2005_tirgem"
    languageId := "hebr1245"
    parameterId := "translate"
    form := "tirgem"
    segments := ["t", "i", "r", "g", "e", "m"]
    source := [
      ⟨"arad-2005", "p. 28"⟩
    ]
    columns := [("Root", "trgm"), ("Binyan", "3"), ("Category", "v")] }

def qibel : Form :=
  { id := "arad2005_qibel"
    languageId := "hebr1245"
    parameterId := "receive"
    form := "qibel"
    segments := ["q", "i", "b", "e", "l"]
    source := [
      ⟨"arad-2005", "p. 29"⟩
    ]
    columns := [("Root", "qbl"), ("Binyan", "3"), ("Category", "v")] }

def hitrakex : Form :=
  { id := "arad2005_hitrakex"
    languageId := "hebr1245"
    parameterId := "become_soft"
    form := "hitrakex"
    segments := ["h", "i", "t", "r", "a", "k", "e", "x"]
    source := [
      ⟨"arad-2005", "p. 29"⟩
    ]
    columns := [("Root", "rkk"), ("Binyan", "7"), ("Category", "v")] }

def shemen : Form :=
  { id := "arad2005_shemen"
    languageId := "hebr1245"
    parameterId := "oil_grease"
    form := "šemen"
    segments := ["š", "e", "m", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2a)"⟩
    ]
    columns := [("Root", "šmn"), ("Pattern", "CeCeC"), ("Category", "n")] }

def shamenet : Form :=
  { id := "arad2005_shamenet"
    languageId := "hebr1245"
    parameterId := "cream"
    form := "šamenet"
    segments := ["š", "a", "m", "e", "n", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2b)"⟩
    ]
    columns := [("Root", "šmn"), ("Pattern", "CaCCeCet"), ("Category", "n")] }

def shuman : Form :=
  { id := "arad2005_shuman"
    languageId := "hebr1245"
    parameterId := "fat"
    form := "šuman"
    segments := ["š", "u", "m", "a", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2c)"⟩
    ]
    columns := [("Root", "šmn"), ("Pattern", "CuCaC"), ("Category", "n")] }

def shamen : Form :=
  { id := "arad2005_shamen"
    languageId := "hebr1245"
    parameterId := "fat_adj"
    form := "šamen"
    segments := ["š", "a", "m", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2d)"⟩
    ]
    columns := [("Root", "šmn"), ("Pattern", "CaCeC"), ("Category", "adj")] }

def hishmin : Form :=
  { id := "arad2005_hishmin"
    languageId := "hebr1245"
    parameterId := "grow_fat_fatten"
    form := "hišmin"
    segments := ["h", "i", "š", "m", "i", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2e)"⟩
    ]
    columns := [("Root", "šmn"), ("Binyan", "5"), ("Category", "v")] }

def shimen : Form :=
  { id := "arad2005_shimen"
    languageId := "hebr1245"
    parameterId := "grease"
    form := "šimen"
    segments := ["š", "i", "m", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2f)"⟩
    ]
    columns := [("Root", "šmn"), ("Binyan", "3"), ("Category", "v")] }

def xashav : Form :=
  { id := "arad2005_xashav"
    languageId := "hebr1245"
    parameterId := "to_think"
    form := "xašav"
    segments := ["x", "a", "š", "a", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3a)"⟩
    ]
    columns := [("Root", "xšb"), ("Binyan", "1"), ("Category", "v")] }

def xishev : Form :=
  { id := "arad2005_xishev"
    languageId := "hebr1245"
    parameterId := "to_calculate"
    form := "xišev"
    segments := ["x", "i", "š", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3b)"⟩
    ]
    columns := [("Root", "xšb"), ("Binyan", "3"), ("Category", "v")] }

def hexshiv : Form :=
  { id := "arad2005_hexshiv"
    languageId := "hebr1245"
    parameterId := "to_consider"
    form := "hexšiv"
    segments := ["h", "e", "x", "š", "i", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3c)"⟩
    ]
    columns := [("Root", "xšb"), ("Binyan", "5"), ("Category", "v")] }

def hitxashev : Form :=
  { id := "arad2005_hitxashev"
    languageId := "hebr1245"
    parameterId := "to_be_considerate"
    form := "hitxašev"
    segments := ["h", "i", "t", "x", "a", "š", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3d)"⟩
    ]
    columns := [("Root", "xšb"), ("Binyan", "7"), ("Category", "v")] }

def maxshev : Form :=
  { id := "arad2005_maxshev"
    languageId := "hebr1245"
    parameterId := "computer"
    form := "maxšev"
    segments := ["m", "a", "x", "š", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29d)"⟩,
      ⟨"arad-2005", "Ch. 7 (3e)"⟩
    ]
    columns := [("Root", "xšb"), ("Pattern", "maCCeC"), ("Category", "n")] }

def maxshava : Form :=
  { id := "arad2005_maxshava"
    languageId := "hebr1245"
    parameterId := "a_thought"
    form := "maxšava"
    segments := ["m", "a", "x", "š", "a", "v", "a"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3f)"⟩
    ]
    columns := [("Root", "xšb"), ("Pattern", "maCCaCa"), ("Category", "n")] }

def xashivut : Form :=
  { id := "arad2005_xashivut"
    languageId := "hebr1245"
    parameterId := "importance"
    form := "xašivut"
    segments := ["x", "a", "š", "i", "v", "u", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3g)"⟩
    ]
    columns := [("Root", "xšb"), ("Pattern", "CCiCut"), ("Category", "n")] }

def xeshbon : Form :=
  { id := "arad2005_xeshbon"
    languageId := "hebr1245"
    parameterId := "arithmetic_bill"
    form := "xešbon"
    segments := ["x", "e", "š", "b", "o", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3h)"⟩
    ]
    columns := [("Root", "xšb"), ("Pattern", "CiCCon"), ("Category", "n")] }

def taxshiv : Form :=
  { id := "arad2005_taxshiv"
    languageId := "hebr1245"
    parameterId := "calculus"
    form := "taxšiv"
    segments := ["t", "a", "x", "š", "i", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3i)"⟩
    ]
    columns := [("Root", "xšb"), ("Pattern", "taCCiC"), ("Category", "n")] }

def qalat : Form :=
  { id := "arad2005_qalat"
    languageId := "hebr1245"
    parameterId := "to_absorb_receive"
    form := "qalat"
    segments := ["q", "a", "l", "a", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4a)"⟩
    ]
    columns := [("Root", "qlt"), ("Binyan", "1"), ("Category", "v")] }

def miqlat : Form :=
  { id := "arad2005_miqlat"
    languageId := "hebr1245"
    parameterId := "a_shelter"
    form := "miqlat"
    segments := ["m", "i", "q", "l", "a", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4c)"⟩
    ]
    columns := [("Root", "qlt"), ("Pattern", "miCCaC"), ("Category", "n")] }

def maqlet : Form :=
  { id := "arad2005_maqlet"
    languageId := "hebr1245"
    parameterId := "a_receiver"
    form := "maqlet"
    segments := ["m", "a", "q", "l", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4d)"⟩
    ]
    columns := [("Root", "qlt"), ("Pattern", "maCCeC"), ("Category", "n")] }

def taqlit : Form :=
  { id := "arad2005_taqlit"
    languageId := "hebr1245"
    parameterId := "a_record"
    form := "taqlit"
    segments := ["t", "a", "q", "l", "i", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4e)"⟩
    ]
    columns := [("Root", "qlt"), ("Pattern", "taCCiC"), ("Category", "n")] }

def qaletet : Form :=
  { id := "arad2005_qaletet"
    languageId := "hebr1245"
    parameterId := "a_cassette"
    form := "qaletet"
    segments := ["q", "a", "l", "e", "t", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4f)"⟩
    ]
    columns := [("Root", "qlt"), ("Pattern", "CaCCeCet"), ("Category", "n")] }

def qelet : Form :=
  { id := "arad2005_qelet"
    languageId := "hebr1245"
    parameterId := "input"
    form := "qelet"
    segments := ["q", "e", "l", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4g)"⟩
    ]
    columns := [("Root", "qlt"), ("Pattern", "CeCeC"), ("Category", "n")] }

def sagar : Form :=
  { id := "arad2005_sagar"
    languageId := "hebr1245"
    parameterId := "close"
    form := "sagar"
    segments := ["s", "a", "g", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5a)"⟩
    ]
    columns := [("Root", "sgr"), ("Binyan", "1"), ("Category", "v")] }

def hisgir : Form :=
  { id := "arad2005_hisgir"
    languageId := "hebr1245"
    parameterId := "extradite"
    form := "hisgir"
    segments := ["h", "i", "s", "g", "i", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5b)"⟩
    ]
    columns := [("Root", "sgr"), ("Binyan", "5"), ("Category", "v")] }

def histager : Form :=
  { id := "arad2005_histager"
    languageId := "hebr1245"
    parameterId := "cocoon_oneself"
    form := "histager"
    segments := ["h", "i", "s", "t", "a", "g", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5c)"⟩
    ]
    columns := [("Root", "sgr"), ("Binyan", "7"), ("Category", "v")] }

def seger : Form :=
  { id := "arad2005_seger"
    languageId := "hebr1245"
    parameterId := "closure"
    form := "seger"
    segments := ["s", "e", "g", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5d)"⟩
    ]
    columns := [("Root", "sgr"), ("Pattern", "CeCeC"), ("Category", "n")] }

def sograyim : Form :=
  { id := "arad2005_sograyim"
    languageId := "hebr1245"
    parameterId := "parentheses"
    form := "sograyim"
    segments := ["s", "o", "g", "r", "a", "y", "i", "m"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5e)"⟩
    ]
    columns := [("Root", "sgr"), ("Pattern", "CoCCayim"), ("Category", "n")] }

def misgeret : Form :=
  { id := "arad2005_misgeret"
    languageId := "hebr1245"
    parameterId := "frame"
    form := "misgeret"
    segments := ["m", "i", "s", "g", "e", "r", "+", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32b)"⟩,
      ⟨"arad-2005", "Ch. 7 (5f)"⟩,
      ⟨"arad-2005", "Ch. 7 (6a)"⟩
    ]
    columns := [("Root", "sgr"), ("Pattern", "miCCeCet"), ("Category", "n")] }

def patax : Form :=
  { id := "arad2005_patax"
    languageId := "hebr1245"
    parameterId := "open_causative"
    form := "patax"
    segments := ["p", "a", "t", "a", "x"]
    source := [
      ⟨"arad-2005", "Ch. 6 (47)"⟩
    ]
    columns := [("Root", "ptx"), ("Binyan", "1"), ("Category", "v"), ("Conjugation", "1"), ("Alternant", "causative")] }

def niftax : Form :=
  { id := "arad2005_niftax"
    languageId := "hebr1245"
    parameterId := "open_inchoative"
    form := "niftax"
    segments := ["n", "i", "f", "t", "a", "x"]
    source := [
      ⟨"arad-2005", "Ch. 6 (47)"⟩
    ]
    columns := [("Root", "ptx"), ("Binyan", "2"), ("Category", "v"), ("Conjugation", "1"), ("Alternant", "inchoative")] }

def qafa : Form :=
  { id := "arad2005_qafa"
    languageId := "hebr1245"
    parameterId := "freeze_inchoative"
    form := "qafaʔ"
    segments := ["q", "a", "f", "a", "ʔ"]
    source := [
      ⟨"arad-2005", "Ch. 6 (48)"⟩
    ]
    columns := [("Root", "qpʔ"), ("Binyan", "1"), ("Category", "v"), ("Conjugation", "2"), ("Alternant", "non-causative")] }

def hiqpi : Form :=
  { id := "arad2005_hiqpi"
    languageId := "hebr1245"
    parameterId := "freeze_causative"
    form := "hiqpiʔ"
    segments := ["h", "i", "q", "p", "i", "ʔ"]
    source := [
      ⟨"arad-2005", "Ch. 6 (48)"⟩
    ]
    columns := [("Root", "qpʔ"), ("Binyan", "5"), ("Category", "v"), ("Conjugation", "2"), ("Alternant", "causative")] }

def namas : Form :=
  { id := "arad2005_namas"
    languageId := "hebr1245"
    parameterId := "melt_inchoative"
    form := "namas"
    segments := ["n", "a", "m", "a", "s"]
    source := [
      ⟨"arad-2005", "Ch. 6 (49)"⟩
    ]
    columns := [("Root", "mss"), ("Binyan", "2"), ("Category", "v"), ("Conjugation", "3"), ("Alternant", "inchoative")] }

def hemes : Form :=
  { id := "arad2005_hemes"
    languageId := "hebr1245"
    parameterId := "melt_causative"
    form := "hemes"
    segments := ["h", "e", "m", "e", "s"]
    source := [
      ⟨"arad-2005", "Ch. 6 (49)"⟩
    ]
    columns := [("Root", "mss"), ("Binyan", "5"), ("Category", "v"), ("Conjugation", "3"), ("Alternant", "causative")] }

def hitxamem : Form :=
  { id := "arad2005_hitxamem"
    languageId := "hebr1245"
    parameterId := "heat_inchoative"
    form := "hitxamem"
    segments := ["h", "i", "t", "x", "a", "m", "e", "m"]
    source := [
      ⟨"arad-2005", "Ch. 6 (50)"⟩
    ]
    columns := [("Root", "xmm"), ("Binyan", "7"), ("Category", "v"), ("Conjugation", "4"), ("Alternant", "inchoative")] }

def ximem : Form :=
  { id := "arad2005_ximem"
    languageId := "hebr1245"
    parameterId := "heat_causative"
    form := "ximem"
    segments := ["x", "i", "m", "e", "m"]
    source := [
      ⟨"arad-2005", "Ch. 6 (50)"⟩
    ]
    columns := [("Root", "xmm"), ("Binyan", "3"), ("Category", "v"), ("Conjugation", "4"), ("Alternant", "causative")] }

def hitbaher : Form :=
  { id := "arad2005_hitbaher"
    languageId := "hebr1245"
    parameterId := "become_clear"
    form := "hitbaher"
    segments := ["h", "i", "t", "b", "a", "h", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 6 (51)"⟩
    ]
    columns := [("Root", "bhr"), ("Binyan", "7"), ("Category", "v"), ("Conjugation", "5"), ("Alternant", "inchoative")] }

def hivhir : Form :=
  { id := "arad2005_hivhir"
    languageId := "hebr1245"
    parameterId := "make_clear"
    form := "hivhir"
    segments := ["h", "i", "v", "h", "i", "r"]
    source := [
      ⟨"arad-2005", "Ch. 6 (51)"⟩
    ]
    columns := [("Root", "bhr"), ("Binyan", "5"), ("Category", "v"), ("Conjugation", "5"), ("Alternant", "causative")] }

def heedim_inchoative : Form :=
  { id := "arad2005_heedim_inchoative"
    languageId := "hebr1245"
    parameterId := "be_red"
    form := "heʔedim"
    segments := ["h", "e", "ʔ", "e", "d", "i", "m"]
    source := [
      ⟨"arad-2005", "Ch. 6 (52)"⟩
    ]
    columns := [("Root", "ʔdm"), ("Binyan", "5"), ("Category", "v"), ("Conjugation", "6"), ("Alternant", "inchoative")] }

def heedim_causative : Form :=
  { id := "arad2005_heedim_causative"
    languageId := "hebr1245"
    parameterId := "redden"
    form := "heʔedim"
    segments := ["h", "e", "ʔ", "e", "d", "i", "m"]
    source := [
      ⟨"arad-2005", "Ch. 6 (52)"⟩
    ]
    columns := [("Root", "ʔdm"), ("Binyan", "5"), ("Category", "v"), ("Conjugation", "6"), ("Alternant", "causative")] }

def taqciv : Form :=
  { id := "arad2005_taqciv"
    languageId := "hebr1245"
    parameterId := "budget"
    form := "taqciv"
    segments := ["t", "a", "q", "c", "i", "v"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12a)"⟩
    ]
    columns := [("Category", "n")] }

def tiqcev : Form :=
  { id := "arad2005_tiqcev"
    languageId := "hebr1245"
    parameterId := "to_budget"
    form := "tiqcev"
    segments := ["t", "i", "q", "c", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12a)"⟩
    ]
    columns := [("Category", "v")] }

def telefon : Form :=
  { id := "arad2005_telefon"
    languageId := "hebr1245"
    parameterId := "telephone"
    form := "telefon"
    segments := ["t", "e", "l", "e", "f", "o", "n"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29a)"⟩
    ]
    columns := [("Category", "n")] }

def tilfen : Form :=
  { id := "arad2005_tilfen"
    languageId := "hebr1245"
    parameterId := "to_telephone"
    form := "tilfen"
    segments := ["t", "i", "l", "f", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29a)"⟩
    ]
    columns := [("Binyan", "3"), ("Category", "v")] }

def mastul : Form :=
  { id := "arad2005_mastul"
    languageId := "hebr1245"
    parameterId := "drunk"
    form := "mastul"
    segments := ["m", "a", "s", "t", "u", "l"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29b)"⟩
    ]
    columns := [("Category", "adj")] }

def hitmastel : Form :=
  { id := "arad2005_hitmastel"
    languageId := "hebr1245"
    parameterId := "to_get_drunk"
    form := "hitmastel"
    segments := ["h", "i", "t", "m", "a", "s", "t", "e", "l"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29b)"⟩
    ]
    columns := [("Binyan", "7"), ("Category", "v")] }

def xrop : Form :=
  { id := "arad2005_xrop"
    languageId := "hebr1245"
    parameterId := "a_snooze"
    form := "xrop"
    segments := ["x", "r", "o", "p"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29c)"⟩
    ]
    columns := [("Category", "n")] }

def xarap : Form :=
  { id := "arad2005_xarap"
    languageId := "hebr1245"
    parameterId := "to_snooze"
    form := "xarap"
    segments := ["x", "a", "r", "a", "p"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29c)"⟩
    ]
    columns := [("Binyan", "1"), ("Category", "v")] }

def mixshev : Form :=
  { id := "arad2005_mixshev"
    languageId := "hebr1245"
    parameterId := "to_computerize"
    form := "mixšev"
    segments := ["m", "i", "x", "š", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12b)"⟩,
      ⟨"arad-2005", "Ch. 2 (29d)"⟩
    ]
    columns := [("Binyan", "3"), ("Category", "v")] }

def taxzuqa : Form :=
  { id := "arad2005_taxzuqa"
    languageId := "hebr1245"
    parameterId := "maintenance"
    form := "taxzuqa"
    segments := ["t", "a", "x", "z", "u", "q", "+", "a"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32a)"⟩
    ]
    columns := [("Root", "xzq"), ("Category", "n")] }

def tixzeq : Form :=
  { id := "arad2005_tixzeq"
    languageId := "hebr1245"
    parameterId := "to_maintain"
    form := "tixzeq"
    segments := ["t", "i", "x", "z", "e", "q"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32a)"⟩
    ]
    columns := [("Category", "v")] }

def misger : Form :=
  { id := "arad2005_misger"
    languageId := "hebr1245"
    parameterId := "to_frame"
    form := "misger"
    segments := ["m", "i", "s", "g", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32b)"⟩,
      ⟨"arad-2005", "Ch. 7 (6b)"⟩
    ]
    columns := [("Binyan", "3"), ("Category", "v")] }

def musgar : Form :=
  { id := "arad2005_musgar"
    languageId := "hebr1245"
    parameterId := "was_framed"
    form := "musgar"
    segments := ["m", "u", "s", "g", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 fn. 2"⟩
    ]
    columns := [("Binyan", "4"), ("Category", "v")] }

def cenzura : Form :=
  { id := "arad2005_cenzura"
    languageId := "hebr1245"
    parameterId := "censorship"
    form := "cenzura"
    segments := ["c", "e", "n", "z", "u", "r", "a"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32c)"⟩
    ]
    columns := [("Category", "n")] }

def cinzer : Form :=
  { id := "arad2005_cinzer"
    languageId := "hebr1245"
    parameterId := "to_censor"
    form := "cinzer"
    segments := ["c", "i", "n", "z", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32c)"⟩
    ]
    columns := [("Category", "v")] }

def qav : Form :=
  { id := "arad2005_qav"
    languageId := "hebr1245"
    parameterId := "line"
    form := "qav"
    segments := ["q", "a", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33a)"⟩
    ]
    columns := [("Category", "n")] }

def qivqev : Form :=
  { id := "arad2005_qivqev"
    languageId := "hebr1245"
    parameterId := "to_draw_a_dotted_line"
    form := "qivqev"
    segments := ["q", "i", "v", "q", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33a)"⟩
    ]
    columns := [("Category", "v")] }

def xov : Form :=
  { id := "arad2005_xov"
    languageId := "hebr1245"
    parameterId := "debt"
    form := "xov"
    segments := ["x", "o", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33b)"⟩
    ]
    columns := [("Category", "n")] }

def xiyev : Form :=
  { id := "arad2005_xiyev"
    languageId := "hebr1245"
    parameterId := "to_debit_oblige"
    form := "xiyev"
    segments := ["x", "i", "y", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33b)"⟩
    ]
    columns := [("Category", "v")] }

def faks : Form :=
  { id := "arad2005_faks"
    languageId := "hebr1245"
    parameterId := "fax"
    form := "faks"
    segments := ["f", "a", "k", "s"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33c)"⟩,
      ⟨"arad-2005", "Ch. 7 (41d)"⟩
    ]
    columns := [("Category", "n")] }

def fikses : Form :=
  { id := "arad2005_fikses"
    languageId := "hebr1245"
    parameterId := "to_fax"
    form := "fikses"
    segments := ["f", "i", "k", "s", "e", "s"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33c)"⟩,
      ⟨"arad-2005", "Ch. 7 (41d)"⟩
    ]
    columns := [("Category", "v")] }

def transfer : Form :=
  { id := "arad2005_transfer"
    languageId := "hebr1245"
    parameterId := "transfer"
    form := "transfer"
    segments := ["t", "r", "a", "n", "s", "f", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12d)"⟩,
      ⟨"arad-2005", "Ch. 7 (39a)"⟩
    ]
    columns := [("Category", "n")] }

def trinsfer : Form :=
  { id := "arad2005_trinsfer"
    languageId := "hebr1245"
    parameterId := "to_transfer"
    form := "trinsfer"
    segments := ["t", "r", "i", "n", "s", "f", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12d)"⟩,
      ⟨"arad-2005", "Ch. 7 (39a)"⟩
    ]
    columns := [("Category", "v")] }

def streptiz : Form :=
  { id := "arad2005_streptiz"
    languageId := "hebr1245"
    parameterId := "striptease"
    form := "streptiz"
    segments := ["s", "t", "r", "e", "p", "t", "i", "z"]
    source := [
      ⟨"arad-2005", "Ch. 7 (39b)"⟩
    ]
    columns := [("Category", "n")] }

def striptez : Form :=
  { id := "arad2005_striptez"
    languageId := "hebr1245"
    parameterId := "to_perform_a_striptease"
    form := "striptez"
    segments := ["s", "t", "r", "i", "p", "t", "e", "z"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12e)"⟩,
      ⟨"arad-2005", "Ch. 7 (39b)"⟩
    ]
    columns := [("Category", "v")] }

def sinxroni : Form :=
  { id := "arad2005_sinxroni"
    languageId := "hebr1245"
    parameterId := "synchronic"
    form := "sinxroni"
    segments := ["s", "i", "n", "x", "r", "o", "n", "i"]
    source := [
      ⟨"arad-2005", "Ch. 7 (39c)"⟩
    ]
    columns := [("Category", "adj")] }

def sinxren : Form :=
  { id := "arad2005_sinxren"
    languageId := "hebr1245"
    parameterId := "synchronize"
    form := "sinxren"
    segments := ["s", "i", "n", "x", "r", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (39c)"⟩
    ]
    columns := [("Category", "v")] }

def qliq : Form :=
  { id := "arad2005_qliq"
    languageId := "hebr1245"
    parameterId := "a_click"
    form := "qliq"
    segments := ["q", "l", "i", "q"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12c)"⟩,
      ⟨"arad-2005", "Ch. 7 (40a)"⟩
    ]
    columns := [("Category", "n")] }

def hiqliq : Form :=
  { id := "arad2005_hiqliq"
    languageId := "hebr1245"
    parameterId := "to_click"
    form := "hiqliq"
    segments := ["h", "i", "q", "l", "i", "q"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12c)"⟩,
      ⟨"arad-2005", "Ch. 7 (40a)"⟩
    ]
    columns := [("Binyan", "5"), ("Category", "v")] }

def fliq : Form :=
  { id := "arad2005_fliq"
    languageId := "hebr1245"
    parameterId := "a_slap"
    form := "fliq"
    segments := ["f", "l", "i", "q"]
    source := [
      ⟨"arad-2005", "Ch. 7 (40b)"⟩
    ]
    columns := [("Category", "n")] }

def hifliq : Form :=
  { id := "arad2005_hifliq"
    languageId := "hebr1245"
    parameterId := "to_slap"
    form := "hifliq"
    segments := ["h", "i", "f", "l", "i", "q"]
    source := [
      ⟨"arad-2005", "Ch. 7 (40b)"⟩
    ]
    columns := [("Binyan", "5"), ("Category", "v")] }

def shpritz : Form :=
  { id := "arad2005_shpritz"
    languageId := "hebr1245"
    parameterId := "a_splash"
    form := "špritz"
    segments := ["š", "p", "r", "i", "t", "z"]
    source := [
      ⟨"arad-2005", "Ch. 7 (40c)"⟩
    ]
    columns := [("Category", "n")] }

def hishpritz : Form :=
  { id := "arad2005_hishpritz"
    languageId := "hebr1245"
    parameterId := "to_splash"
    form := "hišpritz"
    segments := ["h", "i", "š", "p", "r", "i", "t", "z"]
    source := [
      ⟨"arad-2005", "Ch. 7 (40c)"⟩
    ]
    columns := [("Binyan", "5"), ("Category", "v")] }

def xoq : Form :=
  { id := "arad2005_xoq"
    languageId := "hebr1245"
    parameterId := "law"
    form := "xoq"
    segments := ["x", "o", "q"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41a)"⟩
    ]
    columns := [("Category", "n")] }

def xoqeq : Form :=
  { id := "arad2005_xoqeq"
    languageId := "hebr1245"
    parameterId := "legislate"
    form := "xoqeq"
    segments := ["x", "o", "q", "e", "q"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41a)"⟩
    ]
    columns := [("Category", "v")] }

def qod : Form :=
  { id := "arad2005_qod"
    languageId := "hebr1245"
    parameterId := "code"
    form := "qod"
    segments := ["q", "o", "d"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41b)"⟩
    ]
    columns := [("Category", "n")] }

def qoded : Form :=
  { id := "arad2005_qoded"
    languageId := "hebr1245"
    parameterId := "codify"
    form := "qoded"
    segments := ["q", "o", "d", "e", "d"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41b)"⟩
    ]
    columns := [("Category", "v")] }

def dam : Form :=
  { id := "arad2005_dam"
    languageId := "hebr1245"
    parameterId := "blood"
    form := "dam"
    segments := ["d", "a", "m"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41c)"⟩
    ]
    columns := [("Category", "n")] }

def dimem : Form :=
  { id := "arad2005_dimem"
    languageId := "hebr1245"
    parameterId := "bleed"
    form := "dimem"
    segments := ["d", "i", "m", "e", "m"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41c)"⟩
    ]
    columns := [("Category", "v")] }

def chat : Form :=
  { id := "arad2005_chat"
    languageId := "hebr1245"
    parameterId := "chat"
    form := "čat"
    segments := ["č", "a", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41e)"⟩
    ]
    columns := [("Category", "n")] }

def chitet : Form :=
  { id := "arad2005_chitet"
    languageId := "hebr1245"
    parameterId := "to_chat"
    form := "čitet"
    segments := ["č", "i", "t", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41e)"⟩
    ]
    columns := [("Category", "v")] }

def all : List Form := [lamad, nilmad, siper, supar, hiqlit, huqlat, hitpalel, nipec, nupac, xileq, xulaq, histir, hustar, hifqid, hufqad, shamar, tirgem, qibel, hitrakex, shemen, shamenet, shuman, shamen, hishmin, shimen, xashav, xishev, hexshiv, hitxashev, maxshev, maxshava, xashivut, xeshbon, taxshiv, qalat, miqlat, maqlet, taqlit, qaletet, qelet, sagar, hisgir, histager, seger, sograyim, misgeret, patax, niftax, qafa, hiqpi, namas, hemes, hitxamem, ximem, hitbaher, hivhir, heedim_inchoative, heedim_causative, taqciv, tiqcev, telefon, tilfen, mastul, hitmastel, xrop, xarap, mixshev, taxzuqa, tixzeq, misger, musgar, cenzura, cinzer, qav, qivqev, xov, xiyev, faks, fikses, transfer, trinsfer, streptiz, striptez, sinxroni, sinxren, qliq, hiqliq, fliq, hifliq, shpritz, hishpritz, xoq, xoqeq, qod, qoded, dam, dimem, chat, chitet]

def relations : List FormRelation := [
  { id := "arad2005_tiqcev_from_taqciv", form := taqciv, target := tiqcev, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12a)"⟩
    ] },
  { id := "arad2005_tilfen_from_telefon", form := telefon, target := tilfen, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (29a)"⟩
    ] },
  { id := "arad2005_hitmastel_from_mastul", form := mastul, target := hitmastel, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (29b)"⟩
    ] },
  { id := "arad2005_xarap_from_xrop", form := xrop, target := xarap, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (29c)"⟩
    ] },
  { id := "arad2005_mixshev_from_maxshev", form := maxshev, target := mixshev, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12b)"⟩,
      ⟨"arad-2005", "Ch. 2 (29d)"⟩
    ] },
  { id := "arad2005_tixzeq_from_taxzuqa", form := taxzuqa, target := tixzeq, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (32a)"⟩
    ] },
  { id := "arad2005_misger_from_misgeret", form := misgeret, target := misger, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (32b)"⟩,
      ⟨"arad-2005", "Ch. 7 (6b)"⟩,
      ⟨"arad-2005", "Ch. 7 (7b)"⟩
    ] },
  { id := "arad2005_musgar_from_misgeret", form := misgeret, target := musgar, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 fn. 2"⟩
    ] },
  { id := "arad2005_cinzer_from_cenzura", form := cenzura, target := cinzer, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (32c)"⟩
    ] },
  { id := "arad2005_qivqev_from_qav", form := qav, target := qivqev, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (33a)"⟩
    ] },
  { id := "arad2005_xiyev_from_xov", form := xov, target := xiyev, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (33b)"⟩
    ] },
  { id := "arad2005_fikses_from_faks", form := faks, target := fikses, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (33c)"⟩,
      ⟨"arad-2005", "Ch. 7 (41d)"⟩
    ] },
  { id := "arad2005_trinsfer_from_transfer", form := transfer, target := trinsfer, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12d)"⟩,
      ⟨"arad-2005", "Ch. 7 (39a)"⟩
    ] },
  { id := "arad2005_striptez_from_streptiz", form := streptiz, target := striptez, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12e)"⟩,
      ⟨"arad-2005", "Ch. 7 (39b)"⟩
    ] },
  { id := "arad2005_sinxren_from_sinxroni", form := sinxroni, target := sinxren, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (39c)"⟩
    ] },
  { id := "arad2005_hiqliq_from_qliq", form := qliq, target := hiqliq, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12c)"⟩,
      ⟨"arad-2005", "Ch. 7 (40a)"⟩
    ] },
  { id := "arad2005_hifliq_from_fliq", form := fliq, target := hifliq, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (40b)"⟩
    ] },
  { id := "arad2005_hishpritz_from_shpritz", form := shpritz, target := hishpritz, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (40c)"⟩
    ] },
  { id := "arad2005_xoqeq_from_xoq", form := xoq, target := xoqeq, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (41a)"⟩
    ] },
  { id := "arad2005_qoded_from_qod", form := qod, target := qoded, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (41b)"⟩
    ] },
  { id := "arad2005_dimem_from_dam", form := dam, target := dimem, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (41c)"⟩
    ] },
  { id := "arad2005_chitet_from_chat", form := chat, target := chitet, relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (41e)"⟩
    ] }
]

end Arad2005.Forms
