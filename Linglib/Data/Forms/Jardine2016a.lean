module

public import Linglib.Data.Forms.Schema

/-!
# `Jardine2016a` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Jardine2016a.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Jardine2016a.Forms`.
-/

@[expose] public section

namespace Jardine2016a.Forms

open Data.Forms

def f_8_kikopo : Form :=
  { id := "jardine2016a_8_kikopo"
    languageId := "gand1255"
    parameterId := "cup"
    form := "kikópo"
    segments := ["k", "i", "k", "ó", "p", "o"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ]
    columns := [("Underlying", "/ki-kópo/"), ("UnderlyingTones", "OHO"), ("SurfaceTones", "OHO")] }

def f_8_kisiki : Form :=
  { id := "jardine2016a_8_kisiki"
    languageId := "gand1255"
    parameterId := "log"
    form := "kisikî"
    segments := ["k", "i", "s", "i", "k", "î"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ]
    columns := [("Underlying", "/ki-sikí/"), ("UnderlyingTones", "OOH"), ("SurfaceTones", "OOH")] }

def f_8_kitabo : Form :=
  { id := "jardine2016a_8_kitabo"
    languageId := "gand1255"
    parameterId := "book"
    form := "kitabo"
    segments := ["k", "i", "t", "a", "b", "o"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ]
    columns := [("Underlying", "/ki-tabo/"), ("UnderlyingTones", "OOO"), ("SurfaceTones", "OOO")] }

def f_8_mutunda : Form :=
  { id := "jardine2016a_8_mutunda"
    languageId := "gand1255"
    parameterId := "seller"
    form := "mutunda"
    segments := ["m", "u", "t", "u", "n", "d", "a"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ]
    columns := [("Underlying", "/mu-tund-a/"), ("UnderlyingTones", "OOO"), ("SurfaceTones", "OOO")] }

def f_8_mutema : Form :=
  { id := "jardine2016a_8_mutema"
    languageId := "gand1255"
    parameterId := "chopper"
    form := "mutéma"
    segments := ["m", "u", "t", "é", "m", "a"]
    source := [
      ⟨"jardine-2016a", "(8)"⟩
    ]
    columns := [("Underlying", "/mu-tém-a/"), ("UnderlyingTones", "OHO"), ("SurfaceTones", "OHO")] }

def f_9a : Form :=
  { id := "jardine2016a_9a"
    languageId := "gand1255"
    parameterId := "cup_seller"
    form := "mutunda-bikópo"
    segments := ["m", "u", "t", "u", "n", "d", "a", "+", "b", "i", "k", "ó", "p", "o"]
    source := [
      ⟨"jardine-2016a", "(9a)"⟩
    ]
    columns := [("Underlying", "/mu-tund-a+bi-kópo/"), ("UnderlyingTones", "OOOOHO"), ("SurfaceTones", "OOOOHO")] }

def f_9b : Form :=
  { id := "jardine2016a_9b"
    languageId := "gand1255"
    parameterId := "log_chopper"
    form := "mutémá-bísíkî"
    segments := ["m", "u", "t", "é", "m", "á", "+", "b", "í", "s", "í", "k", "î"]
    source := [
      ⟨"jardine-2016a", "(9b)"⟩
    ]
    columns := [("Underlying", "/mu-tém-a+bi-sikí/"), ("UnderlyingTones", "OHOOOH"), ("SurfaceTones", "OHHHHH")] }

def f_10b : Form :=
  { id := "jardine2016a_10b"
    languageId := "gand1255"
    parameterId := "we_were_seen_by_walusimbi"
    form := "tw-áá-láb-wá wálúsimbi"
    segments := ["t", "w", "+", "á", "á", "+", "l", "á", "b", "+", "w", "á", "_", "w", "á", "l", "ú", "s", "i", "m", "b", "i"]
    source := [
      ⟨"jardine-2016a", "(10b)"⟩
    ]
    columns := [("Underlying", "/tw-áa-láb-w-a walúsimbi/"), ("UnderlyingTones", "HHHOOHOO"), ("SurfaceTones", "HHHHHHOO")] }

def f_12a : Form :=
  { id := "jardine2016a_12a"
    languageId := "gand1255"
    parameterId := "we_saw_those_of_walusimbi"
    form := "tw-áá-láb-á byáá-wálúsimbi"
    segments := ["t", "w", "+", "á", "á", "+", "l", "á", "b", "+", "á", "_", "b", "y", "á", "á", "+", "w", "á", "l", "ú", "s", "i", "m", "b", "i"]
    source := [
      ⟨"jardine-2016a", "(12a)"⟩
    ]
    columns := [("Underlying", "/tw-áa-láb-a byaa=walúsimbi/"), ("UnderlyingTones", "HHHOOOOHOO"), ("SurfaceTones", "HHHHHHHHOO")] }

def f_12b : Form :=
  { id := "jardine2016a_12b"
    languageId := "gand1255"
    parameterId := "we_went_with_those_of_walusimbi"
    form := "tw-áá-génd-á ná=byáá=bá=wálúsimbi"
    segments := ["t", "w", "+", "á", "á", "+", "g", "é", "n", "d", "+", "á", "_", "n", "á", "+", "b", "y", "á", "á", "+", "b", "á", "+", "w", "á", "l", "ú", "s", "i", "m", "b", "i"]
    source := [
      ⟨"jardine-2016a", "(12b)"⟩
    ]
    columns := [("Underlying", "/tw-áa-génd-a na=byaa=ba=walúsimbi/"), ("UnderlyingTones", "HHHOOOOOOHOO"), ("SurfaceTones", "HHHHHHHHHHOO")] }

def f_18b : Form :=
  { id := "jardine2016a_18b"
    languageId := "zulu1248"
    parameterId := "no_gloss_18b"
    form := "ámákhósꜜánà"
    segments := ["á", "m", "á", "k", "h", "ó", "s", "ꜜ", "á", "n", "à"]
    source := [
      ⟨"jardine-2016a", "(18b)"⟩
    ]
    columns := [("Underlying", "/ámàkhòsánà/"), ("UnderlyingTones", "HOOHO"), ("SurfaceTones", "HHHHO")] }

def f_21a : Form :=
  { id := "jardine2016a_21a"
    languageId := "sara1340"
    parameterId := "the_handsome_person"
    form := "dí hánsò sëmbë"
    segments := ["d", "í", "_", "h", "á", "n", "s", "ò", "_", "s", "ë", "m", "b", "ë"]
    source := [
      ⟨"jardine-2016a", "(21a)"⟩
    ]
    columns := [("Underlying", "/dí hánso sëmbë/"), ("UnderlyingTones", "HHOOO"), ("SurfaceTones", "HHOOO")] }

def f_21b : Form :=
  { id := "jardine2016a_21b"
    languageId := "sara1340"
    parameterId := "the_handsome_man"
    form := "dí hánsó wómì"
    segments := ["d", "í", "_", "h", "á", "n", "s", "ó", "_", "w", "ó", "m", "ì"]
    source := [
      ⟨"jardine-2016a", "(21b)"⟩
    ]
    columns := [("Underlying", "/dí hánso wómi/"), ("UnderlyingTones", "HHOHO"), ("SurfaceTones", "HHHHO")] }

def f_21c : Form :=
  { id := "jardine2016a_21c"
    languageId := "sara1340"
    parameterId := "the_handsome_woman"
    form := "dí hánsó mújêë"
    segments := ["d", "í", "_", "h", "á", "n", "s", "ó", "_", "m", "ú", "j", "ê", "ë"]
    source := [
      ⟨"jardine-2016a", "(21c)"⟩
    ]
    columns := [("Underlying", "/dí hánso mujêE/"), ("UnderlyingTones", "HHOOHO"), ("SurfaceTones", "HHHHHO")] }

def f_21d : Form :=
  { id := "jardine2016a_21d"
    languageId := "sara1340"
    parameterId := "the_iguana_there_has_eggs"
    form := "dí wájámáká=dé á óbo"
    segments := ["d", "í", "_", "w", "á", "j", "á", "m", "á", "k", "á", "+", "d", "é", "_", "á", "_", "ó", "b", "o"]
    source := [
      ⟨"jardine-2016a", "(21d)"⟩
    ]
    columns := [("Underlying", "/dí wajamáka=dé á óbo/"), ("UnderlyingTones", "HOOHOHHHO"), ("SurfaceTones", "HHHHHHHHO")] }

def f_21e : Form :=
  { id := "jardine2016a_21e"
    languageId := "sara1340"
    parameterId := "the_strong_american_man"
    form := "tàángá ámêêká wómì"
    segments := ["t", "à", "á", "n", "g", "á", "_", "á", "m", "ê", "ê", "k", "á", "_", "w", "ó", "m", "ì"]
    source := [
      ⟨"jardine-2016a", "(21e)"⟩
    ]
    columns := [("Underlying", "/taánga amEEká wómi/"), ("UnderlyingTones", "OHOOOOHHO"), ("SurfaceTones", "OHHHHHHHO")] }

def all : List Form := [f_8_kikopo, f_8_kisiki, f_8_kitabo, f_8_mutunda, f_8_mutema, f_9a, f_9b, f_10b, f_12a, f_12b, f_18b, f_21a, f_21b, f_21c, f_21d, f_21e]

def relations : List FormRelation := []

end Jardine2016a.Forms
