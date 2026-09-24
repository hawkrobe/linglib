module

public import Linglib.Data.Forms.Schema

/-!
# `Karlsson2017` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Karlsson2017.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Karlsson2017.Forms`.
-/

@[expose] public section

namespace Karlsson2017.Forms

open Data.Forms

def auto : Form :=
  { id := "karlsson2017_auto"
    languageId := "finn1318"
    parameterId := "car"
    form := "auto"
    segments := ["auto"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def auton : Form :=
  { id := "karlsson2017_auton"
    languageId := "finn1318"
    parameterId := "car"
    form := "auton"
    segments := ["auto", "n"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def hanet : Form :=
  { id := "karlsson2017_hanet"
    languageId := "finn1318"
    parameterId := "him_her"
    form := "hänet"
    segments := ["häne", "t"]
    comment := "The accusative ending is confined to the personal pronouns."
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "acc"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def maitoa : Form :=
  { id := "karlsson2017_maitoa"
    languageId := "finn1318"
    parameterId := "milk"
    form := "maitoa"
    segments := ["maito", "a"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def vetta : Form :=
  { id := "karlsson2017_vetta"
    languageId := "finn1318"
    parameterId := "water"
    form := "vettä"
    segments := ["vet", "tä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def perhetta : Form :=
  { id := "karlsson2017_perhetta"
    languageId := "finn1318"
    parameterId := "family"
    form := "perhettä"
    segments := ["perhe", "ttä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def autossa : Form :=
  { id := "karlsson2017_autossa"
    languageId := "finn1318"
    parameterId := "car"
    form := "autossa"
    segments := ["auto", "ssa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def autosta : Form :=
  { id := "karlsson2017_autosta"
    languageId := "finn1318"
    parameterId := "car"
    form := "autosta"
    segments := ["auto", "sta"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ela"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def autoon : Form :=
  { id := "karlsson2017_autoon"
    languageId := "finn1318"
    parameterId := "car"
    form := "autoon"
    segments := ["auto", "on"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def maahan : Form :=
  { id := "karlsson2017_maahan"
    languageId := "finn1318"
    parameterId := "country"
    form := "maahan"
    segments := ["maa", "han"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def porvooseen : Form :=
  { id := "karlsson2017_porvooseen"
    languageId := "finn1318"
    parameterId := "porvoo"
    form := "Porvooseen"
    segments := ["Porvoo", "seen"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def poydalla : Form :=
  { id := "karlsson2017_poydalla"
    languageId := "finn1318"
    parameterId := "table"
    form := "pöydällä"
    segments := ["pöydä", "llä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def poydalta : Form :=
  { id := "karlsson2017_poydalta"
    languageId := "finn1318"
    parameterId := "table"
    form := "pöydältä"
    segments := ["pöydä", "ltä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "abl"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def poydalle : Form :=
  { id := "karlsson2017_poydalle"
    languageId := "finn1318"
    parameterId := "table"
    form := "pöydälle"
    segments := ["pöydä", "lle"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "all"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def opettajana : Form :=
  { id := "karlsson2017_opettajana"
    languageId := "finn1318"
    parameterId := "teacher"
    form := "opettajana"
    segments := ["opettaja", "na"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ess"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def opettajaksi : Form :=
  { id := "karlsson2017_opettajaksi"
    languageId := "finn1318"
    parameterId := "teacher"
    form := "opettajaksi"
    segments := ["opettaja", "ksi"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def vaimoineni : Form :=
  { id := "karlsson2017_vaimoineni"
    languageId := "finn1318"
    parameterId := "wife"
    form := "vaimoineni"
    segments := ["vaimo", "ine", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "com"), ("Possessor", "1sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def passitta : Form :=
  { id := "karlsson2017_passitta"
    languageId := "finn1318"
    parameterId := "passport"
    form := "passitta"
    segments := ["passi", "tta"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "abess"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def jalan : Form :=
  { id := "karlsson2017_jalan"
    languageId := "finn1318"
    parameterId := "foot"
    form := "jalan"
    segments := ["jala", "n"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "inst"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kirjani : Form :=
  { id := "karlsson2017_kirjani"
    languageId := "finn1318"
    parameterId := "book"
    form := "kirjani"
    segments := ["kirja", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "1sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kirjasi : Form :=
  { id := "karlsson2017_kirjasi"
    languageId := "finn1318"
    parameterId := "book"
    form := "kirjasi"
    segments := ["kirja", "si"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "2sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kirjansa : Form :=
  { id := "karlsson2017_kirjansa"
    languageId := "finn1318"
    parameterId := "book"
    form := "kirjansa"
    segments := ["kirja", "nsa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def pullo : Form :=
  { id := "karlsson2017_pullo"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pullo"
    segments := ["pullo"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def pullossa : Form :=
  { id := "karlsson2017_pullossa"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pullossa"
    segments := ["pullo", "ssa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def pulloni : Form :=
  { id := "karlsson2017_pulloni"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pulloni"
    segments := ["pullo", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "1sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def pullostani : Form :=
  { id := "karlsson2017_pullostani"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pullostani"
    segments := ["pullo", "sta", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ela"), ("Possessor", "1sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def hyllyssa : Form :=
  { id := "karlsson2017_hyllyssa"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllyssä"
    segments := ["hylly", "ssä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def hyllylla : Form :=
  { id := "karlsson2017_hyllylla"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllyllä"
    segments := ["hylly", "llä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def hyllysi : Form :=
  { id := "karlsson2017_hyllysi"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllysi"
    segments := ["hylly", "si"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "2sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def hyllyllesi : Form :=
  { id := "karlsson2017_hyllyllesi"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllyllesi"
    segments := ["hylly", "lle", "si"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "all"), ("Possessor", "2sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def taloon : Form :=
  { id := "karlsson2017_taloon"
    languageId := "finn1318"
    parameterId := "house"
    form := "taloon"
    segments := ["talo", "on"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def hyllynsa : Form :=
  { id := "karlsson2017_hyllynsa"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllynsä"
    segments := ["hylly", "nsä"]
    comment := "Also 'their shelf'."
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kadessani : Form :=
  { id := "karlsson2017_kadessani"
    languageId := "finn1318"
    parameterId := "hand"
    form := "kädessäni"
    segments := ["käde", "ssä", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", "1sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kateen : Form :=
  { id := "karlsson2017_kateen"
    languageId := "finn1318"
    parameterId := "hand"
    form := "käteen"
    segments := ["käte", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kateesi : Form :=
  { id := "karlsson2017_kateesi"
    languageId := "finn1318"
    parameterId := "hand"
    form := "käteesi"
    segments := ["käte", "e", "si"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", "2sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def katta : Form :=
  { id := "karlsson2017_katta"
    languageId := "finn1318"
    parameterId := "hand"
    form := "kättä"
    segments := ["kät", "tä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def sanoa : Form :=
  { id := "karlsson2017_sanoa"
    languageId := "finn1318"
    parameterId := "say"
    form := "sanoa"
    segments := ["sano", "a"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def syoda : Form :=
  { id := "karlsson2017_syoda"
    languageId := "finn1318"
    parameterId := "eat"
    form := "syödä"
    segments := ["syö", "dä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def juosta : Form :=
  { id := "karlsson2017_juosta"
    languageId := "finn1318"
    parameterId := "run"
    form := "juosta"
    segments := ["juos", "ta"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def juostaksemme : Form :=
  { id := "karlsson2017_juostaksemme"
    languageId := "finn1318"
    parameterId := "run"
    form := "juostaksemme"
    segments := ["juos", "ta", "kse", "mme"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", "1pl"), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def sanoessani : Form :=
  { id := "karlsson2017_sanoessani"
    languageId := "finn1318"
    parameterId := "say"
    form := "sanoessani"
    segments := ["sano", "e", "ssa", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", "1sg"), ("Infinitive", "e"), ("Number", ""), ("Clitic", "")] }

def syodessamme : Form :=
  { id := "karlsson2017_syodessamme"
    languageId := "finn1318"
    parameterId := "eat"
    form := "syödessämme"
    segments := ["syö", "de", "ssä", "mme"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", "1pl"), ("Infinitive", "e"), ("Number", ""), ("Clitic", "")] }

def juosten : Form :=
  { id := "karlsson2017_juosten"
    languageId := "finn1318"
    parameterId := "run"
    form := "juosten"
    segments := ["juos", "te", "n"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "inst"), ("Possessor", ""), ("Infinitive", "e"), ("Number", ""), ("Clitic", "")] }

def syomalla : Form :=
  { id := "karlsson2017_syomalla"
    languageId := "finn1318"
    parameterId := "eat"
    form := "syömällä"
    segments := ["syö", "mä", "llä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def sanomatta : Form :=
  { id := "karlsson2017_sanomatta"
    languageId := "finn1318"
    parameterId := "say"
    form := "sanomatta"
    segments := ["sano", "ma", "tta"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "abess"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def sanomaan : Form :=
  { id := "karlsson2017_sanomaan"
    languageId := "finn1318"
    parameterId := "say"
    form := "sanomaan"
    segments := ["sano", "ma", "an"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def puhuaksesi : Form :=
  { id := "karlsson2017_puhuaksesi"
    languageId := "finn1318"
    parameterId := "speak"
    form := "puhuaksesi"
    segments := ["puhu", "a", "kse", "si"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", "2sg"), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def puhumalla : Form :=
  { id := "karlsson2017_puhumalla"
    languageId := "finn1318"
    parameterId := "speak"
    form := "puhumalla"
    segments := ["puhu", "ma", "lla"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ]
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def autollani : Form :=
  { id := "karlsson2017_autollani"
    languageId := "finn1318"
    parameterId := "car"
    form := "autollani"
    segments := ["auto", "lla", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ade"), ("Possessor", "1sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def autostasi : Form :=
  { id := "karlsson2017_autostasi"
    languageId := "finn1318"
    parameterId := "car"
    form := "autostasi"
    segments := ["auto", "sta", "si"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ela"), ("Possessor", "2sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def autooni : Form :=
  { id := "karlsson2017_autooni"
    languageId := "finn1318"
    parameterId := "car"
    form := "autooni"
    segments := ["auto", "o", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", "1sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def laukkuni : Form :=
  { id := "karlsson2017_laukkuni"
    languageId := "finn1318"
    parameterId := "bag"
    form := "laukkuni"
    segments := ["laukku", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "1sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def laukkusi : Form :=
  { id := "karlsson2017_laukkusi"
    languageId := "finn1318"
    parameterId := "bag"
    form := "laukkusi"
    segments := ["laukku", "si"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "2sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def laukkunsa_3sg : Form :=
  { id := "karlsson2017_laukkunsa_3sg"
    languageId := "finn1318"
    parameterId := "bag"
    form := "laukkunsa"
    segments := ["laukku", "nsa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def laukkumme : Form :=
  { id := "karlsson2017_laukkumme"
    languageId := "finn1318"
    parameterId := "bag"
    form := "laukkumme"
    segments := ["laukku", "mme"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "1pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def laukkunne : Form :=
  { id := "karlsson2017_laukkunne"
    languageId := "finn1318"
    parameterId := "bag"
    form := "laukkunne"
    segments := ["laukku", "nne"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "2pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def laukkunsa_3pl : Form :=
  { id := "karlsson2017_laukkunsa_3pl"
    languageId := "finn1318"
    parameterId := "bag"
    form := "laukkunsa"
    segments := ["laukku", "nsa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "3pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def taloaan : Form :=
  { id := "karlsson2017_taloaan"
    languageId := "finn1318"
    parameterId := "house"
    form := "taloaan"
    segments := ["talo", "a", "an"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def vieraanaan : Form :=
  { id := "karlsson2017_vieraanaan"
    languageId := "finn1318"
    parameterId := "guest"
    form := "vieraanaan"
    segments := ["vieraa", "na", "an"]
    comment := "'as their guest'"
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ess"), ("Possessor", "3pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def saadakseen : Form :=
  { id := "karlsson2017_saadakseen"
    languageId := "finn1318"
    parameterId := "get"
    form := "saadakseen"
    segments := ["saa", "da", "kse", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", "3sg"), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def talossaan : Form :=
  { id := "karlsson2017_talossaan"
    languageId := "finn1318"
    parameterId := "house"
    form := "talossaan"
    segments := ["talo", "ssa", "an"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", "3pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def autollaan : Form :=
  { id := "karlsson2017_autollaan"
    languageId := "finn1318"
    parameterId := "car"
    form := "autollaan"
    segments := ["auto", "lla", "an"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ade"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def isalleen : Form :=
  { id := "karlsson2017_isalleen"
    languageId := "finn1318"
    parameterId := "father"
    form := "isälleen"
    segments := ["isä", "lle", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "all"), ("Possessor", "3pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def aidiltaan : Form :=
  { id := "karlsson2017_aidiltaan"
    languageId := "finn1318"
    parameterId := "mother"
    form := "äidiltään"
    segments := ["äidi", "ltä", "än"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "abl"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def aitiaan : Form :=
  { id := "karlsson2017_aitiaan"
    languageId := "finn1318"
    parameterId := "mother"
    form := "äitiään"
    segments := ["äiti", "ä", "än"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def talonsa : Form :=
  { id := "karlsson2017_talonsa"
    languageId := "finn1318"
    parameterId := "house"
    form := "taloonsa"
    segments := ["talo", "o", "nsa"]
    comment := "'into their house'"
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", "3pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def autonsa : Form :=
  { id := "karlsson2017_autonsa"
    languageId := "finn1318"
    parameterId := "car"
    form := "autonsa"
    segments := ["auto", "nsa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def isaansa : Form :=
  { id := "karlsson2017_isaansa"
    languageId := "finn1318"
    parameterId := "father"
    form := "isäänsä"
    segments := ["isä", "ä", "nsä"]
    comment := "Also the partitive singular."
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", "3pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def aitinsa : Form :=
  { id := "karlsson2017_aitinsa"
    languageId := "finn1318"
    parameterId := "mother"
    form := "äitinsä"
    segments := ["äiti", "nsä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def sanoakseni : Form :=
  { id := "karlsson2017_sanoakseni"
    languageId := "finn1318"
    parameterId := "say"
    form := "sanoakseni"
    segments := ["sano", "a", "kse", "ni"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", "1sg"), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def elaaksemme : Form :=
  { id := "karlsson2017_elaaksemme"
    languageId := "finn1318"
    parameterId := "live"
    form := "elääksemme"
    segments := ["elä", "ä", "kse", "mme"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", "1pl"), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def tavataksesi : Form :=
  { id := "karlsson2017_tavataksesi"
    languageId := "finn1318"
    parameterId := "meet"
    form := "tavataksesi"
    segments := ["tavat", "a", "kse", "si"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", "2sg"), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def juodakseen : Form :=
  { id := "karlsson2017_juodakseen"
    languageId := "finn1318"
    parameterId := "drink"
    form := "juodakseen"
    segments := ["juo", "da", "kse", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", "3sg"), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def ollaksenne : Form :=
  { id := "karlsson2017_ollaksenne"
    languageId := "finn1318"
    parameterId := "be"
    form := "ollaksenne"
    segments := ["ol", "la", "kse", "nne"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", "2pl"), ("Infinitive", "a"), ("Number", ""), ("Clitic", "")] }

def lepaamassa : Form :=
  { id := "karlsson2017_lepaamassa"
    languageId := "finn1318"
    parameterId := "rest"
    form := "lepäämässä"
    segments := ["lepää", "mä", "ssä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def lepaamaan : Form :=
  { id := "karlsson2017_lepaamaan"
    languageId := "finn1318"
    parameterId := "rest"
    form := "lepäämään"
    segments := ["lepää", "mä", "än"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def vetamalla : Form :=
  { id := "karlsson2017_vetamalla"
    languageId := "finn1318"
    parameterId := "pull"
    form := "vetämällä"
    segments := ["vetä", "mä", "llä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ]
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def mainitsematta : Form :=
  { id := "karlsson2017_mainitsematta"
    languageId := "finn1318"
    parameterId := "mention"
    form := "mainitsematta"
    segments := ["mainitse", "ma", "tta"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ]
    columns := [("Case", "abess"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def tekemasta : Form :=
  { id := "karlsson2017_tekemasta"
    languageId := "finn1318"
    parameterId := "do"
    form := "tekemästä"
    segments := ["teke", "mä", "stä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ]
    columns := [("Case", "ela"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def tuleman : Form :=
  { id := "karlsson2017_tuleman"
    languageId := "finn1318"
    parameterId := "come"
    form := "tuleman"
    segments := ["tule", "ma", "n"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ]
    columns := [("Case", "inst"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "")] }

def pullot : Form :=
  { id := "karlsson2017_pullot"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pullot"
    segments := ["pullo", "t"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", ""), ("Number", "t"), ("Clitic", "")] }

def pullokin : Form :=
  { id := "karlsson2017_pullokin"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pullokin"
    segments := ["pullo", "kin"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "kin")] }

def pulloista : Form :=
  { id := "karlsson2017_pulloista"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pulloista"
    segments := ["pullo", "i", "sta"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ela"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def pullossahan : Form :=
  { id := "karlsson2017_pullossahan"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pullossahan"
    segments := ["pullo", "ssa", "han"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "hAn")] }

def pullotkin : Form :=
  { id := "karlsson2017_pullotkin"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pullotkin"
    segments := ["pullo", "t", "kin"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", ""), ("Number", "t"), ("Clitic", "kin")] }

def pullossasiko : Form :=
  { id := "karlsson2017_pullossasiko"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pullossasiko"
    segments := ["pullo", "ssa", "si", "ko"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", "2sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "kO")] }

def pulloissamme : Form :=
  { id := "karlsson2017_pulloissamme"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pulloissamme"
    segments := ["pullo", "i", "ssa", "mme"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", "1pl"), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def pulloistakaan : Form :=
  { id := "karlsson2017_pulloistakaan"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pulloistakaan"
    segments := ["pullo", "i", "sta", "kaan"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ela"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "kAAn")] }

def pulloissannekin : Form :=
  { id := "karlsson2017_pulloissannekin"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pulloissannekin"
    segments := ["pullo", "i", "ssa", "nne", "kin"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", "2pl"), ("Infinitive", ""), ("Number", "i"), ("Clitic", "kin")] }

def hyllyltako : Form :=
  { id := "karlsson2017_hyllyltako"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllyltäkö"
    segments := ["hylly", "ltä", "kö"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "abl"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "kO")] }

def hyllytko : Form :=
  { id := "karlsson2017_hyllytko"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllytkö"
    segments := ["hylly", "t", "kö"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", ""), ("Number", "t"), ("Clitic", "kO")] }

def hyllynhan : Form :=
  { id := "karlsson2017_hyllynhan"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllynhän"
    segments := ["hylly", "n", "hän"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "hAn")] }

def talonsako : Form :=
  { id := "karlsson2017_talonsako"
    languageId := "finn1318"
    parameterId := "house"
    form := "talonsako"
    segments := ["talo", "nsa", "ko"]
    comment := "Also 'their house?'."
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "kO")] }

def hyllyillamme : Form :=
  { id := "karlsson2017_hyllyillamme"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllyillämme"
    segments := ["hylly", "i", "llä", "mme"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ade"), ("Possessor", "1pl"), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def kasi : Form :=
  { id := "karlsson2017_kasi"
    languageId := "finn1318"
    parameterId := "hand"
    form := "käsi"
    segments := ["käsi"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kadet : Form :=
  { id := "karlsson2017_kadet"
    languageId := "finn1318"
    parameterId := "hand"
    form := "kädet"
    segments := ["käde", "t"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", ""), ("Number", "t"), ("Clitic", "")] }

def kasissammehan : Form :=
  { id := "karlsson2017_kasissammehan"
    languageId := "finn1318"
    parameterId := "hand"
    form := "käsissämmehän"
    segments := ["käs", "i", "ssä", "mme", "hän"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", "1pl"), ("Infinitive", ""), ("Number", "i"), ("Clitic", "hAn")] }

def lepaamaanko : Form :=
  { id := "karlsson2017_lepaamaanko"
    languageId := "finn1318"
    parameterId := "rest"
    form := "lepäämäänkö"
    segments := ["lepää", "mä", "än", "kö"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "kO")] }

def vetamallakin : Form :=
  { id := "karlsson2017_vetamallakin"
    languageId := "finn1318"
    parameterId := "pull"
    form := "vetämälläkin"
    segments := ["vetä", "mä", "llä", "kin"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ]
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "kin")] }

def mainitsemattakaan : Form :=
  { id := "karlsson2017_mainitsemattakaan"
    languageId := "finn1318"
    parameterId := "mention"
    form := "mainitsemattakaan"
    segments := ["mainitse", "ma", "tta", "kaan"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ]
    columns := [("Case", "abess"), ("Possessor", ""), ("Infinitive", "ma"), ("Number", ""), ("Clitic", "kAAn")] }

def oppiakseenhan : Form :=
  { id := "karlsson2017_oppiakseenhan"
    languageId := "finn1318"
    parameterId := "learn"
    form := "oppiakseenhan"
    segments := ["oppi", "a", "kse", "en", "han"]
    comment := "Also 'in order for them to learn'."
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", "3sg"), ("Infinitive", "a"), ("Number", ""), ("Clitic", "hAn")] }

def maatamme : Form :=
  { id := "karlsson2017_maatamme"
    languageId := "finn1318"
    parameterId := "country"
    form := "maatamme"
    segments := ["maa", "ta", "mme"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", "1pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def poikannekin : Form :=
  { id := "karlsson2017_poikannekin"
    languageId := "finn1318"
    parameterId := "son"
    form := "poikannekin"
    segments := ["poika", "nne", "kin"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "2pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "kin")] }

def aidiltanihan : Form :=
  { id := "karlsson2017_aidiltanihan"
    languageId := "finn1318"
    parameterId := "mother"
    form := "äidiltänihän"
    segments := ["äidi", "ltä", "ni", "hän"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "abl"), ("Possessor", "1sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "hAn")] }

def isallesiko : Form :=
  { id := "karlsson2017_isallesiko"
    languageId := "finn1318"
    parameterId := "father"
    form := "isällesikö"
    segments := ["isä", "lle", "si", "kö"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "all"), ("Possessor", "2sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "kO")] }

def maahamme : Form :=
  { id := "karlsson2017_maahamme"
    languageId := "finn1318"
    parameterId := "country"
    form := "maahamme"
    segments := ["maa", "ha", "mme"]
    comment := "The source glosses the form 'into her/his/their country'."
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", "1pl"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def perhettaan : Form :=
  { id := "karlsson2017_perhettaan"
    languageId := "finn1318"
    parameterId := "family"
    form := "perhettään"
    segments := ["perhe", "ttä", "än"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def talojaan : Form :=
  { id := "karlsson2017_talojaan"
    languageId := "finn1318"
    parameterId := "house"
    form := "talojaan"
    segments := ["talo", "j", "a", "an"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def renkaitaan : Form :=
  { id := "karlsson2017_renkaitaan"
    languageId := "finn1318"
    parameterId := "ring"
    form := "renkaitaan"
    segments := ["renka", "i", "ta", "an"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def paataan : Form :=
  { id := "karlsson2017_paataan"
    languageId := "finn1318"
    parameterId := "head"
    form := "päätään"
    segments := ["pää", "tä", "än"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def taloansa : Form :=
  { id := "karlsson2017_taloansa"
    languageId := "finn1318"
    parameterId := "house"
    form := "taloansa"
    segments := ["talo", "a", "nsa"]
    comment := "The archaic alternative to talo-a-an."
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kalansa : Form :=
  { id := "karlsson2017_kalansa"
    languageId := "finn1318"
    parameterId := "fish"
    form := "kalansa"
    segments := ["kala", "nsa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kalaansa_ill : Form :=
  { id := "karlsson2017_kalaansa_ill"
    languageId := "finn1318"
    parameterId := "fish"
    form := "kalaansa"
    segments := ["kala", "a", "nsa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kalaansa_part : Form :=
  { id := "karlsson2017_kalaansa_part"
    languageId := "finn1318"
    parameterId := "fish"
    form := "kalaansa"
    segments := ["kala", "a", "nsa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", ""), ("Clitic", "")] }

def kaloihinsa : Form :=
  { id := "karlsson2017_kaloihinsa"
    languageId := "finn1318"
    parameterId := "fish"
    form := "kaloihinsa"
    segments := ["kalo", "i", "hi", "nsa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def taloissa : Form :=
  { id := "karlsson2017_taloissa"
    languageId := "finn1318"
    parameterId := "house"
    form := "taloissa"
    segments := ["talo", "i", "ssa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def taloihin : Form :=
  { id := "karlsson2017_taloihin"
    languageId := "finn1318"
    parameterId := "house"
    form := "taloihin"
    segments := ["talo", "i", "hin"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def taloina : Form :=
  { id := "karlsson2017_taloina"
    languageId := "finn1318"
    parameterId := "house"
    form := "taloina"
    segments := ["talo", "i", "na"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "ess"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def taloille : Form :=
  { id := "karlsson2017_taloille"
    languageId := "finn1318"
    parameterId := "house"
    form := "taloille"
    segments := ["talo", "i", "lle"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "all"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def taloiksi : Form :=
  { id := "karlsson2017_taloiksi"
    languageId := "finn1318"
    parameterId := "house"
    form := "taloiksi"
    segments := ["talo", "i", "ksi"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "transl"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def hyllyja : Form :=
  { id := "karlsson2017_hyllyja"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllyjä"
    segments := ["hylly", "j", "ä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def hyllyjen : Form :=
  { id := "karlsson2017_hyllyjen"
    languageId := "finn1318"
    parameterId := "shelf"
    form := "hyllyjen"
    segments := ["hylly", "j", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def pulloja : Form :=
  { id := "karlsson2017_pulloja"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pulloja"
    segments := ["pullo", "j", "a"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def pullojen : Form :=
  { id := "karlsson2017_pullojen"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pullojen"
    segments := ["pullo", "j", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def tyttoja : Form :=
  { id := "karlsson2017_tyttoja"
    languageId := "finn1318"
    parameterId := "girl"
    form := "tyttöjä"
    segments := ["tyttö", "j", "ä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def tyttojen : Form :=
  { id := "karlsson2017_tyttojen"
    languageId := "finn1318"
    parameterId := "girl"
    form := "tyttöjen"
    segments := ["tyttö", "j", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def pulloissa : Form :=
  { id := "karlsson2017_pulloissa"
    languageId := "finn1318"
    parameterId := "bottle"
    form := "pulloissa"
    segments := ["pullo", "i", "ssa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def maissa : Form :=
  { id := "karlsson2017_maissa"
    languageId := "finn1318"
    parameterId := "country"
    form := "maissa"
    segments := ["ma", "i", "ssa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def risteissa : Form :=
  { id := "karlsson2017_risteissa"
    languageId := "finn1318"
    parameterId := "cross"
    form := "risteissä"
    segments := ["riste", "i", "ssä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def kivissa : Form :=
  { id := "karlsson2017_kivissa"
    languageId := "finn1318"
    parameterId := "stone"
    form := "kivissä"
    segments := ["kiv", "i", "ssä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ]
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def lapsia : Form :=
  { id := "karlsson2017_lapsia"
    languageId := "finn1318"
    parameterId := "child"
    form := "lapsia"
    segments := ["laps", "i", "a"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§8.4"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def talojen : Form :=
  { id := "karlsson2017_talojen"
    languageId := "finn1318"
    parameterId := "house"
    form := "talojen"
    segments := ["talo", "j", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def poikia : Form :=
  { id := "karlsson2017_poikia"
    languageId := "finn1318"
    parameterId := "boy"
    form := "poikia"
    segments := ["poik", "i", "a"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def poikien : Form :=
  { id := "karlsson2017_poikien"
    languageId := "finn1318"
    parameterId := "boy"
    form := "poikien"
    segments := ["poik", "i", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def kirjoja : Form :=
  { id := "karlsson2017_kirjoja"
    languageId := "finn1318"
    parameterId := "book"
    form := "kirjoja"
    segments := ["kirjo", "j", "a"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def kirjojen : Form :=
  { id := "karlsson2017_kirjojen"
    languageId := "finn1318"
    parameterId := "book"
    form := "kirjojen"
    segments := ["kirjo", "j", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def paivia : Form :=
  { id := "karlsson2017_paivia"
    languageId := "finn1318"
    parameterId := "day"
    form := "päiviä"
    segments := ["päiv", "i", "ä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def paivien : Form :=
  { id := "karlsson2017_paivien"
    languageId := "finn1318"
    parameterId := "day"
    form := "päivien"
    segments := ["päiv", "i", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def kasien : Form :=
  { id := "karlsson2017_kasien"
    languageId := "finn1318"
    parameterId := "hand"
    form := "käsien"
    segments := ["käs", "i", "en"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def maita : Form :=
  { id := "karlsson2017_maita"
    languageId := "finn1318"
    parameterId := "country"
    form := "maita"
    segments := ["ma", "i", "ta"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def maiden : Form :=
  { id := "karlsson2017_maiden"
    languageId := "finn1318"
    parameterId := "country"
    form := "maiden"
    segments := ["ma", "i", "den"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def maitten : Form :=
  { id := "karlsson2017_maitten"
    languageId := "finn1318"
    parameterId := "country"
    form := "maitten"
    segments := ["ma", "i", "tten"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def teita : Form :=
  { id := "karlsson2017_teita"
    languageId := "finn1318"
    parameterId := "road"
    form := "teitä"
    segments := ["te", "i", "tä"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def teiden : Form :=
  { id := "karlsson2017_teiden"
    languageId := "finn1318"
    parameterId := "road"
    form := "teiden"
    segments := ["te", "i", "den"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def esteitten : Form :=
  { id := "karlsson2017_esteitten"
    languageId := "finn1318"
    parameterId := "obstacle"
    form := "esteitten"
    segments := ["este", "i", "tten"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def valtioiden : Form :=
  { id := "karlsson2017_valtioiden"
    languageId := "finn1318"
    parameterId := "state"
    form := "valtioiden"
    segments := ["valtio", "i", "den"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def kalojensa : Form :=
  { id := "karlsson2017_kalojensa"
    languageId := "finn1318"
    parameterId := "fish"
    form := "kalojensa"
    segments := ["kalo", "je", "nsa"]
    comment := ""
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ]
    columns := [("Case", "gen"), ("Possessor", "3sg"), ("Infinitive", ""), ("Number", "i"), ("Clitic", "")] }

def all : List Form := [auto, auton, hanet, maitoa, vetta, perhetta, autossa, autosta, autoon, maahan, porvooseen, poydalla, poydalta, poydalle, opettajana, opettajaksi, vaimoineni, passitta, jalan, kirjani, kirjasi, kirjansa, pullo, pullossa, pulloni, pullostani, hyllyssa, hyllylla, hyllysi, hyllyllesi, taloon, hyllynsa, kadessani, kateen, kateesi, katta, sanoa, syoda, juosta, juostaksemme, sanoessani, syodessamme, juosten, syomalla, sanomatta, sanomaan, puhuaksesi, puhumalla, autollani, autostasi, autooni, laukkuni, laukkusi, laukkunsa_3sg, laukkumme, laukkunne, laukkunsa_3pl, taloaan, vieraanaan, saadakseen, talossaan, autollaan, isalleen, aidiltaan, aitiaan, talonsa, autonsa, isaansa, aitinsa, sanoakseni, elaaksemme, tavataksesi, juodakseen, ollaksenne, lepaamassa, lepaamaan, vetamalla, mainitsematta, tekemasta, tuleman, pullot, pullokin, pulloista, pullossahan, pullotkin, pullossasiko, pulloissamme, pulloistakaan, pulloissannekin, hyllyltako, hyllytko, hyllynhan, talonsako, hyllyillamme, kasi, kadet, kasissammehan, lepaamaanko, vetamallakin, mainitsemattakaan, oppiakseenhan, maatamme, poikannekin, aidiltanihan, isallesiko, maahamme, perhettaan, talojaan, renkaitaan, paataan, taloansa, kalansa, kalaansa_ill, kalaansa_part, kaloihinsa, taloissa, taloihin, taloina, taloille, taloiksi, hyllyja, hyllyjen, pulloja, pullojen, tyttoja, tyttojen, pulloissa, maissa, risteissa, kivissa, lapsia, talojen, poikia, poikien, kirjoja, kirjojen, paivia, paivien, kasien, maita, maiden, maitten, teita, teiden, esteitten, valtioiden, kalojensa]

def parameters : List Parameter := [
  { id := "car", name := "car", description := "" },
  { id := "him_her", name := "him, her", description := "" },
  { id := "milk", name := "milk", description := "" },
  { id := "water", name := "water", description := "" },
  { id := "family", name := "family", description := "" },
  { id := "country", name := "country", description := "" },
  { id := "porvoo", name := "Porvoo (place name)", description := "" },
  { id := "table", name := "table", description := "" },
  { id := "teacher", name := "teacher", description := "" },
  { id := "wife", name := "wife", description := "" },
  { id := "passport", name := "passport", description := "" },
  { id := "foot", name := "foot", description := "" },
  { id := "book", name := "book", description := "" },
  { id := "bottle", name := "bottle", description := "" },
  { id := "shelf", name := "shelf", description := "" },
  { id := "house", name := "house", description := "" },
  { id := "hand", name := "hand", description := "" },
  { id := "say", name := "say", description := "" },
  { id := "eat", name := "eat", description := "" },
  { id := "run", name := "run", description := "" },
  { id := "speak", name := "speak", description := "" },
  { id := "bag", name := "bag", description := "" },
  { id := "guest", name := "guest", description := "" },
  { id := "get", name := "get", description := "" },
  { id := "father", name := "father", description := "" },
  { id := "mother", name := "mother", description := "" },
  { id := "live", name := "live", description := "" },
  { id := "meet", name := "meet", description := "" },
  { id := "drink", name := "drink", description := "" },
  { id := "be", name := "be", description := "" },
  { id := "rest", name := "rest", description := "" },
  { id := "pull", name := "pull", description := "" },
  { id := "mention", name := "mention", description := "" },
  { id := "do", name := "do", description := "" },
  { id := "come", name := "come", description := "" },
  { id := "son", name := "son", description := "" },
  { id := "ring", name := "ring", description := "" },
  { id := "head", name := "head", description := "" },
  { id := "fish", name := "fish", description := "" },
  { id := "learn", name := "learn", description := "" },
  { id := "girl", name := "girl", description := "" },
  { id := "cross", name := "cross", description := "" },
  { id := "stone", name := "stone", description := "" },
  { id := "child", name := "child", description := "" },
  { id := "boy", name := "boy, son", description := "" },
  { id := "day", name := "day", description := "" },
  { id := "road", name := "road", description := "" },
  { id := "obstacle", name := "obstacle", description := "" },
  { id := "state", name := "state", description := "" }
]

def relations : List FormRelation := []

end Karlsson2017.Forms
