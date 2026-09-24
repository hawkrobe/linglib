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
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "gen"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "acc"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ela"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "abl"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "all"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ess"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "transl"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "com"), ("Possessor", "1sg"), ("Infinitive", "")] }

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
    columns := [("Case", "abess"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "inst"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "1sg"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "2sg"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "1sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ela"), ("Possessor", "1sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "2sg"), ("Infinitive", "")] }

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
    columns := [("Case", "all"), ("Possessor", "2sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ine"), ("Possessor", "1sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "ill"), ("Possessor", "2sg"), ("Infinitive", "")] }

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
    columns := [("Case", "part"), ("Possessor", ""), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", "a")] }

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
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", "a")] }

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
    columns := [("Case", "nom"), ("Possessor", ""), ("Infinitive", "a")] }

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
    columns := [("Case", "transl"), ("Possessor", "1pl"), ("Infinitive", "a")] }

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
    columns := [("Case", "ine"), ("Possessor", "1sg"), ("Infinitive", "e")] }

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
    columns := [("Case", "ine"), ("Possessor", "1pl"), ("Infinitive", "e")] }

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
    columns := [("Case", "inst"), ("Possessor", ""), ("Infinitive", "e")] }

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
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", "ma")] }

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
    columns := [("Case", "abess"), ("Possessor", ""), ("Infinitive", "ma")] }

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
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "ma")] }

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
    columns := [("Case", "transl"), ("Possessor", "2sg"), ("Infinitive", "a")] }

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
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", "ma")] }

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
    columns := [("Case", "ade"), ("Possessor", "1sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ela"), ("Possessor", "2sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ill"), ("Possessor", "1sg"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "1sg"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "2sg"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "1pl"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "2pl"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "3pl"), ("Infinitive", "")] }

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
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ess"), ("Possessor", "3pl"), ("Infinitive", "")] }

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
    columns := [("Case", "transl"), ("Possessor", "3sg"), ("Infinitive", "a")] }

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
    columns := [("Case", "ine"), ("Possessor", "3pl"), ("Infinitive", "")] }

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
    columns := [("Case", "ade"), ("Possessor", "3sg"), ("Infinitive", "")] }

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
    columns := [("Case", "all"), ("Possessor", "3pl"), ("Infinitive", "")] }

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
    columns := [("Case", "abl"), ("Possessor", "3sg"), ("Infinitive", "")] }

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
    columns := [("Case", "part"), ("Possessor", "3sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ill"), ("Possessor", "3pl"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", "")] }

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
    columns := [("Case", "ill"), ("Possessor", "3pl"), ("Infinitive", "")] }

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
    columns := [("Case", "nom"), ("Possessor", "3sg"), ("Infinitive", "")] }

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
    columns := [("Case", "transl"), ("Possessor", "1sg"), ("Infinitive", "a")] }

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
    columns := [("Case", "transl"), ("Possessor", "1pl"), ("Infinitive", "a")] }

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
    columns := [("Case", "transl"), ("Possessor", "2sg"), ("Infinitive", "a")] }

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
    columns := [("Case", "transl"), ("Possessor", "3sg"), ("Infinitive", "a")] }

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
    columns := [("Case", "transl"), ("Possessor", "2pl"), ("Infinitive", "a")] }

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
    columns := [("Case", "ine"), ("Possessor", ""), ("Infinitive", "ma")] }

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
    columns := [("Case", "ill"), ("Possessor", ""), ("Infinitive", "ma")] }

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
    columns := [("Case", "ade"), ("Possessor", ""), ("Infinitive", "ma")] }

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
    columns := [("Case", "abess"), ("Possessor", ""), ("Infinitive", "ma")] }

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
    columns := [("Case", "ela"), ("Possessor", ""), ("Infinitive", "ma")] }

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
    columns := [("Case", "inst"), ("Possessor", ""), ("Infinitive", "ma")] }

def all : List Form := [auto, auton, hanet, maitoa, vetta, perhetta, autossa, autosta, autoon, maahan, porvooseen, poydalla, poydalta, poydalle, opettajana, opettajaksi, vaimoineni, passitta, jalan, kirjani, kirjasi, kirjansa, pullo, pullossa, pulloni, pullostani, hyllyssa, hyllylla, hyllysi, hyllyllesi, taloon, hyllynsa, kadessani, kateen, kateesi, katta, sanoa, syoda, juosta, juostaksemme, sanoessani, syodessamme, juosten, syomalla, sanomatta, sanomaan, puhuaksesi, puhumalla, autollani, autostasi, autooni, laukkuni, laukkusi, laukkunsa_3sg, laukkumme, laukkunne, laukkunsa_3pl, taloaan, vieraanaan, saadakseen, talossaan, autollaan, isalleen, aidiltaan, aitiaan, talonsa, autonsa, isaansa, aitinsa, sanoakseni, elaaksemme, tavataksesi, juodakseen, ollaksenne, lepaamassa, lepaamaan, vetamalla, mainitsematta, tekemasta, tuleman]

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
  { id := "come", name := "come", description := "" }
]

def relations : List FormRelation := []

end Karlsson2017.Forms
