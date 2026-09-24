module

public import Linglib.Fragments.Slavic.Declension

/-!
# Slovene declension

This file gives the Slovene words [caha-2009] declines in his tables of Slavic syncretism: nouns in
the singular, the dual and the plural, the personal pronouns, and demonstrative and possessive
pronouns. Each is a `Slavic.Declension.Paradigm`, its form in each of the six cases, with the tone
marks of the source.

## References

* [caha-2009]
-/

@[expose] public section

namespace Slovenian.Declension

open Slavic.Declension

/-- *mízi* 'table', dual. -/
def miza_du : Paradigm := ⟨"table", .dual, forms "mízi" "mízi" "mîz" "mízah" "mízama" "mízama"⟩

/-- *brêskev* 'peach', singular. -/
def breskev_sg : Paradigm :=
  ⟨"peach", .singular, forms "brêskev" "brêskev" "brêskve" "brêskvi" "brêskvi" "brêskvijo"⟩

/-- *brêskve* 'peach', plural. -/
def breskev_pl : Paradigm :=
  ⟨"peach", .plural, forms "brêskve" "brêskve" "brêskv" "brêskvah" "brêskvam" "brêskvami"⟩

/-- *jábolko* 'apple', singular. -/
def jabolko_sg : Paradigm :=
  ⟨"apple", .singular, forms "jábolko" "jábolko" "jábolka" "jábolku" "jábolku" "jábolkom"⟩

/-- *kmèta* 'farmer', dual. -/
def kmet_du : Paradigm :=
  ⟨"farmer", .dual, forms "kmèta" "kmèta" "kmêtov" "kmētih" "kmétoma" "kmétoma"⟩

/-- *kmèt* 'farmer', singular. -/
def kmet_sg : Paradigm :=
  ⟨"farmer", .singular, forms "kmèt" "kméta" "kméta" "kmêtu" "kmétu" "kmétom"⟩

/-- *jàz* 'I', singular. -/
def jaz : Paradigm := ⟨"I", .singular, forms "jàz" "mȩ́ne" "mȩ́ne" "mȩ́ni" "mȩ́ni" "menój"⟩

/-- *mo̧ji* 'my', plural. -/
def moj_mpl : Paradigm :=
  ⟨"my", .plural, forms "mo̧ji" "mo̧ji" "mo̧jih" "mo̧jih" "mo̧jim" "mo̧jimi"⟩

/-- *dvâ* 'two', dual. -/
def dva : Paradigm := ⟨"two", .dual, forms "dvâ" "dvâ" "dvēh" "dvēh" "dvēma" "dvēma"⟩

/-- *mî* 'we', plural. -/
def mi : Paradigm := ⟨"we", .plural, forms "mî" "nàs" "nàs" "nàs" "nàm" "na̧mi"⟩

/-- *mîdva* 'we two', dual. -/
def midva : Paradigm := ⟨"we two", .dual, forms "mîdva" "náju" "náju" "náju" "náma" "náma"⟩

/-- *nìt* 'thread', singular. -/
def nit_sg : Paradigm := ⟨"thread", .singular, forms "nìt" "nìt" "níti" "níti" "níti" "nítjo"⟩

/-- *gospá* 'lady', singular. -/
def gospa_sg : Paradigm :=
  ⟨"lady", .singular, forms "gospá" "gospó" "gospé" "gospé" "gospé" "gospó"⟩

/-- *dní* 'day', dual. -/
def dan_du : Paradigm := ⟨"day", .dual, forms "dní" "dní" "dní" "dnéh" "dnéma" "dnéma"⟩

/-- *računovodja* 'accountant', singular. -/
def racunovodja_sg : Paradigm :=
  ⟨"accountant", .singular, forms "računovodja" "računovodja" "računovodja"
    "računovodju" "računovodju" "računovodjem"⟩

/-- *tô* 'this', singular. -/
def ta_n : Paradigm := ⟨"this", .singular, forms "tô" "tô" "têga" "têm" "têmu" "têm"⟩

/-- *pótniki* 'traveller', plural. -/
def potnik_pl : Paradigm :=
  ⟨"traveller", .plural, forms "pótniki" "pótnike" "pótnikov" "pótnikih" "pótnikom" "pótniki"⟩

/-- *tâ* 'this', singular. -/
def ta_f : Paradigm := ⟨"this", .singular, forms "tâ" "tô" "tê" "têj" "têj" "tô"⟩

/-- *tîsto* 'that', singular. -/
def tisti_n : Paradigm :=
  ⟨"that", .singular, forms "tîsto" "tîsto" "tîstega" "tîstem" "tîstemu" "tîstim"⟩

/-- *váše* 'your', singular. -/
def vas_n : Paradigm := ⟨"your", .singular, forms "váše" "váše" "vášega" "vášem" "vášemu" "vášim"⟩

/-- `paradigms` lists the entries. -/
def paradigms : List Paradigm :=
  [miza_du, breskev_sg, breskev_pl, jabolko_sg, kmet_du, kmet_sg, jaz, moj_mpl, dva, mi, midva,
    nit_sg, gospa_sg, dan_du, racunovodja_sg, ta_n, potnik_pl, ta_f, tisti_n, vas_n]

end Slovenian.Declension
