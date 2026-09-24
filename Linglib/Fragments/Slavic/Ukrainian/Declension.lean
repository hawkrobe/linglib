module

public import Linglib.Fragments.Slavic.Declension

/-!
# Ukrainian declension

This file gives the Ukrainian words [caha-2009] declines in his tables of Slavic syncretism, in his
transliteration: `ı` is и, `i` is і, `j` is й, and an acute marks the stress. Each is a
`Slavic.Declension.Paradigm`, its form in each of the six cases. Where two grammars decline a word
differently, the second paradigm is primed.

## References

* [caha-2009]
-/

@[expose] public section

namespace Ukrainian.Declension

open Slavic.Declension

/-- *kraj* 'region', singular. -/
def kraj_sg : Paradigm :=
  ⟨"region", .singular, forms "kraj" "kraj" "kráju" "krajú" "krájevi" "krájem"⟩

/-- *velíki* 'big', plural. -/
def velykyj_pl : Paradigm :=
  ⟨"big", .plural, forms "velíki" "velíki" "velíkıch" "velíkıch" "velíkım" "velíkımı"⟩

/-- *znannjá* 'knowledge', singular. -/
def znannja_sg : Paradigm :=
  ⟨"knowledge", .singular, forms "znannjá" "znannjá" "znannjá" "znanni̇́" "znannjú" "znannjám"⟩

/-- *mı* 'we', plural. -/
def my : Paradigm := ⟨"we", .plural, forms "mı" "nas" "nas" "nas" "nam" "námı"⟩

/-- *kasír* 'cashier', singular. -/
def kasyr_sg : Paradigm :=
  ⟨"cashier", .singular, forms "kasír" "kasíra" "kasíra" "kasírovi" "kasírovi" "kasírom"⟩

/-- *kasírı* 'cashier', plural. -/
def kasyr_pl : Paradigm :=
  ⟨"cashier", .plural, forms "kasírı" "kasíriv" "kasíriv" "kasírach" "kasíram" "kasíramı"⟩

/-- *mátı* 'mother', singular. -/
def maty_sg : Paradigm :=
  ⟨"mother", .singular, forms "mátı" "mátir" "máteri" "máteri" "máteri" "mátirju"⟩

/-- *ruká* 'hand', singular. -/
def ruka_sg : Paradigm := ⟨"hand", .singular, forms "ruká" "rúku" "rukí" "ruci̇́" "ruci̇́" "rukóju"⟩

/-- *ja* 'I', singular. -/
def ja : Paradigm := ⟨"I", .singular, forms "ja" "mené" "mené" "meni̇́" "meni̇́" "mnóju"⟩

/-- *velíkıj* 'big', singular. -/
def velykyj_msg : Paradigm :=
  ⟨"big", .singular, forms "velíkıj" "velíkıj" "velíkogo" "velíkomu" "velíkomu" "velíkım"⟩

/-- *sto* 'hundred', singular. -/
def sto : Paradigm := ⟨"hundred", .singular, forms "sto" "sto" "sta" "sta" "sta" "sta"⟩

/-- *kraj* 'region', singular. -/
def kraj_sg' : Paradigm :=
  ⟨"region", .singular, forms "kraj" "kraj" "kráju" "kráji" "kráju" "krájem"⟩

/-- *bezkrajij* 'endless', singular. -/
def bezkrajij_msg : Paradigm :=
  ⟨"endless", .singular, forms "bezkrajij" "bezkrajij" "bezkrajogo"
    "bezkrajomu" "bezkrajomu" "bezkrajim"⟩

/-- *bezkrajij* 'endless', singular. -/
def bezkrajij_msg' : Paradigm :=
  ⟨"endless", .singular, forms "bezkrajij" "bezkrajij" "bezkrajogo"
    "bezkrajim" "bezkrajomu" "bezkrajim"⟩

/-- *velíkıj* 'big', singular. -/
def velykyj_msg' : Paradigm :=
  ⟨"big", .singular, forms "velíkıj" "velíkıj" "velíkogo" "velíkim" "velíkomu" "velíkım"⟩

/-- `paradigms` lists the entries. -/
def paradigms : List Paradigm :=
  [kraj_sg, velykyj_pl, znannja_sg, my, kasyr_sg, kasyr_pl, maty_sg, ruka_sg, ja, velykyj_msg, sto,
    kraj_sg', bezkrajij_msg, bezkrajij_msg', velykyj_msg']

end Ukrainian.Declension
