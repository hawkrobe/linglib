module

public import Linglib.Fragments.Slavic.Declension

/-!
# Czech declension

This file gives the Czech words [caha-2009] declines in his tables of Slavic syncretism: nouns,
adjectives, pronouns and numerals. Each is a `Slavic.Declension.Paradigm`, its form in each of the
six cases. An entry marked colloquial is the colloquial paradigm Caha sets beside the literary one,
and where the tables decline a word in two ways without naming the variety, the second paradigm is
primed.

## References

* [caha-2009]
-/

@[expose] public section

namespace Czech.Declension

open Slavic.Declension

/-- *okno* 'window', singular. -/
def okno_sg : Paradigm := ⟨"window", .singular, forms "okno" "okno" "okna" "okně" "oknu" "oknem"⟩

/-- *ulice* 'street', singular. -/
def ulice_sg : Paradigm :=
  ⟨"street", .singular, forms "ulice" "ulici" "ulice" "ulici" "ulici" "ulicí"⟩

/-- *muži* 'man', plural. -/
def muz_pl : Paradigm := ⟨"man", .plural, forms "muži" "muže" "mužů" "mužích" "mužům" "muži"⟩

/-- *muž* 'man', singular. -/
def muz_sg : Paradigm := ⟨"man", .singular, forms "muž" "muže" "muže" "muži" "muži" "mužem"⟩

/-- *dobrá* 'good', singular. -/
def dobry_fsg : Paradigm :=
  ⟨"good", .singular, forms "dobrá" "dobrou" "dobré" "dobré" "dobré" "dobrou"⟩

/-- *dobrý* 'good', plural. -/
def dobry_mpl' : Paradigm :=
  ⟨"good", .plural, forms "dobrý" "dobrý" "dobrých" "dobrých" "dobrým" "dobrými"⟩

/-- *větší* 'bigger', singular. -/
def vetsi_msg : Paradigm :=
  ⟨"bigger", .singular, forms "větší" "většího" "většího" "větším" "většímu" "větším"⟩

/-- *oba* 'both', dual. -/
def oba : Paradigm := ⟨"both", .dual, forms "oba" "oba" "obou" "obou" "oběma" "oběma"⟩

/-- *stroj* 'machine', singular. -/
def stroj_sg : Paradigm :=
  ⟨"machine", .singular, forms "stroj" "stroj" "stroje" "stroji" "stroji" "strojem"⟩

/-- *stroje* 'machine', plural. -/
def stroj_pl : Paradigm :=
  ⟨"machine", .plural, forms "stroje" "stroje" "strojů" "strojích" "strojům" "stroji"⟩

/-- *kosti* 'bone', plural. -/
def kost_pl : Paradigm :=
  ⟨"bone", .plural, forms "kosti" "kosti" "kostí" "kostech" "kostem" "kostmi"⟩

/-- *ty* 'that', plural. -/
def ty : Paradigm := ⟨"that", .plural, forms "ty" "ty" "těch" "těch" "těm" "těmi"⟩

/-- *vila* 'villa', singular. -/
def vila_sg : Paradigm := ⟨"villa", .singular, forms "vila" "vilu" "vily" "vile" "vile" "vilou"⟩

/-- *Míša* 'Michelle', singular. -/
def misa_sg : Paradigm := ⟨"Michelle", .singular, forms "Míša" "Míšu" "Míši" "Míše" "Míše" "Míšou"⟩

/-- *voli* 'ox', plural. -/
def vul_pl : Paradigm := ⟨"ox", .plural, forms "voli" "voly" "volů" "volech" "volům" "voly"⟩

/-- *hoši* 'boy', plural. -/
def hoch_pl : Paradigm := ⟨"boy", .plural, forms "hoši" "hochy" "hochů" "hoších" "hochům" "hochy"⟩

/-- *pán* 'sir', singular. -/
def pan_sg : Paradigm := ⟨"sir", .singular, forms "pán" "pána" "pána" "pánovi" "pánovi" "pánem"⟩

/-- *ten* 'that', singular. -/
def ten : Paradigm := ⟨"that", .singular, forms "ten" "toho" "toho" "tom" "tomu" "tím"⟩

/-- *my* 'we', plural. -/
def my' : Paradigm := ⟨"we", .plural, forms "my" "nás" "nás" "nás" "nám" "náma"⟩

/-- *ona* 'she', singular. -/
def ona : Paradigm := ⟨"she", .singular, forms "ona" "ji" "jí" "jí" "jí" "jí"⟩

/-- *naše* 'our', singular. -/
def nase_fsg : Paradigm := ⟨"our", .singular, forms "naše" "naši" "naší" "naší" "naší" "naší"⟩

/-- *zátěž* 'stress', singular. -/
def zatez_sg : Paradigm :=
  ⟨"stress", .singular, forms "zátěž" "zátěž" "zátěže" "zátěži" "zátěži" "zátěží"⟩

/-- *žena* 'woman', singular. -/
def zena_sg : Paradigm := ⟨"woman", .singular, forms "žena" "ženu" "ženy" "ženě" "ženě" "ženou"⟩

/-- *kluci* 'boy', plural. -/
def kluk_pl : Paradigm := ⟨"boy", .plural, forms "kluci" "kluky" "kluků" "klucích" "klukům" "kluky"⟩

/-- *kluci* 'boy', plural, colloquial. -/
def kluk_pl_colloquial : Paradigm :=
  ⟨"boy", .plural, forms "kluci" "kluky" "kluků" "klukách" "klukům" "klukama"⟩

/-- *muži* 'man', plural, colloquial. -/
def muz_pl_colloquial : Paradigm :=
  ⟨"man", .plural, forms "muži" "muže" "mužů" "mužích" "mužům" "mužema"⟩

/-- *ženy* 'woman', plural. -/
def zena_pl : Paradigm := ⟨"woman", .plural, forms "ženy" "ženy" "žen" "ženách" "ženám" "ženami"⟩

/-- *písně* 'song', plural. -/
def pisen_pl : Paradigm :=
  ⟨"song", .plural, forms "písně" "písně" "písní" "písních" "písním" "písněmi"⟩

/-- *dobré* 'good', plural. -/
def dobry_mpl : Paradigm :=
  ⟨"good", .plural, forms "dobré" "dobré" "dobrých" "dobrých" "dobrým" "dobrými"⟩

/-- *kost* 'bone', singular. -/
def kost_sg : Paradigm := ⟨"bone", .singular, forms "kost" "kost" "kosti" "kosti" "kosti" "kostí"⟩

/-- *hrad* 'castle', singular. -/
def hrad_sg : Paradigm :=
  ⟨"castle", .singular, forms "hrad" "hrad" "hradu" "hradu" "hradu" "hradem"⟩

/-- *my* 'we', plural. -/
def my : Paradigm := ⟨"we", .plural, forms "my" "nás" "nás" "nás" "nám" "námi"⟩

/-- *město* 'city', singular. -/
def mesto_sg : Paradigm :=
  ⟨"city", .singular, forms "město" "město" "města" "městu" "městu" "městem"⟩

/-- *větší* 'bigger', singular. -/
def vetsi_nsg : Paradigm :=
  ⟨"bigger", .singular, forms "větší" "větší" "většího" "větším" "většímu" "větším"⟩

/-- *ono* 'it', singular. -/
def ono : Paradigm := ⟨"it", .singular, forms "ono" "je" "jeho" "jem" "jemu" "jím"⟩

/-- *naše* 'our', singular. -/
def nase_nsg : Paradigm := ⟨"our", .singular, forms "naše" "naše" "našeho" "našem" "našemu" "naším"⟩

/-- *větší* 'bigger', singular. -/
def vetsi_fsg : Paradigm :=
  ⟨"bigger", .singular, forms "větší" "větší" "větší" "větší" "větší" "větší"⟩

/-- *větší* 'bigger', plural. -/
def vetsi_npl : Paradigm :=
  ⟨"bigger", .plural, forms "větší" "větší" "větších" "větších" "větším" "většími"⟩

/-- *ona* 'they', plural. -/
def ona_npl : Paradigm := ⟨"they", .plural, forms "ona" "je" "jich" "jich" "jim" "jimi"⟩

/-- *ta* 'that', singular. -/
def ta : Paradigm := ⟨"that", .singular, forms "ta" "tu" "té" "té" "té" "tou"⟩

/-- *dva* 'two', dual. -/
def dva : Paradigm := ⟨"two", .dual, forms "dva" "dva" "dvou" "dvou" "dvěma" "dvěma"⟩

/-- *pět* 'five', plural. -/
def pet : Paradigm := ⟨"five", .plural, forms "pět" "pět" "pěti" "pěti" "pěti" "pěti"⟩

/-- `paradigms` lists the entries. -/
def paradigms : List Paradigm :=
  [okno_sg, ulice_sg, muz_pl, muz_sg, dobry_fsg, dobry_mpl', vetsi_msg, oba, stroj_sg, stroj_pl,
    kost_pl, ty, vila_sg, misa_sg, vul_pl, hoch_pl, pan_sg, ten, my', ona, nase_fsg, zatez_sg,
    zena_sg, kluk_pl, kluk_pl_colloquial, muz_pl_colloquial, zena_pl, pisen_pl, dobry_mpl, kost_sg,
    hrad_sg, my, mesto_sg, vetsi_nsg, ono, nase_nsg, vetsi_fsg, vetsi_npl, ona_npl, ta, dva, pet]

end Czech.Declension
