module

public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Linglib.Fragments.Slavic.Czech.Nouns
public import Linglib.Studies.Blake1994

/-!
# Caha (2009): The Nanosyntax of Case

This file formalizes Caha's Universal Contiguity (10): non-accidental case syncretism targets
contiguous regions of a sequence of cases that is the same in every language, nominative,
accusative, genitive, dative, instrumental, comitative. The evidence is the Slavic declensions of
chapter 8, read along the Slavic sequence with the prepositional between the genitive and the
dative (13). The paradigms of Caha's tables that are not contiguous are the ones whose syncretism
he treats as a phonological conflation or an accidental homophony, a Ukrainian variant he leaves
open, and a Slovene paradigm he passes over.

## Main definitions

* `sequence`: the Case sequence (10b)
* `Paradigm`, `forms`: a word of the tables in one number, by its forms along the Slavic sequence
  (13), nominative, accusative, genitive, prepositional, dative, instrumental
* `paradigms`: the Serbian, Slovene, Czech, Slovak and Ukrainian tables of chapter 8
* `accounts`, `analyses`: Caha's treatment of the paradigms with an offending syncretism
* `czechCase`, `Declines`: the Czech case at each place of the sequence, and a noun of the Czech
  fragment declining a paradigm of the tables at a place

## Main results

* `exists_position_lt`: Blake's hierarchy orders the cases of the sequence as it does
* `not_isContiguous_iff`: the paradigms of the tables that are not contiguous
* `supersetSpellable_form`: Superset spellout generates the other paradigms
* `isContiguous_analysis`: the underlying forms Caha gives are contiguous
* `isNone_iff_adjacent`: the syncretisms (67) calls non-accidental are the adjacent ones
* `declines_czechNouns`, `declines_hrad_mesto_iff`, `declines_colloquial_iff`: Caha's literary
  Czech noun paradigms are the fragment's declensions after Short and *Mluvnice češtiny*

## Implementation notes

Two cells are syncretic when their forms are identical, which ignores Caha's shading. Some of his
column headings are wrong, and the glosses are the fragments': Czech *kost* is 'bone', not
'castle', the Czech *ta* of note 26 is feminine singular, and the Slovene *dva* of (16) is 'two',
not 'both'. The Ukrainian *velíkıj* 'big' is printed *velík-ij* in (69).

The Serbian and Slovene forms keep the tone marks of the source, and the Ukrainian ones Caha's
transliteration, in which `ı` is и, `i` is і, `j` is й, and an acute marks the stress. An entry
marked colloquial is the colloquial paradigm Caha sets beside the literary one, and where the
tables decline a word in two ways without naming the variety, as where two grammars decline a
Ukrainian word differently, the second paradigm is primed.

## References

* [caha-2009]
* [blake-1994]
* [short-1993-czech]
* [komarek-etal-1986]
-/

@[expose] public section

namespace Caha2009

open Morphology (IsContiguous)
open Morphology.Containment (SupersetSpellable isContiguous_iff_spelloutGenerable)

/-! ### The Case sequence -/

/-- `sequence` is the Case sequence (10b): nominative, accusative, genitive, dative,
instrumental, comitative. -/
def sequence : Fin 6 → Case := ![.nom, .acc, .gen, .dat, .inst, .com]

/-- Blake's hierarchy, less the positions the sequence leaves out, orders the cases of the sequence
as the sequence does (48): each has a position, and a later case a later one. -/
theorem exists_position_lt {i j : Fin 6} (h : i < j) :
    ∃ p q, Blake1994.position (sequence i) = some p ∧ Blake1994.position (sequence j) = some q ∧
      p < q := by
  revert i j; decide

/-! ### The Slavic tables -/

/-- A word of the tables in one number, by its forms along the Slavic sequence (13): nominative,
accusative, genitive, prepositional, dative, instrumental. -/
structure Paradigm where
  /-- The word's gloss. -/
  gloss : String
  /-- The number of the forms. -/
  number : Number
  /-- The forms along the sequence. -/
  form : Morphology.Paradigm 6 String

instance : DecidableEq Paradigm := fun a b ↦
  decidable_of_iff (a.gloss = b.gloss ∧ a.number = b.number ∧ a.form = b.form) <| by
    cases a; cases b; simp

/-- `forms nom acc gen loc dat inst` are the forms along the sequence. -/
def forms (nom acc gen loc dat inst : String) : Morphology.Paradigm 6 String :=
  ![nom, acc, gen, loc, dat, inst]

/-! #### Serbian

The Serbian words of the tables: seven nouns in the singular and the plural, and the personal
pronouns. -/

namespace Serbian

/-- *sîn* 'son', singular. -/
def sin_sg : Paradigm := ⟨"son", .singular, forms "sîn" "sîna" "sîna" "sînu" "sînu" "sînom"⟩

/-- *grâd* 'city', singular. -/
def grad_sg : Paradigm := ⟨"city", .singular, forms "grâd" "grâd" "grâda" "grádu" "grâdu" "grâdom"⟩

/-- *muž* 'man', singular. -/
def muz_sg : Paradigm := ⟨"man", .singular, forms "muž" "muža" "muža" "mužu" "mužu" "mužem"⟩

/-- *sèlo* 'village', singular. -/
def selo_sg : Paradigm := ⟨"village", .singular, forms "sèlo" "sèlo" "sèla" "sèlu" "sèlu" "sèlom"⟩

/-- *srce* 'heart', singular. -/
def srce_sg : Paradigm := ⟨"heart", .singular, forms "srce" "srce" "srca" "srcu" "srcu" "srcem"⟩

/-- *òvca* 'sheep', singular. -/
def ovca_sg : Paradigm := ⟨"sheep", .singular, forms "òvca" "òvcu" "òvcē" "òvci" "òvci" "òvcōm"⟩

/-- *smȑt* 'death', singular. -/
def smrt_sg : Paradigm := ⟨"death", .singular, forms "smȑt" "smȑt" "smȑti" "smȑti" "smȑti" "smr̀ću"⟩

/-- *sȉnovi* 'son', plural. -/
def sin_pl : Paradigm :=
  ⟨"son", .plural, forms "sȉnovi" "sȉnove" "sinóvā" "sȉnovima" "sȉnovima" "sȉnovima"⟩

/-- *grȁdovi* 'city', plural. -/
def grad_pl : Paradigm :=
  ⟨"city", .plural, forms "grȁdovi" "grȁdove" "gradóvā" "grȁdovima" "grȁdovima" "grȁdovima"⟩

/-- *muževi* 'man', plural. -/
def muz_pl : Paradigm :=
  ⟨"man", .plural, forms "muževi" "muževe" "mȕžēvā" "muževima" "muževima" "muževima"⟩

/-- *sȅla* 'village', plural. -/
def selo_pl : Paradigm :=
  ⟨"village", .plural, forms "sȅla" "sȅla" "sêlā" "sȅlima" "sȅlima" "sȅlima"⟩

/-- *srca* 'heart', plural. -/
def srce_pl : Paradigm := ⟨"heart", .plural, forms "srca" "srca" "sr̂cā" "srcima" "srcima" "srcima"⟩

/-- *ôvce* 'sheep', plural. -/
def ovca_pl : Paradigm := ⟨"sheep", .plural, forms "ôvce" "ôvce" "ovácā" "óvcama" "óvcama" "óvcama"⟩

/-- *smȑti* 'death', plural. -/
def smrt_pl : Paradigm :=
  ⟨"death", .plural, forms "smȑti" "smȑti" "smr̂tī" "smȑtima" "smȑtima" "smȑtima"⟩

/-- *ja* 'I', singular. -/
def ja : Paradigm := ⟨"I", .singular, forms "ja" "mene" "mene" "meni" "meni" "mnom"⟩

/-- *ti* 'you', singular. -/
def ti : Paradigm := ⟨"you", .singular, forms "ti" "tebe" "tebe" "tebi" "tebi" "tobom"⟩

/-- *on/ono* 'he, it', singular. -/
def on : Paradigm := ⟨"he, it", .singular, forms "on/ono" "njega" "njega" "njemu" "njemu" "njim"⟩

/-- *ona* 'she', singular. -/
def ona : Paradigm := ⟨"she", .singular, forms "ona" "nju" "nje" "njoj" "njoj" "njom"⟩

/-- *mi* 'we', plural. -/
def mi : Paradigm := ⟨"we", .plural, forms "mi" "nas" "nas" "nama" "nama" "nama"⟩

/-- *vi* 'you', plural. -/
def vi : Paradigm := ⟨"you", .plural, forms "vi" "vas" "vas" "vama" "vama" "vama"⟩

/-- *oni/ona/one* 'they', plural. -/
def oni : Paradigm := ⟨"they", .plural, forms "oni/ona/one" "njih" "njih" "njima" "njima" "njima"⟩

/-- `paradigms` lists the entries. -/
def paradigms : List Paradigm :=
  [sin_sg, grad_sg, muz_sg, selo_sg, srce_sg, ovca_sg, smrt_sg, sin_pl, grad_pl, muz_pl, selo_pl,
    srce_pl, ovca_pl, smrt_pl, ja, ti, on, ona, mi, vi, oni]

end Serbian

/-! #### Slovenian

The Slovene words of the tables: nouns in the singular, the dual and the plural, the personal
pronouns, and demonstrative and possessive pronouns. -/

namespace Slovenian

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

end Slovenian

/-! #### Czech

The Czech words of the tables. -/

namespace Czech

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

end Czech

/-! #### Slovak

The Slovak words the tables decline beside their Czech counterparts. -/

namespace Slovak

/-- *ona* 'she', singular. -/
def ona : Paradigm := ⟨"she", .singular, forms "ona" "ju" "jej" "jej" "njej" "njou"⟩

/-- *naša* 'our', singular. -/
def nase_fsg : Paradigm := ⟨"our", .singular, forms "naša" "našu" "našej" "našej" "našej" "našou"⟩

/-- *ulica* 'street', singular. -/
def ulica_sg : Paradigm :=
  ⟨"street", .singular, forms "ulica" "ulicu" "ulice" "ulici" "ulici" "ulicou"⟩

/-- *tlač* 'press', singular. -/
def tlac_sg : Paradigm := ⟨"press", .singular, forms "tlač" "tlač" "tlače" "tlači" "tlači" "tlačou"⟩

/-- `paradigms` lists the entries. -/
def paradigms : List Paradigm :=
  [ona, nase_fsg, ulica_sg, tlac_sg]

end Slovak

/-! #### Ukrainian

The Ukrainian words of the tables. -/

namespace Ukrainian

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

end Ukrainian

/-- `paradigms` lists the paradigms of Caha's Slavic tables. -/
def paradigms : List Paradigm :=
  Serbian.paradigms ++ Slovenian.paradigms ++ Czech.paradigms ++ Slovak.paradigms ++
    Ukrainian.paradigms

/-! ### Contiguity -/

/-- Caha accounts for an offending syncretism as a phonological conflation of distinct forms or as
an accidental homophony of distinct lexical entries. -/
inductive Account
  | conflation
  | accidental
  deriving DecidableEq, Repr

/-- `accounts` pairs each paradigm Caha accounts for with his account. -/
def accounts : List (Paradigm × Account) :=
  [(Slovenian.ta_n, .conflation), (Slovenian.potnik_pl, .conflation),
    (Slovenian.ta_f, .accidental), (Ukrainian.bezkrajij_msg', .conflation),
    (Czech.ulice_sg, .accidental), (Czech.muz_pl, .conflation), (Czech.dobry_fsg, .conflation),
    (Czech.vetsi_msg, .conflation), (Czech.vetsi_nsg, .conflation), (Czech.vul_pl, .conflation),
    (Czech.hoch_pl, .conflation), (Czech.kluk_pl, .conflation)]

/-- `offenders` lists the paradigms Caha accounts for, the Ukrainian variant of 'region' he leaves
open (70), and the Slovene 'lady' (16), whose accusative–instrumental *gospó* he leaves unshaded
although he takes that syncretism to be confined to the declension of 'this'. -/
def offenders : List Paradigm :=
  accounts.map Prod.fst ++ [Ukrainian.kraj_sg', Slovenian.gospa_sg]

/-- A paradigm of the tables is not contiguous exactly when it is an offender. -/
theorem not_isContiguous_iff :
    ∀ p ∈ paradigms, ¬ IsContiguous p.form ↔ p ∈ offenders := by
  decide +kernel

/-- Superset spellout generates every paradigm of the tables but the offenders. -/
theorem supersetSpellable_form {p : Paradigm} (hp : p ∈ paradigms) (h : p ∉ offenders) :
    SupersetSpellable p.form :=
  (isContiguous_iff_spelloutGenerable _).1 <|
    not_not.1 fun hc ↦ h ((not_isContiguous_iff p hp).1 hc)

/-- `analyses` pairs a paradigm with the underlying ending or lexical index Caha gives each cell,
or `""`: the indexed endings of 'street' (40), the underlying endings of (19), (32), (52), (58)
and note 26, and the endings of p. 270. -/
def analyses : List (Paradigm × Morphology.Paradigm 6 String) :=
  [(Czech.ulice_sg, forms "e1" "i1" "e2" "i2" "i2" "í2"),
    (Czech.muz_pl, forms "i" "" "" "" "" "y"),
    (Czech.hoch_pl, forms "" "" "" "" "" "yø"),
    (Czech.vetsi_nsg, forms "e" "e" "eho" "em" "emu" "ím"),
    (Czech.dobry_fsg, forms "a" "u" "é" "é" "é" "ou"),
    (Slovenian.ta_n, forms "" "" "" "" "" "îm"),
    (Ukrainian.bezkrajij_msg', forms "" "" "" "im" "" "ım")]

/-- Each analyzed paradigm is an offender, and its forms paired with their underlying endings
are contiguous. -/
theorem isContiguous_analysis :
    ∀ a ∈ analyses, a.1 ∈ offenders ∧ IsContiguous fun i ↦ (a.1.form i, a.2 i) := by
  decide

/-! ### The Czech syncretisms -/

/-- `czechCase i` is the Czech case at the place `i` of the Slavic sequence. -/
def czechCase : Fin 6 → _root_.Czech.Case := ![.nom, .acc, .gen, .loc, .dat, .inst]

/-- `Adjacent c d` holds when `d` follows `c` in the Slavic sequence. -/
def Adjacent (c d : _root_.Czech.Case) : Prop :=
  ∃ i : Fin 5, czechCase i.castSucc = c ∧ czechCase i.succ = d

instance (c d : _root_.Czech.Case) : Decidable (Adjacent c d) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- `table67` is Caha's summary of the Czech syncretisms (67), each with his account, `none` for
the non-accidental ones. -/
def table67 : List (_root_.Czech.Case × _root_.Czech.Case × Option Account) :=
  [(.nom, .acc, none), (.nom, .gen, some .accidental), (.nom, .inst, some .conflation),
    (.acc, .gen, none), (.acc, .loc, some .accidental), (.acc, .inst, some .conflation),
    (.gen, .loc, none), (.loc, .dat, none), (.loc, .inst, some .conflation), (.dat, .inst, none)]

/-- The syncretisms (67) calls non-accidental are the ones of adjacent cases. -/
theorem isNone_iff_adjacent : ∀ r ∈ table67, r.2.2 = none ↔ Adjacent r.1 r.2.1 := by
  decide

/-! ### Caha's Czech nouns and Short's declensions

Caha's Czech noun paradigms are those of the fragment's declension classes, the classes of
[short-1993-czech]'s tables with the stem conditions of [komarek-etal-1986]: each form of the
literary paradigms is one of the forms the fragment gives the noun. The plural of *kluk* 'boy'
depends on the stem conditions, since the tables alone would give *kluki* and *klukech* where Caha
has *kluci* and *klucích*. Caha's *hradu* and *městu* are the locative singular in *-u* that Short
describes beside the tables' *-ě* for the hard inanimates (p. 466) and the neuters (p. 467), and
his colloquial paradigms depart from the literary declension in the locative and the
instrumental. -/

/-- A noun of the fragment declines a paradigm of the tables at a place of the sequence when the
paradigm's form there is one of the noun's forms in that case and the paradigm's number. -/
def Declines (n : _root_.Czech.Noun) (p : Paradigm) (i : Fin 6) : Prop :=
  ∃ h : p.number ∈ _root_.Czech.Declension.numbers,
    _root_.Czech.Declension.segments (p.form i) ∈ n.forms (czechCase i, ⟨_, h⟩)

instance (n : _root_.Czech.Noun) (p : Paradigm) (i : Fin 6) : Decidable (Declines n p i) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- The literary paradigms of the tables that decline nouns of the fragment, with the nouns. -/
def czechNouns : List (Paradigm × _root_.Czech.Noun) :=
  [(Czech.muz_sg, _root_.Czech.muz), (Czech.muz_pl, _root_.Czech.muz),
    (Czech.stroj_sg, _root_.Czech.stroj), (Czech.stroj_pl, _root_.Czech.stroj),
    (Czech.kost_sg, _root_.Czech.kost), (Czech.kost_pl, _root_.Czech.kost),
    (Czech.zena_sg, _root_.Czech.zena), (Czech.zena_pl, _root_.Czech.zena),
    (Czech.kluk_pl, _root_.Czech.kluk)]

/-- The fragment declines each literary paradigm of the tables at every place. -/
theorem declines_czechNouns : ∀ x ∈ czechNouns, ∀ i, Declines x.2 x.1 i := by
  decide +kernel

/-- The endings of Short's table on the bare stem do not give Caha's nominative *kluci* and
locative *klucích*. -/
theorem kluk_pl_not_mem_table :
    _root_.Czech.Declension.segments (Czech.kluk_pl.form 0) ∉
        (_root_.Czech.Declension.Class.chlap.endings (.of .nom .plural)).map
          (_root_.Czech.kluk.stem ++ ·) ∧
      _root_.Czech.Declension.segments (Czech.kluk_pl.form 3) ∉
        (_root_.Czech.Declension.Class.chlap.endings (.of .loc .plural)).map
          (_root_.Czech.kluk.stem ++ ·) := by
  decide +kernel

/-- The fragment declines Caha's *hrad* and *město* at every place but the locative, where Caha
has *hradu* and *městu* and the fragment the tables' *hradě* and *městě*. -/
theorem declines_hrad_mesto_iff (i : Fin 6) :
    (Declines _root_.Czech.hrad Czech.hrad_sg i ↔ czechCase i ≠ .loc) ∧
      (Declines _root_.Czech.mesto Czech.mesto_sg i ↔ czechCase i ≠ .loc) := by
  revert i; decide +kernel

/-- The colloquial *klukách* and *klukama* and *mužema* are not the literary declension, which
the colloquial paradigms follow at the other places. -/
theorem declines_colloquial_iff (i : Fin 6) :
    (Declines _root_.Czech.kluk Czech.kluk_pl_colloquial i ↔
        czechCase i ≠ .loc ∧ czechCase i ≠ .inst) ∧
      (Declines _root_.Czech.muz Czech.muz_pl_colloquial i ↔ czechCase i ≠ .inst) := by
  revert i; decide +kernel

end Caha2009
