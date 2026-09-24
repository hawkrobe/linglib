module

public import Linglib.Fragments.Slavic.Declension

/-!
# Serbian declension

This file gives the Serbian words [caha-2009] declines in his tables of Slavic syncretism: seven
nouns in the singular and the plural, and the personal pronouns. Each is a
`Slavic.Declension.Paradigm`, its form in each of the six cases, with the tone marks of the source.

## References

* [caha-2009]
-/

@[expose] public section

namespace Serbian.Declension

open Slavic.Declension

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

end Serbian.Declension
