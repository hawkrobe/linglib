module

public import Linglib.Fragments.Slavic.Declension

/-!
# Slovak declension

This file gives the Slovak words [caha-2009] declines beside their Czech counterparts. Each is a
`Slavic.Declension.Paradigm`, its form in each of the six cases.

## References

* [caha-2009]
-/

@[expose] public section

namespace Slovak.Declension

open Slavic.Declension

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

end Slovak.Declension
