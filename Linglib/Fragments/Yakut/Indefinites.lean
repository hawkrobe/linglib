import Linglib.Features.IndefiniteType

/-!
# Yakut (Sakha) Indefinite Pronouns
@cite{haspelmath-1997} @cite{bubnov-2026}

Yakut has a two-way split: *-ere* covers both specific-known and
specific-unknown functions (ABB pattern), while *-eme* covers the
non-specific function.

*-ere* is type (ii) specific (dep(v,x)): its semantics requires
constancy within each epistemic world, permitting both SK and SU
contexts but excluding NS.
-/

set_option autoImplicit false

namespace Fragments.Yakut.Indefinites

open Features.IndefiniteType

/-- Yakut *-ere*: specific unknown + specific known (ABB).
    D&A type (ii) specific: dep(v,x).
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def ereEntry : IndefiniteEntry where
  language := "Yakut"
  form := "-ere"
  gloss := "some (specific)"
  specType := .specific
  allowsSK := true
  allowsSU := true
  allowsNS := false
  source := "Haspelmath 1997"

/-- Yakut *-eme*: non-specific only.
    D&A type (iii) non-specific: var(v,x).
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def emeEntry : IndefiniteEntry where
  language := "Yakut"
  form := "-eme"
  gloss := "some (non-specific)"
  specType := .nonSpecific
  allowsSK := false
  allowsSU := false
  allowsNS := true
  source := "Haspelmath 1997"

/-- The Yakut indefinite paradigm: an ABB-pattern two-way split. -/
def paradigm : List IndefiniteEntry := [ereEntry, emeEntry]

theorem paradigm_consistent : paradigm.all (·.distributionConsistent) := by decide

end Fragments.Yakut.Indefinites
