import Linglib.Core.IndefiniteType

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

open Core.IndefiniteType

/-- Yakut *-ere*: specific unknown + specific known (ABB).
    D&A type (ii) specific: dep(v,x).
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def ere : IndefiniteEntry where
  language := "Yakut"
  form := "-ere"
  gloss := "some (specific)"
  specType := .specific
  allowsSK := true; allowsSU := true; allowsNS := false
  source := "Haspelmath 1997"

/-- Yakut *-eme*: non-specific only.
    D&A type (iii) non-specific: var(v,x).
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def eme : IndefiniteEntry where
  language := "Yakut"
  form := "-eme"
  gloss := "some (non-specific)"
  specType := .nonSpecific
  allowsSK := false; allowsSU := false; allowsNS := true
  source := "Haspelmath 1997"

theorem ere_consistent : ere.distributionConsistent = true := rfl
theorem eme_consistent : eme.distributionConsistent = true := rfl

end Fragments.Yakut.Indefinites
