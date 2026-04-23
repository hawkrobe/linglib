import Linglib.Features.IndefiniteType

/-!
# Latin Indefinite Pronouns
@cite{haspelmath-1997} @cite{bubnov-2026}

Latin has a two-way split in the SK–SU–NS region of Haspelmath's map:
*ali-* covers the non-specific and specific-unknown functions (AAB
pattern), while *-dam* covers the specific-known function.

*ali-* is type (iv) epistemic (var(∅,x)): its semantics permits both
SU and NS contexts, and since *-dam* only covers SK, there is no
competition — *ali-*'s distribution matches its semantic profile.
-/

set_option autoImplicit false

namespace Fragments.Latin.Indefinites

open Features.IndefiniteType

/-- Latin *ali-*: non-specific + specific unknown (AAB pattern).
    D&A type (iv) epistemic: var(∅,x). Distribution matches profile.
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def ali : IndefiniteEntry where
  language := "Latin"
  form := "ali-"
  gloss := "some (non-specific/unknown)"
  specType := .epistemic
  allowsSK := false; allowsSU := true; allowsNS := true
  source := "Haspelmath 1997"

/-- Latin *-dam*: specific known only.
    D&A type (v): dep(∅,x).
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def dam : IndefiniteEntry where
  language := "Latin"
  form := "-dam"
  gloss := "some (known)"
  specType := .specificKnown
  allowsSK := true; allowsSU := false; allowsNS := false
  source := "Haspelmath 1997"

theorem ali_consistent : ali.distributionConsistent = true := rfl
theorem dam_consistent : dam.distributionConsistent = true := rfl

end Fragments.Latin.Indefinites
