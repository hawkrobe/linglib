import Linglib.Typology.Indefinite

/-!
# Kannada Indefinite Pronouns
@cite{haspelmath-1997} @cite{degano-aloni-2025} @cite{bubnov-2026} @cite{wals-2013}

Kannada indefinites are formed by suffixing particles to interrogative
pronouns: *yāru-oo* 'someone (specific unknown)', *yāru-aadaruu* 'anyone
(non-specific)', etc. Per @cite{wals-2013} F46A, Kannada is classified
`.interrogativeBased`.

*-oo* is the canonical example of D&A type vii specific-unknown
(`dep(v,x) ∧ var(∅,x)`): a conjunctive requirement making the referent
constant within each epistemic world but varying across worlds — "specific
but unknown." This conjunctive type is cross-linguistically rare
(@cite{bubnov-2026} §6, @cite{degano-aloni-2025}).
-/

set_option autoImplicit false

namespace Fragments.Kannada.Indefinites

open Typology.Indefinite

/-- Kannada *-oo*: specific-unknown indefinite suffix on interrogative
    bases (e.g., *yāru-oo* 'someone'). D&A type vii: `dep(v,x) ∧ var(∅,x)`.
    @cite{haspelmath-1997}, @cite{degano-aloni-2025}. -/
def ooEntry : IndefiniteEntry where
  language := "Kannada"
  form := "yāru-oo"
  gloss := "someone (specific unknown)"
  basis := .interrogative
  functions := {.specificUnknown}

/-- Kannada *-aadaruu*: non-specific indefinite suffix on interrogative
    bases (e.g., *yāru-aadaruu* 'anyone'). D&A type iii: `var(v,x)`. -/
def aadaruuEntry : IndefiniteEntry where
  language := "Kannada"
  form := "yāru-aadaruu"
  gloss := "anyone (non-specific)"
  basis := .interrogative
  functions := {.irrealis}

/-- The Kannada indefinite paradigm: SK gap, NS + SU only. -/
def paradigm : IndefiniteParadigm where
  language := "Kannada"
  isoCode := "kan"
  forms := [ooEntry, aadaruuEntry]

/-- Kannada's WALS F46A classification: single basis `.interrogative`
    across both forms → derives `.interrogativeBased`. -/
theorem kannada_paradigm_is_interrogativeBased :
    paradigm.toWALS46A = some .interrogativeBased := rfl

end Fragments.Kannada.Indefinites
