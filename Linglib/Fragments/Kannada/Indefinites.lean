import Linglib.Features.IndefiniteType

/-!
# Kannada Indefinite Pronouns
@cite{haspelmath-1997} @cite{degano-aloni-2025} @cite{bubnov-2026}

Kannada *-oo* is the canonical example of D&A type (vii) specific
unknown: it imposes a conjunctive requirement dep(v,x) ∧ var(∅,x).
The referent is constant within each epistemic world (dep(v,x)) but
differs across worlds (var(∅,x)) — "specific but unknown." This
conjunctive restriction makes type (vii) cross-linguistically rare
(@cite{bubnov-2026} §6, @cite{degano-aloni-2025}).
-/

set_option autoImplicit false

namespace Fragments.Kannada.Indefinites

open Features.IndefiniteType

/-- Kannada *-oo*: specific unknown (type vii).
    D&A semantics: dep(v,x) ∧ var(∅,x). Rare conjunctive type.
    @cite{haspelmath-1997}, @cite{degano-aloni-2025}. -/
def ooEntry : IndefiniteEntry where
  language := "Kannada"
  form := "-oo"
  gloss := "some (specific unknown)"
  specType := .specificUnknown
  allowsSK := false
  allowsSU := true
  allowsNS := false
  source := "Haspelmath 1997, Degano & Aloni 2025"

/-- Kannada *-aadaruu*: non-specific.
    D&A type (iii): var(v,x). -/
def aadaruuEntry : IndefiniteEntry where
  language := "Kannada"
  form := "-aadaruu"
  gloss := "some (non-specific)"
  specType := .nonSpecific
  allowsSK := false
  allowsSU := false
  allowsNS := true
  source := "Haspelmath 1997"

/-- The Kannada indefinite paradigm: SK gap, NS + SU only. -/
def paradigm : List IndefiniteEntry := [ooEntry, aadaruuEntry]

theorem paradigm_consistent : paradigm.all (·.distributionConsistent) := by decide

end Fragments.Kannada.Indefinites
