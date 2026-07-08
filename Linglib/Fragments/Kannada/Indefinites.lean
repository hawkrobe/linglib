import Linglib.Syntax.Category.Pronoun.IndefiniteParadigm

/-!
# Kannada Indefinite Pronouns
[haspelmath-1997] [degano-aloni-2025] [bubnov-2026] [wals-2013]

Kannada indefinites are formed by suffixing particles to interrogative
pronouns: *yāru-oo* 'someone (specific unknown)', *yāru-aadaruu* 'anyone
(non-specific)', etc. Per [wals-2013] F46A, Kannada is classified
`.interrogativeBased`.

*-oo* is the canonical example of D&A type vii specific-unknown
(`dep(v,x) ∧ var(∅,x)`): a conjunctive requirement making the referent
constant within each epistemic world but varying across worlds — "specific
but unknown." This conjunctive type is cross-linguistically rare
([bubnov-2026] §6, [degano-aloni-2025]).
-/

set_option autoImplicit false

namespace Kannada.Indefinites

open Indefinite

/-- Kannada *-oo*: specific-unknown indefinite suffix on interrogative
    bases (e.g., *yāru-oo* 'someone'). D&A type vii: `dep(v,x) ∧ var(∅,x)`.
    [haspelmath-1997], [degano-aloni-2025]. -/
def ooEntry : IndefinitePronoun where
  form := "yāru-oo"
  ontology := .person
  basis := .interrogative
  functions := {.specificUnknown}

/-- Kannada *-aadaruu*: non-specific indefinite suffix on interrogative
    bases (e.g., *yāru-aadaruu* 'anyone'). D&A type iii: `var(v,x)`. -/
def aadaruuEntry : IndefinitePronoun where
  form := "yāru-aadaruu"
  ontology := .person
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

end Kannada.Indefinites
