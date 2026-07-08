import Linglib.Syntax.Category.Pronoun.IndefiniteParadigm

/-!
# Russian Indefinite Pronoun Paradigm
[haspelmath-1997] [bubnov-2026] [degano-aloni-2025]
[wals-2013]

Russian has a three-way split among indefinite pronouns, central to
[bubnov-2026]'s argument against nanosyntactic containment for
indefinites. The three series suffix/prefix to interrogative bases
(*kto* 'who', *čto* 'what', etc.); per [wals-2013] F46A, Russian is
classified `.interrogativeBased`.

| Series        | Form         | Haspelmath function | D&A type        |
|---------------|--------------|---------------------|-----------------|
| *-нибудь*     | *kto-nibud'* | non-specific        | (iii) nonSpec   |
| *-то*         | *kto-to*     | specific unknown    | (iv) epistemic  |
| *кое-*        | *koe-kto*    | specific known      | (v) specKnown   |

Note on *-to*: [bubnov-2026] §7 maps *-to* to ∃_epistemic with
semantics `var(∅,x)` — D&A type iv epistemic. Its restriction to the
specific-unknown function (not also non-specific) is due to paradigmatic
competition with *-nibud'*. The D&A theoretical profile of type iv
permits both SU and NS, but *-to*'s actual distribution is SU only —
captured by `IndefinitePronoun.consistentWith` in
`Semantics/Quantification/DeganoAloni2025.lean`.
-/

set_option autoImplicit false

namespace Russian.Indefinites

open Indefinite

/-- *кто-нибудь* (*kto-nibud'*): non-specific indefinite, interrogative
    `kto` 'who' + suffix `-nibud'`. Imperatives, questions, irrealis.
    "Купи что-нибудь" 'Buy something [I don't care what]'. D&A type iii. -/
def nibudEntry : IndefinitePronoun where
  form := "kto-nibud'"
  ontology := .person
  basis := .interrogative
  functions := {.irrealis}

/-- *кто-то* (*kto-to*): specific-unknown function. Speaker believes
    there is a specific referent but doesn't know which. "Кто-то пришёл"
    'Someone [specific] came'.

    [bubnov-2026] §7 maps *-to* to ∃_epistemic with semantics
    `var(∅,x)` — D&A type iv epistemic. The D&A profile of type iv permits
    both SU and NS, but *-to*'s actual distribution is SU only because
    *-nibud'* (type iii) blocks it for NS. The narrower-than-profile claim
    is `consistentWith` (subset, not equality). -/
def toEntry : IndefinitePronoun where
  form := "kto-to"
  ontology := .person
  basis := .interrogative
  functions := {.specificUnknown}

/-- *кое-кто* (*koe-kto*): specific-known indefinite, prefix `koe-` +
    interrogative `kto`. Speaker knows the referent's identity.
    "Кое-кто пришёл" 'Someone [I know who] came'. D&A type v `dep(∅,x)`. -/
def koeEntry : IndefinitePronoun where
  form := "koe-kto"
  ontology := .person
  basis := .interrogative
  functions := {.specificKnown}

/-- The Russian paradigm exhibits an ABC pattern: three distinct
    interrogative-based forms for three distinct functions. No
    morphological containment. -/
def paradigm : IndefiniteParadigm where
  language := "Russian"
  isoCode := "rus"
  forms := [nibudEntry, toEntry, koeEntry]

/-- Russian paradigm exhibits Haspelmath's ABC syncretism: all three
    SK/SU/NS functions distinct. -/
theorem russian_paradigm_is_ABC : paradigm.syncretism = some .ABC := rfl

/-- Russian's WALS F46A classification: single basis `.interrogative`
    across all three forms → derives `.interrogativeBased`. -/
theorem russian_paradigm_is_interrogativeBased :
    paradigm.toWALS46A = some .interrogativeBased := rfl

end Russian.Indefinites
