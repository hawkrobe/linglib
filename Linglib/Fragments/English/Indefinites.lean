import Linglib.Syntax.Category.Pronoun.IndefiniteParadigm

/-!
# English Indefinite Pronouns
[haspelmath-1997] [wals-2013]

English forms its indefinite pronouns by prefixing `some-` to the
generic-noun stems `-one`, `-body`, `-thing`, `-where` — yielding
*someone*, *somebody*, *something*, *somewhere* (and parallel `any-`,
`no-`, `every-` series). Per [wals-2013] F46A, English is classified
`.genericNounBased` on this basis.

The single `some-` series covers all three SK/SU/NS functions on
[haspelmath-1997]'s map, yielding the AAA syncretism (D&A type i
unmarked).
-/

set_option autoImplicit false

namespace English.Indefinites

open Indefinite

/-- English `some-` series (*someone*, *somebody*, *something*, …):
    AAA syncretism, D&A type i unmarked. The form is generic-noun-based
    (the host stems `-one`, `-body`, `-thing` are nouns), per WALS F46A. -/
def someEntry : IndefinitePronoun where
  form := "someone/-body/-thing"
  ontology := .person
  basis := .genericNoun
  functions := {.specificKnown, .specificUnknown, .irrealis}

/-- The English indefinite paradigm (one series, parallel to *any-*/*no-*
    not yet formalized). -/
def paradigm : IndefiniteParadigm where
  language := "English"
  isoCode := "eng"
  forms := [someEntry]

/-- English `some-` covers all three SK/SU/NS functions: AAA syncretism. -/
theorem english_paradigm_is_AAA : paradigm.syncretism = some .AAA := rfl

/-- English's WALS F46A classification: derived from the paradigm's
    morphological-basis distribution (single basis `.genericNoun` →
    F46A `.genericNounBased`). Cross-check vs `F46A.allData` lives in
    `Studies/Haspelmath1997.lean`. -/
theorem english_paradigm_is_genericNounBased :
    paradigm.toWALS46A = some .genericNounBased := rfl

end English.Indefinites
