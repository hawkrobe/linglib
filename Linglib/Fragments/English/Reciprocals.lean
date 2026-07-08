import Linglib.Fragments.English.Pronouns
import Linglib.Syntax.Reciprocal

/-!
# English Reciprocal Fragment
[nordlinger-2023]

English encodes reciprocity with the bipartite quantificational NP
*each other* (bivalent; [nordlinger-2023] ex. 1b), with *one another* as
a variant, plus a closed class of inherently reciprocal predicates
(*quarrel*, *meet*, *kiss*; ex. 7). Both are formally distinct from the
reflexive *themselves*. Pronoun entries live in
`Fragments/English/Pronouns.lean`; the markers here derive their forms
from those entries.
-/

namespace English.Reciprocals

open Reciprocal

/-- each other — bipartite quantificational reciprocal (form derived
    from the pronoun entry `English.Pronouns.eachOther`). -/
def eachOther : ReciprocalMarker :=
  { form := Pronouns.eachOther.form, strategy := .bipartiteNP }

/-- The closed class of inherently reciprocal predicates (*quarrel*,
    *meet*; [nordlinger-2023] ex. 7). Lexicon-formed per [siloni-2012],
    though *kiss*/*hug* resist the discontinuous construction (fn. 32). -/
def lexicalClass : ReciprocalMarker :=
  { form := "quarrel/meet (lexical class)", strategy := .lexical }

/-- Marker inventory, primary strategy first. -/
def markers : List ReciprocalMarker := [eachOther, lexicalClass]

end English.Reciprocals
