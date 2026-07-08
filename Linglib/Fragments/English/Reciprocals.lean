import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Syntax.Reciprocal

/-!
# English Reciprocal Fragment
[nordlinger-2023]

English encodes reciprocity with the bipartite quantificational NP
*each other* (bivalent; [nordlinger-2023] ex. 1b), with *one another* as
a variant, plus a closed class of inherently reciprocal predicates
(*quarrel*, *meet*, *kiss*; ex. 7). Both are formally distinct from the
reflexive *themselves*. The bipartite marker derives its form from the
pronoun entry in `Fragments/English/Pronouns.lean`; the lexical strategy
has no exponent, so it is carried by the verb entries themselves
(`lexicalReciprocals`), not by a marker — and correctly does not feed
`Reciprocal.ofInventory` (WALS counts constructions, not lexical
predicates).
-/

namespace English.Reciprocals

open Reciprocal

/-- each other — bipartite quantificational reciprocal (form derived
    from the pronoun entry `English.Pronouns.eachOther`). -/
def eachOther : Marker :=
  { form := Pronouns.eachOther.form, strategy := .bipartiteNP }

/-- The inherently reciprocal predicates (*quarrel*, *meet*;
    [nordlinger-2023] ex. 7), referenced as verb entries — the lexical
    strategy marks predicates, not forms. Lexicon-formed per
    [siloni-2012], though *kiss*/*hug* resist the discontinuous
    construction (fn. 32). Entries beyond *meet* pending in
    `Predicates/Verbal.lean`. -/
def lexicalReciprocals : List Predicates.Verbal.VerbEntry :=
  [Predicates.Verbal.meet]

/-- Marker inventory. -/
def markers : List Marker := [eachOther]

end English.Reciprocals
