import Linglib.Syntax.Reflex
import Linglib.Fragments.Mayan.Params

/-!
# Kaqchikel Extraction Morphology (Agent Focus)

Theory-neutral extraction-marking data for Kaqchikel (K'ichean, Mayan),
from the Patzún variety described by [erlewine-2016]. Agent Focus (AF)
is the dedicated verb form marking local Ā-extraction of the transitive
subject, with no Set A slot. Patient extraction
never triggers it, long-distance subject extraction triggers it on the
embedded verb only, intervening preverbal material obviates it, and
when both arguments are 1st/2nd person the full-agreement transitive
appears even under subject extraction. Intransitive verbs never undergo
AF, so the marked subject is A, not S. Extraction of a locative,
instrument, dative or benefactive phrase may add the fronting particle
*wi* to the verbal complex; in this variety the particle is optional,
and benefactives license it where other varieties' do not
([mendes-ranero-2021]). Reasons and temporals never license it, and
manners and purposes are unattested with it ([elkins-torrence-brown-2026]).

## Main declarations

* `Kaqchikel.Extraction.realize`: the reflexes extraction from each
  `Mayan.ExtractionSite` licenses.

## Implementation notes

The verb form AF alternates on is the pan-Mayan `Mayan.VerbForm`
(`Fragments/Mayan/Params.lean`); the AF agreement paradigm is in
`Agreement.lean`; the focus construction's realization, with AF as its
verb-hosted reflex, is in `Focus.lean`; the interpreting OT and Voice
analyses live in `Studies/Erlewine2016.lean` and
`Studies/CoonMateoPedroPreminger2014.lean`.

## References

* [elkins-torrence-brown-2026]
* [erlewine-2016]
* [mendes-ranero-2021]
-/


namespace Kaqchikel

namespace Extraction

/-- The hosts of Kaqchikel reflexes: the verb stem, the verbal complex
the enclitic *wi* attaches to, and the extracted phrase itself, which
the focus construction marks. -/
inductive Host where
  | verb
  | verbalComplex
  | phrase
  deriving DecidableEq, Repr

/-- Transitive-subject extraction switches the verb to AF (the Agent
Focus suffix, with Set A suppressed, [erlewine-2016]); extraction of a
locative, instrument, dative or benefactive phrase licenses *wi* on the
verbal complex ([mendes-ranero-2021]); nothing else is marked. -/
def realize : Mayan.ExtractionSite → Finset (Reflex Host)
  | .core .A => {.morpheme .verb}
  | .adjunct .instrument | .adjunct .benefactive | .adjunct .dative | .adjunct .locative =>
      {.morpheme .verbalComplex}
  | _ => ∅

end Extraction

end Kaqchikel
