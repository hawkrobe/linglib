import Linglib.Morphology.Realization
import Linglib.Syntax.Extraction

/-!
# Kaqchikel Extraction Morphology (Agent Focus)

Theory-neutral extraction-marking data for Kaqchikel (K'ichean, Mayan),
from the Patzún variety described by [erlewine-2016]. Agent Focus (AF)
is the dedicated verb form marking local Ā-extraction of the transitive
subject: the suffix *-ö* or *-n*, with no Set A slot. Patient extraction
never triggers it, long-distance subject extraction triggers it on the
embedded verb only, intervening preverbal material obviates it, and
when both arguments are 1st/2nd person the full-agreement transitive
appears even under subject extraction. Intransitive verbs never undergo
AF, so the marked "subject" is A, not S.

## Main declarations

* `Kaqchikel.Extraction.realize`: the overt reflexes of extraction from
  each target position, with `Kaqchikel.Extraction.strategy` as the
  WALS-style label.

## Implementation notes

The verb form AF alternates on is the pan-Mayan `Mayan.VerbForm`
(`Fragments/Mayan/Params.lean`); the AF agreement paradigm is in
`Agreement.lean`; the focus construction's realization, with AF as its
verb-hosted reflex, is in `Focus.lean`; the interpreting OT and Voice
analyses live in `Studies/Erlewine2016.lean` and
`Studies/CoonMateoPedroPreminger2014.lean`.
-/

namespace Kaqchikel

namespace Extraction

/-- Reflex hosts for Kaqchikel extraction marking. -/
inductive Site where
  | verb
  deriving DecidableEq, Repr

/-- Transitive-subject extraction switches the verb to AF (the suffix
    *-ö* or *-n*, with Set A suppressed, [erlewine-2016]); nothing else
    is marked. -/
def realize : _root_.Extraction.ExtractionTarget → List (Morphology.Reflex Site)
  | .subject => [.morpheme .verb]
  | _ => []

/-- WALS-style label: a dedicated morpheme marks extraction. -/
def strategy : _root_.Extraction.ExtractionMarkingStrategy := .dedicatedMorpheme

end Extraction

end Kaqchikel
