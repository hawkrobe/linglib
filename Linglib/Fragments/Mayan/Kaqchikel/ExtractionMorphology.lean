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

Despite the traditional Mayanist name, AF is not a focus construction:
its four triggers are wh-questions, relative clauses, focus fronting,
and argument existentials ([erlewine-2016] §2.2). The realization of
the focus construction, with AF as its verb-hosted reflex under
A-focus, is in `Focus.lean`.

## Main declarations

* `Kaqchikel.extractionStrategy`, `Kaqchikel.extractionMarkedPositions`,
  `Kaqchikel.extractionDistinguishesPosition`: the extraction profile.

## Implementation notes

The verb form AF alternates on is the pan-Mayan `Mayan.VerbForm`
(`Fragments/Mayan/Params.lean`); the AF agreement paradigm is in
`Agreement.lean`; the interpreting OT and Voice analyses live in
`Studies/Erlewine2016.lean` and
`Studies/CoonMateoPedroPreminger2014.lean`.
-/

namespace Kaqchikel

/-- Kaqchikel marks transitive-subject extraction with dedicated AF
    morphology: the suffix *-ö* or *-n*, with Set A suppressed
    ([erlewine-2016]). -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .dedicatedMorpheme
def extractionMarkedPositions : List Extraction.ExtractionTarget := [.subject]
def extractionDistinguishesPosition : Bool := true

end Kaqchikel
