import Linglib.Data.UD.UPOS
import Linglib.Syntax.Reciprocal
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Wambaya reciprocals

Wambaya marks reciprocity with the bound morpheme *-ngg-* (glossed RR) in the auxiliary's pronominal
complex, a bound reciprocal pronoun in the sense of [evans-2008] that serves both the reciprocal and
the reflexive function: *Alag-bulu wurlu-ngg-a nyurrunyurru* 'The two children are chasing each
other' ([nordlinger-2023] ex. 11, from [nordlinger-1998]).

## TODO

The subject's case under reciprocalization is unrecorded: ex. 11 glosses the dual subject as
nominative, while the ergative subject that keeps a reciprocal clause transitive is shown for
Warlpiri (ex. 18b).

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [R. Nordlinger, *A grammar of Wambaya, Northern Territory (Australia)* (1998)][nordlinger-1998]
* [N. Evans, *Reciprocal Constructions: Towards a Structural Typology* (2008)][evans-2008]
-/

namespace Wambaya.Reciprocals


/-- -ngg- (RR) — reciprocal/reflexive bound morpheme in the auxiliary.
    The gloss value represents the morpheme; surface allomorphs vary
    by auxiliary paradigm. -/
def rrMorpheme : Word :=
  { form :="-ngg-", cat := .PART }

open Reciprocal in
/-- The RR morpheme as a typological marker: a bound reciprocal pronoun
    serving both reciprocal and reflexive functions (form derived from
    `rrMorpheme`). -/
def rr : Marker :=
  { form := rrMorpheme.form, strategy := .boundPronoun
  , readings := {.reciprocal, .reflexive} }

open Reciprocal in
/-- Marker inventory. -/
def markers : Finset Marker := {rr}

end Wambaya.Reciprocals
