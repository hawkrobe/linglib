module

public import Linglib.Data.UD.UPOS
public import Linglib.Syntax.Reciprocal
public import Linglib.Morphology.Word.Basic

@[expose] public section

open Morphology (Word)

/-!
# Wambaya reciprocals

Wambaya marks reflexivity and reciprocity with the clitic *-ngg-* (glossed RR) in the object
position of the second-position auxiliary: *Alag-bulu wurlu-ngg-a nyurrunyurru* 'The two children
are chasing each other' ([nordlinger-2023] ex. 11, from [nordlinger-1998]). Though it looks like a
reflexive/reciprocal object pronoun such as Warlpiri *-nyanu*, the clause is intransitive
([evans-et-al-2007]): the subject noun phrase is nominative rather than ergative (their (27)), a
controlled complement takes the subject-control form (29), and *-ngg-* also occurs with
semi-transitive verbs, whose objects the auxiliary never cross-references (30). It is a
valency-reducing marker of the predicate, not an argument.

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [R. Nordlinger, *A grammar of Wambaya, Northern Territory (Australia)* (1998)][nordlinger-1998]
* [N. Evans, A. Gaby and R. Nordlinger, *Valency Mismatches and the Coding of Reciprocity in
  Australian Languages* (2007)][evans-et-al-2007]
-/

namespace Wambaya.Reciprocals


/-- -ngg- (RR) — reciprocal/reflexive bound morpheme in the auxiliary.
    The gloss value represents the morpheme; surface allomorphs vary
    by auxiliary paradigm. -/
def rrMorpheme : Word :=
  { form :="-ngg-", cat := .PART }

open Reciprocal in
/-- The RR clitic as a reciprocal marker, reflexive as well; it marks the predicate rather than
    filling the object slot ([evans-et-al-2007]). -/
def rr : Marker :=
  { form := rrMorpheme.form, strategy := .recipClitic, readings := {.reciprocal, .reflexive} }

open Reciprocal in
/-- Marker inventory. -/
def markers : Finset Marker := {rr}

end Wambaya.Reciprocals
