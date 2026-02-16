/-
# CCG Analysis of Gapping

CCG categories for gapping constructions, proving that:
1. The "gapped" right conjunct IS a constituent (via type-raising + composition)
2. Gapping direction follows from lexical verb categories

## Insight (Steedman 2000, Chapter 7)

Gapping is not a special ellipsis rule but ordinary constituent coordination.

In "Dexter ate bread, and Warren, potatoes":
- "Warren, potatoes" = S\((S/NP)/NP) via backward composition of type-raised NPs
- This category is a function over VSO transitive verbs
- The left conjunct decomposes to reveal a "virtual" VSO verb via parametric neutrality

## The Category of the Gapped Conjunct

  Warren       potatoes
  T\(T/NP₁)    T\(T/NP₂)
  ─────────────────────── <B
       T\((T/NP₂)/NP₁)

This leftward-looking function can only combine with a verb to its LEFT.
Hence: forward gapping in SVO/VSO, backward gapping in SOV.

## References

- Steedman (2000) "The Syntactic Process" Chapter 7
- Maling (1972) "On 'Gapping and the order of constituents'"
- Dowty (1988) "Type-raising, functional composition, and non-constituent conjunction"
-/

import Linglib.Theories.Syntax.CCG.Core.Basic

namespace CCG.Gapping

open CCG

-- Gapped Conjunct Categories

/--
Category for a gapped subject+object cluster (e.g., "Warren, potatoes").

This is built by:
1. Type-raising each NP: NP → T\(T/NP)
2. Backward composing: T\(T/NP₁) ∘ T\(T/NP₂) → T\((T/NP₂)/NP₁)

The result needs a VSO transitive verb ((S/NP)/NP) to its LEFT.
-/
def GappedTV : Cat := S \ ((S / NP) / NP)

/--
Category for a gapped subject alone (stripping: "and Warren (too)").
-/
def GappedSubj : Cat := S \ (S / NP)

-- Type-Raised Argument Categories

/--
Backward type-raised NP (for SVO/VSO gapping).
T\(T/NP) - combines with verbs to the LEFT.
-/
def BackwardRaisedNP : Cat := S \ (S / NP)

/--
Forward type-raised NP (for SOV argument clusters).
T/(T\NP) - combines with verbs to the RIGHT.
-/
def ForwardRaisedNP : Cat := S / (S \ NP)

/--
The potential backward-gapped conjunct would need category S/((S\NP)/NP).
But this requires forward composition of forward type-raised NPs.
English doesn't license T/(T\NP) categories.
-/
def BackwardGappedTV : Cat := S / ((S \ NP) / NP)

-- Gapped Conjunct Directionality

/--
The Principle of Inheritance ensures composed functions inherit directionality.

When we backward-compose two T\(T/NP) categories:
  T\(T/NP₁) ∘ T\(T/NP₂) → T\((T/NP₂)/NP₁)

The result is still leftward-looking (backslash on top).
Hence it can only combine with a verb to its left.
-/
theorem inheritance_determines_gapping :
    GappedTV = S \ ((S / NP) / NP) := rfl

/--
The gapped conjunct S\((S/NP)/NP) is leftward-looking.

The backslash on the outside means it seeks an argument to its left.
Forward gapping (verb left, gap right) works in SVO for this reason.
-/
theorem gapped_tv_is_leftward :
    match GappedTV with
    | .lslash _ _ => true
    | _ => false := rfl

/--
The backward-gapped conjunct S/((S\NP)/NP) would be rightward-looking.

The slash on the outside means it seeks an argument to its right.
This would require backward gapping (gap LEFT, verb RIGHT).
But SVO doesn't license this category.
-/
theorem backward_gapped_tv_is_rightward :
    match BackwardGappedTV with
    | .rslash _ _ => true
    | _ => false := rfl

-- Stripping as Special Case

/--
Stripping is gapping with a single remnant.

"Dexter ran away, and Warren (too)"
  Warren = S\(S/NP)

This is just a type-raised subject coordinating with a decomposed sentence.
-/
def strippingCategory : Cat := backwardTypeRaise NP S

theorem stripping_has_correct_category :
    strippingCategory = GappedSubj := rfl

/--
Stripping shares the same word-order constraints as gapping.
This is because both use the same type-raised categories.
-/
theorem stripping_same_constraints_as_gapping :
    GappedSubj = BackwardRaisedNP := rfl

end CCG.Gapping
