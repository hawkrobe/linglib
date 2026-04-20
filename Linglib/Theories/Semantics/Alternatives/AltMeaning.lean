/-!
# Two-Dimensional Alternative Meanings
@cite{rooth-1985} @cite{rooth-1992} @cite{kratzer-selkirk-2020}

The O-value / A-value pair from Rooth-style alternative semantics.
Every expression has an *ordinary* denotation (`oValue`) and an
*alternatives* set (`aValue`); focus features and operators manipulate
the latter while typically preserving the former.

This file isolates the bare data structure. Categorical refinements
(@cite{fox-katzir-2011}) live in `Categorical.lean`; structural
alternatives (@cite{katzir-2007}) live in `Structural.lean`;
[FoC]/[G] feature semantics live in `Theories/Semantics/Focus/`.
-/

namespace Semantics.Alternatives

/-- Two-dimensional meaning in @cite{rooth-1992}-style alternative semantics.
    Every expression has an O-value and an A-value.

    @cite{kratzer-selkirk-2020} §3, §8. -/
structure AltMeaning (α : Type) where
  /-- O(rdinary)-value: the actual denotation -/
  oValue : α
  /-- A(lternatives)-value: the set of alternatives (including oValue) -/
  aValue : List α

/-- The O-value of a non-featured expression equals its ordinary denotation.
    The A-value of a non-featured expression is a singleton containing
    its O-value (no alternatives evoked). -/
def AltMeaning.unfeatured {α : Type} (x : α) : AltMeaning α :=
  { oValue := x, aValue := [x] }

@[simp] theorem AltMeaning.unfeatured_oValue {α : Type} (x : α) :
    (AltMeaning.unfeatured x).oValue = x := rfl

@[simp] theorem AltMeaning.unfeatured_aValue {α : Type} (x : α) :
    (AltMeaning.unfeatured x).aValue = [x] := rfl

end Semantics.Alternatives
