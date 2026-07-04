import Mathlib.Data.Set.Insert

/-!
# Two-Dimensional Alternative Meanings
[rooth-1985] [rooth-1992] [kratzer-selkirk-2020]

The O-value / A-value pair from Rooth-style alternative semantics.
Every expression has an *ordinary* denotation (`oValue`) and an
*alternatives* set (`aValue`); focus features and operators manipulate
the latter while typically preserving the former.

This file isolates the bare data structure. Symmetry-based refinements
([fox-katzir-2011]) live in `Symmetric.lean`; structural
alternatives ([katzir-2007]) live in `Structural.lean`;
[FoC]/[G] feature semantics live in `Semantics/Focus/`.
-/

namespace Alternatives

/-- Two-dimensional meaning in [rooth-1992]-style alternative semantics.
    Every expression has an O-value and an A-value.

    [kratzer-selkirk-2020] §3, §8. -/
structure AltMeaning (α : Type*) where
  /-- O(rdinary)-value: the actual denotation -/
  oValue : α
  /-- A(lternatives)-value: the set of alternatives (including oValue) -/
  aValue : List α

/-- The O-value of a non-featured expression equals its ordinary denotation.
    The A-value of a non-featured expression is a singleton containing
    its O-value (no alternatives evoked). -/
def AltMeaning.unfeatured {α : Type*} (x : α) : AltMeaning α :=
  { oValue := x, aValue := [x] }

@[simp] theorem AltMeaning.unfeatured_oValue {α : Type*} (x : α) :
    (AltMeaning.unfeatured x).oValue = x := rfl

@[simp] theorem AltMeaning.unfeatured_aValue {α : Type*} (x : α) :
    (AltMeaning.unfeatured x).aValue = [x] := rfl

/-- The alternative set as a `Set` — the theory-side carrier; `aValue`
is its list presentation. -/
def AltMeaning.aSet {α : Type*} (m : AltMeaning α) : Set α :=
  {a | a ∈ m.aValue}

@[simp] theorem AltMeaning.mem_aSet {α : Type*} {m : AltMeaning α} {a : α} :
    a ∈ m.aSet ↔ a ∈ m.aValue := Iff.rfl

@[simp] theorem AltMeaning.unfeatured_aSet {α : Type*} (x : α) :
    (AltMeaning.unfeatured x).aSet = {x} := by
  ext a
  exact List.mem_singleton.trans Set.mem_singleton_iff.symm

end Alternatives
