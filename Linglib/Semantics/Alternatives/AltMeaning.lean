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

/-! ### The composition engine

Alternative semantics composes pointwise ([rooth-1985]): the O-value
applies ordinarily while the A-value collects applications of
alternative functions to alternative arguments (Hamblin functional
application). `AltMeaning` is the product of the identity and list
monads, so the engine is a lawful `Monad`: `pure` is `unfeatured`,
`<$>`/`<*>` are the recursive clauses of the two-dimensional semantics,
and `oValue` is a monad morphism onto the ordinary dimension. -/

namespace AltMeaning

universe u
variable {α β : Type u}

instance : Monad AltMeaning where
  pure := unfeatured
  bind m f := ⟨(f m.oValue).oValue, m.aValue.flatMap fun a => (f a).aValue⟩

instance : LawfulMonad AltMeaning := LawfulMonad.mk'
  (id_map := fun m => by
    cases m; simp [Functor.map, unfeatured])
  (pure_bind := fun x f => by
    simp [bind, pure, unfeatured])
  (bind_assoc := fun m f g => by
    cases m; simp [bind, List.flatMap_assoc])

/-- The O-projection is a monad morphism: composition preserves the
ordinary dimension. -/
@[simp] theorem oValue_pure (x : α) : (pure x : AltMeaning α).oValue = x := rfl

@[simp] theorem oValue_bind (m : AltMeaning α) (f : α → AltMeaning β) :
    (m >>= f).oValue = (f m.oValue).oValue := rfl

@[simp] theorem oValue_map (f : α → β) (m : AltMeaning α) :
    (f <$> m).oValue = f m.oValue := rfl

@[simp] theorem oValue_seq (mf : AltMeaning (α → β)) (ma : AltMeaning α) :
    (mf <*> ma).oValue = mf.oValue ma.oValue := rfl

/-- Membership in a mapped A-set: the image law of the engine. -/
@[simp] theorem mem_aSet_map {f : α → β} {m : AltMeaning α} {b : β} :
    b ∈ (f <$> m).aSet ↔ ∃ a ∈ m.aSet, f a = b := by
  simp [Functor.map, aSet, unfeatured, eq_comm]

/-- Membership in an applied A-set: Hamblin functional application. -/
@[simp] theorem mem_aSet_seq {mf : AltMeaning (α → β)} {ma : AltMeaning α}
    {b : β} :
    b ∈ (mf <*> ma).aSet ↔ ∃ g ∈ mf.aSet, ∃ a ∈ ma.aSet, g a = b := by
  simp [Seq.seq, aSet, unfeatured, eq_comm]

/-- Rooth's containment constraint: the A-value contains the O-value. -/
def WellFormed (m : AltMeaning α) : Prop := m.oValue ∈ m.aValue

theorem WellFormed.unfeatured (x : α) :
    (AltMeaning.unfeatured x).WellFormed := List.mem_singleton.mpr rfl

/-- Composition preserves well-formedness. -/
theorem WellFormed.bind {m : AltMeaning α} {f : α → AltMeaning β}
    (hm : m.WellFormed) (hf : ∀ a, (f a).WellFormed) :
    (m >>= f).WellFormed :=
  List.mem_flatMap.mpr ⟨m.oValue, hm, hf _⟩

theorem WellFormed.map {f : α → β} {m : AltMeaning α} (hm : m.WellFormed) :
    (f <$> m).WellFormed :=
  hm.bind fun a => WellFormed.unfeatured (f a)

end AltMeaning

end Alternatives
