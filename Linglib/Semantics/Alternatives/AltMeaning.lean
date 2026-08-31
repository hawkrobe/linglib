import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Lattice

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
@[ext]
structure AltMeaning (α : Type*) where
  /-- O(rdinary)-value: the actual denotation -/
  oValue : α
  /-- A(lternatives)-value: the alternatives, which by Rooth's containment constraint include the
  ordinary value — see `WellFormed`, kept a predicate rather than a field so that the composition
  engine below is a `Monad`. -/
  aValue : Set α

/-- The O-value of a non-featured expression equals its ordinary denotation.
    The A-value of a non-featured expression is a singleton containing
    its O-value (no alternatives evoked). -/
def AltMeaning.unfeatured {α : Type*} (x : α) : AltMeaning α :=
  { oValue := x, aValue := {x} }

@[simp] theorem AltMeaning.unfeatured_oValue {α : Type*} (x : α) :
    (AltMeaning.unfeatured x).oValue = x := rfl

@[simp] theorem AltMeaning.unfeatured_aValue {α : Type*} (x : α) :
    (AltMeaning.unfeatured x).aValue = {x} := rfl

/-! ### The composition engine

Alternative semantics composes pointwise ([rooth-1985]): the O-value
applies ordinarily while the A-value collects applications of
alternative functions to alternative arguments (Hamblin functional
application). `AltMeaning` is the product of the identity and set
monads, so the engine is a lawful `Monad`: `pure` is `unfeatured`,
`<$>`/`<*>` are the recursive clauses of the two-dimensional semantics,
and `oValue` is a monad morphism onto the ordinary dimension. -/

namespace AltMeaning

universe u
variable {α β : Type u}

instance : Monad AltMeaning where
  pure := unfeatured
  bind m f := ⟨(f m.oValue).oValue, ⋃ a ∈ m.aValue, (f a).aValue⟩

instance : LawfulMonad AltMeaning := LawfulMonad.mk'
  (id_map := fun m => by
    cases m; simp [Functor.map, bind, pure, unfeatured])
  (pure_bind := fun x f => by
    simp [bind, pure, unfeatured])
  (bind_assoc := fun m f g => by
    cases m; simp [bind, Set.biUnion_iUnion])

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
@[simp] theorem mem_aValue_map {f : α → β} {m : AltMeaning α} {b : β} :
    b ∈ (f <$> m).aValue ↔ ∃ a ∈ m.aValue, f a = b := by
  simp [Functor.map, bind, pure, unfeatured, eq_comm]

/-- Membership in an applied A-set: Hamblin functional application. -/
@[simp] theorem mem_aValue_seq {mf : AltMeaning (α → β)} {ma : AltMeaning α}
    {b : β} :
    b ∈ (mf <*> ma).aValue ↔ ∃ g ∈ mf.aValue, ∃ a ∈ ma.aValue, g a = b := by
  simp [Seq.seq, bind, pure, unfeatured, eq_comm]

/-! ### `aValue` as a morphism into the `Set` applicative

Together with the `oValue` monad-morphism laws above, these exhibit
the alternatives monad as a span `Id ⟵ AltMeaning ⟶ Set`: ordinary
meaning and focal-target set are its two structure-preserving
projections. Hamblin application is the image of `<*>` under `aValue`. -/

theorem aValue_pure (a : α) : (pure a : AltMeaning α).aValue = {a} := by
  ext b; simp [pure, unfeatured]

theorem aValue_seq (mf : AltMeaning (α → β)) (ma : AltMeaning α) :
    (mf <*> ma).aValue = mf.aValue.seq ma.aValue := by
  ext b; simp only [mem_aValue_seq, Set.mem_seq_iff]

theorem aValue_bind (m : AltMeaning α) (f : α → AltMeaning β) :
    (m >>= f).aValue = {b | ∃ a ∈ m.aValue, b ∈ (f a).aValue} := by
  ext b; simp [Bind.bind, bind]

/-- Rooth's containment constraint: the A-value contains the O-value. -/
def WellFormed (m : AltMeaning α) : Prop := m.oValue ∈ m.aValue

theorem WellFormed.unfeatured (x : α) :
    (AltMeaning.unfeatured x).WellFormed := rfl

/-- Composition preserves well-formedness. -/
theorem WellFormed.bind {m : AltMeaning α} {f : α → AltMeaning β}
    (hm : m.WellFormed) (hf : ∀ a, (f a).WellFormed) :
    (m >>= f).WellFormed :=
  Set.mem_biUnion hm (hf _)

theorem WellFormed.map {f : α → β} {m : AltMeaning α} (hm : m.WellFormed) :
    (f <$> m).WellFormed :=
  hm.bind fun a => WellFormed.unfeatured (f a)

/-! ### Givenness -/

/-- Given with respect to `a`: the alternatives have collapsed to the
singleton `{a}` ([kratzer-selkirk-2020] (46)). -/
def Given (m : AltMeaning α) (a : α) : Prop := m.aValue = {a}

/-- Unfeatured meanings are Given with respect to their value. -/
theorem Given.unfeatured (x : α) : (unfeatured x).Given x :=
  unfeatured_aValue x

/-- A Given function collapses Hamblin composition to application on
the argument's alternatives — deaccented material contributes exactly
its ordinary value. -/
theorem Given.aValue_seq {mf : AltMeaning (α → β)} {f : α → β}
    (h : mf.Given f) (ma : AltMeaning α) :
    (mf <*> ma).aValue = f '' ma.aValue := by
  ext b
  simp only [mem_aValue_seq, Set.mem_image]
  constructor
  · rintro ⟨g, hg, a, ha, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp (h ▸ hg)
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨f, h ▸ rfl, a, ha, rfl⟩

end AltMeaning

end Alternatives
