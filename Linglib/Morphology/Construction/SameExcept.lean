/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Construction.Schema
import Mathlib.Data.Set.Function

/-!
# Same-except relations

Two items over a shared position space are the *same except* at a set `S` of
positions when they agree everywhere outside `S` ([culicover-jackendoff-2012];
[jackendoff-audring-2020] §3.7). This is literally `Set.EqOn` on the complement,
so the relation inherits mathlib's equal-on API. William James' observation that
comparison presupposes a common frame is the domain-general root; the shared
position type `Pos` encodes the Gentner-Sagi structural-alignment
presupposition — the two items are already put into correspondence.

What happens at the except-positions classifies the relation. In an
**elaboration**, one side is decorated and the other empty (`⊥`): the same as
the other plus something else. In a **contrast**, both sides are decorated and
differ. [jackendoff-audring-2020] add a third reading for the schema-to-instance
case, where the item strictly dominates the schema (`Instantiation`); they hedge
what to call it, and strict order is one settled reading, not William James' or
[culicover-jackendoff-2012]'s. The three cases are intentionally
non-exhaustive — double contrasts and elaborations in different places satisfy
none.

A schema itself expresses a same-except relation to its instances
(`Instantiation.instantiates`): the instantiation case entails
`Schema.Instantiates`.

## Main declarations

- `SameExcept` — agreement off a position set (`Set.EqOn` on the complement)
- `SameExcept.symm`, `SameExcept.mono`, `SameExcept.trans` — the equal-on API
- `Elaboration`, `Contrast`, `Instantiation` — the classification at the
  except-positions
- `Contrast.symm` — contrast is symmetric
- `Instantiation.instantiates` — the schema-instance relation is a same-except relation
-/

namespace Morphology.Construction

variable {Pos α : Type*}

/-- Two items are the *same except* at `S` when they agree off `S`: `Set.EqOn`
on the complement. -/
abbrev SameExcept (f g : Pos → α) (S : Set Pos) : Prop := Set.EqOn f g Sᶜ

/-- Same-except is symmetric. -/
theorem SameExcept.symm {f g : Pos → α} {S : Set Pos} (h : SameExcept f g S) :
    SameExcept g f S :=
  Set.EqOn.symm h

/-- Same-except is monotone in the except-set: agreeing off a smaller set implies
agreeing off a larger one. -/
theorem SameExcept.mono {f g : Pos → α} {S T : Set Pos} (hST : S ⊆ T)
    (h : SameExcept f g S) : SameExcept f g T :=
  Set.EqOn.mono (Set.compl_subset_compl_of_subset hST) h

/-- Same-except is transitive at a fixed except-set. -/
theorem SameExcept.trans {f g k : Pos → α} {S : Set Pos}
    (h₁ : SameExcept f g S) (h₂ : SameExcept g k S) : SameExcept f k S :=
  Set.EqOn.trans h₁ h₂

section PartialOrder
variable [PartialOrder α]

/-- The schema-to-instance case: same except at `S`, where the second strictly
dominates the first — [jackendoff-audring-2020]'s added third reading. -/
def Instantiation (f g : Pos → α) (S : Set Pos) : Prop :=
  SameExcept f g S ∧ ∀ p ∈ S, f p < g p

/-- The schema-instance relation is a same-except relation: an instantiation of a
schema's description entails `Schema.Instantiates`. -/
theorem Instantiation.instantiates {s : Schema Pos α} {w : Pos → α} {S : Set Pos}
    (h : Instantiation s.body w S) : s.Instantiates w := by
  intro p
  by_cases hp : p ∈ S
  · exact (h.2 p hp).le
  · exact (h.1 hp).le

end PartialOrder

section OrderBot
variable [PartialOrder α] [OrderBot α]

/-- An elaboration: same except at `S`, where the first side is present and the
second empty — the same as the other plus something else. -/
def Elaboration (f g : Pos → α) (S : Set Pos) : Prop :=
  SameExcept f g S ∧ ∀ p ∈ S, f p ≠ ⊥ ∧ g p = ⊥

/-- A contrast: same except at `S`, where both sides are present and distinct. -/
def Contrast (f g : Pos → α) (S : Set Pos) : Prop :=
  SameExcept f g S ∧ ∀ p ∈ S, f p ≠ ⊥ ∧ g p ≠ ⊥ ∧ f p ≠ g p

/-- Contrast is symmetric. -/
theorem Contrast.symm {f g : Pos → α} {S : Set Pos} (h : Contrast f g S) :
    Contrast g f S :=
  ⟨h.1.symm, fun p hp => ⟨(h.2 p hp).2.1, (h.2 p hp).1, ((h.2 p hp).2.2).symm⟩⟩

end OrderBot

end Morphology.Construction
