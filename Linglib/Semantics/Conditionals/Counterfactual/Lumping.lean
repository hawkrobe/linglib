module

public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.Max

/-!
# Lumping

This file defines Kratzer's lumping relation between propositions. Situations are the elements of
a type with a parthood preorder, propositions are sets of situations, and the worlds are the
maximal situations. A proposition `p` lumps a proposition `q` in a world `w` when `p` is true in
`w` and `q` is true in every part of `w` in which `p` is true. The file also defines the logical
relations of [kratzer-2012] §5.3.3, which quantify over worlds only, and shows that under the
discrete order, where every situation is a world, lumping collapses to joint truth.

## Main definitions

* `Counterfactual.Lumps`: lumping at a situation.
* `Counterfactual.worlds`: the maximal situations.
* `Counterfactual.Follows`, `Counterfactual.IsConsistent`, `Counterfactual.IsCompatible`: logical
  consequence, consistency, and compatibility.

## Implementation notes

Kratzer defines lumping for worlds. `Lumps` is stated for any situation, and the restriction to
worlds is an `IsMax` hypothesis.

## References

* [A. Kratzer, *An investigation of the lumps of thought* (1989)][kratzer-1989]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
-/

@[expose] public section

namespace Conditional.Counterfactual

open Set

/-! ### Lumping

[kratzer-2012] defines lumping on p. 118, crediting its second condition to Yablo's local
implication (p. 114, footnote 4). -/

section LumpingCore

variable {S : Type*} [Preorder S]

/-- `p` lumps `q` at `w` when `p` is true at `w` and `q` is true at every part of `w` at which `p`
is true ([kratzer-2012] p. 118). -/
structure Lumps (p q : Set S) (w : S) : Prop where
  /-- `p` is true at `w`. -/
  holds : w ∈ p
  /-- `q` is true at every part of `w` at which `p` is true. -/
  localImpl : ∀ ⦃s⦄, s ≤ w → s ∈ p → s ∈ q

namespace Lumps

variable {p q r : Set S} {w : S}

/-- Setting `s = w` in the local-implication conjunct: `q` is true at
    `w` whenever `p` lumps `q` there. -/
theorem holds_target (h : Lumps p q w) : w ∈ q :=
  h.localImpl le_rfl h.holds

/-- A true proposition lumps itself (reflexivity, conditional on truth). -/
theorem refl_of_holds (hp : w ∈ p) : Lumps p p w :=
  ⟨hp, fun _ _ h ↦ h⟩

/-- Lumping composes. -/
theorem trans (hpq : Lumps p q w) (hqr : Lumps q r w) : Lumps p r w :=
  ⟨hpq.holds, fun _ hs hps ↦ hqr.localImpl hs (hpq.localImpl hs hps)⟩

/-- If `p` lumps both `q` and `r` at `w`, it lumps their intersection. -/
theorem inter (hq : Lumps p q w) (hr : Lumps p r w) : Lumps p (q ∩ r) w :=
  ⟨hq.holds, fun _ hs hps ↦ ⟨hq.localImpl hs hps, hr.localImpl hs hps⟩⟩

/-- A stronger proposition true at `w` lumps whatever `p` lumps there. -/
theorem mono_left {p' : Set S} (hp' : p' ⊆ p) (hp'w : w ∈ p')
    (h : Lumps p q w) : Lumps p' q w :=
  ⟨hp'w, fun _ hs hps ↦ h.localImpl hs (hp' hps)⟩

/-- Lumping is preserved by weakening the lumped proposition. -/
theorem mono_right {q' : Set S} (hq' : q ⊆ q') (h : Lumps p q w) :
    Lumps p q' w :=
  ⟨h.holds, fun _ hs hps ↦ hq' (h.localImpl hs hps)⟩

/-- A proposition true at every part of `w` is lumped by every proposition true at `w`. -/
theorem of_local_universal (hp : w ∈ p) (hq : ∀ ⦃s⦄, s ≤ w → s ∈ q) :
    Lumps p q w :=
  ⟨hp, fun _ hs _ ↦ hq hs⟩

end Lumps

end LumpingCore

/-! ### Logical relations

The logical relations of [kratzer-2012] §5.3.3 (p. 118) quantify over worlds only, and so agree
with their possible-worlds counterparts on the worlds. -/

section LogicalRelations

variable (S : Type*) [Preorder S]

/-- The worlds of a situation structure, its maximal situations. -/
def worlds : Set S := {s | IsMax s}

variable {S}

@[simp] theorem mem_worlds {s : S} : s ∈ worlds S ↔ IsMax s := Iff.rfl

/-- A proposition is valid when every world satisfies it ([kratzer-2012] p. 118). -/
def IsValid (p : Set S) : Prop := worlds S ⊆ p

/-- `q` follows from `A` when every world satisfying all of `A` satisfies `q`
([kratzer-2012] p. 118). -/
def Follows (A : Set (Set S)) (q : Set S) : Prop :=
  worlds S ∩ ⋂₀ A ⊆ q

/-- A set of propositions is consistent when some world satisfies all of them
([kratzer-2012] p. 118). -/
def IsConsistent (A : Set (Set S)) : Prop :=
  (worlds S ∩ ⋂₀ A).Nonempty

/-- A proposition is compatible with a set of propositions when adding it keeps the set
consistent ([kratzer-2012] p. 118). -/
def IsCompatible (p : Set S) (A : Set (Set S)) : Prop :=
  IsConsistent (insert p A)

/-- `p` is compatible with `A` iff its complement does not follow from `A`. -/
theorem isCompatible_iff_not_follows_compl {p : Set S} {A : Set (Set S)} :
    IsCompatible p A ↔ ¬ Follows A pᶜ := by
  simp only [IsCompatible, IsConsistent, Follows, Set.sInter_insert, Set.not_subset,
    Set.Nonempty, Set.mem_inter_iff, Set.mem_compl_iff, not_not]
  exact ⟨fun ⟨s, hw, hp, hA⟩ ↦ ⟨s, ⟨hw, hA⟩, hp⟩, fun ⟨s, ⟨hw, hA⟩, hp⟩ ↦ ⟨s, hw, hp, hA⟩⟩

/-- Two propositions are logically equivalent when they agree on the worlds ([kratzer-2012]
p. 118). -/
def LogEquiv (p q : Set S) : Prop := p ∩ worlds S = q ∩ worlds S

/-! ### Characterizations -/

/-- A premise in a set is a logical consequence of the set. -/
theorem Follows.of_mem {A : Set (Set S)} {p : Set S}
    (hp : p ∈ A) : Follows A p :=
  Set.inter_subset_right.trans (Set.sInter_subset_of_mem hp)

/-- Validity is logical consequence from no premises. -/
theorem isValid_iff_follows_empty {p : Set S} :
    IsValid p ↔ Follows (∅ : Set (Set S)) p := by
  simp only [IsValid, Follows, Set.sInter_empty, Set.inter_univ]

/-- A set of propositions is consistent iff the empty proposition does not follow from it. -/
theorem isConsistent_iff_not_follows_empty_set {A : Set (Set S)} :
    IsConsistent A ↔ ¬ Follows A (∅ : Set S) := by
  simp only [IsConsistent, Follows, Set.subset_empty_iff,
    ← Set.nonempty_iff_ne_empty]

/-- Compatibility with `A` is consistency of `A` with the proposition added. -/
@[simp] theorem isCompatible_iff_isConsistent_insert
    {p : Set S} {A : Set (Set S)} :
    IsCompatible p A ↔ IsConsistent (insert p A) := Iff.rfl

end LogicalRelations

/-! ### Lumping and logical consequence -/

section LumpingBridge

variable {S : Type*} [Preorder S]

/-- If `p` lumps `q` at every world where `p` holds, then `q` follows from `p`. -/
theorem Lumps.follows_singleton {p q : Set S}
    (h : ∀ w ∈ worlds S, w ∈ p → Lumps p q w) :
    Follows {p} q := by
  intro w hw
  have hwW : w ∈ worlds S := hw.1
  have hwp : w ∈ p := (Set.mem_sInter.mp hw.2) p (Set.mem_singleton p)
  exact (h w hwW hwp).holds_target

end LumpingBridge

/-! ### Possible-worlds reduction

Under the discrete order parthood is equality, every situation is a world, and lumping at `w` is
joint truth at `w`. -/

section DiscreteCorollary

/-- The discrete partial order, on which `≤` is equality. -/
@[reducible] def discreteOrder (X : Type*) : PartialOrder X where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h _ := h

variable (G : Type)

local instance : PartialOrder G := discreteOrder G

/-- Under the discrete order every situation is a world. -/
theorem discrete_isMax (s : G) : IsMax s := fun _ h ↦ h.symm.le

/-- Under the discrete order every proposition is persistent. -/
theorem discrete_monotone (p : G → Prop) : Monotone p := fun _ _ h hp ↦ h ▸ hp

/-- Lumping in a discrete frame collapses to joint truth at the index. -/
theorem Lumps.discrete_iff (p q : Set G) (w : G) :
    Lumps p q w ↔ (w ∈ p ∧ w ∈ q) := by
  refine ⟨fun h ↦ ⟨h.holds, h.holds_target⟩, fun ⟨hp, hq⟩ ↦ ⟨hp, ?_⟩⟩
  intro s hs _
  -- `s ≤ w` in `discreteOrder` reduces by definition to `s = w`.
  obtain rfl : s = w := hs
  exact hq

end DiscreteCorollary

end Conditional.Counterfactual
