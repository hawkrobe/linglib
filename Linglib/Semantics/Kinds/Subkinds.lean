import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic

/-!
# Reference to ad hoc kinds
[mendia-2020]

[mendia-2020] (L&P 43:589-631) argues that *ad hoc* kind reference —
uses of `that kind of dog` to refer to a kind no lexicalized noun names — is
best analysed by giving speakers the ability to choose, in context, an
equivalence relation on the instances of a base kind. Members of each
equivalence class then instantiate a subkind, and `that kind of N` picks
out one such class via demonstration.

Subkinds-as-equivalence-classes is *exactly* mathlib's `Setoid`. This file
provides Mendia's linguistic vocabulary (`subkindOf`, `instantiates`,
`disjointness_condition`) on top of `Setoid` directly — no parallel struct
is introduced. [carlson-1977]'s Disjointness Condition is then a
corollary of the standard fact that distinct equivalence classes are
disjoint.

Consumers:

* `Studies/Snyder2026.lean` — instantiates the framework
  for the kind TWO with subkinds `2_ℕ, 2_ℤ, 2_ℚ, 2_ℝ` (Snyder §4.3, §5).
* `Semantics/Kinds/MeaningPreservation.lean` — singular kinds satisfy
  the framework with the discrete partition (one-class-per-kind).
-/

namespace Semantics.Kinds.Subkinds

variable {Atom : Type*}

/-- The subkind containing `a` under the salient kind-formation `s`: its
    equivalence class.

    [mendia-2020]: "For any entities instantiating a kind k, we can
    exhaustively partition those entities into disjoint subsets via a
    salient equivalence relation, where members of the resulting equivalence
    classes instantiate subkinds of k." -/
def subkindOf (s : Setoid Atom) (a : Atom) : Set Atom := {x | s.r a x}

/-- An entity instantiates a subkind iff it belongs to that equivalence
    class. -/
def instantiates (s : Setoid Atom) (a x : Atom) : Prop :=
  x ∈ subkindOf s a

/-- [carlson-1977]'s Disjointness Condition, derived from the
    equivalence-class structure. Distinct classes of any equivalence
    relation are disjoint as subsets of the carrier. -/
theorem disjointness_condition (s : Setoid Atom) {a b : Atom} (h : ¬ s.r a b) :
    Disjoint (subkindOf s a) (subkindOf s b) := by
  rw [Set.disjoint_iff]
  rintro x ⟨ha, hb⟩
  exact h (s.iseqv.trans ha (s.iseqv.symm hb))

/-- Two atoms instantiate the same subkind iff they are equivalent under
    the salient relation. -/
theorem subkindOf_eq_iff (s : Setoid Atom) (a b : Atom) :
    subkindOf s a = subkindOf s b ↔ s.r a b := by
  refine ⟨fun hEq => ?_, fun hRel => ?_⟩
  · have ha : a ∈ subkindOf s b := hEq ▸ s.iseqv.refl a
    exact s.iseqv.symm ha
  · ext x
    exact ⟨fun h => s.iseqv.trans (s.iseqv.symm hRel) h,
           fun h => s.iseqv.trans hRel h⟩

/-- Distinct subkinds (under the salient relation) are unequal as sets. -/
theorem subkindOf_ne (s : Setoid Atom) {a b : Atom} (h : ¬ s.r a b) :
    subkindOf s a ≠ subkindOf s b :=
  fun hEq => h ((subkindOf_eq_iff s a b).mp hEq)

/-- Membership in a subkind via the salient relation. -/
theorem mem_subkindOf (s : Setoid Atom) {a x : Atom} :
    x ∈ subkindOf s a ↔ s.r a x := Iff.rfl

end Semantics.Kinds.Subkinds
