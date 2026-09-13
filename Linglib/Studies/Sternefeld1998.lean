import Linglib.Semantics.Plurality.Algebra
import Linglib.Semantics.Plurality.Reciprocal

/-!
# Sternefeld (1998): Reciprocity and cumulative predication

This file formalizes [sternefeld-1998]'s derivation of the readings of plural and reciprocal
sentences from the placement of Link's `*` and Krifka's `**` at Logical Form, on
[schwarzschild-1996]'s set-based ontology: pluralities are finite sets of individuals, an
individual is its singleton, and sum is union. Weak distributivity is `**R` and weak
reciprocity is `**` of the relation with non-identity conjoined into it, so the reciprocal
carries no quantifier of its own; strong distributivity and strong reciprocity are iterated
`*`. We prove that for a relation between individuals each form is the corresponding formula
of [langendoen-1978], that Langendoen's weak reciprocity always entails the cumulation form,
and that the converse fails in Langendoen's model where two individuals relate to a third only
jointly.

## Implementation notes

* A relation between individuals enters the set-based ontology as its image under singleton
  formation, `Relation.Map R ({·}) ({·})`; this is the paper's D-based case (§2.3), and
  Langendoen's formulae are the substrate schemes `Reciprocal.WeakReciprocity` and
  `Reciprocal.StrongReciprocity` of `R` itself.
* Denotations are nonempty, so the equivalences carry the nonemptiness, or for strong
  reciprocity the two-member, hypothesis that `*` and `**` build in and Langendoen's formulae
  leave vacuous.
* The n-ary `***` (§3.1), dependent plurals (§3.2–3.3), LF movement (§3.4), the Geach–Kaplan
  sentence (§3.6) and the cover pragmatics of §4 are not formalized.

## References

* [sternefeld-1998]
* [langendoen-1978]
* [krifka-1986]
* [link-1983]
* [schwarzschild-1996]
-/

namespace Sternefeld1998

open Mereology Plurality.Algebra Plurality.Cumulativity Reciprocal

variable {α β : Type*}

/-! ### Relations between individuals -/

@[simp]
theorem map_singleton_singleton (R : α → β → Prop) (a : α) (b : β) :
    Relation.Map R ({·}) ({·}) ({a} : Finset α) ({b} : Finset β) ↔ R a b := by
  simp [Relation.Map, Finset.singleton_inj]

/-- `*` of a relation between individuals, in its second argument, holds of the nonempty
pluralities all of whose members are related to the first. -/
theorem star_map_iff [DecidableEq β] (R : α → β → Prop) (a : α) (B : Finset β) :
    star (Relation.Map R ({·}) ({·}) ({a} : Finset α)) B ↔ B.Nonempty ∧ ∀ b ∈ B, R a b := by
  rw [star_iff_of_subset_range_singleton]
  · simp only [map_singleton_singleton]
  · rintro _ ⟨_, b, _, _, rfl⟩
    exact ⟨b, rfl⟩

private theorem star_map_subset_range [DecidableEq β] (R : α → β → Prop)
    (B : Finset α → Finset β) :
    {x : Finset α | star (Relation.Map R ({·}) ({·}) x) (B x)} ⊆
      Set.range ({·} : α → Finset α) :=
  λ _ h =>
    let ⟨_, hy, _⟩ := algClosure_has_base h
    let ⟨a, _, _, ha, _⟩ := hy
    ⟨a, ha⟩

variable [DecidableEq α] [DecidableEq β]

/-! ### Weak distributivity and weak reciprocity -/

/-- Weak distributivity (2b) is `⟨A, B⟩ ∈ **R` (26a) between nonempty pluralities. -/
theorem cumulation_map_iff (R : α → β → Prop) {A : Finset α} (hA : A.Nonempty) (B : Finset β) :
    Cumulation (Relation.Map R ({·}) ({·})) A B ↔ Cumulative R A B :=
  (cumulation_map_singleton R A B).trans (and_iff_right hA)

/-- Weak reciprocity (6), (26b): the reciprocal NP denotes the others, and non-identity is
conjoined into the relation before cumulation. -/
def WR (R : Finset α → Finset α → Prop) (A : Finset α) : Prop :=
  Cumulation (λ x y => R x y ∧ x ≠ y) A A

/-- Langendoen's weak reciprocity (25b) between individuals entails (26b), for any relation
over pluralities. -/
theorem wr_of_weakReciprocity {R : Finset α → Finset α → Prop} {A : Finset α}
    (hA : A.Nonempty) (h : WeakReciprocity (λ a b => R {a} {b}) A) : WR R A := by
  have := (cumulation_map_singleton (λ a b => R {a} {b} ∧ a ≠ b) A A).2
    ⟨hA, (weakReciprocity_iff_cumulative_strict _ _).1 h⟩
  refine this.mono ?_
  rintro x y ⟨a, b, ⟨hab, hne⟩, rfl, rfl⟩
  exact ⟨hab, Finset.singleton_injective.ne hne⟩

/-- For a relation between individuals, (26b) is Langendoen's (25b). -/
theorem wr_map_iff (R : α → α → Prop) {A : Finset α} (hA : A.Nonempty) :
    WR (Relation.Map R ({·}) ({·})) A ↔ WeakReciprocity R A := by
  have : (λ x y : Finset α => Relation.Map R ({·}) ({·}) x y ∧ x ≠ y) =
      Relation.Map (λ a b => R a b ∧ a ≠ b) ({·}) ({·}) := by
    ext x y
    constructor
    · rintro ⟨⟨a, b, hab, rfl, rfl⟩, hne⟩
      exact ⟨a, b, ⟨hab, Finset.singleton_injective.ne_iff.1 hne⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨hab, hne⟩, rfl, rfl⟩
      exact ⟨⟨a, b, hab, rfl, rfl⟩, Finset.singleton_injective.ne hne⟩
  rw [WR, this, cumulation_map_singleton, and_iff_right hA,
    weakReciprocity_iff_cumulative_strict]

/-! ### Langendoen's model

`A = {a, b, c}` and `R = {⟨{a, b}, c⟩, ⟨c, a⟩, ⟨c, b⟩}` (§3): the As relate to each other,
but no individual relates to `c` on its own, so (25b) fails while (26b) holds. -/

/-- Langendoen's relation: `a` and `b` relate to `c` jointly, and `c` relates to each. -/
def langendoenModel (x y : Finset (Fin 3)) : Prop :=
  (x = {0, 1} ∧ y = {2}) ∨ (x = {2} ∧ y = {0}) ∨ (x = {2} ∧ y = {1})

instance : DecidableRel langendoenModel := λ _ _ => by
  unfold langendoenModel; infer_instance

/-- Langendoen's relation is not a relation between individuals. -/
theorem langendoenModel_ne_map (R : Fin 3 → Fin 3 → Prop) :
    langendoenModel ≠ Relation.Map R ({·}) ({·}) := by
  intro h
  have hL : langendoenModel {0, 1} {2} := Or.inl ⟨rfl, rfl⟩
  rw [h] at hL
  obtain ⟨a, -, -, ha, -⟩ := hL
  revert a
  decide

/-- (26b) holds in Langendoen's model. -/
theorem wr_langendoenModel : WR langendoenModel Finset.univ := by
  have h₁ : ({0, 1} : Finset (Fin 3)) ⊔ ({2} ⊔ {2}) = Finset.univ := by decide
  have h₂ : ({2} : Finset (Fin 3)) ⊔ ({0} ⊔ {1}) = Finset.univ := by decide
  have h := (Cumulation.of_rel (R := λ x y => langendoenModel x y ∧ x ≠ y)
      (x := {0, 1}) (y := {2}) (by decide)).sup
    ((Cumulation.of_rel (x := {2}) (y := {0}) (by decide)).sup
      (Cumulation.of_rel (x := {2}) (y := {1}) (by decide)))
  simpa only [WR, h₁, h₂] using h

/-- (25b) fails in Langendoen's model. -/
theorem not_weakReciprocity_langendoenModel :
    ¬ WeakReciprocity (λ a b => langendoenModel {a} {b}) Finset.univ := by
  decide

/-! ### Strong distributivity and strong reciprocity by iterated `*` -/

/-- Strong distributivity by iterated `*` (7): `A ∈ *{x : B ∈ *{y : R(x, y)}}`. -/
def SD (R : α → β → Prop) (A : Finset α) (B : Finset β) : Prop :=
  star (λ x : Finset α => star (Relation.Map R ({·}) ({·}) x) B) A

/-- Strong reciprocity by iterated `*` (48b): `A ∈ *λx[{y : y ∈ A ∧ y ≠ x} ∈ *λy.R(x, y)]`,
the reciprocal interpreted in situ as one NP. -/
def SR (R : α → α → Prop) (A : Finset α) : Prop :=
  star (λ x : Finset α =>
    star (Relation.Map R ({·}) ({·}) x) (A.filter λ b => ({b} : Finset α) ≠ x)) A

/-- (7) is Langendoen's strong distributivity (2a) between nonempty pluralities. -/
theorem sd_iff (R : α → β → Prop) {A : Finset α} {B : Finset β} (hA : A.Nonempty)
    (hB : B.Nonempty) : SD R A B ↔ ∀ a ∈ A, ∀ b ∈ B, R a b := by
  rw [SD, star_iff_of_subset_range_singleton (star_map_subset_range R λ _ => B),
    and_iff_right hA]
  exact forall₂_congr λ a _ => (star_map_iff R a B).trans (and_iff_right hB)

/-- (48b) is Langendoen's strong reciprocity (3a) on a plurality of two or more. -/
theorem sr_iff (R : α → α → Prop) {A : Finset α} :
    SR R A ↔ 2 ≤ A.card ∧ StrongReciprocity R A := by
  rw [SR, star_iff_of_subset_range_singleton (star_map_subset_range R _)]
  simp only [star_map_iff, Finset.mem_filter, ne_eq, Finset.singleton_inj,
    Finset.filter_nonempty_iff, StrongReciprocity]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    obtain ⟨⟨b, hb, hba⟩, -⟩ := h a ha
    exact ⟨Finset.one_lt_card.2 ⟨a, ha, b, hb, Ne.symm hba⟩,
      λ x hx y hy hyx => (h x hx).2 y ⟨hy, hyx⟩⟩
  · rintro ⟨hcard, h⟩
    refine ⟨Finset.card_pos.1 (by omega), λ a ha => ⟨?_, λ b ⟨hb, hba⟩ => h a ha b hb hba⟩⟩
    obtain ⟨b, hb, hba⟩ := A.exists_mem_ne hcard a
    exact ⟨b, hb, hba⟩

end Sternefeld1998
