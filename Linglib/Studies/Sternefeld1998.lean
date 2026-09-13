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

* A relation over pluralities is D-based when it holds only between singletons (§2.3); its
  restriction to individuals is `R {a} {b}`, and Langendoen's formulae are the substrate
  schemes `Reciprocal.WeakReciprocity` and `Reciprocal.StrongReciprocity` of that restriction.
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

/-! ### D-based relations -/

/-- A relation over pluralities is D-based when it holds only between individuals, that is
between singletons (§2.3). -/
def DBased (R : Finset α → Finset β → Prop) : Prop :=
  ∀ ⦃x y⦄, R x y → ∃ a b, x = {a} ∧ y = {b}

theorem DBased.apply {R : Finset α → Finset β → Prop} (hR : DBased R) (x : Finset α) :
    ∀ ⦃y⦄, R x y → ∃ b, y = {b} := λ _ h =>
  let ⟨_, b, _, hb⟩ := hR h
  ⟨b, hb⟩

/-- `*` of a D-based relation's second argument is D-based in the first. -/
theorem DBased.star [DecidableEq β] {R : Finset α → Finset β → Prop} (hR : DBased R)
    (B : Finset α → Finset β) : ∀ ⦃x⦄, star (R x) (B x) → ∃ a, x = {a} :=
  λ _ h =>
    let ⟨_, hy, _⟩ := algClosure_has_base h
    let ⟨a, _, ha, _⟩ := hR hy
    ⟨a, ha⟩

/-- A D-based relation is the singleton image of its restriction to individuals. -/
theorem DBased.eq_map {R : Finset α → Finset β → Prop} (h : DBased R) :
    R = Relation.Map (λ a b => R {a} {b}) ({·}) ({·}) := by
  ext x y
  constructor
  · intro hxy
    obtain ⟨a, b, rfl, rfl⟩ := h hxy
    exact ⟨a, b, hxy, rfl, rfl⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact hab

variable [DecidableEq α] [DecidableEq β]

/-- `*` of a predicate true of individuals only is the distributive `D` (15): it holds of the
nonempty pluralities all of whose members satisfy it. -/
theorem star_iff_of_dBased {P : Finset α → Prop} (hP : ∀ ⦃x⦄, P x → ∃ a, x = {a})
    {x : Finset α} : star P x ↔ x.Nonempty ∧ ∀ a ∈ x, P {a} := by
  have : P = (· ∈ ({·} : α → Finset α) '' {a | P {a}}) := by
    ext s
    constructor
    · intro hs
      obtain ⟨a, rfl⟩ := hP hs
      exact ⟨a, hs, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  conv_lhs => rw [this]
  rw [star_image_singleton]
  exact Iff.rfl

/-! ### Weak distributivity and weak reciprocity -/

/-- Weak distributivity (2b) is `⟨A, B⟩ ∈ **R` (26a) for a D-based `R` between nonempty
pluralities. -/
theorem cumulation_iff_cumulative {R : Finset α → Finset β → Prop} (hR : DBased R)
    {A : Finset α} (hA : A.Nonempty) (B : Finset β) :
    Cumulation R A B ↔ Cumulative (λ a b => R {a} {b}) A B := by
  conv_lhs => rw [hR.eq_map]
  rw [cumulation_map_singleton, and_iff_right hA]

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

/-- For a D-based `R`, (26b) is Langendoen's (25b): weak reciprocity between individuals. -/
theorem wr_iff {R : Finset α → Finset α → Prop} (hR : DBased R) {A : Finset α}
    (hA : A.Nonempty) : WR R A ↔ WeakReciprocity (λ a b => R {a} {b}) A := by
  have hR' : DBased (λ x y => R x y ∧ x ≠ y) := λ x y h => hR h.1
  rw [WR, cumulation_iff_cumulative hR' hA, weakReciprocity_iff_cumulative_strict]
  simp only [ne_eq, Finset.singleton_inj]

/-! ### Langendoen's model

`A = {a, b, c}` and `R = {⟨{a, b}, c⟩, ⟨c, a⟩, ⟨c, b⟩}` (§3): the As relate to each other,
but no individual relates to `c` on its own, so (25b) fails while (26b) holds. -/

/-- Langendoen's relation: `a` and `b` relate to `c` jointly, and `c` relates to each. -/
def langendoenModel (x y : Finset (Fin 3)) : Prop :=
  (x = {0, 1} ∧ y = {2}) ∨ (x = {2} ∧ y = {0}) ∨ (x = {2} ∧ y = {1})

instance : DecidableRel langendoenModel := λ _ _ => by
  unfold langendoenModel; infer_instance

theorem not_dBased_langendoenModel : ¬ DBased langendoenModel := by
  intro h
  obtain ⟨a, -, ha, -⟩ := h (Or.inl ⟨rfl, rfl⟩)
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
def SD (R : Finset α → Finset β → Prop) (A : Finset α) (B : Finset β) : Prop :=
  star (λ x => star (R x) B) A

/-- Strong reciprocity by iterated `*` (48b): `A ∈ *λx[{y : y ∈ A ∧ y ≠ x} ∈ *λy.R(x, y)]`,
the reciprocal interpreted in situ as one NP. -/
def SR (R : Finset α → Finset α → Prop) (A : Finset α) : Prop :=
  star (λ x => star (R x) (A.filter λ b => ({b} : Finset α) ≠ x)) A

/-- For a D-based `R`, (7) is Langendoen's strong distributivity (2a) between nonempty
pluralities. -/
theorem sd_iff {R : Finset α → Finset β → Prop} (hR : DBased R) {A : Finset α} {B : Finset β}
    (hA : A.Nonempty) (hB : B.Nonempty) : SD R A B ↔ ∀ a ∈ A, ∀ b ∈ B, R {a} {b} := by
  have hout : ∀ ⦃x⦄, star (R x) B → ∃ a, x = {a} := hR.star _
  rw [SD, star_iff_of_dBased hout, and_iff_right hA]
  refine forall₂_congr λ a _ => ?_
  rw [star_iff_of_dBased (hR.apply _), and_iff_right hB]

/-- For a D-based `R`, (48b) is Langendoen's strong reciprocity (3a) on a plurality of two or
more. -/
theorem sr_iff {R : Finset α → Finset α → Prop} (hR : DBased R) {A : Finset α} :
    SR R A ↔ 2 ≤ A.card ∧ StrongReciprocity (λ a b => R {a} {b}) A := by
  have hout : ∀ ⦃x⦄, star (R x) (A.filter λ b => ({b} : Finset α) ≠ x) → ∃ a, x = {a} :=
    hR.star _
  rw [SR, star_iff_of_dBased hout]
  simp only [star_iff_of_dBased (hR.apply _), Finset.mem_filter, ne_eq,
    Finset.singleton_inj, Finset.filter_nonempty_iff, StrongReciprocity]
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
