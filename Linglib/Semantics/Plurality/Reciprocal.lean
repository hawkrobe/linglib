import Mathlib.Logic.Relation
import Mathlib.Order.Partition.Finpartition
import Linglib.Semantics.Plurality.Cumulativity

/-!
# Reciprocal predicates

The interpretation schemes of reciprocal sentences, as conditions on a relation `R` and a
plurality `X`: Strong, Intermediate and Weak Reciprocity from [langendoen-1978], Partitioned
Strong Reciprocity from [fiengo-lasnik-1973], Inclusive Alternative Ordering from
[kanski-1987], and One-way Weak Reciprocity from [dalrymple-et-al-1998], whose survey fixes the
definitions used here. The schemes form an entailment lattice on pluralities of two or more
(`strong_imp_partitionedStrong`, `partitionedStrong_imp_weak`, `strong_imp_intermediate`,
`intermediate_imp_weak`, `weak_imp_oneWay`, `oneWay_imp_inclusiveAlternative`), and Weak
Reciprocity is definitionally the cumulation `**` of the relation with non-identity conjoined
into it (`weakReciprocity_iff_cumulative_strict`).

The second half is the configurational typology of [evans-et-al-2011b] and [majid-et-al-2011]:
the pairwise, chain, ring, radial and melee shapes of a mutual event, as exact-extension
conditions on `(R, X)`, with their symmetry and participant-exhaustiveness as theorems
locating each shape in the lattice.

## Implementation notes

* Intermediate Reciprocity is `Relation.TransGen` of `R` restricted to `X`; Partitioned Strong
  Reciprocity is a `Finpartition` of `X` into cells of two or more; adjacency in a chain or ring
  is a pair of consecutive positions in a duplicate-free list.
* The two-member condition that [dalrymple-et-al-1998] build into each scheme is a hypothesis
  of the entailments rather than a conjunct of the definitions.

## TODO

* The Alternative schemes SAR and IAR, and the Strongest Meaning Hypothesis as an operator
  selecting among schemes.

## References

* [langendoen-1978], [fiengo-lasnik-1973], [kanski-1987], [dalrymple-et-al-1998]
* [beck-2001], [sternefeld-1998]
* [evans-et-al-2011b], [majid-et-al-2011]
-/

namespace Reciprocal

open _root_.Plurality.Cumulativity

variable {A : Type*} {R : A → A → Prop} {X : Finset A}

/-! ### The interpretation schemes -/

/-- Strong Reciprocity: every distinct pair in `X` satisfies `R`. -/
def StrongReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, y ≠ x → R x y

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (StrongReciprocity R X) := by
  unfold StrongReciprocity; infer_instance

theorem strongReciprocity_iff_pairwise : StrongReciprocity R X ↔ (X : Set A).Pairwise R :=
  ⟨λ h _ hx _ hy hxy => h _ hx _ hy hxy.symm, λ h _ hx _ hy hyx => h hx hy hyx.symm⟩

/-- Partitioned Strong Reciprocity ([fiengo-lasnik-1973]): `X` splits into disjoint cells of two
or more within each of which Strong Reciprocity holds. -/
def PartitionedStrongReciprocity [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ P : Finpartition X, ∀ c ∈ P.parts, 2 ≤ c.card ∧ StrongReciprocity R c

/-- Intermediate Reciprocity ([langendoen-1978]): any two distinct members of `X` are
connected by an `R`-chain through `X`. -/
def IntermediateReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, y ≠ x → Relation.TransGen (λ a b => a ∈ X ∧ b ∈ X ∧ R a b) x y

/-- Weak Reciprocity ([langendoen-1978]): every member of `X` is `R`-related to a distinct
other member in both directions, as subject and as object. -/
def WeakReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  (∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y) ∧ (∀ y ∈ X, ∃ x ∈ X, R x y ∧ x ≠ y)

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (WeakReciprocity R X) := by
  unfold WeakReciprocity; infer_instance

/-- One-way Weak Reciprocity ([dalrymple-et-al-1998]): the first direction of Weak
Reciprocity. -/
def OneWayWeakReciprocity (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (OneWayWeakReciprocity R X) := by
  unfold OneWayWeakReciprocity; infer_instance

/-- Inclusive Alternative Ordering ([kanski-1987]): each member of `X` is `R`-related to a
distinct other member in one direction or the other. -/
def InclusiveAlternativeOrdering (R : A → A → Prop) (X : Finset A) : Prop :=
  ∀ x ∈ X, ∃ y ∈ X, x ≠ y ∧ (R x y ∨ R y x)

instance [DecidableEq A] (R : A → A → Prop) [DecidableRel R] (X : Finset A) :
    Decidable (InclusiveAlternativeOrdering R X) := by
  unfold InclusiveAlternativeOrdering; infer_instance

/-! ### The entailment lattice -/

theorem strong_imp_partitionedStrong [DecidableEq A] (hcard : 2 ≤ X.card)
    (hSR : StrongReciprocity R X) : PartitionedStrongReciprocity R X :=
  ⟨Finpartition.indiscrete (Finset.card_pos.1 (by omega)).ne_empty, λ c hc => by
    rw [Finpartition.indiscrete, Finset.mem_singleton] at hc
    exact hc ▸ ⟨hcard, hSR⟩⟩

theorem partitionedStrong_imp_weak [DecidableEq A] (h : PartitionedStrongReciprocity R X) :
    WeakReciprocity R X := by
  obtain ⟨P, hP⟩ := h
  refine ⟨λ x hx => ?_, λ x hx => ?_⟩ <;>
  · obtain ⟨c, hc, hxc⟩ := P.exists_mem hx
    obtain ⟨hcard, hSR⟩ := hP c hc
    obtain ⟨y, hy, hyx⟩ := c.exists_mem_ne hcard x
    first
      | exact ⟨y, P.le hc hy, hSR x hxc y hy hyx, hyx.symm⟩
      | exact ⟨y, P.le hc hy, hSR y hy x hxc hyx.symm, hyx⟩

theorem strong_imp_intermediate (hSR : StrongReciprocity R X) : IntermediateReciprocity R X :=
  λ x hx y hy hyx => .single ⟨hx, hy, hSR x hx y hy hyx⟩

private theorem exists_rel_ne_of_transGen {r : A → A → Prop} {x y : A}
    (h : Relation.TransGen r x y) (hyx : y ≠ x) : ∃ z, z ≠ x ∧ r x z := by
  induction h with
  | single h => exact ⟨_, hyx, h⟩
  | @tail b c _ hbc ih =>
    by_cases hbx : b = x
    · exact ⟨c, hyx, hbx ▸ hbc⟩
    · exact ih hbx

theorem intermediate_imp_weak [DecidableEq A] (hcard : 2 ≤ X.card)
    (h : IntermediateReciprocity R X) : WeakReciprocity R X := by
  refine ⟨λ x hx => ?_, λ x hx => ?_⟩
  · obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    obtain ⟨z, hzx, -, hz, hR⟩ := exists_rel_ne_of_transGen (h x hx y hy hyx) hyx
    exact ⟨z, hz, hR, hzx.symm⟩
  · obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    have := (h y hy x hx hyx.symm).swap
    obtain ⟨z, hzx, hz, -, hR⟩ := exists_rel_ne_of_transGen this hyx
    exact ⟨z, hz, hR, hzx⟩

theorem strong_imp_weak [DecidableEq A] (hcard : 2 ≤ X.card) (hSR : StrongReciprocity R X) :
    WeakReciprocity R X :=
  intermediate_imp_weak hcard (strong_imp_intermediate hSR)

theorem weak_imp_oneWay (hWR : WeakReciprocity R X) : OneWayWeakReciprocity R X :=
  hWR.1

theorem oneWay_imp_inclusiveAlternative (hOWR : OneWayWeakReciprocity R X) :
    InclusiveAlternativeOrdering R X := λ x hx =>
  let ⟨y, hy, hRxy, hxy⟩ := hOWR x hx
  ⟨y, hy, hxy, Or.inl hRxy⟩

/-! ### Cumulation -/

/-- Weak Reciprocity is `**` of the relation with non-identity conjoined into it, the bivalent
common ground of [beck-2001] and [sternefeld-1998]. -/
theorem weakReciprocity_iff_cumulative_strict (R : A → A → Prop) (X : Finset A) :
    WeakReciprocity R X ↔ Cumulative (λ a b => R a b ∧ a ≠ b) X X := Iff.rfl

theorem weakReciprocity_imp_cumulative (R : A → A → Prop) (X : Finset A)
    (hWR : WeakReciprocity R X) : Cumulative R X X :=
  ⟨λ x hx => let ⟨y, hy, hRxy, _⟩ := hWR.1 x hx; ⟨y, hy, hRxy⟩,
   λ y hy => let ⟨x, hx, hRxy, _⟩ := hWR.2 y hy; ⟨x, hx, hRxy⟩⟩

/-! ### Configurational typology

The event configurations of [evans-et-al-2011b] and [majid-et-al-2011], as exact-extension
conditions on `(R, X)`. Pairwise strengthens to Partitioned Strong Reciprocity, ring yields
One-way Weak Reciprocity, chain and radial yield Inclusive Alternative Ordering, and melee is
by definition the failure of Inclusive Alternative Ordering. -/

/-- `y` immediately follows `x` in `l`. -/
def Consecutive (l : List A) (x y : A) : Prop := ∃ i, l[i]? = some x ∧ l[i + 1]? = some y

theorem Consecutive.mem_left {l : List A} {x y : A} (h : Consecutive l x y) : x ∈ l :=
  let ⟨_, hx, _⟩ := h
  List.mem_of_getElem? hx

theorem Consecutive.mem_right {l : List A} {x y : A} (h : Consecutive l x y) : y ∈ l :=
  let ⟨_, _, hy⟩ := h
  List.mem_of_getElem? hy

theorem Consecutive.ne {l : List A} (hnd : l.Nodup) {x y : A} (h : Consecutive l x y) :
    x ≠ y := by
  obtain ⟨i, hx, hy⟩ := h
  rintro rfl
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 hx).1
  have := (List.getElem?_inj hi hnd).1 (hx.trans hy.symm)
  omega

theorem Consecutive.asymm {l : List A} (hnd : l.Nodup) {x y : A} (hxy : Consecutive l x y) :
    ¬ Consecutive l y x := by
  rintro ⟨j, hy', hx'⟩
  obtain ⟨i, hx, hy⟩ := hxy
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 hx).1
  have h₁ := (List.getElem?_inj hi hnd).1 (hx.trans hx'.symm)
  have h₂ := (List.getElem?_inj (List.getElem?_eq_some_iff.1 hy).1 hnd).1 (hy.trans hy'.symm)
  omega

theorem exists_consecutive_or_getLast {l : List A} {x : A} (hx : x ∈ l) :
    (∃ y, Consecutive l x y) ∨ l.getLast? = some x := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  have hlt : i < l.length := (List.getElem?_eq_some_iff.1 hi).1
  by_cases h : i + 1 < l.length
  · exact Or.inl ⟨l[i + 1], i, hi, List.getElem?_eq_getElem h⟩
  · right
    rw [List.getLast?_eq_getElem?]
    convert hi using 2
    omega

theorem exists_consecutive_of_getLast {l : List A} (hlen : 2 ≤ l.length) {x : A}
    (hx : l.getLast? = some x) : ∃ y, Consecutive l y x := by
  rw [List.getLast?_eq_getElem?] at hx
  refine ⟨l[l.length - 2], l.length - 2, List.getElem?_eq_getElem (by omega), ?_⟩
  convert hx using 2
  omega

/-- `R` is symmetric within `X`: every realized pair is mutual. -/
def PairSymmetricOn (R : A → A → Prop) (X : Finset A) : Prop :=
  (X : Set A).Pairwise λ x y => R x y → R y x

/-- Pairwise configuration ([majid-et-al-2011]): the participants split into two-member cells
and `R` holds exactly within cells. -/
def PairwiseConfig [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ P : Finpartition X, (∀ c ∈ P.parts, c.card = 2) ∧
    ∀ x y, R x y ↔ ∃ c ∈ P.parts, x ∈ c ∧ y ∈ c ∧ x ≠ y

/-- Chain configuration ([majid-et-al-2011]): the participants form a line and `R` holds
exactly from each member to the next. -/
def ChainConfig [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ l : List A, l.Nodup ∧ l.toFinset = X ∧ 2 ≤ l.length ∧ ∀ x y, R x y ↔ Consecutive l x y

/-- Ring configuration ([majid-et-al-2011]): a chain whose last member acts on the first. -/
def RingConfig [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ l : List A, l.Nodup ∧ l.toFinset = X ∧ 3 ≤ l.length ∧
    ∀ x y, R x y ↔ Consecutive l x y ∨ (l.getLast? = some x ∧ l.head? = some y)

/-- Radial configuration ([majid-et-al-2011]): one central participant acts on each of the
others. -/
def RadialConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ c ∈ X, 2 ≤ X.card ∧ ∀ x y, R x y ↔ x = c ∧ y ∈ X ∧ y ≠ c

/-- Melee configuration ([majid-et-al-2011]): some interaction, but participation is not
exhaustive. -/
def MeleeConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  (∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ R x y) ∧ ¬ InclusiveAlternativeOrdering R X

/-! #### Symmetry -/

theorem StrongReciprocity.pairSymmetricOn (h : StrongReciprocity R X) : PairSymmetricOn R X :=
  λ _ hx _ hy hxy _ => h _ hy _ hx hxy

theorem PairwiseConfig.pairSymmetricOn [DecidableEq A] (h : PairwiseConfig R X) :
    PairSymmetricOn R X := by
  obtain ⟨P, -, hiff⟩ := h
  intro x _ y _ _ hR
  obtain ⟨c, hc, hxc, hyc, hne⟩ := (hiff x y).1 hR
  exact (hiff y x).2 ⟨c, hc, hyc, hxc, hne.symm⟩

theorem ChainConfig.not_pairSymmetricOn [DecidableEq A] (h : ChainConfig R X) :
    ¬ PairSymmetricOn R X := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  obtain ⟨b, hb⟩ := exists_consecutive_of_getLast hlen
    (List.getLast?_eq_getElem?.trans (List.getElem?_eq_getElem (by omega)))
  intro hsym
  exact hb.asymm hnd ((hiff _ _).1 (hsym (List.mem_toFinset.2 hb.mem_left)
    (List.mem_toFinset.2 hb.mem_right) (hb.ne hnd) ((hiff _ _).2 hb)))

theorem RingConfig.not_pairSymmetricOn [DecidableEq A] (h : RingConfig R X) :
    ¬ PairSymmetricOn R X := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  obtain ⟨b, hb⟩ := exists_consecutive_of_getLast (by omega : 2 ≤ l.length)
    (List.getLast?_eq_getElem?.trans (List.getElem?_eq_getElem (by omega)))
  intro hsym
  rcases (hiff _ _).1 (hsym (List.mem_toFinset.2 hb.mem_left) (List.mem_toFinset.2 hb.mem_right)
      (hb.ne hnd) ((hiff _ _).2 (Or.inl hb))) with hba | ⟨-, hhead⟩
  · exact hb.asymm hnd hba
  · obtain ⟨i, hi, hi'⟩ := hb
    have hi₁ : i + 1 < l.length := (List.getElem?_eq_some_iff.1 hi').1
    have e₁ := (List.getElem?_inj hi₁ hnd).1
      (hi'.trans (List.getElem?_eq_getElem (by omega)).symm)
    rw [List.head?_eq_getElem?] at hhead
    have e₂ := (List.getElem?_inj (by omega : 0 < l.length) hnd).1 (hhead.trans hi.symm)
    omega

theorem RadialConfig.not_pairSymmetricOn [DecidableEq A] (h : RadialConfig R X) :
    ¬ PairSymmetricOn R X := by
  obtain ⟨c, hc, hcard, hiff⟩ := h
  obtain ⟨y, hy, hyc⟩ := X.exists_mem_ne hcard c
  intro hsym
  exact hyc ((hiff y c).1 (hsym hc hy hyc.symm ((hiff c y).2 ⟨rfl, hy, hyc⟩))).1

/-! #### Exhaustiveness

Participant-exhaustiveness is Inclusive Alternative Ordering, the weakest scheme; every
configuration but melee entails it, and melee denies it by definition. -/

theorem PairwiseConfig.partitionedStrong [DecidableEq A] (h : PairwiseConfig R X) :
    PartitionedStrongReciprocity R X :=
  let ⟨P, hcells, hiff⟩ := h
  ⟨P, λ c hc => ⟨(hcells c hc).ge, λ x hx y hy hne => (hiff x y).2 ⟨c, hc, hx, hy, hne.symm⟩⟩⟩

theorem PairwiseConfig.inclusiveAlternativeOrdering [DecidableEq A] (h : PairwiseConfig R X) :
    InclusiveAlternativeOrdering R X :=
  oneWay_imp_inclusiveAlternative (partitionedStrong_imp_weak h.partitionedStrong).1

theorem ChainConfig.inclusiveAlternativeOrdering [DecidableEq A] (h : ChainConfig R X) :
    InclusiveAlternativeOrdering R X := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  intro x hx
  rcases exists_consecutive_or_getLast (List.mem_toFinset.1 hx) with ⟨y, hy⟩ | hlast
  · exact ⟨y, List.mem_toFinset.2 hy.mem_right, hy.ne hnd, Or.inl ((hiff x y).2 hy)⟩
  · obtain ⟨y, hy⟩ := exists_consecutive_of_getLast hlen hlast
    exact ⟨y, List.mem_toFinset.2 hy.mem_left, (hy.ne hnd).symm, Or.inr ((hiff y x).2 hy)⟩

theorem RingConfig.oneWayWeak [DecidableEq A] (h : RingConfig R X) :
    OneWayWeakReciprocity R X := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  intro x hx
  rcases exists_consecutive_or_getLast (List.mem_toFinset.1 hx) with ⟨y, hy⟩ | hlast
  · exact ⟨y, List.mem_toFinset.2 hy.mem_right, (hiff x y).2 (Or.inl hy), hy.ne hnd⟩
  · have hhead : l.head? = some l[0] :=
      List.head?_eq_getElem?.trans (List.getElem?_eq_getElem (by omega))
    refine ⟨l[0], List.mem_toFinset.2 (List.getElem_mem _),
      (hiff x _).2 (Or.inr ⟨hlast, hhead⟩), λ hx0 => ?_⟩
    rw [List.getLast?_eq_getElem?, hx0] at hlast
    have := (List.getElem?_inj (by omega : l.length - 1 < l.length) hnd).1
      (hlast.trans (List.getElem?_eq_getElem (by omega)).symm)
    omega

theorem RingConfig.inclusiveAlternativeOrdering [DecidableEq A] (h : RingConfig R X) :
    InclusiveAlternativeOrdering R X :=
  oneWay_imp_inclusiveAlternative h.oneWayWeak

theorem RadialConfig.inclusiveAlternativeOrdering [DecidableEq A] (h : RadialConfig R X) :
    InclusiveAlternativeOrdering R X := by
  obtain ⟨c, hc, hcard, hiff⟩ := h
  intro x hx
  by_cases hxc : x = c
  · subst hxc
    obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    exact ⟨y, hy, hyx.symm, Or.inl ((hiff x y).2 ⟨rfl, hy, hyx⟩)⟩
  · exact ⟨c, hc, hxc, Or.inr ((hiff c x).2 ⟨rfl, hx, hxc⟩)⟩

end Reciprocal
