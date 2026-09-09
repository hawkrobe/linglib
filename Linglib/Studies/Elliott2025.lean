import Linglib.Data.Examples.Elliott2025
import Linglib.Semantics.Quantification.Lattice
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Card
import Mathlib.Order.Minimal
import Mathlib.Tactic.FinCases

/-!
# Elliott (2025): Determiners as predicates

This file formalizes [elliott-2025]'s predicative theory of determiners. Against the relational
treatment of Generalized Quantifier theory ([montague-1973], [barwise-cooper-1981],
[keenan-stavi-1986]), determiners denote predicates of structured entities: the domain of
individuals is polarized, each individual coming as a positive `x⁺` or a negative `x⁻` tag, and
groups are coherent joins of polarized atoms, so that a noun denotes the maximal groups of
polarized individuals falling under it, one for each way of dividing its extension into a
positive and a negative cell. Numerals and other determiners are cardinality constraints on the
positive and negative atoms of a group, composition proceeds by covert existential raising and a
distributivity operator ([link-1983], [link-1987]) that predicates the scope of the positive atoms
and its negation of the negative atoms, and since a group records which restrictor individuals
are not in the scope, the resulting truth conditions match the relational ones: the problems of
upper bounds ([van-benthem-1986]), existential entailment and *zero* ([bylinina-nouwen-2018])
that beset the classical predicative theory of numerals ([rothstein-2017]) do not arise. Coherent
groups are the trivalent functions on the individuals, which yields the correspondence between
predicates and determiners of §4.3: a relational determiner maps to a predicate and back
meaning-preservingly exactly when it is conservative, every predicate yields a conservative
determiner, and the Härtig quantifier collapses to a universal, so conservativity is a structural
consequence of the theory rather than a constraint. Finally, since *all* and *no* pick out a
single group of the noun's, existential raising over them is scopeless ([schwarzschild-2002]) and
they show no exceptional scope ([reinhart-1997], [charlow-2014]), whereas *exactly two* does.

## Implementation notes

* A group is a trivalent function `Group α := α → Tri`, the article's isomorphic presentation of
  the coherent polarized domain (§4.3); parthood is the pointwise order over the flat order on
  `Tri`, so coherence is automatic and a noun's denotation is mathlib's `Maximal`. Numbers of atoms
  are `Set.ncard`, on a `Finite` domain.
* The covert existential quantifier and the ∆-operator are `raise` and `Group.delta`; the single
  lemma `sentence_iff` reduces every predicative sentence to the determiner applied to the group
  `triFunction N vp` that records the scope on the noun's extension, from which the truth
  conditions (29), (30), (34), (45) follow.
* The maps (40) and (44) are `Det.ofGQ` and `Det.toGQ`; their composite is `Q R (R ∩ S)`, so the
  Birkhoff-style isomorphism is between predicates and the conservative sublattice
  `Quantification.ConsGQ`. The counts of §4.3 are stated for Boolean-valued predicates on
  `Fin n`.
* The examples are `Data.Examples.Elliott2025`.

## References

* [elliott-2025]
* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [montague-1973]
* [van-benthem-1986]
* [link-1983]
* [link-1987]
* [rothstein-2017]
* [bylinina-nouwen-2018]
* [schwarzschild-2002]
* [reinhart-1997]
* [charlow-2014]
-/

namespace Elliott2025

open Quantification Data.Examples Elliott2025.Examples

/-! ### The classical predicative theory of numerals (§2) -/

section Classical

variable {α : Type*}

/-- The classical predicative theory: a plurality is a nonempty finite set of individuals, a
modified numeral a cardinality predicate (9)/(11), composed with the noun and the distributed
scope by existential closure (5). -/
def classicalLessThan (n : ℕ) (N vp : α → Prop) : Prop :=
  ∃ X : Finset α, X.Nonempty ∧ X.card < n ∧ (∀ x ∈ X, N x) ∧ ∀ x ∈ X, vp x

/-- Van Benthem's problem, (10): the upper bound is inert, since any sub-plurality of the
sneezers sneezed, so *less than three boys sneezed* comes out equivalent to *a boy sneezed*. -/
theorem classicalLessThan_iff (N vp : α → Prop) :
    classicalLessThan 3 N vp ↔ ∃ x, N x ∧ vp x := by
  constructor
  · rintro ⟨X, ⟨x, hx⟩, -, hN, hvp⟩
    exact ⟨x, hN x hx, hvp x hx⟩
  · rintro ⟨x, hN, hvp⟩
    exact ⟨{x}, Finset.singleton_nonempty x, by simp, by simpa, by simpa⟩

/-- The problem of *zero*, (13): as a cardinality predicate on nonempty pluralities, *zero* is
trivially false. -/
theorem classical_zero_false (N vp : α → Prop) :
    ¬ ∃ X : Finset α, X.Nonempty ∧ X.card = 0 ∧ (∀ x ∈ X, N x) ∧ ∀ x ∈ X, vp x := by
  rintro ⟨X, hX, hcard, -⟩
  exact hX.card_pos.ne' hcard

end Classical

/-! ### Polarity in the individual domain (§3) -/

/-- The status of an individual in a group: a positive atom `x⁺`, a negative atom `x⁻`, or absent,
the third value `#` of the trivalent presentation (§4.3). -/
inductive Tri
  | pos
  | neg
  | blank
  deriving DecidableEq, Fintype

/-- Parthood among statuses: absence lies below either polarity, and the polarities are
incomparable, so no group has both `x⁺` and `x⁻` as parts, coherence (16). -/
instance : PartialOrder Tri where
  le a b := a = .blank ∨ a = b
  le_refl _ := Or.inr rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | rfl
    · exact Or.inl rfl
    · exact hbc
  le_antisymm a b hab hba := by
    rcases hab with rfl | rfl
    · rcases hba with rfl | rfl <;> rfl
    · rfl

theorem Tri.le_iff (a b : Tri) : a ≤ b ↔ a = .blank ∨ a = b := Iff.rfl

/-- A group of polarized individuals, (14)–(16): a coherent join of polarized atoms, presented as
a trivalent function on the individuals (38), with pointwise parthood. -/
abbrev Group (α : Type*) := α → Tri

section Groups

variable {α : Type*}

/-- Polarized functional application (15), extended to absent individuals: a predicate holds of
`x⁺` as of `x`, of `x⁻` as its negation. -/
def Tri.Apply (f : α → Prop) (x : α) : Tri → Prop
  | .pos => f x
  | .neg => ¬ f x
  | .blank => True

/-- The ∆-operator (17): a predicate holds distributively of a group when it applies to each
atomic part, positively or negatively. -/
def Group.delta (f : α → Prop) (X : Group α) : Prop := ∀ x, Tri.Apply f x (X x)

/-- The positive atoms of a group (21a). -/
def Group.posAtoms (X : Group α) : Set α := {x | X x = .pos}

/-- The negative atoms of a group (21b). -/
def Group.negAtoms (X : Group α) : Set α := {x | X x = .neg}

/-- The atoms of a group (21c), positive or negative. -/
def Group.atoms (X : Group α) : Set α := {x | X x ≠ .blank}

/-- The group recording, on the extension of `N`, which individuals satisfy `vp`: positive atoms
`N ∩ vp`, negative atoms `N ∖ vp`. -/
noncomputable def triFunction (N vp : α → Prop) : Group α := λ x =>
  open Classical in if N x then (if vp x then .pos else .neg) else .blank

theorem triFunction_pos_iff (N vp : α → Prop) (x : α) :
    triFunction N vp x = .pos ↔ N x ∧ vp x := by
  unfold triFunction
  split_ifs <;> simp [*]

theorem triFunction_neg_iff (N vp : α → Prop) (x : α) :
    triFunction N vp x = .neg ↔ N x ∧ ¬ vp x := by
  unfold triFunction
  split_ifs <;> simp [*]

theorem triFunction_blank_iff (N vp : α → Prop) (x : α) :
    triFunction N vp x = .blank ↔ ¬ N x := by
  unfold triFunction
  split_ifs <;> simp [*]

@[simp] theorem posAtoms_triFunction (N vp : α → Prop) :
    (triFunction N vp).posAtoms = {x | N x ∧ vp x} :=
  Set.ext λ x => triFunction_pos_iff N vp x

@[simp] theorem negAtoms_triFunction (N vp : α → Prop) :
    (triFunction N vp).negAtoms = {x | N x ∧ ¬ vp x} :=
  Set.ext λ x => triFunction_neg_iff N vp x

@[simp] theorem atoms_triFunction (N vp : α → Prop) : (triFunction N vp).atoms = {x | N x} :=
  Set.ext λ x => not_congr (triFunction_blank_iff N vp x) |>.trans not_not

/-- A group is determined by its atoms and the scope they record. -/
theorem triFunction_atoms_pos (X : Group α) :
    triFunction (λ x => X x ≠ .blank) (λ x => X x = .pos) = X := by
  funext x
  unfold triFunction
  split_ifs with h₁ h₂
  · exact h₂.symm
  · cases hx : X x <;> simp_all
  · exact (not_not.mp h₁).symm

/-- The scope recorded by a group and its complement are absorbed by the restrictor: the group
for `N` and `N ∩ vp` is the group for `N` and `vp`. -/
theorem triFunction_and_absorb (N vp : α → Prop) :
    triFunction N (λ x => N x ∧ vp x) = triFunction N vp := by
  funext x
  unfold triFunction
  split_ifs <;> simp_all

/-- A noun (19): the maximal groups all of whose atoms fall under the noun. -/
def noun (N : α → Prop) : Set (Group α) := {X | Maximal (λ X : Group α => ∀ x ∈ X.atoms, N x) X}

/-- (20): the maximal groups of polarized `N`-individuals are those whose atoms are exactly the
`N`-individuals, one for every division of the extension into positive and negative atoms. -/
theorem mem_noun_iff (N : α → Prop) (X : Group α) : X ∈ noun N ↔ ∀ x, X x ≠ .blank ↔ N x := by
  classical
  constructor
  · rintro ⟨hP, hmax⟩ x
    refine ⟨hP x, λ hN => ?_⟩
    by_cases hb : X x = .blank
    · exfalso
      have hle : X ≤ Function.update X x .pos := λ y => by
        by_cases hy : y = x
        · subst hy
          rw [Function.update_self, hb]
          exact Or.inl rfl
        · rw [Function.update_of_ne hy]
      have := hmax (y := Function.update X x .pos) (λ y hy => by
        by_cases hyx : y = x
        · exact hyx ▸ hN
        · exact hP y (by simpa [Group.atoms, hyx] using hy)) hle x
      simp [hb, Tri.le_iff] at this
    · exact hb
  · intro h
    refine ⟨λ x hx => (h x).mp hx, λ Y hY hle y => ?_⟩
    by_cases hb : X y = .blank
    · have hYb : Y y = .blank := by
        by_contra hc
        exact (h y).mpr (hY y hc) hb
      rw [hYb, hb]
    · have := hle y
      rw [Tri.le_iff] at this
      rcases this with h' | h'
      · exact absurd h' hb
      · exact Or.inr h'.symm

/-- On the noun's groups, the ∆-operator singles out the group recording the scope: the
distributed scope holds of the positive atoms and fails of the negative ones exactly when the
group is `triFunction N vp` (41). -/
theorem delta_iff_eq_triFunction {N vp : α → Prop} {X : Group α} (hX : X ∈ noun N) :
    X.delta vp ↔ X = triFunction N vp := by
  rw [mem_noun_iff] at hX
  constructor
  · intro hd
    funext x
    have hx := hX x
    have hdx := hd x
    unfold triFunction
    split_ifs with hN hvp
    · cases h : X x
      · rfl
      · rw [h] at hdx
        exact absurd hvp hdx
      · exact absurd (hx.mpr hN) (by simp [h])
    · cases h : X x
      · rw [h] at hdx
        exact absurd hdx hvp
      · rfl
      · exact absurd (hx.mpr hN) (by simp [h])
    · by_contra h
      exact hN (hx.mp h)
  · rintro rfl x
    unfold Tri.Apply
    cases h : triFunction N vp x
    · exact ((triFunction_pos_iff N vp x).mp h).2
    · exact ((triFunction_neg_iff N vp x).mp h).2
    · trivial

end Groups

/-! ### Determiners as predicates (§4.1–4.2) -/

/-- A determiner: a predicate of groups. -/
abbrev Det (α : Type*) := Group α → Prop

section Determiners

variable {α : Type*}

/-- Bare numerals (23), with an at-least semantics: at least `n` positive atoms. -/
def atLeast (n : ℕ) : Det α := λ X => n ≤ X.posAtoms.ncard

/-- *exactly n* (27a), and *zero* (31) as `exactly 0`. -/
def exactly (n : ℕ) : Det α := λ X => X.posAtoms.ncard = n

/-- *less than n* (27b). -/
def lessThan (n : ℕ) : Det α := λ X => X.posAtoms.ncard < n

/-- *all* (32a): no negative atoms. -/
def all : Det α := λ X => X.negAtoms = ∅

/-- *some* (32b): some positive atom. -/
def someDet : Det α := λ X => X.posAtoms ≠ ∅

/-- *not all* (33a), the negation of *all*. -/
def notAll : Det α := λ X => ¬ all X

/-- *none* (33b), the negation of *some*. -/
def noneDet : Det α := λ X => ¬ someDet X

/-- *most* (36): more positive than negative atoms. -/
def most : Det α := λ X => X.negAtoms.ncard < X.posAtoms.ncard

/-- Covert existential raising (5) over the groups of the noun that satisfy the determiner, with
an arbitrary continuation. -/
def raise (D : Det α) (N : α → Prop) (φ : Group α → Prop) : Prop :=
  ∃ X, D X ∧ X ∈ noun N ∧ φ X

/-- A simple distributive sentence, `[∃ [D N]] ∆ vp`, (26). -/
def sentence (D : Det α) (N vp : α → Prop) : Prop := raise D N (Group.delta vp)

/-- The composition lemma: a predicative sentence holds exactly when the determiner holds of the
group that records the scope on the noun's extension, (42). -/
theorem sentence_iff (D : Det α) (N vp : α → Prop) : sentence D N vp ↔ D (triFunction N vp) := by
  constructor
  · rintro ⟨X, hD, hX, hd⟩
    rwa [(delta_iff_eq_triFunction hX).mp hd] at hD
  · intro hD
    refine ⟨triFunction N vp, hD, ?_, (delta_iff_eq_triFunction ?_).mpr rfl⟩ <;>
      exact (mem_noun_iff N _).mpr λ x => not_congr (triFunction_blank_iff N vp x) |>.trans not_not

/-- (29): *exactly two boys sneezed* says that exactly two boys sneezed. -/
theorem sentence_exactly (n : ℕ) (N vp : α → Prop) :
    sentence (exactly n) N vp ↔ {x | N x ∧ vp x}.ncard = n := by
  rw [sentence_iff, exactly, posAtoms_triFunction]

/-- (30): *less than three boys sneezed* says that fewer than three boys sneezed, with neither
the problem of upper bounds nor existential entailment. -/
theorem sentence_lessThan (n : ℕ) (N vp : α → Prop) :
    sentence (lessThan n) N vp ↔ {x | N x ∧ vp x}.ncard < n := by
  rw [sentence_iff, lessThan, posAtoms_triFunction]

/-- Bare numerals with the at-least semantics (26). -/
theorem sentence_atLeast (n : ℕ) (N vp : α → Prop) :
    sentence (atLeast n) N vp ↔ n ≤ {x | N x ∧ vp x}.ncard := by
  rw [sentence_iff, atLeast, posAtoms_triFunction]

/-- (34): *all boys sneezed* has universal truth conditions. -/
theorem sentence_all (N vp : α → Prop) : sentence all N vp ↔ ∀ x, N x → vp x := by
  rw [sentence_iff, all, negAtoms_triFunction, Set.eq_empty_iff_forall_notMem]
  simp

/-- *some boys sneezed* has existential truth conditions. -/
theorem sentence_someDet (N vp : α → Prop) : sentence someDet N vp ↔ ∃ x, N x ∧ vp x := by
  rw [sentence_iff, someDet, posAtoms_triFunction, ← Set.nonempty_iff_ne_empty]
  rfl

/-- *no boys sneezed*. -/
theorem sentence_noneDet (N vp : α → Prop) : sentence noneDet N vp ↔ ∀ x, N x → ¬ vp x := by
  rw [sentence_iff, noneDet, someDet, posAtoms_triFunction, not_not,
    Set.eq_empty_iff_forall_notMem]
  simp

/-- (31): *zero boys sneezed* is equivalent to *no boys sneezed*, *zero* being a cardinality
predicate like any other numeral. -/
theorem sentence_zero_iff_noneDet [Finite α] (N vp : α → Prop) :
    sentence (exactly 0) N vp ↔ sentence noneDet N vp := by
  rw [sentence_exactly, sentence_noneDet, Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  simp

/-- (45): *most* has its relational truth conditions (35). -/
theorem sentence_most (N vp : α → Prop) :
    sentence most N vp ↔ {x | N x ∧ ¬ vp x}.ncard < {x | N x ∧ vp x}.ncard := by
  rw [sentence_iff, most, posAtoms_triFunction, negAtoms_triFunction]

end Determiners

/-! ### Conservativity and the predicative theory (§4.3) -/

section Conservativity

variable {α : Type*}

/-- Mapping from determiners to predicates (40): apply the relational determiner to the atoms
and the positive atoms of the group. -/
def Det.ofGQ (Q : GQ α) : Det α := λ X => Q (λ x => X x ≠ .blank) (λ x => X x = .pos)

/-- Mapping from predicates to determiners (44): the truth conditions of the predicative
sentence. -/
def Det.toGQ (D : Det α) : GQ α := λ R S => sentence D R S

/-- (42): the composite of the two mappings evaluates the determiner at the restrictor and the
intersection of restrictor and scope. -/
theorem toGQ_ofGQ (Q : GQ α) (R S : α → Prop) :
    (Det.ofGQ Q).toGQ R S ↔ Q R (λ x => R x ∧ S x) := by
  rw [Det.toGQ, sentence_iff, Det.ofGQ]
  have h₁ : (λ x => triFunction R S x ≠ Tri.blank) = R :=
    funext λ x => propext (not_congr (triFunction_blank_iff R S x) |>.trans not_not)
  have h₂ : (λ x => triFunction R S x = Tri.pos) = λ x => R x ∧ S x :=
    funext λ x => propext (triFunction_pos_iff R S x)
  rw [h₁, h₂]

/-- The mapping to predicates is meaning-preserving exactly for conservative determiners. -/
theorem toGQ_ofGQ_eq_iff (Q : GQ α) : (Det.ofGQ Q).toGQ = Q ↔ Conservative Q := by
  constructor
  · intro h R S
    have := toGQ_ofGQ Q R S
    rwa [h] at this
  · intro hQ
    funext R S
    exact propext ((toGQ_ofGQ Q R S).trans (hQ R S).symm)

/-- (46): every predicate yields a conservative determiner. Conservativity is a structural
consequence of the predicative theory. -/
theorem toGQ_conservative (D : Det α) : Conservative D.toGQ := by
  intro R S
  simp only [Det.toGQ, sentence_iff, triFunction_and_absorb]

/-- The other composite is the identity: a predicate is recovered from its determiner. -/
theorem ofGQ_toGQ (D : Det α) : Det.ofGQ D.toGQ = D := by
  funext X
  simp only [Det.ofGQ, Det.toGQ, sentence_iff, triFunction_atoms_pos]

/-- The Härtig quantifier (1), equal cardinality of restrictor and scope, the standard
non-conservative example. -/
noncomputable def hartig [Finite α] : GQ α := λ A B => {x | A x}.ncard = {x | B x}.ncard

/-- (43): mapped to a predicate and back, the Härtig quantifier becomes the universal. -/
theorem hartig_ofGQ_toGQ [Finite α] (R S : α → Prop) :
    (Det.ofGQ hartig).toGQ R S ↔ ∀ x, R x → S x := by
  rw [toGQ_ofGQ, hartig]
  constructor
  · intro h x hR
    have hsub : {x | R x ∧ S x} ⊆ {x | R x} := λ _ hx => hx.1
    have heq := Set.eq_of_subset_of_ncard_le hsub h.le
    exact ((Set.ext_iff.mp heq x).mpr hR).2
  · intro h
    congr 1
    exact Set.ext λ x => ⟨λ hx => ⟨hx, h x hx⟩, λ hx => hx.1⟩

/-- The isomorphism of §4.3 made precise: predicates of groups are order-isomorphic to the
conservative determiners `ConsGQ`. -/
noncomputable def consGQOrderIso : ConsGQ α ≃o Det α :=
  Equiv.toOrderIso
    { toFun := λ Q => Det.ofGQ Q.1
      invFun := λ D => ⟨D.toGQ, toGQ_conservative D⟩
      left_inv := λ Q => Subtype.ext ((toGQ_ofGQ_eq_iff Q.1).mpr Q.2)
      right_inv := ofGQ_toGQ }
    (λ {_ _} h _ => h _ _)
    (λ {D₁ D₂} h R S hs => (sentence_iff D₂ R S).mpr (h _ ((sentence_iff D₁ R S).mp hs)))

/-- The count of §4.3: on `n` individuals there are `2 ^ 3 ^ n` Boolean predicates of groups,
one power of two per trivalent function. -/
theorem card_predicates (n : ℕ) : Fintype.card (Group (Fin n) → Bool) = 2 ^ 3 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fun, Fintype.card_fin,
    show Fintype.card Tri = 3 by decide]

/-- Against `2 ^ 4 ^ n` relational determiners. -/
theorem card_relational (n : ℕ) :
    Fintype.card ((Fin n → Bool) → (Fin n → Bool) → Bool) = 2 ^ 4 ^ n := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul, ← mul_pow]
  rfl

end Conservativity

/-! ### Existential and distributive scope (§5) -/

section Scope

variable {α : Type*}

/-- The universal picks out the noun's wholly positive group. -/
theorem all_mem_noun_iff {N : α → Prop} {X : Group α} (hX : X ∈ noun N) :
    all X ↔ X = triFunction N (λ _ => True) := by
  rw [mem_noun_iff] at hX
  constructor
  · intro h
    funext x
    have hx := hX x
    have hn : X x ≠ .neg := λ hneg => Set.eq_empty_iff_forall_notMem.mp h x hneg
    by_cases hN : N x
    · have hpos : X x = .pos := by
        cases hc : X x
        · rfl
        · exact absurd hc hn
        · exact absurd (hx.mpr hN) (by simp [hc])
      rw [hpos, triFunction]
      simp [hN]
    · have hb : X x = .blank := Classical.byContradiction λ hc => hN (hx.mp hc)
      rw [hb, triFunction]
      simp [hN]
  · rintro rfl
    rw [all, negAtoms_triFunction]
    simp

/-- The negative determiner picks out the noun's wholly negative group. -/
theorem noneDet_mem_noun_iff {N : α → Prop} {X : Group α} (hX : X ∈ noun N) :
    noneDet X ↔ X = triFunction N (λ _ => False) := by
  rw [mem_noun_iff] at hX
  constructor
  · intro h
    have hp : ∀ x, X x ≠ .pos := λ x hpos =>
      h (Set.nonempty_iff_ne_empty.mp ⟨x, hpos⟩)
    funext x
    have hx := hX x
    by_cases hN : N x
    · have hneg : X x = .neg := by
        cases hc : X x
        · exact absurd hc (hp x)
        · rfl
        · exact absurd (hx.mpr hN) (by simp [hc])
      rw [hneg, triFunction]
      simp [hN]
    · have hb : X x = .blank := Classical.byContradiction λ hc => hN (hx.mp hc)
      rw [hb, triFunction]
      simp [hN]
  · rintro rfl
    rw [noneDet, someDet, posAtoms_triFunction, not_not]
    simp

/-- (49): existential raising of *all N* over any continuation is scopeless, since the noun
phrase denotes a singleton; the quantificational force stays with the ∆-operator inside. -/
theorem raise_all (N : α → Prop) (φ : Group α → Prop) :
    raise all N φ ↔ φ (triFunction N (λ _ => True)) := by
  constructor
  · rintro ⟨X, hall, hX, hφ⟩
    rwa [(all_mem_noun_iff hX).mp hall] at hφ
  · intro hφ
    have hX : triFunction N (λ _ => True) ∈ noun N := (mem_noun_iff N _).mpr λ x =>
      not_congr (triFunction_blank_iff N _ x) |>.trans not_not
    exact ⟨_, (all_mem_noun_iff hX).mpr rfl, hX, hφ⟩

/-- Likewise for *no N*, (48b). -/
theorem raise_noneDet (N : α → Prop) (φ : Group α → Prop) :
    raise noneDet N φ ↔ φ (triFunction N (λ _ => False)) := by
  constructor
  · rintro ⟨X, hnone, hX, hφ⟩
    rwa [(noneDet_mem_noun_iff hX).mp hnone] at hφ
  · intro hφ
    have hX : triFunction N (λ _ => False) ∈ noun N := (mem_noun_iff N _).mpr λ x =>
      not_congr (triFunction_blank_iff N _ x) |>.trans not_not
    exact ⟨_, (noneDet_mem_noun_iff hX).mpr rfl, hX, hφ⟩

/-- (50): *exactly two* picks out several groups of a three-element noun, so its existential
raising is not scopeless and an exceptional scope reading is predicted. -/
theorem exactly_two_not_singleton :
    ∃ X Y : Group (Fin 3), X ≠ Y ∧ X ∈ noun (λ _ => True) ∧ Y ∈ noun (λ _ => True) ∧
      exactly 2 X ∧ exactly 2 Y := by
  refine ⟨![Tri.pos, Tri.pos, Tri.neg], ![Tri.pos, Tri.neg, Tri.pos], by decide,
    (mem_noun_iff _ _).mpr (by decide), (mem_noun_iff _ _).mpr (by decide), ?_, ?_⟩
  · have h : Group.posAtoms ![Tri.pos, Tri.pos, Tri.neg] = {0, 1} :=
      Set.ext λ i => by fin_cases i <;> simp [Group.posAtoms]
    show Set.ncard _ = 2
    rw [h]
    exact Set.ncard_pair (by decide)
  · have h : Group.posAtoms ![Tri.pos, Tri.neg, Tri.pos] = {0, 2} :=
      Set.ext λ i => by fin_cases i <;> simp [Group.posAtoms]
    show Set.ncard _ = 2
    rw [h]
    exact Set.ncard_pair (by decide)

end Scope

end Elliott2025
