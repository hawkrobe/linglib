import Linglib.Semantics.Quantification.Lattice
import Linglib.Semantics.Quantification.Counting
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Atoms
import Mathlib.Tactic.FinCases

/-!
# Keenan and Stavi (1986): A Semantic Characterization of Natural Language Determiners

This file formalizes the Conservativity Theorem of [keenan-stavi-1986]: the possible determiner
denotations, the Boolean closure of the denotations of a few simple determiners, are exactly the
conservative functions, those with `f R T ↔ f R (R ⊓ T)`. The generators are the Appendix's two
individual-anchored determiners `Sₐ` and `Eₐ`, *John's one or more* and *John's zero or more* when
`a` is all John possesses (`S`, `E`); every conservative function is the join of the atoms
`atom p q` at the pairs where it holds, each atom is a meet of generators and their complements,
and so the Boolean subalgebra the generators generate is the conservative algebra
(`closure_generators`). Counting the atoms, three cells per individual, gives PROP 4: on `n`
individuals there are `2 ^ 3 ^ n` conservative functions among the `2 ^ 4 ^ n` functions from
properties to sets of properties (`card_consGQ`), 512 among 65,536 for two individuals.

Section 3.3 characterizes the determiners of existential-*there* sentences as the existential
functions, `f R T ↔ f (R ⊓ T) ⊤`: *at least n* is one, *every* and *the two* are not, the class
is closed under the Boolean operations (PROP 13) and isomorphic to the sets of properties through
`f ↦ f(1)` (PROP 15, `existentialEquiv`), so has `2 ^ 2 ^ n` members. The cardinal functions of
Section 3.4, deciding by the number of individuals in restrictor and scope, are the `2 ^ (n + 1)`
subsets of `{0, …, n}` (PROP 14), all existential, and *no ... but John* is existential without
being cardinal.

## Implementation notes

Conservativity and the existential property are the substrate's `Conservative` and
`Existential`, and the conservative algebra is `ConsGQ`; the three classes are Boolean
subalgebras of `GQ α`, and the counts are `Nat.card`s over a `Fintype` universe. The
(In)effability Theorems of Section 3.6, which quantify over the English determiner expressions,
are not formalized.

## References

* [keenan-stavi-1986]
-/

namespace KeenanStavi1986

open Quantification BooleanSubalgebra

variable {α : Type*}

/-! ### The Conservativity Theorem (Section 2.5 and the Appendix) -/

/-- `Sₐ`: the restrictor and the scope both hold of the individual `a`, the denotation (8) of
*John's one or more* when `a` is all John possesses. -/
def S (a : α) : GQ α := λ R T => R a ∧ T a

/-- `Eₐ`: the scope holds of `a` if the restrictor does, *John's zero or more*. -/
def E (a : α) : GQ α := λ R T => R a → T a

/-- The generators of the conservative algebra: `Sₐ` and `Eₐ` for every individual. -/
def generators (α : Type*) : Set (GQ α) := Set.range S ∪ Set.range E

theorem conservative_S (a : α) : Conservative (S a) :=
  λ _ _ => ⟨λ h => ⟨h.1, h⟩, λ h => ⟨h.1, h.2.2⟩⟩

theorem conservative_E (a : α) : Conservative (E a) :=
  λ _ _ => ⟨λ h hR => ⟨hR, h hR⟩, λ h hR => (h hR).2⟩

/-- The atom `f_{pq}` of the conservative algebra: true at the restrictor `p` and exactly the
scopes meeting `p` in `q`. -/
def atom (p q : α → Prop) : GQ α := λ R T => R = p ∧ R ⊓ T = q

theorem conservative_atom (p q : α → Prop) : Conservative (atom p q) := λ R T => by
  show R = p ∧ R ⊓ T = q ↔ R = p ∧ R ⊓ (R ⊓ T) = q
  rw [← inf_assoc, inf_idem]

/-- `atom p q` lies below a conservative `f` exactly when `f` holds at `(p, q)`. -/
theorem atom_le_iff {f : GQ α} (hf : Conservative f) {p q : α → Prop} (h : q ≤ p) :
    atom p q ≤ f ↔ f p q :=
  ⟨λ hle => hle p q ⟨rfl, inf_eq_right.mpr h⟩, λ hpq R T ⟨hR, hT⟩ => by
    subst hR; subst hT; exact (hf _ _).mpr hpq⟩

/-- The atoms of the conservative algebra are the `atom p q` with `q ≤ p`. -/
theorem isAtom_atom {p q : α → Prop} (h : q ≤ p) :
    IsAtom (⟨atom p q, conservative_atom p q⟩ : ConsGQ α) := by
  refine ⟨λ hbot => ?_, λ b hb => ?_⟩
  · exact (congrArg (λ f : ConsGQ α => f.1 p q) hbot).mp ⟨rfl, inf_eq_right.mpr h⟩
  · by_contra hne
    obtain ⟨R, T, hRT⟩ : ∃ R T, b.1 R T := by
      by_contra hall
      push Not at hall
      exact hne (Subtype.ext (funext₂ λ R T => propext ⟨hall R T, False.elim⟩))
    have hle : b.1 ≤ atom p q := hb.le
    obtain ⟨rfl, rfl⟩ := hle R T hRT
    refine hb.not_ge λ R' T' ⟨hR', hT'⟩ => ?_
    subst hR'
    exact (b.2.iff_of_inf_eq hT').mpr hRT

/-- Every conservative function is the join of the atoms at the pairs where it holds: the
conservative algebra is atomic. -/
theorem eq_iSup_atom {f : GQ α} (hf : Conservative f) :
    f = ⨆ pq ∈ {pq : (α → Prop) × (α → Prop) | f pq.1 pq.2}, atom pq.1 pq.2 := by
  funext R T
  apply propext
  simp only [iSup_apply, iSup_Prop_eq, exists_prop, Set.mem_ofPred_eq, Prod.exists, atom]
  constructor
  · exact λ h => ⟨R, R ⊓ T, (hf R T).mp h, rfl, rfl⟩
  · rintro ⟨p, q, h, rfl, rfl⟩
    exact (hf _ _).mpr h

/-- The Appendix's decomposition of an atom into generators: `Sₐ` over the individuals in `q`,
the complements of `Sₐ` and `Eₐ` over those in `p` but not in `q`, and the complement of `Sₐ`
with `Eₐ` over those outside `p`. -/
theorem atom_eq_iInf (p q : α → Prop) :
    atom p q = (⨅ a ∈ {a | q a}, S a) ⊓ (⨅ a ∈ {a | p a ∧ ¬ q a}, (S a)ᶜ ⊓ (E a)ᶜ) ⊓
      ⨅ a ∈ {a | ¬ p a}, (S a)ᶜ ⊓ E a := by
  funext R T
  apply propext
  simp only [atom, Pi.inf_apply, iInf_apply, iInf_Prop_eq, Pi.compl_apply, compl_iff_not,
    inf_Prop_eq, Set.mem_ofPred_eq, S, E]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨λ _ h => h, λ _ ⟨hR, hq⟩ => ⟨hq, λ h => hq ⟨hR, h hR⟩⟩⟩,
      λ _ hR => ⟨λ h => hR h.1, λ h => absurd h hR⟩⟩
  · rintro ⟨⟨hq, hp⟩, hn⟩
    refine ⟨funext λ a => propext ?_, funext λ a => propext ?_⟩
    · by_cases hpa : p a
      · by_cases hqa : q a
        · exact iff_of_true (hq a hqa).1 hpa
        · exact iff_of_true (of_not_imp (hp a ⟨hpa, hqa⟩).2) hpa
      · exact iff_of_false (λ hR => (hn a hpa).1 ⟨hR, (hn a hpa).2 hR⟩) hpa
    · by_cases hqa : q a
      · exact iff_of_true (hq a hqa) hqa
      · by_cases hpa : p a
        · exact iff_of_false (hp a ⟨hpa, hqa⟩).1 hqa
        · exact iff_of_false (hn a hpa).1 hqa

theorem atom_mem_closure [Finite α] (p q : α → Prop) :
    atom p q ∈ closure (generators α) := by
  rw [atom_eq_iInf]
  refine inf_mem (inf_mem (biInf_mem (Set.toFinite _) λ a _ => ?_)
    (biInf_mem (Set.toFinite _) λ a _ => ?_)) (biInf_mem (Set.toFinite _) λ a _ => ?_)
  · exact subset_closure (Or.inl ⟨a, rfl⟩)
  · exact inf_mem (compl_mem (subset_closure (Or.inl ⟨a, rfl⟩)))
      (compl_mem (subset_closure (Or.inr ⟨a, rfl⟩)))
  · exact inf_mem (compl_mem (subset_closure (Or.inl ⟨a, rfl⟩))) (subset_closure (Or.inr ⟨a, rfl⟩))

/-- The Conservativity Theorem: the Boolean algebra generated by the `Sₐ` and `Eₐ` is the
algebra of conservative functions. -/
theorem closure_generators [Finite α] : closure (generators α) = conservativeSubalgebra := by
  refine le_antisymm (closure_le.2 ?_) λ f hf => ?_
  · rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    exacts [conservative_S a, conservative_E a]
  · rw [eq_iSup_atom (mem_conservativeSubalgebra.mp hf)]
    exact biSup_mem (Set.toFinite _) λ pq _ => atom_mem_closure pq.1 pq.2

/-! ### Counting the conservative functions (Section 2.7) -/

/-- The index of the atoms: restrictor–scope pairs with the scope inside the restrictor. -/
abbrev Atoms (α : Type*) := {pq : (α → Prop) × (α → Prop) // pq.2 ≤ pq.1}

/-- A conservative function is its values on the atoms, and any values extend to one. -/
noncomputable def consEquiv : ConsGQ α ≃ (Atoms α → Prop) where
  toFun f pq := f.1 pq.1.1 pq.1.2
  invFun g := ⟨λ R T => g ⟨(R, R ⊓ T), inf_le_left⟩, λ R T =>
    Iff.of_eq (congrArg g (Subtype.ext (Prod.ext rfl (by
      show R ⊓ T = R ⊓ (R ⊓ T)
      rw [← inf_assoc, inf_idem]))))⟩
  left_inv f := Subtype.ext (funext₂ λ R T => propext (f.2 R T).symm)
  right_inv g := funext λ pq => congrArg g (Subtype.ext (Prod.ext rfl (inf_eq_right.mpr pq.2)))

open Classical in
/-- A pair `q ≤ p` sorts each individual into one of three cells, in `q`, in `p` but not `q`,
or outside `p`, and any sorting arises. -/
noncomputable def atomsEquiv : Atoms α ≃ (α → Fin 3) where
  toFun pq x := if pq.1.2 x then 2 else if pq.1.1 x then 1 else 0
  invFun c := ⟨(λ x => c x ≠ 0, λ x => c x = 2), λ x hx => by
    show c x ≠ 0
    rw [show c x = 2 from hx]
    decide⟩
  left_inv := λ ⟨⟨p, q⟩, h⟩ => by
    refine Subtype.ext (Prod.ext (funext λ x => propext ?_) (funext λ x => propext ?_))
    · by_cases hq : q x
      · have hp : p x := h x hq
        simp [hq, hp]
      · by_cases hp : p x <;> simp [hq, hp]
    · by_cases hq : q x
      · simp [hq]
      · by_cases hp : p x <;> simp +decide [hq, hp]
  right_inv c := funext λ x => by
    dsimp only
    by_cases h2 : c x = 2
    · simp [h2]
    · by_cases h0 : c x = 0
      · simp [h0]
      · have h1 : c x = 1 := by omega
        simp +decide [h1]

theorem card_atoms [Fintype α] : Nat.card (Atoms α) = 3 ^ Fintype.card α := by
  rw [Nat.card_congr atomsEquiv, Nat.card_fun, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- PROP 4: with `n` individuals there are `2 ^ 3 ^ n` conservative functions. -/
theorem card_consGQ [Fintype α] : Nat.card (ConsGQ α) = 2 ^ 3 ^ Fintype.card α := by
  rw [Nat.card_congr consEquiv, Nat.card_fun, card_atoms, Nat.card_eq_fintype_card,
    Fintype.card_prop]

/-- Among `2 ^ 4 ^ n` functions from properties to sets of properties. -/
theorem card_gq [Fintype α] : Nat.card (GQ α) = 2 ^ 4 ^ Fintype.card α := by
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Prop),
    Fintype.card_prop, Nat.card_eq_fintype_card, ← pow_mul, ← mul_pow]
  norm_num

/-! ### Existential determiners (Section 3.3) -/

/-- PROP 13: the existential functions are closed under the Boolean operations. -/
def existentialSubalgebra : BooleanSubalgebra (GQ α) where
  carrier := {f | Existential f}
  supClosed' _ hf _ hg R T := or_congr (hf R T) (hg R T)
  infClosed' _ hf _ hg R T := and_congr (hf R T) (hg R T)
  compl_mem' hf R T := not_congr (hf R T)
  bot_mem' _ _ := Iff.rfl

@[simp] theorem mem_existentialSubalgebra {f : GQ α} :
    f ∈ existentialSubalgebra ↔ Existential f :=
  Iff.rfl

/-- Existential functions are conservative: E-Det lies in DDet. -/
theorem existentialSubalgebra_le :
    existentialSubalgebra ≤ (conservativeSubalgebra : BooleanSubalgebra (GQ α)) :=
  λ _ hf R T => by
    rw [hf R T, hf R (λ x => R x ∧ T x)]
    simp only [and_self_left]

/-- (99)–(100): *at least n* is existential. -/
theorem existential_at_least_n [Fintype α] (n : ℕ) :
    Existential (at_least_n_sem (α := α) n) := by
  classical
  intro R T
  simp only [at_least_n_sem]
  rw [count_eq_decidable (λ x => (R x ∧ T x) ∧ True), count_eq_decidable (λ x => R x ∧ T x),
    count_congr_iff (Q := λ x => R x ∧ T x) λ _ => iff_of_eq (and_true _)]

/-- *every* is not existential: with two lawyers, one of them a doctor, *every lawyer is a
doctor* is false while *every lawyer who is a doctor is an individual* is true. -/
theorem not_existential_every : ¬ Existential (every_sem : GQ (Fin 2)) := λ h =>
  absurd ((h (λ _ => True) (· = 0)).mpr λ _ _ => trivial) λ h' =>
    absurd (h' 1 trivial) (by decide)

open Classical in
/-- (43): *the n*, the universal on a restrictor of exactly `n` individuals. -/
noncomputable def theN [Fintype α] (n : ℕ) : GQ α := λ R T => count R = n ∧ every_sem R T

/-- *the two* is not existential: with three individuals, two of them with the scope
property, *the two individuals have it* is false while *the two individuals who have it are
individuals* is true. -/
theorem not_existential_theN : ¬ Existential (theN (α := Fin 3) 2) := by
  intro h
  have key := (h (λ _ => True) (· ≠ 2)).mpr
  simp only [theN, every_sem, true_and, imp_true_iff, and_true, true_imp_iff] at key
  rw [count_eq_decidable (λ x : Fin 3 => x ≠ 2), count_eq_decidable (λ _ : Fin 3 => True)] at key
  simp only [count, countOn] at key
  revert key
  decide

/-- (42): *no ... but J*, true when restrictor and scope meet in exactly the individual `a`. -/
def noBut (a : α) : GQ α := λ R T => R ⊓ T = (· = a)

/-- (103): *no ... but John* is existential. -/
theorem existential_noBut (a : α) : Existential (noBut a) := λ R T => by
  show R ⊓ T = (· = a) ↔ (R ⊓ T) ⊓ (⊤ : α → Prop) = (· = a)
  rw [inf_top_eq]

/-- PROP 15: an existential function is determined by its set of properties `f(1)`, and every
set of properties arises. -/
noncomputable def existentialEquiv : existentialSubalgebra (α := α) ≃ ((α → Prop) → Prop) where
  toFun f T := f.1 ⊤ T
  invFun g := ⟨λ R T => g (R ⊓ T), λ R T => Iff.of_eq (congrArg g (inf_top_eq _).symm)⟩
  left_inv f := Subtype.ext (funext₂ λ R T => propext ((f.2 ⊤ (R ⊓ T)).trans (by
    show f.1 (⊤ ⊓ (R ⊓ T)) ⊤ ↔ f.1 R T
    rw [top_inf_eq]
    exact (f.2 R T).symm)))
  right_inv g := funext λ T => congrArg g (top_inf_eq T)

/-- With `n` individuals there are `2 ^ 2 ^ n` existential functions. -/
theorem card_existential [Fintype α] :
    Nat.card (existentialSubalgebra (α := α)) = 2 ^ 2 ^ Fintype.card α := by
  rw [Nat.card_congr existentialEquiv, Nat.card_fun, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop, Nat.card_eq_fintype_card]

/-! ### Cardinal determiners (Section 3.4) -/

/-- (102): a cardinal function decides by the number of individuals in restrictor and scope. -/
def Cardinal (f : GQ α) : Prop :=
  ∀ R T R' T' : α → Prop,
    Nat.card {x // R x ∧ T x} = Nat.card {x // R' x ∧ T' x} → (f R T ↔ f R' T')

/-- PROP 14(a): the cardinal functions are closed under the Boolean operations. -/
def cardinalSubalgebra : BooleanSubalgebra (GQ α) where
  carrier := {f | Cardinal f}
  supClosed' _ hf _ hg R T R' T' h := or_congr (hf R T R' T' h) (hg R T R' T' h)
  infClosed' _ hf _ hg R T R' T' h := and_congr (hf R T R' T' h) (hg R T R' T' h)
  compl_mem' hf R T R' T' h := not_congr (hf R T R' T' h)
  bot_mem' _ _ _ _ _ := Iff.rfl

@[simp] theorem mem_cardinalSubalgebra {f : GQ α} : f ∈ cardinalSubalgebra ↔ Cardinal f :=
  Iff.rfl

/-- PROP 14(c): cardinal functions are existential. -/
theorem cardinalSubalgebra_le :
    cardinalSubalgebra ≤ (existentialSubalgebra : BooleanSubalgebra (GQ α)) :=
  λ _ hf R T =>
    hf R T _ _ (Nat.card_congr (Equiv.subtypeEquivRight λ _ => (iff_of_eq (and_true _)).symm))

/-- *no ... but John* is not cardinal: it separates two singletons of equal size. -/
theorem not_cardinal_noBut : ¬ Cardinal (noBut (0 : Fin 2)) := by
  intro h
  have key := (h (· = 0) (· = 0) (· = 1) (· = 1)
    (by simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]; decide)).mp (inf_idem _)
  rw [noBut, inf_idem] at key
  exact absurd ((congrFun key 1).mp rfl) (by decide)

private theorem exists_ofSize [Fintype α] (k : Fin (Fintype.card α + 1)) :
    ∃ t ⊆ (Finset.univ : Finset α), t.card = k :=
  Finset.exists_subset_card_eq ((Nat.lt_succ_iff.mp k.2).trans_eq Finset.card_univ.symm)

/-- A set of `k` individuals, for `k` at most the size of the universe. -/
noncomputable def ofSize [Fintype α] (k : Fin (Fintype.card α + 1)) : Finset α :=
  Classical.choose (exists_ofSize k)

theorem card_ofSize [Fintype α] (k : Fin (Fintype.card α + 1)) :
    Nat.card {x // x ∈ ofSize k ∧ x ∈ ofSize k} = k := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight λ _ => and_self_iff), Nat.card_eq_finsetCard]
  exact (Classical.choose_spec (exists_ofSize k)).2

/-- PROP 14(b): a cardinal function is a set of numbers between `0` and `n`, read off the sets
of each size, and any set of numbers arises. -/
noncomputable def cardinalEquiv [Fintype α] :
    cardinalSubalgebra (α := α) ≃ (Fin (Fintype.card α + 1) → Prop) where
  toFun f k := f.1 (· ∈ ofSize k) (· ∈ ofSize k)
  invFun g := ⟨λ R T => g ⟨Nat.card {x // R x ∧ T x},
      Nat.lt_succ_of_le ((Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq
        Nat.card_eq_fintype_card)⟩,
    λ _ _ _ _ h => Iff.of_eq (congrArg g (Fin.ext h))⟩
  left_inv f := Subtype.ext (funext₂ λ R T => propext (f.2 _ _ R T (card_ofSize _)))
  right_inv g := funext λ k => congrArg g (Fin.ext (card_ofSize k))

theorem card_cardinal [Fintype α] :
    Nat.card (cardinalSubalgebra (α := α)) = 2 ^ (Fintype.card α + 1) := by
  rw [Nat.card_congr cardinalEquiv, Nat.card_fun, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_prop, Fintype.card_fin]

/-- Two individuals: 512 conservative functions among 65,536, of which 8 are cardinal. -/
theorem two_individuals :
    Nat.card (ConsGQ (Fin 2)) = 512 ∧ Nat.card (GQ (Fin 2)) = 65536 ∧
      Nat.card (cardinalSubalgebra (α := Fin 2)) = 8 := by
  simp only [card_consGQ, card_gq, card_cardinal, Fintype.card_fin]
  decide

/-- Three individuals: 16 cardinal functions among 256 existential ones. -/
theorem three_individuals :
    Nat.card (cardinalSubalgebra (α := Fin 3)) = 16 ∧
      Nat.card (existentialSubalgebra (α := Fin 3)) = 256 := by
  simp only [card_cardinal, card_existential, Fintype.card_fin]
  decide

end KeenanStavi1986
