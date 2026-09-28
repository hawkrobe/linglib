module

public import Linglib.Core.Data.Set.Sups
public import Linglib.Logic.Bilateral.Defs
public import Linglib.Logic.Truthmaker.Basic
public import Mathlib.Algebra.Group.DivInvMonoid

/-!
# Bilateral truthmaker propositions

This file defines Kit Fine's bilateral propositions. A bilateral proposition pairs a set of
verifiers with a set of falsifiers. Negation swaps the two sets, conjunction fuses verifiers and
pools falsifiers, and disjunction pools verifiers and fuses falsifiers.

The possible states form a lower set `P`, and two states are compatible when their fusion is
possible. A proposition is exclusive when no verifier is compatible with a falsifier, and
exhaustive when every possible state is compatible with a verifier or a falsifier. The maximal
possible states are the worlds, and a proposition is true at a world containing one of its
verifiers. When the states form a complete lattice, the subject-matter of a proposition is the
fusion of all its verifiers and falsifiers.

## Main definitions

* `Truthmaker.BilProp`: a set of verifiers and a set of falsifiers, with negation as an
  `InvolutiveNeg` instance.
* `Truthmaker.BilProp.conj`, `Truthmaker.BilProp.disj`: conjunction and disjunction.
* `Truthmaker.BilProp.Exclusive`, `Truthmaker.BilProp.Exhaustive`: the two halves of bivalence.
* `Truthmaker.BilProp.subjectMatter`: the fusion of all verifiers and falsifiers.
* `Truthmaker.Canonical.possible`, `Truthmaker.Canonical.atom`: Fine's canonical space, whose
  states are sets of literals, and its atomic propositions.

## Main results

* `Truthmaker.BilProp.neg_conj`, `Truthmaker.BilProp.neg_disj`: De Morgan's laws.
* `Truthmaker.BilProp.Exclusive.conj`, `Truthmaker.BilProp.Exhaustive.conj`: conjunction preserves
  exclusivity and exhaustivity, and so do negation and disjunction.
* `Truthmaker.BilProp.exclusive_iff`: a proposition is exclusive exactly when no possible state
  makes it both true and false.
* `Truthmaker.BilProp.Exhaustive.mem_upperClosure`: an exhaustive proposition is true or false at
  every world.
* `Truthmaker.BilProp.subjectMatter_neg`, `Truthmaker.BilProp.subjectMatter_conj`: negation keeps
  the subject-matter, and conjunction fuses subject-matters.
* `Truthmaker.Canonical.mem_upperClosure_disj_neg_atom`,
  `Truthmaker.Canonical.subjectMatter_disj_neg_atom_injective`: the excluded middle `a ∨ ¬a` of
  an atom is true at every world, yet distinct atoms give excluded middles with distinct
  subject-matters, each an impossible state.

## Implementation notes

Fine defines conjunction only between propositions with a verifier and disjunction only between
propositions with a falsifier. Here both are total, and the subject-matter lemmas carry the
nonemptiness hypotheses instead.

## References

* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
* [K. Fine, *A Theory of Truthmaker Content II: Subject-matter, Common Content, Remainder and
  Ground* (2017)][fine-2017b]
* [K. Fine, *Truthmaker Semantics* (2017)][fine-2017]
-/

@[expose] public section

open SetFamily

namespace Truthmaker

/-- A bilateral proposition is a set of verifying states together with a set of falsifying
states. -/
@[ext]
structure BilProp (S : Type*) where
  /-- The states that exactly verify the proposition. -/
  ver : Set S
  /-- The states that exactly falsify the proposition. -/
  fal : Set S

namespace BilProp

variable {S : Type*}

/-- The negation of a bilateral proposition swaps its verifiers and its falsifiers. -/
instance : InvolutiveNeg (BilProp S) where
  neg A := ⟨A.fal, A.ver⟩
  neg_neg _ := rfl

@[simp] theorem ver_neg (A : BilProp S) : (-A).ver = A.fal := rfl

@[simp] theorem fal_neg (A : BilProp S) : (-A).fal = A.ver := rfl

/-- Verification and falsification form a bilateral logic whose negation is `-`. -/
theorem isBilateral : Bilateral.IsBilateral (ver (S := S)) fal Neg.neg :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

section SemilatticeSup

variable [SemilatticeSup S] {P : LowerSet S} {A B : BilProp S}

/-- The conjunction of `A` and `B` is verified by the fusion of a verifier of each and falsified
by a falsifier of either. -/
def conj (A B : BilProp S) : BilProp S :=
  ⟨A.ver ⊻ B.ver, A.fal ∪ B.fal⟩

/-- The disjunction of `A` and `B` is verified by a verifier of either and falsified by the fusion
of a falsifier of each. -/
def disj (A B : BilProp S) : BilProp S :=
  ⟨A.ver ∪ B.ver, A.fal ⊻ B.fal⟩

@[simp] theorem ver_conj (A B : BilProp S) : (A.conj B).ver = A.ver ⊻ B.ver := rfl

@[simp] theorem fal_conj (A B : BilProp S) : (A.conj B).fal = A.fal ∪ B.fal := rfl

@[simp] theorem ver_disj (A B : BilProp S) : (A.disj B).ver = A.ver ∪ B.ver := rfl

@[simp] theorem fal_disj (A B : BilProp S) : (A.disj B).fal = A.fal ⊻ B.fal := rfl

@[simp] theorem neg_conj (A B : BilProp S) : -(A.conj B) = (-A).disj (-B) := rfl

@[simp] theorem neg_disj (A B : BilProp S) : -(A.disj B) = (-A).conj (-B) := rfl

/-- A bilateral proposition is exclusive over the possible states `P` if the fusion of a verifier
with a falsifier is never possible. -/
def Exclusive (P : LowerSet S) (A : BilProp S) : Prop :=
  ∀ ⦃s⦄, s ∈ A.ver → ∀ ⦃t⦄, t ∈ A.fal → s ⊔ t ∉ P

/-- A bilateral proposition is exhaustive over the possible states `P` if every possible state has
a possible fusion with a verifier or with a falsifier. -/
def Exhaustive (P : LowerSet S) (A : BilProp S) : Prop :=
  ∀ ⦃s⦄, s ∈ P → (∃ t ∈ A.ver, s ⊔ t ∈ P) ∨ ∃ t ∈ A.fal, s ⊔ t ∈ P

theorem Exclusive.neg (h : A.Exclusive P) : (-A).Exclusive P :=
  fun s hs t ht hst ↦ h ht hs (sup_comm s t ▸ hst)

theorem Exhaustive.neg (h : A.Exhaustive P) : (-A).Exhaustive P :=
  fun _ hs ↦ (h hs).symm

@[simp] theorem exclusive_neg : (-A).Exclusive P ↔ A.Exclusive P :=
  ⟨fun h ↦ neg_neg A ▸ h.neg, .neg⟩

@[simp] theorem exhaustive_neg : (-A).Exhaustive P ↔ A.Exhaustive P :=
  ⟨fun h ↦ neg_neg A ▸ h.neg, .neg⟩

theorem Exclusive.conj (hA : A.Exclusive P) (hB : B.Exclusive P) : (A.conj B).Exclusive P := by
  rintro _ hs t ht hst
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.1 hs
  rcases ht with ht | ht
  · exact hA ha ht (P.lower (sup_le_sup_right le_sup_left t) hst)
  · exact hB hb ht (P.lower (sup_le_sup_right le_sup_right t) hst)

theorem Exhaustive.conj (hA : A.Exhaustive P) (hB : B.Exhaustive P) :
    (A.conj B).Exhaustive P := by
  intro s hs
  obtain ⟨a, ha, hsa⟩ | ⟨t, ht, hst⟩ := hA hs
  · obtain ⟨b, hb, hsab⟩ | ⟨t, ht, hsat⟩ := hB hsa
    · exact .inl ⟨a ⊔ b, Set.sup_mem_sups ha hb, sup_assoc s a b ▸ hsab⟩
    · exact .inr ⟨t, .inr ht, P.lower (sup_le_sup_right le_sup_left t) hsat⟩
  · exact .inr ⟨t, .inl ht, hst⟩

theorem Exclusive.disj (hA : A.Exclusive P) (hB : B.Exclusive P) : (A.disj B).Exclusive P :=
  (hA.neg.conj hB.neg).neg

theorem Exhaustive.disj (hA : A.Exhaustive P) (hB : B.Exhaustive P) :
    (A.disj B).Exhaustive P :=
  (hA.neg.conj hB.neg).neg

/-- A proposition is exclusive exactly when no possible state contains both a verifier and a
falsifier of it. -/
theorem exclusive_iff :
    A.Exclusive P ↔ ∀ s ∈ P, s ∈ upperClosure A.ver → s ∉ upperClosure A.fal := by
  refine ⟨fun h s hs hv hf ↦ ?_, fun h a ha b hb hab ↦ ?_⟩
  · obtain ⟨a, ha, has⟩ := mem_upperClosure.1 hv
    obtain ⟨b, hb, hbs⟩ := mem_upperClosure.1 hf
    exact h ha hb (P.lower (sup_le has hbs) hs)
  · exact h _ hab (mem_upperClosure.2 ⟨a, ha, le_sup_left⟩)
      (mem_upperClosure.2 ⟨b, hb, le_sup_right⟩)

/-- An exhaustive proposition is true or false at every world, a maximal possible state. -/
theorem Exhaustive.mem_upperClosure (h : A.Exhaustive P) {w : S} (hw : Maximal (· ∈ P) w) :
    w ∈ upperClosure A.ver ∨ w ∈ upperClosure A.fal := by
  obtain ⟨t, ht, hwt⟩ | ⟨t, ht, hwt⟩ := h hw.prop
  · exact .inl ⟨t, ht, le_sup_right.trans (hw.le_of_ge hwt le_sup_left)⟩
  · exact .inr ⟨t, ht, le_sup_right.trans (hw.le_of_ge hwt le_sup_left)⟩

/-- The excluded middle of an exhaustive proposition is true at every world. -/
theorem Exhaustive.mem_upperClosure_disj_neg (h : A.Exhaustive P) {w : S}
    (hw : Maximal (· ∈ P) w) : w ∈ upperClosure (A.disj (-A)).ver := by
  simpa [upperClosure_union] using h.mem_upperClosure hw

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice S] {A B : BilProp S}

/-- The subject-matter of a bilateral proposition is the fusion of all its verifiers and all its
falsifiers. -/
def subjectMatter (A : BilProp S) : S :=
  sSup A.ver ⊔ sSup A.fal

@[simp] theorem subjectMatter_neg (A : BilProp S) : (-A).subjectMatter = A.subjectMatter :=
  sup_comm _ _

/-- The subject-matter of a conjunction of propositions with verifiers fuses their
subject-matters. -/
theorem subjectMatter_conj (hA : A.ver.Nonempty) (hB : B.ver.Nonempty) :
    (A.conj B).subjectMatter = A.subjectMatter ⊔ B.subjectMatter := by
  simp only [subjectMatter, ver_conj, fal_conj, Set.sSup_sups hA hB, sSup_union]
  exact sup_sup_sup_comm _ _ _ _

/-- The subject-matter of a disjunction of propositions with falsifiers fuses their
subject-matters. -/
theorem subjectMatter_disj (hA : A.fal.Nonempty) (hB : B.fal.Nonempty) :
    (A.disj B).subjectMatter = A.subjectMatter ⊔ B.subjectMatter := by
  simp only [subjectMatter, ver_disj, fal_disj, Set.sSup_sups hA hB, sSup_union]
  exact sup_sup_sup_comm _ _ _ _

/-- The excluded middle of a proposition with a verifier and a falsifier has the subject-matter of
the proposition. -/
theorem subjectMatter_disj_neg (hv : A.ver.Nonempty) (hf : A.fal.Nonempty) :
    (A.disj (-A)).subjectMatter = A.subjectMatter := by
  rw [subjectMatter_disj hf hv, subjectMatter_neg, sup_idem]

end CompleteLattice

end BilProp

namespace Canonical

open BilProp

variable {α : Type*}

/-- The possible states of the canonical space are the consistent sets of literals, where
`(a, true)` asserts the atom `a` and `(a, false)` denies it. -/
def possible : LowerSet (Set (α × Bool)) where
  carrier := {L | ∀ a, (a, true) ∈ L → (a, false) ∉ L}
  lower' := by
    intro L K hKL hL a ht hf
    exact hL a (hKL ht) (hKL hf)

theorem mem_possible {L : Set (α × Bool)} :
    L ∈ possible ↔ ∀ a, (a, true) ∈ L → (a, false) ∉ L :=
  Iff.rfl

/-- The atomic proposition `a` is verified by its assertion and falsified by its denial. -/
def atom (a : α) : BilProp (Set (α × Bool)) :=
  ⟨{{(a, true)}}, {{(a, false)}}⟩

theorem exclusive_atom (a : α) : (atom a).Exclusive possible := by
  rintro _ rfl _ rfl h
  exact h a (.inl rfl) (.inr rfl)

theorem exhaustive_atom (a : α) : (atom a).Exhaustive possible := by
  intro L hL
  by_cases hf : (a, false) ∈ L
  · refine .inr ⟨{(a, false)}, rfl, ?_⟩
    rwa [show L ⊔ {(a, false)} = L from Set.union_eq_left.2 (Set.singleton_subset_iff.2 hf)]
  · refine .inl ⟨{(a, true)}, rfl, fun b hb hb' ↦ ?_⟩
    rcases hb' with hb' | hb'
    · rcases hb with hb | hb
      · exact hL b hb hb'
      · obtain rfl := (Prod.mk.inj hb).1
        exact hf hb'
    · exact Bool.false_ne_true (Prod.mk.inj hb').2

theorem subjectMatter_atom (a : α) : (atom a).subjectMatter = {(a, true), (a, false)} := by
  simpa [subjectMatter, atom] using Set.pair_comm _ _

/-- The excluded middle of an atom is true at every world of the canonical space. -/
theorem mem_upperClosure_disj_neg_atom (a : α) {w : Set (α × Bool)}
    (hw : Maximal (· ∈ possible) w) : w ∈ upperClosure ((atom a).disj (-atom a)).ver :=
  (exhaustive_atom a).mem_upperClosure_disj_neg hw

theorem subjectMatter_disj_neg_atom (a : α) :
    ((atom a).disj (-atom a)).subjectMatter = {(a, true), (a, false)} := by
  rw [subjectMatter_disj_neg ⟨_, rfl⟩ ⟨_, rfl⟩, subjectMatter_atom]

/-- The subject-matter of the excluded middle of an atom is an impossible state. -/
theorem subjectMatter_disj_neg_atom_not_mem (a : α) :
    ((atom a).disj (-atom a)).subjectMatter ∉ possible := by
  rw [subjectMatter_disj_neg_atom]
  exact fun h ↦ h a (.inl rfl) (.inr rfl)

/-- Excluded middles of distinct atoms have distinct subject-matters. -/
theorem subjectMatter_disj_neg_atom_injective :
    Function.Injective fun a : α ↦ ((atom a).disj (-atom a)).subjectMatter := by
  intro a b h
  have : (a, true) ∈ ({(b, true), (b, false)} : Set (α × Bool)) := by
    simp only [subjectMatter_disj_neg_atom] at h
    rw [← h]
    exact .inl rfl
  simpa using this

end Canonical

end Truthmaker
