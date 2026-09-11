/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Linglib.Syntax.Category.Numeral.Composition

/-!
# Ionin and Matushansky (2006): The Composition of Complex Cardinals

This file formalizes the semantics of complex cardinals of [ionin-matushansky-2006]: a simplex
cardinal is a modifier of type ⟨⟨e,t⟩,⟨e,t⟩⟩ that partitions a plurality into as many cells as it
names, each satisfying its complement, (5) and (6) (`cardMod`, `IsPart`), so that *two hundred
books* is iterated complementation and multiplication needs no rule of its own, (9)
(`cardMod_cardMod_atoms`), in agreement with the PHRASE projection rule of [hurford-1975]. The
rival semantic types are ruled out as in Section 2.2: under predicate conjunction *two hundred
books* is contradictory, (12), or satisfied by a hundred books, (13). The countability
presupposition (23), that a cardinal's complement denotes equicardinal pluralities
(`Equicardinal`), is what makes `n` cells of size `k` count `n·k`. Addition is coordination of
xNPs (Section 4): *twenty-two books* is *twenty books and two books* on the split reading (52),
which computes the sum under the full split of (56b) (`coord_card`), while the joint reading
(56a) is contradictory for distinct cardinals.

## Implementation notes

* Pluralities are finite sets and a partition is a `Finset` of nonempty pairwise disjoint cells
  whose union is the plurality, the finite counterpart of `Plurality.Cover.IsPartition`, chosen
  so that cardinalities can be counted.
* The exclusion of overlap in the split reading, which the paper attributes to the Gricean maxim
  of Manner (Section 4.2.1), is a hypothesis of `coord_card`, not derived.

## References

* [ionin-matushansky-2006]
* [hurford-1975]
-/

namespace IoninMatushansky2006

variable {α : Type*} [DecidableEq α]

/-! ### Partitions and the cardinal modifier (5)–(7) -/

/-- (6): `S` is a partition of `x` — nonempty, pairwise-disjoint
cells whose union is `x`. Finset counterpart of
`Plurality.Cover.IsPartition`. -/
def IsPart (S : Finset (Finset α)) (x : Finset α) : Prop :=
  (∀ s ∈ S, s ≠ ∅) ∧ (S : Set (Finset α)).PairwiseDisjoint id ∧
    S.sup id = x

/-- (5): `⟦n⟧ = λP λx. ∃S [Π(S)(x) ∧ |S| = n ∧ ∀s∈S P(s)]` — the
cardinal as an ⟨⟨e,t⟩,⟨e,t⟩⟩ modifier. -/
def cardMod (n : ℕ) (P : Finset α → Prop) (x : Finset α) : Prop :=
  ∃ S : Finset (Finset α), IsPart S x ∧ S.card = n ∧ ∀ s ∈ S, P s

/-- The atomic complement: singleton pluralities of `P`-individuals —
what §3.1 atomicity requirement makes the lexical xNP denote. -/
def IsAtomOf (P : α → Prop) (s : Finset α) : Prop :=
  ∃ a, P a ∧ s = {a}

/-- (23) countability presupposition: all pluralities in the
complement's denotation have the same cardinality. -/
def Equicardinal (P : Finset α → Prop) (k : ℕ) : Prop :=
  ∀ s, P s → s.card = k

omit [DecidableEq α] in
theorem equicardinal_atoms (P : α → Prop) : Equicardinal (IsAtomOf P) 1 :=
  λ _ ⟨_, _, hs⟩ => hs ▸ Finset.card_singleton _

/-- **Keystone**: `n` cells of uniform size `k` make a plurality of
`n·k` — the definedness cascade (23) presupposition feeds. -/
theorem card_of_cardMod {P : Finset α → Prop} {k n : ℕ} {x : Finset α}
    (hP : Equicardinal P k) (h : cardMod n P x) : x.card = n * k := by
  obtain ⟨S, ⟨-, hdisj, hsup⟩, hcard, hall⟩ := h
  rw [← hsup, Finset.sup_eq_biUnion, Finset.card_biUnion (by
    exact λ s hs t ht hst => hdisj hs ht hst)]
  simp only [id_eq]
  rw [Finset.sum_const_nat λ s hs => hP s (hall s hs), hcard]

/-! ### Simple and iterated modification (8)–(9) -/

/-- Partition into singletons: the canonical witness for atomic
complements. -/
private theorem cardMod_atoms_of {P : α → Prop} {x : Finset α}
    (hx : ∀ a ∈ x, P a) : cardMod x.card (IsAtomOf P) x := by
  refine ⟨x.image ({·}), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp +contextual [Finset.eq_empty_iff_forall_notMem]
  · intro s hs t ht hst
    simp only [Finset.coe_image, Set.mem_image] at hs ht
    obtain ⟨a, -, rfl⟩ := hs; obtain ⟨b, -, rfl⟩ := ht
    exact Finset.disjoint_singleton.mpr λ hab => hst (by rw [hab])
  · ext a
    simp
  · rw [Finset.card_image_of_injective _ λ a b => by simp]
  · simp only [Finset.mem_image]
    rintro s ⟨a, ha, rfl⟩
    exact ⟨a, hx a ha, rfl⟩

/-- (8): *hundred books* denotes the 100-atom pluralities of
books — `cardMod` over an atomic complement counts atoms. -/
theorem cardMod_atoms_iff (n : ℕ) (P : α → Prop) (x : Finset α) :
    cardMod n (IsAtomOf P) x ↔ x.card = n ∧ ∀ a ∈ x, P a := by
  constructor
  · intro h
    have hcard := card_of_cardMod (equicardinal_atoms P) h
    obtain ⟨S, ⟨-, -, hsup⟩, -, hall⟩ := h
    refine ⟨by omega, λ a ha => ?_⟩
    rw [← hsup, Finset.mem_sup] at ha
    obtain ⟨s, hs, has⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hall s hs
    obtain rfl := Finset.mem_singleton.mp has
    exact hb
  · rintro ⟨rfl, hx⟩
    exact cardMod_atoms_of hx

/-- Partitions into `n` uniform cells of size `k ≥ 1` exist whenever the
cardinality is right — the constructive half of iterated modification. -/
private theorem cardMod_of_card {P : Finset α → Prop} {k : ℕ} (hk : 1 ≤ k) :
    ∀ (n : ℕ) (x : Finset α), (∀ y ⊆ x, y.card = k → P y) →
      x.card = n * k → cardMod n P x := by
  intro n
  induction n with
  | zero =>
    intro x _ hx
    rw [Nat.zero_mul, Finset.card_eq_zero] at hx
    exact ⟨∅, ⟨by simp, by simp, by simp [hx]⟩, rfl, by simp⟩
  | succ n ih =>
    intro x hsub hx
    obtain ⟨t, htx, ht⟩ : ∃ t ⊆ x, t.card = k :=
      Finset.exists_subset_card_eq
        (by rw [hx]; exact Nat.le_mul_of_pos_left k n.succ_pos)
    obtain ⟨S, ⟨hne, hdisj, hsup⟩, hcard, hall⟩ :=
      ih (x \ t) (λ y hy => hsub y (hy.trans Finset.sdiff_subset))
        (by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr htx, hx, ht,
          Nat.succ_mul]; omega)
    have htS : t ∉ S := λ h => by
      have hsub' := Finset.sup_le_iff.mp hsup.le t h
      have hte : t = ∅ := Finset.eq_empty_of_forall_notMem λ a ha =>
        (Finset.mem_sdiff.mp (hsub' ha)).2 ha
      rw [hte, Finset.card_empty] at ht
      omega
    refine ⟨insert t S, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact λ h => by simp [h] at ht; omega
      · exact hne s hs
    · intro s hs u hu hsu
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hs hu
      have hcell : ∀ v ∈ S, Disjoint t v := λ v hv => by
        have hvsub := Finset.sup_le_iff.mp hsup.le v hv
        exact Finset.disjoint_left.mpr λ a hat hav =>
          (Finset.mem_sdiff.mp (hvsub hav)).2 hat
      rcases hs with rfl | hs <;> rcases hu with rfl | hu
      · exact absurd rfl hsu
      · exact hcell u hu
      · exact (hcell s hs).symm
      · exact hdisj hs hu hsu
    · rw [Finset.sup_insert, hsup]
      simpa [Finset.union_comm] using Finset.sdiff_union_of_subset htx
    · rw [Finset.card_insert_of_notMem htS, hcard]
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hsub s htx ht
      · exact hall s hs

/-- **(9): iterated modification multiplies.** *two hundred books*
= `⟦two⟧(⟦hundred⟧(⟦books⟧))` denotes the `2 × 100`-atom pluralities —
complex cardinals need no semantic rule beyond ordinary composition. -/
theorem cardMod_cardMod_atoms {m : ℕ} (hm : 1 ≤ m) (n : ℕ) (P : α → Prop)
    (x : Finset α) :
    cardMod n (cardMod m (IsAtomOf P)) x ↔ x.card = n * m ∧ ∀ a ∈ x, P a := by
  constructor
  · intro h
    have hEq : Equicardinal (cardMod m (IsAtomOf P) : Finset α → Prop) m :=
      λ s hs => ((cardMod_atoms_iff m P s).mp hs).1
    refine ⟨card_of_cardMod hEq h, λ a ha => ?_⟩
    obtain ⟨S, ⟨-, -, hsup⟩, -, hall⟩ := h
    rw [← hsup, Finset.mem_sup] at ha
    obtain ⟨s, hs, has⟩ := ha
    exact ((cardMod_atoms_iff m P s).mp (hall s hs)).2 a has
  · rintro ⟨hcard, hx⟩
    refine cardMod_of_card hm n x (λ y hyx hyc => ?_) hcard
    exact (cardMod_atoms_iff m P y).mpr ⟨hyc, λ a ha => hx a (hyx ha)⟩

/-- Iterated modification computes [hurford-1975]'s PHRASE projection
rule: `⟦[n m] books⟧` counts `(Phrase.mk n m).value` atoms. -/
theorem iterated_matches_phrase (n : Syntax.Numeral.Number)
    (m : Syntax.Numeral.M) (P : α → Prop) (x : Finset α) :
    cardMod n.value (cardMod m.value (IsAtomOf P)) x ↔
      x.card = (Syntax.Numeral.Phrase.mk n m).value ∧ ∀ a ∈ x, P a :=
  cardMod_cardMod_atoms m.value_pos n.value P x

/-! ### Ruling out the predicate theory (§2.2, (12)–(13)) -/

private theorem isPart_of {S : Finset (Finset α)} {x : Finset α}
    (h1 : ∀ s ∈ S, s ≠ ∅) (h2 : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t)
    (h3 : S.sup id = x) : IsPart S x :=
  ⟨h1, λ s hs t ht hst =>
    h2 s (Finset.mem_coe.mp hs) t (Finset.mem_coe.mp ht) hst, h3⟩

omit [DecidableEq α] in
/-- (12): under bare predicate conjunction *two hundred books* is
self-contradictory — nothing has cardinality 2 and 100 at once. -/
theorem predicate_conjunction_contradictory (x : Finset α) :
    ¬ (x.card = 2 ∧ x.card = 100) := by omega

/-- (13), scaled to *two four*: with partition-based predicate
meanings *conjoined* instead of composed, a plurality of just 4 satisfies
both conjuncts — where the modifier reading demands 2 × 4 = 8. -/
theorem predicate_theory_undershoots :
    ∃ x : Finset (Fin 4),
      cardMod 2 (λ _ => True) x ∧ cardMod 4 (λ _ => True) x ∧
        x.card = 4 :=
  ⟨Finset.univ,
    ⟨{{0, 1}, {2, 3}}, isPart_of (by decide) (by decide) (by decide),
      by decide, λ _ _ => trivial⟩,
    ⟨{{0}, {1}, {2}, {3}}, isPart_of (by decide) (by decide) (by decide),
      by decide, λ _ _ => trivial⟩,
    by decide⟩

/-! ### Addition as coordination (§4, (52)) -/

/-- (52): coordinated xNPs split the plurality —
`⟦A and B⟧ = λx. ∃y z [x = y⊕z ∧ A(y) ∧ B(z)]`. -/
def coordSem (A B : Finset α → Prop) (x : Finset α) : Prop :=
  ∃ y z, x = y ∪ z ∧ A y ∧ B z

/-- Under the full split (the paper's (56b); overlap excluded pragmatically by
Gricean manner, §4.2.1), coordination computes addition:
*twenty-two books* counts 20 + 2 atoms. -/
theorem coord_card {P : α → Prop} {n m : ℕ} {x : Finset α}
    (h : ∃ y z, Disjoint y z ∧ x = y ∪ z ∧
      cardMod n (IsAtomOf P) y ∧ cardMod m (IsAtomOf P) z) :
    x.card = n + m ∧ ∀ a ∈ x, P a := by
  obtain ⟨y, z, hd, rfl, hy, hz⟩ := h
  obtain ⟨hyc, hyP⟩ := (cardMod_atoms_iff n P y).mp hy
  obtain ⟨hzc, hzP⟩ := (cardMod_atoms_iff m P z).mp hz
  refine ⟨by rw [Finset.card_union_of_disjoint hd, hyc, hzc], λ a ha => ?_⟩
  rcases Finset.mem_union.mp ha with h | h
  exacts [hyP a h, hzP a h]

/-- (56a): the joint reading is semantically impossible for
distinct cardinals — no plurality is 20 atoms and 2 atoms at once. -/
theorem no_joint_reading {P : α → Prop} {n m : ℕ} (hnm : n ≠ m)
    (x : Finset α) :
    ¬ (cardMod n (IsAtomOf P) x ∧ cardMod m (IsAtomOf P) x) := by
  rintro ⟨hn, hm⟩
  have h1 := ((cardMod_atoms_iff n P x).mp hn).1
  have h2 := ((cardMod_atoms_iff m P x).mp hm).1
  omega

end IoninMatushansky2006
