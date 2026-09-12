import Linglib.Semantics.Quantification.Witness
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Quantification.NumberTree
import Mathlib.Data.Finset.Powerset

/-!
# Lücking and Ginzburg (2022): Referential Transparency as the Proper Treatment for Quantification

This file formalizes the denotations of quantified noun phrases in the referential
transparency theory of [lucking-ginzburg-2022]. In place of the sets of sets of generalized
quantifier theory ([barwise-cooper-1981]), a quantified noun phrase denotes a set of ordered
bipartitions of the head noun's extension into a reference set and its complement (`BP`,
`allBP`), the quantifier word acting as a sieve on them through a descriptive condition on
the two cardinalities (`QCond`, `sieve`). Conservativity holds by construction, only the
restrictor being partitioned (`qcond_conservative`); a verb phrase predicates on the
reference set and anti-predicates on the complement set, which for *every* gives the
classical truth conditions (`every_truth_conditions`); and the quantifier perspective,
whether the bipartition with an empty reference set survives the sieve, is derived from the
denotation and gates anaphora to the complement set (`deriveQPersp`). The paper's minimal
pair: *few* and *a few* share their condition, but *a few* carries a reference individual,
so its denotation lacks the empty-reference bipartition and the complement set is
inaccessible (`few_dog_qpersp`, `aFew_dog_qpersp`). Reference sets are witness sets in the
sense of [barwise-cooper-1981] (`bp_refset_is_witnessSet`), and the denotations over a noun
with `k` instances number `2 ^ (k + 1) - 1`, fewer than the conservative generalized
quantifiers of [van-benthem-1984] (`rttQuantifierCount_lt_conservative`).

## Implementation notes

Conditions are relations on the two cardinalities, quantity-invariant by construction; the
contextual standard of *many* is a parameter and that of *few* is simplified to a strict
comparison. The paper's third perspective value for degenerate denotations collapses into
the non-empty one, which gates anaphora identically. The dialogue and gesture data, the
clarification-request diagnostics, and the type-theoretic encoding are not represented.

## References

* [lucking-ginzburg-2022]
* [barwise-cooper-1981]
* [van-benthem-1984]
-/

namespace LuckingGinzburg2022

open Quantification

variable {α : Type} [DecidableEq α]

/-! ### Ordered set bipartitions -/

/-- An ordered set bipartition (the paper's (15)): a reference set and a complement set,
disjoint with union the head noun's extension; the two conditions are verified extrinsically
so that the type decides. -/
structure BP (α : Type) where
  refset : Finset α
  compset : Finset α
  deriving DecidableEq

/-- The union of the two sets, the head noun's extension. -/
def BP.maxset (b : BP α) : Finset α := b.refset ∪ b.compset

/-- All ordered bipartitions of a set: each subset with its complement. -/
def allBP (S : Finset α) : Finset (BP α) :=
  S.powerset.map ⟨λ R => ⟨R, S \ R⟩, λ a b h => by simp [BP.mk.injEq] at h; exact h.1⟩

theorem allBP_card (S : Finset α) : (allBP S).card = 2 ^ S.card := by
  simp [allBP, Finset.card_map, Finset.card_powerset]

theorem allBP_maxset (S : Finset α) (b : BP α) (h : b ∈ allBP S) : b.maxset = S := by
  simp [allBP, Finset.mem_map] at h
  obtain ⟨R, hR, rfl⟩ := h
  exact Finset.union_sdiff_of_subset hR

theorem allBP_refset_sub (S : Finset α) (b : BP α) (h : b ∈ allBP S) : b.refset ⊆ S := by
  simp [allBP, Finset.mem_map] at h
  obtain ⟨R, hR, rfl⟩ := h
  exact hR

/-! ### Descriptive quantifier conditions -/

/-- A descriptive quantifier condition (§4.2): a relation on the cardinalities of the
reference and complement sets. -/
abbrev QCond := ℕ → ℕ → Prop

/-- The sieve: the bipartitions meeting the condition. -/
def sieve (qc : QCond) [DecidableRel qc] (bps : Finset (BP α)) : Finset (BP α) :=
  bps.filter λ b => qc b.refset.card b.compset.card

/-- *every*: an empty complement set. -/
def every_qcond : QCond := λ _ c => c = 0

/-- *no*: an empty reference set. -/
def no_qcond : QCond := λ r _ => r = 0

/-- *some*: a non-empty reference set. -/
def some_qcond : QCond := λ r _ => 1 ≤ r

/-- *most*: the reference set outnumbers the complement set. -/
def most_qcond : QCond := λ r c => c < r

/-- *few*: the complement set outnumbers the reference set. -/
def few_qcond : QCond := λ r c => r < c

/-- *many* (the paper's (39)): the reference set exceeds a contextual standard. -/
def many_qcond (θ : ℕ) : QCond := λ r _ => θ < r

instance : DecidableRel every_qcond := λ _ c => inferInstanceAs (Decidable (c = 0))
instance : DecidableRel no_qcond := λ r _ => inferInstanceAs (Decidable (r = 0))
instance : DecidableRel some_qcond := λ r _ => inferInstanceAs (Decidable (1 ≤ r))
instance : DecidableRel most_qcond := λ r c => inferInstanceAs (Decidable (c < r))
instance : DecidableRel few_qcond := λ r c => inferInstanceAs (Decidable (r < c))
instance (θ : ℕ) : DecidableRel (many_qcond θ) := λ r _ => inferInstanceAs (Decidable (θ < r))

/-! ### Quantifier perspective -/

/-- The quantifier perspective (the paper's (47)–(48)): whether the bipartition with an
empty reference set belongs to the denotation, in which case the complement set is
accessible to anaphora. -/
inductive QPerspective
  | refsetEmpty
  | refsetNonempty
  deriving DecidableEq, Repr

/-- The perspective derived from a sieved set of bipartitions. -/
def deriveQPersp (bps : Finset (BP α)) : QPerspective :=
  if ∃ b ∈ bps, b.refset = ∅ then .refsetEmpty else .refsetNonempty

/-- The reference individual of *a few* (the paper's (46)) requires a non-empty reference
set. -/
def refindFilter (bps : Finset (BP α)) : Finset (BP α) := bps.filter λ b => b.refset.Nonempty

/-! ### The dogs -/

/-- Three dogs. -/
inductive Dog
  | fido | rex | spot
  deriving DecidableEq, Fintype

/-- The extension of *dog*. -/
def dogs : Finset Dog := Finset.univ

theorem dog_bipartitions_card : (allBP dogs).card = 8 := by decide

/-- *every*: the sole surviving bipartition has all dogs in the reference set. -/
theorem every_dog_qpersp :
    deriveQPersp (sieve every_qcond (allBP dogs)) = .refsetNonempty := by decide

/-- *no*: the sole surviving bipartition has an empty reference set. -/
theorem no_dog_qpersp : deriveQPersp (sieve no_qcond (allBP dogs)) = .refsetEmpty := by decide

theorem some_dog_qpersp :
    deriveQPersp (sieve some_qcond (allBP dogs)) = .refsetNonempty := by decide

theorem most_dog_qpersp :
    deriveQPersp (sieve most_qcond (allBP dogs)) = .refsetNonempty := by decide

/-- *few*: the empty-reference bipartition survives, so the complement set is accessible,
*Few dogs barked. They slept through.* -/
theorem few_dog_qpersp : deriveQPersp (sieve few_qcond (allBP dogs)) = .refsetEmpty := by
  decide

/-- *a few*: the same condition, but the reference individual excludes the empty-reference
bipartition, so the complement set is inaccessible. -/
theorem aFew_dog_qpersp :
    deriveQPersp (refindFilter (sieve few_qcond (allBP dogs))) = .refsetNonempty := by
  decide

/-! ### Witness sets and conservativity -/

/-- Every reference set is a witness set of the head noun. -/
theorem bp_refset_is_witnessSet [Fintype α] (P : α → Prop) [DecidablePred P] (b : BP α)
    (h : b ∈ allBP (fullExtFinset P)) : WitnessSet P b.refset :=
  ⟨λ _ ha => (Finset.mem_filter.mp (allBP_refset_sub _ b h ha)).2⟩

/-- The generalized quantifier of a condition: the verb phrase holds throughout the
reference set of some surviving bipartition. -/
def qcondToGQ (qc : QCond) [DecidableRel qc] [Fintype α] (N : α → Prop) [DecidablePred N]
    (Q : α → Prop) : Prop :=
  ∃ b ∈ allBP (Finset.univ.filter N), qc b.refset.card b.compset.card ∧ ∀ a ∈ b.refset, Q a

/-- Conservativity holds by construction: the reference set lies within the restrictor. -/
theorem qcond_conservative [Fintype α] (qc : QCond) [DecidableRel qc] (N Q : α → Prop)
    [DecidablePred N] : qcondToGQ qc N Q ↔ qcondToGQ qc N λ x => N x ∧ Q x := by
  constructor
  · rintro ⟨b, hmem, hqc, hQ⟩
    exact ⟨b, hmem, hqc, λ a ha =>
      ⟨(Finset.mem_filter.mp (allBP_refset_sub _ b hmem ha)).2, hQ a ha⟩⟩
  · rintro ⟨b, hmem, hqc, hNQ⟩
    exact ⟨b, hmem, hqc, λ a ha => (hNQ a ha).2⟩

/-- The number of denotations over a noun with `k` instances (§4.8): the non-empty sets of
its `2 ^ k` bipartitions. -/
def rttQuantifierCount (k : ℕ) : ℕ := 2 ^ (k + 1) - 1

/-- Fewer denotations than conservative generalized quantifiers, at every size. -/
theorem rttQuantifierCount_lt_conservative (k : ℕ) :
    rttQuantifierCount k < conservativeQuantifierCount k :=
  calc 2 ^ (k + 1) - 1 < 2 ^ (k + 1) := Nat.sub_lt (Nat.two_pow_pos _) one_pos
    _ ≤ 2 ^ ((k + 1) * (k + 2) / 2) := Nat.pow_le_pow_right two_pos
        ((Nat.le_div_iff_mul_le two_pos).mpr (Nat.mul_le_mul_left _ (by omega)))

/-! ### Anti-predication -/

/-- Anti-predication (§4.5): the verb phrase holds of every member of the reference set and
fails of every member of the complement set. -/
def antiPredication (VP : α → Prop) (b : BP α) : Prop :=
  (∀ a ∈ b.refset, VP a) ∧ ∀ a ∈ b.compset, ¬ VP a

/-- *every N VP*: some surviving bipartition is anti-predicated exactly when the verb phrase
holds throughout the extension, the sole survivor having everything in its reference set. -/
theorem every_truth_conditions (S : Finset α) (VP : α → Prop) :
    (∃ b ∈ sieve every_qcond (allBP S), antiPredication VP b) ↔ ∀ a ∈ S, VP a := by
  constructor
  · rintro ⟨b, hb, hanti⟩
    have hmem := (Finset.mem_filter.mp hb).1
    have hqc := (Finset.mem_filter.mp hb).2
    rw [allBP, Finset.mem_map] at hmem
    obtain ⟨R, hR, rfl⟩ := hmem
    rw [Finset.mem_powerset] at hR
    have hcomp : S \ R = ∅ := Finset.card_eq_zero.mp hqc
    intro a haS
    apply hanti.1
    by_contra h
    exact absurd (hcomp ▸ Finset.mem_sdiff.mpr ⟨haS, h⟩) (by simp)
  · intro hall
    refine ⟨⟨S, S \ S⟩, Finset.mem_filter.mpr ⟨?_, ?_⟩, hall, λ _ ha => ?_⟩
    · rw [allBP, Finset.mem_map]
      exact ⟨S, Finset.mem_powerset.mpr (Finset.Subset.refl S), rfl⟩
    · simp [every_qcond]
    · simp at ha

end LuckingGinzburg2022
