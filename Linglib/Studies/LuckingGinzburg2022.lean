module

public import Linglib.Semantics.Quantification.Witness
public import Linglib.Semantics.Quantification.NP
public import Linglib.Semantics.Quantification.NumberTree
public import Mathlib.Data.Finset.Powerset

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
inaccessible (`few_dog_qpersp`, `aFew_dog_qpersp`). Read as a generalized quantifier
(`qcondToGQ`), a condition lives on the head noun, and the reference set of every surviving
bipartition is a witness set of that quantifier in the sense of [barwise-cooper-1981]
(`bp_refset_is_witness`). The denotations over a noun with `k`
instances number `2 ^ (k + 1) - 1`, fewer than the conservative generalized quantifiers of
[van-benthem-1984] (`rttQuantifierCount_lt_conservative`).

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

@[expose] public section

namespace LuckingGinzburg2022

open Quantifier Quantifier.GQ Quantifier.NP

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
  S.powerset.map ⟨fun R ↦ ⟨R, S \ R⟩, fun a b h ↦ by simp [BP.mk.injEq] at h; exact h.1⟩

/-- A set of `k` elements has `2 ^ k` ordered bipartitions. -/
theorem allBP_card (S : Finset α) : (allBP S).card = 2 ^ S.card := by
  simp [allBP, Finset.card_map, Finset.card_powerset]

/-- The two sets of a bipartition of `S` make up `S`. -/
theorem allBP_maxset (S : Finset α) (b : BP α) (h : b ∈ allBP S) : b.maxset = S := by
  simp [allBP, Finset.mem_map] at h
  obtain ⟨R, hR, rfl⟩ := h
  exact Finset.union_sdiff_of_subset hR

/-- The reference set of a bipartition of `S` lies within `S`. -/
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
  bps.filter fun b ↦ qc b.refset.card b.compset.card

/-- *every*: an empty complement set. -/
def every_qcond : QCond := fun _ c ↦ c = 0

/-- *no*: an empty reference set. -/
def no_qcond : QCond := fun r _ ↦ r = 0

/-- *some*: a non-empty reference set. -/
def some_qcond : QCond := fun r _ ↦ 1 ≤ r

/-- *most*: the reference set outnumbers the complement set. -/
def most_qcond : QCond := fun r c ↦ c < r

/-- *few*: the complement set outnumbers the reference set. -/
def few_qcond : QCond := fun r c ↦ r < c

/-- *many* (the paper's (39)): the reference set exceeds a contextual standard. -/
def many_qcond (θ : ℕ) : QCond := fun r _ ↦ θ < r

instance : DecidableRel every_qcond := fun _ c ↦ inferInstanceAs (Decidable (c = 0))
instance : DecidableRel no_qcond := fun r _ ↦ inferInstanceAs (Decidable (r = 0))
instance : DecidableRel some_qcond := fun r _ ↦ inferInstanceAs (Decidable (1 ≤ r))
instance : DecidableRel most_qcond := fun r c ↦ inferInstanceAs (Decidable (c < r))
instance : DecidableRel few_qcond := fun r c ↦ inferInstanceAs (Decidable (r < c))
instance (θ : ℕ) : DecidableRel (many_qcond θ) := fun r _ ↦ inferInstanceAs (Decidable (θ < r))

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
def refindFilter (bps : Finset (BP α)) : Finset (BP α) := bps.filter fun b ↦ b.refset.Nonempty

/-! ### The dogs -/

/-- Three dogs. -/
inductive Dog
  | fido | rex | spot
  deriving DecidableEq, Fintype

/-- The extension of *dog*. -/
def dogs : Finset Dog := Finset.univ

/-- Three dogs have eight ordered bipartitions. -/
theorem dog_bipartitions_card : (allBP dogs).card = 8 := by decide

/-- *every*: the sole surviving bipartition has all dogs in the reference set. -/
theorem every_dog_qpersp :
    deriveQPersp (sieve every_qcond (allBP dogs)) = .refsetNonempty := by decide

/-- *no*: the sole surviving bipartition has an empty reference set. -/
theorem no_dog_qpersp : deriveQPersp (sieve no_qcond (allBP dogs)) = .refsetEmpty := by decide

/-- *some*: every surviving bipartition has a non-empty reference set. -/
theorem some_dog_qpersp :
    deriveQPersp (sieve some_qcond (allBP dogs)) = .refsetNonempty := by decide

/-- *most*: every surviving bipartition has a non-empty reference set. -/
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

/-- The generalized quantifier of a condition: the verb phrase holds throughout the
reference set of some surviving bipartition. -/
def qcondToGQ (qc : QCond) [DecidableRel qc] [Fintype α] (N : α → Prop) [DecidablePred N] :
    NP α :=
  fun Q ↦ ∃ b ∈ sieve qc (allBP {x | N x}), ∀ a ∈ b.refset, Q a

/-- The reference set of a surviving bipartition lies within the head noun. -/
theorem refset_sub_of_mem_sieve [Fintype α] {qc : QCond} [DecidableRel qc] {N : α → Prop}
    [DecidablePred N] {b : BP α} (h : b ∈ sieve qc (allBP {x | N x})) {a : α}
    (ha : a ∈ b.refset) : N a :=
  (Finset.mem_filter.1 (allBP_refset_sub _ b (Finset.mem_filter.1 h).1 ha)).2

/-- Conservativity holds by construction: the quantifier lives on the head noun, since the
reference set lies within it. -/
theorem qcond_conservative [Fintype α] (qc : QCond) [DecidableRel qc] (N : α → Prop)
    [DecidablePred N] : LivesOn (qcondToGQ qc N) N := fun _ ↦
  ⟨fun ⟨b, hb, hQ⟩ ↦ ⟨b, hb, fun _ ha ↦ ⟨refset_sub_of_mem_sieve hb ha, hQ _ ha⟩⟩,
    fun ⟨b, hb, hNQ⟩ ↦ ⟨b, hb, fun _ ha ↦ (hNQ _ ha).2⟩⟩

/-- The reference set of a surviving bipartition is a witness set of the quantifier: it lies
within the head noun, and the quantifier holds of it, the bipartition itself verifying it. -/
theorem bp_refset_is_witness [Fintype α] (qc : QCond) [DecidableRel qc] (N : α → Prop)
    [DecidablePred N] {b : BP α} (h : b ∈ sieve qc (allBP {x | N x})) :
    Witness (qcondToGQ qc N) N (· ∈ b.refset) :=
  ⟨fun _ ↦ refset_sub_of_mem_sieve h, b, h, fun _ ↦ id⟩

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
    refine ⟨⟨S, S \ S⟩, Finset.mem_filter.mpr ⟨?_, ?_⟩, hall, fun _ ha ↦ ?_⟩
    · rw [allBP, Finset.mem_map]
      exact ⟨S, Finset.mem_powerset.mpr (Finset.Subset.refl S), rfl⟩
    · simp [every_qcond]
    · simp at ha

end LuckingGinzburg2022
