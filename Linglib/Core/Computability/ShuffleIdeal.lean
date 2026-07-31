/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Find
import Mathlib.Order.WellFoundedSet
import Linglib.Core.Computability.StrictlyPiecewise

/-!
# Shuffle ideals and sublist-closed languages

The **shuffle ideal** of a word `w` is its upward closure `{v | w <+ v}` under the subsequence
order: the words that scatter `w` inside themselves. We show that a shuffle ideal is regular,
by computing its left quotients — greedily matching `w` against a prefix leaves a suffix of `w`
still to match, so only `|w| + 1` quotients arise. Over a finite alphabet the subsequence order
is a well-quasi-order (Higman's lemma [higman-1952]), so a downward closed language has finitely
many minimal forbidden words and is therefore the complement of finitely many shuffle ideals;
regularity of such a language is **Haines' theorem**. Combining the two gives the characterisation
of the strictly piecewise languages: `L` is `SP_k` for some `k` exactly when `L` is downward
closed under subsequences [rogers-heinz-et-al-2010].

## Main definitions

* `Language.shuffleIdeal w`: the words containing `w` as a subsequence.
* `Language.IsSublistClosed L`: `L` is downward closed under `<+`.
* `Language.maxMatch w x`: the length of the longest prefix of `w` that `x` already contains.

## Main results

* `Language.isRegular_shuffleIdeal`: shuffle ideals are regular.
* `List.wellQuasiOrdered_sublist`: Higman's lemma for words over a finite alphabet.
* `Language.IsSublistClosed.isRegular`: Haines' theorem.
* `Language.exists_isStrictlyPiecewise_iff_isSublistClosed`: `SP` is exactly sublist-closure.
-/

open List

variable {α : Type*}

/-! ### Higman's lemma for words -/

/-- `List.SublistForall₂` at equality is the subsequence order. -/
theorem List.sublistForall₂_eq_iff {l₁ l₂ : List α} : SublistForall₂ Eq l₁ l₂ ↔ l₁ <+ l₂ := by
  simp [List.sublistForall₂_iff, List.forall₂_eq_eq_eq]

/-- **Higman's lemma** for words [higman-1952]: over a finite alphabet the subsequence order is a
well-quasi-order, so every infinite sequence of words has an earlier term embedding in a later
one. Specialises mathlib's `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` to
equality, where the alphabet is well-quasi-ordered by pigeonhole. -/
theorem List.wellQuasiOrdered_sublist [Finite α] :
    WellQuasiOrdered (fun l₁ l₂ : List α => l₁ <+ l₂) := by
  rw [← Set.partiallyWellOrderedOn_univ_iff, Set.partiallyWellOrderedOn_iff_exists_lt]
  refine fun f _ => ?_
  obtain ⟨m, n, hmn, h⟩ := Set.partiallyWellOrderedOn_iff_exists_lt.mp
    (Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ (Eq : α → α → Prop)
      Set.finite_univ.partiallyWellOrderedOn) f fun _ _ _ => Set.mem_univ _
  exact ⟨m, n, hmn, List.sublistForall₂_eq_iff.mp h⟩

namespace Language

variable {L : Language α}

/-! ### Shuffle ideals -/

/-- The **shuffle ideal** of `w`: the words admitting `w` as a subsequence. -/
def shuffleIdeal (w : List α) : Language α := {v | w <+ v}

@[simp] theorem mem_shuffleIdeal {w v : List α} : v ∈ shuffleIdeal w ↔ w <+ v := Iff.rfl

theorem self_mem_shuffleIdeal (w : List α) : w ∈ shuffleIdeal w := Sublist.refl w

@[simp] theorem shuffleIdeal_nil : shuffleIdeal ([] : List α) = ⊤ :=
  Set.ext fun x => iff_of_true (nil_sublist x) trivial

/-- Shuffle ideals are **antitone**: a longer word is harder to scatter. -/
theorem shuffleIdeal_anti {v w : List α} (h : v <+ w) : shuffleIdeal w ≤ shuffleIdeal v :=
  fun _ hx => h.trans hx

/-! ### Sublist-closed languages -/

/-- A language is **sublist-closed** when deleting symbols never leaves it. -/
def IsSublistClosed (L : Language α) : Prop := ∀ ⦃v w : List α⦄, v <+ w → w ∈ L → v ∈ L

/-- The complement of a sublist-closed language is upward closed: inserting symbols cannot
re-enter it. -/
theorem IsSublistClosed.mem_compl_of_sublist (hL : L.IsSublistClosed) {v w : List α}
    (hvw : v <+ w) (hv : v ∈ Lᶜ) : w ∈ Lᶜ := fun hw => hv (hL hvw hw)

/-- The complement of a shuffle ideal — avoiding `w` as a subsequence — is sublist-closed. -/
theorem isSublistClosed_compl_shuffleIdeal (w : List α) : (shuffleIdeal w)ᶜ.IsSublistClosed :=
  fun _ _ hvw hw hm => hw (hm.trans hvw)

/-- Sublist-closure is preserved by intersection: conjoining constraints keeps them all. -/
theorem IsSublistClosed.inf {M : Language α} (hL : L.IsSublistClosed) (hM : M.IsSublistClosed) :
    (L ⊓ M).IsSublistClosed := fun _ _ hvw hw => ⟨hL hvw hw.1, hM hvw hw.2⟩

/-- Sublist-closure is preserved by arbitrary intersections. -/
theorem isSublistClosed_iInter {ι : Sort*} {L : ι → Language α}
    (h : ∀ i, (L i).IsSublistClosed) : IsSublistClosed (⋂ i, L i) :=
  fun _ _ hvw hw => Set.mem_iInter.mpr fun i => h i hvw (Set.mem_iInter.mp hw i)

/-! ### Greedy matching and regularity -/

section DecidableEq
variable [DecidableEq α]

/-- The length of the longest prefix of `w` that occurs as a subsequence of `x`. Greedy matching
is optimal: consuming this much of `w` against `x` leaves the easiest remaining obligation. -/
def maxMatch (w x : List α) : ℕ := Nat.findGreatest (fun m => w.take m <+ x) w.length

theorem maxMatch_le (w x : List α) : maxMatch w x ≤ w.length := Nat.findGreatest_le _

theorem take_maxMatch_sublist (w x : List α) : w.take (maxMatch w x) <+ x :=
  Nat.findGreatest_spec (P := fun m => w.take m <+ x) (Nat.zero_le _) (by simp)

theorem le_maxMatch {w x : List α} {j : ℕ} (hj : j ≤ w.length) (h : w.take j <+ x) :
    j ≤ maxMatch w x := Nat.le_findGreatest hj h

/-- **Greedy matching is optimal**: `w` scatters into `x ++ v` exactly when the part of `w` left
over after its longest `x`-matchable prefix scatters into `v`. -/
theorem sublist_append_iff_drop_maxMatch (w x v : List α) :
    w <+ x ++ v ↔ w.drop (maxMatch w x) <+ v := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
    have hj : l₁.length ≤ maxMatch (l₁ ++ l₂) x :=
      le_maxMatch (by simp) (by rw [List.take_left]; exact h₁)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    rw [hd, ← List.drop_drop, List.drop_left]
    exact (List.drop_sublist _ _).trans h₂
  · have := (take_maxMatch_sublist w x).append h
    rwa [List.take_append_drop] at this

/-- Reading `x` turns the shuffle ideal of `w` into the shuffle ideal of what is left of `w`. -/
theorem leftQuotient_shuffleIdeal (w x : List α) :
    (shuffleIdeal w).leftQuotient x = shuffleIdeal (w.drop (maxMatch w x)) := by
  ext v; exact sublist_append_iff_drop_maxMatch w x v

/-- A shuffle ideal is **regular**. Its left quotients are the shuffle ideals of the suffixes of
`w`, of which there are at most `|w| + 1`, so Myhill–Nerode applies. -/
theorem isRegular_shuffleIdeal (w : List α) : (shuffleIdeal w).IsRegular := by
  refine isRegular_iff_finite_range_leftQuotient.mpr (Set.Finite.subset
    (Set.finite_range fun j : Fin (w.length + 1) => shuffleIdeal (w.drop j)) ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨maxMatch w x, Nat.lt_succ_of_le (maxMatch_le w x)⟩, (leftQuotient_shuffleIdeal w x).symm⟩

end DecidableEq

/-! ### The finite forbidden basis -/

/-- Every member of a language dominates a `<+`-minimal member: proper subsequences shorten. -/
theorem exists_minimal_sublist (L : Language α) {w : List α} (hw : w ∈ L) :
    ∃ m ∈ L, m <+ w ∧ ∀ v ∈ L, v <+ m → v = m := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases h : ∀ v ∈ L, v <+ w → v = w
    · exact ⟨w, hw, Sublist.refl w, h⟩
    · push Not at h
      obtain ⟨v, hv, hvw, hne⟩ := h
      obtain ⟨m, hm, hmv, hmin⟩ := ih v.length
        (hn ▸ lt_of_le_of_ne hvw.length_le fun hl => hne (hvw.eq_of_length hl)) hv rfl
      exact ⟨m, hm, hmv.trans hvw, hmin⟩

/-- **Finite forbidden basis**: over a finite alphabet a sublist-closed language is avoidance of
finitely many forbidden subsequences. The `<+`-minimal non-members form an antichain, hence are
finite by Higman's lemma, and every non-member contains one. -/
theorem IsSublistClosed.exists_finset_compl_eq [Finite α] (hL : L.IsSublistClosed) :
    ∃ F : Finset (List α), Lᶜ = ⋃ m ∈ F, shuffleIdeal m := by
  have hfin : {m | m ∈ Lᶜ ∧ ∀ v ∈ Lᶜ, v <+ m → v = m}.Finite :=
    IsAntichain.finite_of_partiallyWellOrderedOn (fun _ ha _ hb hne hab => hne (hb.2 _ ha.1 hab))
      (Set.partiallyWellOrderedOn_of_wellQuasiOrdered List.wellQuasiOrdered_sublist _)
  refine ⟨hfin.toFinset, Set.ext fun w => ?_⟩
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq, exists_prop]
  exact ⟨fun hw => (exists_minimal_sublist Lᶜ hw).imp fun _ ⟨hm, hmw, hmin⟩ => ⟨⟨hm, hmin⟩, hmw⟩,
    fun ⟨_, hm, hmw⟩ => hL.mem_compl_of_sublist hmw hm.1⟩

/-! ### Haines' theorem -/

/-- The empty language is regular: a one-state automaton accepting nothing. -/
theorem isRegular_zero : (0 : Language α).IsRegular :=
  ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, rfl⟩

/-- Regular languages are closed under finite unions, by iterating `Language.IsRegular.add`. -/
theorem isRegular_biUnion {ι : Type*} (F : Finset ι) {f : ι → Set (List α)}
    (hf : ∀ i ∈ F, Language.IsRegular (f i)) : Language.IsRegular (⋃ i ∈ F, f i) := by
  classical
  induction F using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]; exact isRegular_zero
  | insert i F hi ih =>
    rw [Finset.set_biUnion_insert, ← Language.add_def]
    exact (hf i (by simp)).add (ih fun j hj => hf j (by simp [hj]))

/-- **Haines' theorem**: over a finite alphabet every sublist-closed language is regular. It is
the complement of the finitely many shuffle ideals of its minimal forbidden subsequences, and
each of those is regular. -/
theorem IsSublistClosed.isRegular [Finite α] [DecidableEq α] (hL : L.IsSublistClosed) :
    L.IsRegular :=
  have ⟨F, hF⟩ := hL.exists_finset_compl_eq
  IsRegular.of_compl (hF ▸ isRegular_biUnion F fun m _ => isRegular_shuffleIdeal m)

/-! ### Strictly piecewise languages are exactly the sublist-closed ones -/

/-- A language is strictly piecewise at some width iff it is sublist-closed
[rogers-heinz-et-al-2010]. Forwards is `IsStrictlyPiecewise.mem_of_sublist`; backwards, take the
grammar to be `L` itself at the width bounding the finite forbidden basis, so that any word
outside `L` is already refuted by a basis word it contains. -/
theorem exists_isStrictlyPiecewise_iff_isSublistClosed [Finite α] :
    (∃ k, L.IsStrictlyPiecewise k) ↔ L.IsSublistClosed := by
  refine ⟨fun ⟨_, hk⟩ _ _ hvw hw => hk.mem_of_sublist hvw hw, fun hL => ?_⟩
  obtain ⟨F, hF⟩ := hL.exists_finset_compl_eq
  refine ⟨F.sup List.length, L, Set.ext fun w => ?_⟩
  refine ⟨fun h => by_contra fun hwL => ?_, fun hw s _ hs => hL hs hw⟩
  obtain ⟨m, hm, hmw⟩ := Set.mem_iUnion₂.mp (hF ▸ hwL : w ∈ ⋃ m ∈ F, shuffleIdeal m)
  exact (hF ▸ Set.mem_biUnion hm (self_mem_shuffleIdeal m) : m ∈ Lᶜ)
    (h m (Finset.le_sup hm) hmw)

end Language
