/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Nat.Find
import Linglib.Core.Order.WellFoundedSet
import Linglib.Core.Computability.StrictlyPiecewise

/-!
# Shuffle ideals and sublist-closed languages

The **shuffle ideal** of a word `w` is the language `{v | w <+ v}` of words containing `w` as a
subsequence, and a language is **sublist-closed** when it is downward closed under the sublist
order. This file proves that shuffle ideals are regular; that over a finite alphabet a
sublist-closed language is the complement of finitely many shuffle ideals (by Higman's lemma
[higman-1952]) and hence regular (Haines' theorem); and that the sublist-closed languages are
exactly the strictly piecewise ones.

## Main definitions

* `Language.shuffleIdeal w`: the words containing `w` as a subsequence.
* `Language.IsSublistClosed L`: `L` is downward closed under `<+`.
* `List.maxMatch w x`: the length of the longest prefix of `w` occurring as a subsequence of `x`.

## Main results

* `Language.isRegular_shuffleIdeal`: shuffle ideals are regular.
* `Language.IsSublistClosed.exists_finset_compl_eq_biSup_shuffleIdeal`: the finite forbidden
  basis.
* `Language.IsSublistClosed.isRegular`: Haines' theorem.
* `Language.exists_isStrictlyPiecewise_iff_isSublistClosed`: `SP` is exactly sublist-closure.
-/

open List

variable {α : Type*}

/-! ### Minimal sublists and greedy matching -/

namespace List

theorem exists_minimal_sublist {s : Set (List α)} {w : List α} (hw : w ∈ s) :
    ∃ m ∈ s, m <+ w ∧ ∀ v ∈ s, v <+ m → v = m := by
  obtain ⟨m, ⟨hm, hmw⟩, hmin⟩ :=
    (measure List.length).wf.has_min {u | u ∈ s ∧ u <+ w} ⟨w, hw, Sublist.refl w⟩
  exact ⟨m, hm, hmw, fun v hv hvm => hvm.eq_of_length <| le_antisymm hvm.length_le <|
    not_lt.1 fun h => hmin v ⟨hv, hvm.trans hmw⟩ h⟩

variable [DecidableEq α]

/-- The length of the longest prefix of `w` occurring as a subsequence of `x`. -/
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
  · obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := sublist_append_iff.mp h
    have hj : l₁.length ≤ maxMatch (l₁ ++ l₂) x :=
      le_maxMatch (by simp) (by rw [take_left]; exact h₁)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    rw [hd, ← drop_drop, drop_left]
    exact (drop_sublist _ _).trans h₂
  · have := (take_maxMatch_sublist w x).append h
    rwa [take_append_drop] at this

end List

namespace Language

variable {L : Language α}

/-! ### Shuffle ideals -/

/-- The **shuffle ideal** of `w`: the words admitting `w` as a subsequence. -/
def shuffleIdeal (w : List α) : Language α := {v | w <+ v}

@[simp] theorem mem_shuffleIdeal {w v : List α} : v ∈ shuffleIdeal w ↔ w <+ v := Iff.rfl

theorem self_mem_shuffleIdeal (w : List α) : w ∈ shuffleIdeal w := Sublist.refl w

@[simp] theorem shuffleIdeal_nil : shuffleIdeal ([] : List α) = ⊤ :=
  Set.ext fun x => iff_of_true (nil_sublist x) trivial

/-- `shuffleIdeal` carries concatenation to language product; with `shuffleIdeal_nil` this is the
classical description of the shuffle ideal of `a₁ ⋯ aₙ` as `Σ*a₁Σ* ⋯ aₙΣ*`. -/
theorem shuffleIdeal_append (w v : List α) :
    shuffleIdeal (w ++ v) = shuffleIdeal w * shuffleIdeal v := by
  ext x
  simp only [mem_shuffleIdeal, mem_mul, append_sublist_iff]
  constructor
  · rintro ⟨x₁, x₂, rfl, h₁, h₂⟩; exact ⟨x₁, h₁, x₂, h₂, rfl⟩
  · rintro ⟨x₁, h₁, x₂, h₂, rfl⟩; exact ⟨x₁, x₂, rfl, h₁, h₂⟩

theorem shuffleIdeal_le_shuffleIdeal_iff {v w : List α} :
    shuffleIdeal w ≤ shuffleIdeal v ↔ v <+ w :=
  ⟨fun h => h (self_mem_shuffleIdeal w), fun h _ hx => h.trans hx⟩

theorem shuffleIdeal_injective : Function.Injective (shuffleIdeal (α := α)) := fun _ _ h =>
  (shuffleIdeal_le_shuffleIdeal_iff.mp h.ge).antisymm (shuffleIdeal_le_shuffleIdeal_iff.mp h.le)

/-! ### Sublist-closed languages -/

/-- A language is **sublist-closed** when deleting symbols never leaves it. -/
def IsSublistClosed (L : Language α) : Prop := ∀ ⦃v w : List α⦄, v <+ w → w ∈ L → v ∈ L

theorem IsSublistClosed.mem_compl_of_sublist (hL : L.IsSublistClosed) {v w : List α}
    (hvw : v <+ w) (hv : v ∈ Lᶜ) : w ∈ Lᶜ := fun hw => hv (hL hvw hw)

theorem isSublistClosed_compl_shuffleIdeal (w : List α) : (shuffleIdeal w)ᶜ.IsSublistClosed :=
  fun _ _ hvw hw hm => hw (hm.trans hvw)

theorem isSublistClosed_iff_shuffleIdeal_le :
    L.IsSublistClosed ↔ ∀ w ∈ Lᶜ, shuffleIdeal w ≤ Lᶜ :=
  ⟨fun hL _ hw _ hx => hL.mem_compl_of_sublist hx hw,
    fun h _ _ hvw hw => by_contra fun hv => h _ hv hvw hw⟩

theorem isSublistClosed_top : (⊤ : Language α).IsSublistClosed := fun _ _ _ _ => trivial

theorem isSublistClosed_bot : (⊥ : Language α).IsSublistClosed := fun _ _ _ h => h

theorem IsSublistClosed.inf {M : Language α} (hL : L.IsSublistClosed) (hM : M.IsSublistClosed) :
    (L ⊓ M).IsSublistClosed := fun _ _ hvw hw => ⟨hL hvw hw.1, hM hvw hw.2⟩

theorem IsSublistClosed.sup {M : Language α} (hL : L.IsSublistClosed) (hM : M.IsSublistClosed) :
    (L ⊔ M).IsSublistClosed := fun _ _ hvw hw => hw.imp (hL hvw) (hM hvw)

theorem isSublistClosed_iInf {ι : Sort*} {L : ι → Language α}
    (h : ∀ i, (L i).IsSublistClosed) : IsSublistClosed (⨅ i, L i) :=
  fun _ _ hvw hw => Set.mem_iInter.mpr fun i => h i hvw (Set.mem_iInter.mp hw i)

theorem isSublistClosed_iSup {ι : Sort*} {L : ι → Language α}
    (h : ∀ i, (L i).IsSublistClosed) : IsSublistClosed (⨆ i, L i) :=
  fun _ _ hvw hw => Set.mem_iUnion.mpr ((Set.mem_iUnion.mp hw).imp fun i => h i hvw)

/-! ### Regularity of shuffle ideals -/

theorem leftQuotient_shuffleIdeal [DecidableEq α] (w x : List α) :
    (shuffleIdeal w).leftQuotient x = shuffleIdeal (w.drop (w.maxMatch x)) := by
  ext v; exact sublist_append_iff_drop_maxMatch w x v

/-- A shuffle ideal is **regular**: its left quotients are the shuffle ideals of the suffixes of
`w`, of which there are at most `|w| + 1`, so Myhill–Nerode applies. -/
theorem isRegular_shuffleIdeal (w : List α) : (shuffleIdeal w).IsRegular := by
  classical
  refine isRegular_iff_finite_range_leftQuotient.mpr (Set.Finite.subset
    (Set.finite_range fun j : Fin (w.length + 1) => shuffleIdeal (w.drop j)) ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨w.maxMatch x, Nat.lt_succ_of_le (w.maxMatch_le x)⟩, (leftQuotient_shuffleIdeal w x).symm⟩

/-! ### The finite forbidden basis -/

/-- **Finite forbidden basis**: over a finite alphabet a sublist-closed language is avoidance of
finitely many forbidden subsequences. The `<+`-minimal non-members form an antichain, hence are
finite by Higman's lemma, and every non-member contains one. -/
theorem IsSublistClosed.exists_finset_compl_eq_biSup_shuffleIdeal [Finite α]
    (hL : L.IsSublistClosed) : ∃ F : Finset (List α), Lᶜ = ⨆ m ∈ F, shuffleIdeal m := by
  have hfin : {m | m ∈ Lᶜ ∧ ∀ v ∈ Lᶜ, v <+ m → v = m}.Finite :=
    IsAntichain.finite_of_wellQuasiOrdered (fun _ ha _ hb hne hab => hne (hb.2 _ ha.1 hab))
      List.wellQuasiOrdered_sublist
  refine ⟨hfin.toFinset, le_antisymm (fun w hw => ?_) (iSup₂_le fun m hm =>
    isSublistClosed_iff_shuffleIdeal_le.mp hL m (hfin.mem_toFinset.mp hm).1)⟩
  obtain ⟨m, hm, hmw, hmin⟩ := List.exists_minimal_sublist hw
  exact mem_iSup.mpr ⟨m, mem_iSup.mpr ⟨hfin.mem_toFinset.mpr ⟨hm, hmin⟩, hmw⟩⟩

/-! ### Haines' theorem -/

theorem isRegular_bot : (⊥ : Language α).IsRegular :=
  ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, rfl⟩

theorem isRegular_biSup {ι : Type*} (F : Finset ι) {f : ι → Language α}
    (hf : ∀ i ∈ F, (f i).IsRegular) : (⨆ i ∈ F, f i).IsRegular := by
  classical
  induction F using Finset.induction with
  | empty => simpa using isRegular_bot
  | insert i F hi ih =>
    rw [Finset.iSup_insert]
    exact (hf i (by simp)).add (ih fun j hj => hf j (by simp [hj]))

/-- **Haines' theorem**: over a finite alphabet every sublist-closed language is regular. It is
the complement of the finitely many shuffle ideals of its minimal forbidden subsequences, and
each of those is regular. -/
theorem IsSublistClosed.isRegular [Finite α] (hL : L.IsSublistClosed) : L.IsRegular :=
  have ⟨F, hF⟩ := hL.exists_finset_compl_eq_biSup_shuffleIdeal
  IsRegular.of_compl (hF ▸ isRegular_biSup F fun m _ => isRegular_shuffleIdeal m)

/-! ### Strictly piecewise languages are exactly the sublist-closed ones -/

/-- A language is strictly piecewise at some width iff it is sublist-closed. Forwards is
`IsStrictlyPiecewise.mem_of_sublist`; backwards, take the grammar to be `L` itself at the width
bounding the finite forbidden basis, so that any word outside `L` is already refuted by a basis
word it contains. -/
theorem exists_isStrictlyPiecewise_iff_isSublistClosed [Finite α] :
    (∃ k, L.IsStrictlyPiecewise k) ↔ L.IsSublistClosed := by
  refine ⟨fun ⟨_, hk⟩ _ _ hvw hw => hk.mem_of_sublist hvw hw, fun hL => ?_⟩
  obtain ⟨F, hF⟩ := hL.exists_finset_compl_eq_biSup_shuffleIdeal
  have hFmem : ∀ w, w ∈ Lᶜ ↔ ∃ m ∈ F, m <+ w := fun w => by
    rw [show Lᶜ = _ from hF]; simp [Language.mem_iSup]
  refine ⟨F.sup List.length, L, Set.ext fun w => ?_⟩
  refine ⟨fun h => by_contra fun hwL => ?_, fun hw s _ hs => hL hs hw⟩
  obtain ⟨m, hm, hmw⟩ := (hFmem w).mp hwL
  exact (hFmem m).mpr ⟨m, hm, Sublist.refl m⟩ (h m (Finset.le_sup hm) hmw)

end Language
