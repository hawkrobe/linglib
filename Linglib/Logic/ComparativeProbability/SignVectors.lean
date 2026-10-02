module

public import Linglib.Logic.ComparativeProbability.Scott
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Anti-dominating pairs among balanced comparisons on four atoms

A comparison on four atoms is a sign vector `v : Fin 4 → SignType`, with positive side
`posSupport v` and negative side `negSupport v`. Two comparisons are *mergeable* when no atom
carries the same nonzero sign in both, and they *anti-dominate* each other when the positive side
of each lies in the negative side of the other. A family of at most five pairwise non-mergeable
comparisons with nonempty positive sides, balanced by strictly positive rational weights, contains
an anti-dominating pair. This is the finite combinatorial core of cancellation on `Fin 4`.

## Main declarations

* `ComparativeProbability.Mergeable`: no atom carries the same nonzero sign in both comparisons.
* `ComparativeProbability.exists_antidominating_pair`: the anti-domination theorem.

## Implementation notes

Sizes 1–3 fall to coefficient arithmetic.  For sizes 4–5: full-support
families are forced into 2-element positive supports by the `𝟙`-functional and
die by a pigeonhole on the three complementary pairs of 2-subsets; families
with a zero coordinate die through the *s-shape chain*, in which a singleton-positive
weight-3 member forces a cascade closing into a 3-cycle whose Stiemke witness
is nonnegative on every admissible sign pattern and positive somewhere,
contradicting balance.  The arity is hardcoded because the pigeonhole and
`decide` steps are `Fin 4`-specific.  The counting steps read the supports as the finsets
`pos v` and `neg v`, and the hypotheses are threaded flat through private lemmas.
-/

@[expose] public section

namespace ComparativeProbability

open Finset

/-- Two comparisons are mergeable when no atom carries the same nonzero sign in both. -/
def Mergeable {W : Type*} (v w : W → SignType) : Prop :=
  Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)

theorem Mergeable.symm {W : Type*} {v w : W → SignType} (h : Mergeable v w) : Mergeable w v :=
  ⟨h.1.symm, h.2.symm⟩

variable {S : Finset (Fin 4 → SignType)} {d : (Fin 4 → SignType) → ℚ}

/-- A non-mergeable pair shares a same-sign coordinate. -/
private lemma exists_eq_of_not_mergeable {v w : Fin 4 → SignType} (h : ¬Mergeable v w) :
    ∃ j, (v j = 1 ∧ w j = 1) ∨ (v j = -1 ∧ w j = -1) := by
  rw [Mergeable, not_and_or, Set.not_disjoint_iff, Set.not_disjoint_iff] at h
  rcases h with ⟨j, hv, hw⟩ | ⟨j, hv, hw⟩
  exacts [⟨j, .inl ⟨hv, hw⟩⟩, ⟨j, .inr ⟨hv, hw⟩⟩]

/-! ### Sizes 1 and 2 are impossible -/

private lemma core_card_one (hd : ∀ v ∈ S, 0 < d v) (hbal : ∀ i, ∑ v ∈ S, d v * (v i : ℚ) = 0)
    (hposne : ∀ v ∈ S, ∃ i, v i = 1) (h1 : #S = 1) : False := by
  obtain ⟨v, rfl⟩ := card_eq_one.1 h1
  obtain ⟨i, hi⟩ := hposne v (mem_singleton_self v)
  simpa [hi, (hd v (mem_singleton_self v)).ne'] using hbal i

private lemma core_card_two (hd : ∀ v ∈ S, 0 < d v) (hbal : ∀ i, ∑ v ∈ S, d v * (v i : ℚ) = 0)
    (hmerge : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Mergeable v w) (h2 : #S = 2) : False := by
  obtain ⟨v, w, hvw, rfl⟩ := card_eq_two.1 h2
  have hv : v ∈ ({v, w} : Finset _) := by simp
  have hw : w ∈ ({v, w} : Finset _) := by simp
  -- a shared nonzero sign makes the balance at that coordinate a sum of two positive terms
  refine hmerge v hv w hw hvw ⟨Set.disjoint_left.2 fun i hvi hwi ↦ ?_,
    Set.disjoint_left.2 fun i hvi hwi ↦ ?_⟩ <;>
  · have h := hbal i
    rw [sum_pair hvw, show v i = _ from hvi, show w i = _ from hwi] at h
    norm_num at h
    linarith [hd v hv, hd w hw]

/-! ### Weight-4 dichotomy, sharing, and the size-3 case -/

/-- A full-support pair with disjoint positive supports anti-dominates. -/
private lemma antidominating_of_ne_zero {v w : Fin 4 → SignType} (hv : ∀ i, v i ≠ 0)
    (hw : ∀ i, w i ≠ 0) (hdisj : Disjoint (posSupport v) (posSupport w)) :
    posSupport v ⊆ negSupport w ∧ posSupport w ⊆ negSupport v := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · rcases (w i).trichotomy with h | h | h
    exacts [h, absurd h (hw i), absurd h (Set.disjoint_left.1 hdisj hi)]
  · rcases (v i).trichotomy with h | h | h
    exacts [h, absurd h (hv i), absurd hi (Set.disjoint_left.1 hdisj h)]

/-- When two of three members share a same-sign coordinate, balance there forces the third
member's weight to be the sum of theirs. -/
private lemma trio_eq {a b c : SignType} {da db dc : ℚ} (hda : 0 < da) (hdb : 0 < db)
    (hdc : 0 < dc) (hshare : (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1))
    (hbal : da * a + db * b + dc * c = 0) : dc = da + db := by
  rcases hshare with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases c.trichotomy with rfl | rfl | rfl <;>
    norm_num at hbal <;> linarith

private lemma core_card_three (hd : ∀ v ∈ S, 0 < d v)
    (hbal : ∀ i, ∑ v ∈ S, d v * (v i : ℚ) = 0)
    (hmerge : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Mergeable v w) (h3 : #S = 3) : False := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.1 h3
  have ha : a ∈ ({a, b, c} : Finset _) := by simp
  have hb : b ∈ ({a, b, c} : Finset _) := by simp
  have hc : c ∈ ({a, b, c} : Finset _) := by simp
  have hbal' (i) : d a * (a i : ℚ) + d b * b i + d c * c i = 0 := by
    have h := hbal i
    rw [sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton] at h
    linarith
  obtain ⟨j₁, hsh₁⟩ := exists_eq_of_not_mergeable (hmerge a ha b hb hab)
  have e1 := trio_eq (hd a ha) (hd b hb) (hd c hc) hsh₁ (hbal' j₁)
  obtain ⟨j₂, hsh₂⟩ := exists_eq_of_not_mergeable (hmerge a ha c hc hac)
  have e2 := trio_eq (c := b j₂) (hd a ha) (hd c hc) (hd b hb) hsh₂ (by linarith [hbal' j₂])
  linarith [hd a ha]

/-! ### Members have at most one zero coordinate -/

/-- `ip u w` pairs a rational functional `u` with a comparison `w`. -/
private def ip (u : Fin 4 → ℚ) (w : Fin 4 → SignType) : ℚ := ∑ i, u i * w i

/-- Every functional sums to zero against a balanced family. -/
private lemma ip_functional (hbal : ∀ i, ∑ v ∈ S, d v * (v i : ℚ) = 0) (u : Fin 4 → ℚ) :
    ∑ w ∈ S, d w * ip u w = 0 := by
  calc ∑ w ∈ S, d w * ip u w = ∑ i, u i * ∑ w ∈ S, d w * w i := by
        simp only [ip, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun i _ ↦ sum_congr rfl fun w _ ↦ by ring
    _ = 0 := by simp [hbal]

/-- `pos w` is the finset of positive coordinates of `w`. -/
private def pos (w : Fin 4 → SignType) : Finset (Fin 4) := {i | w i = 1}

/-- `neg w` is the finset of negative coordinates of `w`. -/
private def neg (w : Fin 4 → SignType) : Finset (Fin 4) := {i | w i = -1}

@[simp] private lemma mem_pos {w : Fin 4 → SignType} {i : Fin 4} : i ∈ pos w ↔ w i = 1 := by
  simp [pos]

@[simp] private lemma mem_neg {w : Fin 4 → SignType} {i : Fin 4} : i ∈ neg w ↔ w i = -1 := by
  simp [neg]

private lemma coe_pos (w : Fin 4 → SignType) : (pos w : Set (Fin 4)) = posSupport w := by
  ext; simp

private lemma disjoint_pos_neg (w : Fin 4 → SignType) : Disjoint (pos w) (neg w) :=
  disjoint_filter.2 fun i _ h1 h2 ↦ by simp [h1] at h2

/-- The `𝟙`-functional of a comparison counts positives minus negatives. -/
private lemma ip_one_eq (w : Fin 4 → SignType) : ip 1 w = #(pos w) - #(neg w) := by
  have key (a : SignType) : (a : ℚ) = (if a = 1 then 1 else 0) - (if a = -1 then 1 else 0) := by
    rcases a.trichotomy with rfl | rfl | rfl <;> norm_num
  simp only [ip, Pi.one_apply, one_mul, pos, neg, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ ↦ key (w i)

/-- A comparison has at most four signed coordinates. -/
private lemma card_pos_add_card_neg_le (w : Fin 4 → SignType) : #(pos w) + #(neg w) ≤ 4 := by
  rw [← card_union_of_disjoint (disjoint_pos_neg w)]
  exact (card_le_univ _).trans_eq (Fintype.card_fin 4)

/-- No member of a balanced non-mergeable family has two zero coordinates. -/
private lemma at_most_one_zero (hd : ∀ v ∈ S, 0 < d v)
    (hbal : ∀ i, ∑ v ∈ S, d v * (v i : ℚ) = 0) (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hmerge : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Mergeable v w)
    {v : Fin 4 → SignType} (hvS : v ∈ S) {i₁ i₂ : Fin 4} (hne : i₁ ≠ i₂)
    (hz1 : v i₁ = 0) (hz2 : v i₂ = 0) : False := by
  set supp : Finset (Fin 4) := {i | v i ≠ 0} with hsupp
  have hsupp_card : #supp ≤ 2 := by
    have hsub : supp ⊆ univ \ {i₁, i₂} := fun i hi ↦ by
      simp only [hsupp, mem_filter, mem_univ, true_and] at hi
      simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and]
      rintro (rfl | rfl) <;> contradiction
    calc #supp ≤ #(univ \ {i₁, i₂}) := card_le_card hsub
      _ = 2 := by rw [card_univ_sdiff, card_pair hne, Fintype.card_fin]
  set u : Fin 4 → ℚ := fun i ↦ v i with hu
  -- `ip u v ≥ 1`
  have hvv : 1 ≤ ip u v := by
    obtain ⟨k, hk⟩ := hposne v hvS
    calc (1 : ℚ) = u k * v k := by simp [hu, hk]
      _ ≤ ∑ i, u i * v i := single_le_sum (fun i _ ↦ mul_self_nonneg (u i)) (mem_univ k)
  -- `ip u w ≥ 0` for every other member
  have hge : ∀ w ∈ S, w ≠ v → 0 ≤ ip u w := by
    intro w hwS hwv
    obtain ⟨j, hsh⟩ := exists_eq_of_not_mergeable (hmerge v hvS w hwS (Ne.symm hwv))
    have hjsupp : j ∈ supp := by
      rcases hsh with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [hsupp, h1]
    have hjterm : u j * w j = 1 := by
      rcases hsh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [hu, h1, h2]
    have hip_supp : ip u w = ∑ i ∈ supp, u i * w i := by
      refine (sum_filter_of_ne fun i _ hne0 ↦ ?_).symm
      intro h0
      exact hne0 (by simp [hu, h0])
    have hbound : ∀ i ∈ supp.erase j, -1 ≤ u i * w i := fun i _ ↦ by
      rcases (v i).trichotomy with h | h | h <;> rcases (w i).trichotomy with h' | h' | h' <;>
        simp [hu, h, h']
    have hcard_erase : #(supp.erase j) ≤ 1 := by
      rw [card_erase_of_mem hjsupp]; omega
    have hsum_erase : -1 ≤ ∑ i ∈ supp.erase j, u i * w i :=
      calc (-1 : ℚ) ≤ #(supp.erase j) • (-1 : ℚ) := by
            have : (#(supp.erase j) : ℚ) ≤ 1 := by exact_mod_cast hcard_erase
            simp only [nsmul_eq_mul]; linarith
        _ ≤ ∑ i ∈ supp.erase j, u i * w i := card_nsmul_le_sum _ _ _ hbound
    rw [hip_supp, ← add_sum_erase _ _ hjsupp, hjterm]
    linarith
  -- the balance functional `u` is strictly positive on the family
  have hpos : 0 < ∑ w ∈ S, d w * ip u w := by
    refine sum_pos' (fun w hwS ↦ ?_) ⟨v, hvS, mul_pos (hd v hvS) (by linarith)⟩
    rcases eq_or_ne w v with rfl | hwv
    · exact mul_nonneg (hd w hwS).le (by linarith)
    · exact mul_nonneg (hd w hwS).le (hge w hwS hwv)
  exact hpos.ne' (ip_functional hbal u)

/-! ### The weight-3 singleton-positive kill

A singleton-positive weight-3 member `x` (one `+1`, one `0`, two `-1`s) forces,
via the functional `w ↦ w p + w ζ`, an *s-shape* companion `y₁` (zero at `x`'s
positive coordinate, `-1` at `x`'s zero); `y₁` is again singleton-positive
weight-3, so the forcing iterates.  Pairwise admissibility kills one branch of
the second iterate, pinning the 3-cycle `x, y₁, y₂`, whose Stiemke witness
`w ↦ w p + w i + w ζ - w j` is nonnegative on every admissible sign pattern
and positive at `x`, contradicting balance. -/

private lemma fin4_exhaust : ∀ p ζ i j k : Fin 4, p ≠ ζ → i ≠ p → i ≠ ζ →
    j ≠ p → j ≠ ζ → i ≠ j → k = p ∨ k = ζ ∨ k = i ∨ k = j := by
  decide

private lemma exists_fourth : ∀ p ζ i : Fin 4, p ≠ ζ → i ≠ p → i ≠ ζ →
    ∃ j, j ≠ p ∧ j ≠ ζ ∧ j ≠ i := by
  decide

private lemma posSupport_eq_singleton {x : Fin 4 → SignType} {p ζ : Fin 4}
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    posSupport x = {p} := by
  ext k
  simp only [mem_posSupport, Set.mem_singleton_iff]
  refine ⟨fun hk ↦ by_contra fun hkp ↦ ?_, by rintro rfl; exact hxp⟩
  rcases eq_or_ne k ζ with rfl | hkζ
  · simp [hxζ] at hk
  · simp [hxn k hkp hkζ] at hk

private lemma negSupport_eq_pair {x : Fin 4 → SignType} {p ζ i j : Fin 4}
    (hpζ : p ≠ ζ) (hip : i ≠ p) (hiζ : i ≠ ζ) (hjp : j ≠ p) (hjζ : j ≠ ζ)
    (hij : i ≠ j) (hxp : x p = 1) (hxζ : x ζ = 0)
    (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    negSupport x = {i, j} := by
  ext k
  simp only [mem_negSupport, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨fun hk ↦ ?_, by rintro (rfl | rfl) <;> apply hxn <;> assumption⟩
  rcases fin4_exhaust p ζ i j k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
  · simp [hxp] at hk
  · simp [hxζ] at hk
  · exact .inl rfl
  · exact .inr rfl

/-- Against a singleton-positive weight-3 member, non-mergeability and non-anti-domination
become coordinatewise sign constraints. -/
private lemma constraints_of_sp3 (hmerge : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Mergeable v w)
    (hno : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → posSupport v ⊆ negSupport w → ¬posSupport w ⊆ negSupport v)
    {x w : Fin 4 → SignType} (hxS : x ∈ S) (hwS : w ∈ S) (hxw : x ≠ w)
    {p ζ i j : Fin 4} (hpζ : p ≠ ζ) (hip : i ≠ p) (hiζ : i ≠ ζ)
    (hjp : j ≠ p) (hjζ : j ≠ ζ) (hij : i ≠ j)
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    (w p = 1 ∨ w i = -1 ∨ w j = -1) ∧ (w p ≠ -1 ∨ w ζ = 1) := by
  have hsx := posSupport_eq_singleton hxp hxζ hxn
  have hnx := negSupport_eq_pair hpζ hip hiζ hjp hjζ hij hxp hxζ hxn
  constructor
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    refine hmerge x hxS w hwS hxw ⟨?_, ?_⟩
    · rw [hsx, Set.disjoint_singleton_left]; exact h1
    · rw [hnx, Set.disjoint_insert_left, Set.disjoint_singleton_left]; exact ⟨h2, h3⟩
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    refine hno x hxS w hwS hxw (by rw [hsx, Set.singleton_subset_iff]; exact h1) fun k hk ↦ ?_
    rw [hnx]
    rcases fin4_exhaust p ζ i j k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · simp [mem_posSupport.1 hk] at h1
    · exact absurd hk h2
    · exact .inl rfl
    · exact .inr rfl

/-- Under the pair constraints with the pinned 3-cycle, every admissible sign pattern has
nonnegative witness value. -/
private lemma wt3_witness_bound (wp wi wj wz : SignType)
    (h1 : wp = 1 ∨ wi = 1 ∨ wj = 1 ∨ wz = 1)
    (h2p : wp = 0 → wi ≠ 0 ∧ wj ≠ 0 ∧ wz ≠ 0)
    (h2i : wi = 0 → wj ≠ 0 ∧ wz ≠ 0)
    (h2j : wj = 0 → wz ≠ 0)
    (hgx : wp = 1 ∨ wi = -1 ∨ wj = -1)
    (hax : wp ≠ -1 ∨ wz = 1)
    (hgy1 : wi = 1 ∨ wj = -1 ∨ wz = -1)
    (hay1 : wi ≠ -1 ∨ wp = 1)
    (hgy2 : wz = 1 ∨ wp = -1 ∨ wj = -1)
    (hay2 : wz ≠ -1 ∨ wi = 1) :
    0 ≤ (wp : ℚ) + wi + wz - wj := by
  cases wp <;> cases wi <;> cases wj <;> cases wz <;> simp_all +decide <;> norm_num

/-- A singleton-positive weight-3 member forces an *s-shape* companion, which is zero at the
    member's positive coordinate, `-1` at its zero coordinate, and splits ±1 on the remaining
    two. -/
private lemma s_shape_forcing (hd : ∀ v ∈ S, 0 < d v)
    (hbal : ∀ i, ∑ v ∈ S, d v * (v i : ℚ) = 0) (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hmerge : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Mergeable v w)
    (hno : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → posSupport v ⊆ negSupport w → ¬posSupport w ⊆ negSupport v)
    {x : Fin 4 → SignType} (hxS : x ∈ S) {p ζ : Fin 4} (hpζ : p ≠ ζ)
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    ∃ y ∈ S, ∃ i j : Fin 4, i ≠ p ∧ i ≠ ζ ∧ j ≠ p ∧ j ≠ ζ ∧ i ≠ j ∧
      y p = 0 ∧ y ζ = -1 ∧ y i = 1 ∧ y j = -1 := by
  have hsx := posSupport_eq_singleton hxp hxζ hxn
  -- the functional `w ↦ w p + w ζ` sums to zero over `S`
  have hF : ∑ w ∈ S, d w * ((w p : ℚ) + w ζ) = 0 := by
    simp_rw [mul_add]
    rw [sum_add_distrib, hbal p, hbal ζ, add_zero]
  -- `x`'s term is positive, so some member has `w p + w ζ < 0`
  obtain ⟨y, hyS, hy⟩ : ∃ w ∈ S, (w p : ℚ) + w ζ < 0 := by
    by_contra hall
    push Not at hall
    refine (sum_pos' (fun w hw ↦ mul_nonneg (hd w hw).le (hall w hw)) ⟨x, hxS, ?_⟩).ne' hF
    simpa [hxp, hxζ] using hd x hxS
  have hxy : x ≠ y := by
    rintro rfl; norm_num [hxp, hxζ] at hy
  -- pin the shape of `y`: `y p = 0` and `y ζ = -1`
  have hyp : y p = 0 := by
    rcases (y p).trichotomy with h | h | h
    · -- `y p = -1` forces `y ζ = 1` by no-anti-domination, making the term `0`
      exfalso
      have hsub : posSupport x ⊆ negSupport y := by
        rw [hsx, Set.singleton_subset_iff]; exact h
      obtain ⟨m, hmy, hmx⟩ := Set.not_subset.1 (hno x hxS y hyS hxy hsub)
      rw [mem_posSupport] at hmy
      rw [mem_negSupport] at hmx
      have hmp : m ≠ p := by rintro rfl; simp [h] at hmy
      obtain rfl : m = ζ := by_contra fun hmζ ↦ hmx (hxn m hmp hmζ)
      norm_num [h, hmy] at hy
    · exact h
    · exfalso
      rcases (y ζ).trichotomy with h' | h' | h' <;> norm_num [h, h'] at hy
  have hyζ : y ζ = -1 := by
    rcases (y ζ).trichotomy with h | h | h
    · exact h
    all_goals norm_num [hyp, h] at hy
  -- `y`'s positive coordinate is off `{p, ζ}`
  obtain ⟨i, hyi⟩ := hposne y hyS
  have hip : i ≠ p := by rintro rfl; simp [hyp] at hyi
  have hiζ : i ≠ ζ := by rintro rfl; simp [hyζ] at hyi
  -- the fourth coordinate carries `-1`, by non-mergeability with `x`
  obtain ⟨j, hjp, hjζ, hji⟩ := exists_fourth p ζ i hpζ hip hiζ
  have hyj : y j = -1 := by
    have hdp : Disjoint (posSupport x) (posSupport y) := by
      rw [hsx, Set.disjoint_singleton_left, mem_posSupport, hyp]; decide
    obtain ⟨m, hmx, hmy⟩ := Set.not_disjoint_iff.1 fun hdn ↦ hmerge x hxS y hyS hxy ⟨hdp, hdn⟩
    rw [mem_negSupport] at hmx hmy
    rcases fin4_exhaust p ζ i j m hpζ hip hiζ hjp hjζ (Ne.symm hji) with rfl | rfl | rfl | rfl
    · simp [hxp] at hmx
    · simp [hxζ] at hmx
    · simp [hyi] at hmy
    · exact hmy
  exact ⟨y, hyS, i, j, hip, hiζ, hjp, hjζ, Ne.symm hji, hyp, hyζ, hyi, hyj⟩

/-- No member is singleton-positive of weight 3, since the s-shape chain closes into a 3-cycle
    whose Stiemke witness is nonnegative on all of `S` and positive at `x`, contradicting
    balance. -/
private lemma sp3_kill (hd : ∀ v ∈ S, 0 < d v)
    (hbal : ∀ i, ∑ v ∈ S, d v * (v i : ℚ) = 0) (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hmerge : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Mergeable v w)
    (hno : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → posSupport v ⊆ negSupport w → ¬posSupport w ⊆ negSupport v)
    {x : Fin 4 → SignType} (hxS : x ∈ S) {p ζ : Fin 4} (hpζ : p ≠ ζ)
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) : False := by
  obtain ⟨y₁, hy₁S, i, j, hip, hiζ, hjp, hjζ, hij, hy₁p, hy₁ζ, hy₁i, hy₁j⟩ :=
    s_shape_forcing hd hbal hposne hmerge hno hxS hpζ hxp hxζ hxn
  -- `y₁` is singleton-positive weight-3 with roles (pos `i`, zero `p`, negs `{j, ζ}`)
  have hy₁n : ∀ k, k ≠ i → k ≠ p → y₁ k = -1 := by
    intro k hki hkp
    rcases fin4_exhaust p ζ i j k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · exact absurd rfl hkp
    · exact hy₁ζ
    · exact absurd rfl hki
    · exact hy₁j
  obtain ⟨y₂, hy₂S, a, b, hai, hap, hbi, hbp, hab, hy₂i, hy₂p, hy₂a, hy₂b⟩ :=
    s_shape_forcing hd hbal hposne hmerge hno hy₁S hip hy₁i hy₁p hy₁n
  -- `a` and `b` land in `{ζ, j}`
  have ha : a = ζ ∨ a = j := by
    rcases fin4_exhaust p ζ i j a hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · exact absurd rfl hap
    · exact Or.inl rfl
    · exact absurd rfl hai
    · exact Or.inr rfl
  have hb : b = ζ ∨ b = j := by
    rcases fin4_exhaust p ζ i j b hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · exact absurd rfl hbp
    · exact Or.inl rfl
    · exact absurd rfl hbi
    · exact Or.inr rfl
  rcases ha with rfl | rfl
  · -- `a = ζ`: live 3-cycle; pin `b = j`
    rcases hb with rfl | rfl
    · exact hab rfl
    · -- the witness functional `G w = w p + w i + w a - w b` sums to zero
      have hG : ∑ w ∈ S, d w * ((w p : ℚ) + w i + w a - w b) = 0 := by
        simp_rw [mul_sub, mul_add]
        rw [sum_sub_distrib, sum_add_distrib, sum_add_distrib, hbal p, hbal i, hbal a, hbal b]
        norm_num
      -- ... and `y₂`'s remaining structure
      have hy₂n : ∀ k, k ≠ a → k ≠ i → y₂ k = -1 := by
        intro k hkζ hki
        rcases fin4_exhaust p a i b k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
        · exact hy₂p
        · exact absurd rfl hkζ
        · exact absurd rfl hki
        · exact hy₂b
      -- every term of the witness functional is nonnegative
      have hterm : ∀ w ∈ S, 0 ≤ (w p : ℚ) + w i + w a - w b := by
        intro w hw
        rcases eq_or_ne w x with rfl | hwx
        · simp [hxp, hxζ, hxn i hip hiζ, hxn b hjp hjζ]
        rcases eq_or_ne w y₁ with rfl | hwy₁
        · simp [hy₁p, hy₁ζ, hy₁i, hy₁j]
        rcases eq_or_ne w y₂ with rfl | hwy₂
        · simp [hy₂p, hy₂i, hy₂a, hy₂b]
        -- otherwise: translate the pair constraints and close by sign arithmetic
        have hpos1 : w p = 1 ∨ w i = 1 ∨ w b = 1 ∨ w a = 1 := by
          obtain ⟨k, hk⟩ := hposne w hw
          rcases fin4_exhaust p a i b k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
          · exact Or.inl hk
          · exact Or.inr (Or.inr (Or.inr hk))
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
        have hamoz : ∀ {k₁ k₂ : Fin 4}, k₁ ≠ k₂ → w k₁ = 0 → w k₂ ≠ 0 :=
          fun hne hz1 hz2 ↦ at_most_one_zero hd hbal hposne hmerge hw hne hz1 hz2
        have h2p : w p = 0 → w i ≠ 0 ∧ w b ≠ 0 ∧ w a ≠ 0 := fun hz ↦
          ⟨hamoz (Ne.symm hip) hz, hamoz (Ne.symm hjp) hz, hamoz hpζ hz⟩
        have h2i : w i = 0 → w b ≠ 0 ∧ w a ≠ 0 := fun hz ↦ ⟨hamoz hij hz, hamoz hiζ hz⟩
        have h2j : w b = 0 → w a ≠ 0 := fun hz ↦ hamoz hjζ hz
        obtain ⟨hgx, hax⟩ := constraints_of_sp3 hmerge hno hxS hw (Ne.symm hwx)
          hpζ hip hiζ hjp hjζ hij hxp hxζ hxn
        obtain ⟨hgy1, hay1⟩ := constraints_of_sp3 hmerge hno hy₁S hw (Ne.symm hwy₁)
          hip (Ne.symm hij) hjp (Ne.symm hiζ) (Ne.symm hpζ) hjζ hy₁i hy₁p hy₁n
        obtain ⟨hgy2, hay2⟩ := constraints_of_sp3 hmerge hno hy₂S hw (Ne.symm hwy₂)
          (Ne.symm hiζ) hpζ (Ne.symm hip) hjζ (Ne.symm hij) (Ne.symm hjp) hy₂a hy₂i hy₂n
        exact wt3_witness_bound (w p) (w i) (w b) (w a) hpos1 h2p h2i h2j hgx hax hgy1 hay1
          hgy2 hay2
      refine (sum_pos' (fun w hw ↦ mul_nonneg (hd w hw).le (hterm w hw)) ⟨x, hxS, ?_⟩).ne' hG
      simpa [hxp, hxζ, hxn i hip hiζ, hxn b hjp hjζ] using hd x hxS
  · -- `a = j`: `y₂` merges with `x`, a contradiction
    have hxy₂ : x ≠ y₂ := by rintro rfl; simp [hxp] at hy₂p
    rcases hb with rfl | rfl
    · -- `b = ζ`: `y₂ = (-1@p, 0@i, +1@j, -1@ζ)`
      refine hmerge x hxS y₂ hy₂S hxy₂ ⟨?_, ?_⟩
      · rw [posSupport_eq_singleton hxp hxζ hxn, Set.disjoint_singleton_left, mem_posSupport,
          hy₂p]
        decide
      · rw [negSupport_eq_pair hpζ hip hiζ hjp hjζ hij hxp hxζ hxn, Set.disjoint_insert_left,
          Set.disjoint_singleton_left, mem_negSupport, mem_negSupport, hy₂i, hy₂a]
        decide
    · exact hab rfl

/-! ### Sizes 4 and 5 -/

/-- The six 2-element subsets of `Fin 4` split into three complementary pairs;
    `pairClass` names the pair. -/
private def pairClass (P : Finset (Fin 4)) : Fin 3 :=
  if P = {0, 1} ∨ P = {2, 3} then 0 else if P = {0, 2} ∨ P = {1, 3} then 1 else 2

/-- Distinct 2-subsets in the same complement class are complementary, hence disjoint. -/
private lemma pairClass_eq_disjoint : ∀ P Q : Finset (Fin 4),
    #P = 2 → #Q = 2 → P ≠ Q → pairClass P = pairClass Q → P ∩ Q = ∅ := by
  decide

private lemma core_card_ge4 (hd : ∀ v ∈ S, 0 < d v)
    (hbal : ∀ i, ∑ v ∈ S, d v * (v i : ℚ) = 0) (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hmerge : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Mergeable v w) (hc45 : #S = 4 ∨ #S = 5) :
    ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ posSupport v ⊆ negSupport w ∧ posSupport w ⊆ negSupport v := by
  by_contra hno
  push Not at hno
  -- Every member has at least two positive coordinates: singleton-positive
  -- members die on balance (weight 4 directly, weight 3 via the s-shape chain).
  have hcard2 : ∀ v ∈ S, 2 ≤ #(pos v) := by
    intro v hv
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := hposne v hv
    -- `pos v` has one element and contains `k`, so it is `{k}`.
    have hk' : posSupport v = {k} := by
      rw [← coe_pos, ← coe_singleton, coe_inj]
      exact eq_singleton_iff_unique_mem.2
        ⟨mem_pos.2 hk, fun x hx ↦ card_le_one.1 (by omega) x hx k (mem_pos.2 hk)⟩
    by_cases hzero : ∃ m, v m = 0
    · -- weight-3 singleton-positive: the s-shape chain kill
      obtain ⟨m, hm⟩ := hzero
      have hmk : k ≠ m := by rintro rfl; simp [hk] at hm
      have hvn : ∀ l, l ≠ k → l ≠ m → v l = -1 := by
        intro l hlk hlm
        rcases (v l).trichotomy with h | h | h
        · exact h
        · exact (at_most_one_zero hd hbal hposne hmerge hv hlm h hm).elim
        · exact absurd (by rw [← Set.mem_singleton_iff, ← hk']; exact h) hlk
      exact sp3_kill hd hbal hposne hmerge hno hv hmk hk hm hvn
    · -- full-support singleton-positive: balance at `k` kills directly
      push Not at hzero
      have hnok : ∀ w ∈ S, w ≠ v → w k ≠ -1 := by
        intro w hw hwv hwk
        have hsub : posSupport v ⊆ negSupport w := by
          rw [hk', Set.singleton_subset_iff]; exact hwk
        obtain ⟨m, hmw, hmv⟩ := Set.not_subset.1 (hno v hv w hw (Ne.symm hwv) hsub)
        rw [mem_posSupport] at hmw
        rw [mem_negSupport] at hmv
        have hm1 : v m = 1 := by
          rcases (v m).trichotomy with h | h | h
          exacts [absurd h hmv, absurd h (hzero m), h]
        obtain rfl : m = k := by rw [← Set.mem_singleton_iff, ← hk']; exact hm1
        simp [hmw] at hwk
      refine (sum_pos' (fun w hw ↦ ?_) ⟨v, hv, by simpa [hk] using hd v hv⟩).ne' (hbal k)
      rcases eq_or_ne w v with rfl | hwv
      · simpa [hk] using (hd w hw).le
      · rcases (w k).trichotomy with h | h | h
        · exact absurd h (hnok w hw hwv)
        · simp [h]
        · simpa [h] using (hd w hw).le
  have hone := ip_functional hbal 1
  have hip_nonneg : ∀ w ∈ S, 0 ≤ ip 1 w := fun w hw ↦ by
    have := hcard2 w hw
    have := card_pos_add_card_neg_le w
    rw [ip_one_eq, sub_nonneg]
    exact_mod_cast (by omega : #(neg w) ≤ #(pos w))
  by_cases hall : ∀ v ∈ S, ∀ i, v i ≠ 0
  · -- Case A: every member has full support
    -- positive supports pairwise intersect
    have hint : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Disjoint (pos v) (pos w) := by
      intro v hv w hw hvw hdisj
      rw [← disjoint_coe, coe_pos, coe_pos] at hdisj
      obtain ⟨had1, had2⟩ := antidominating_of_ne_zero (hall v hv) (hall w hw) hdisj
      exact hno v hv w hw hvw had1 had2
    -- the `𝟙`-functional forces all positive supports to have exactly 2 elements
    have hterm0 : ∀ w ∈ S, #(pos w) = 2 := by
      intro w hw
      have hz := (sum_eq_zero_iff_of_nonneg fun w hw ↦ mul_nonneg (hd w hw).le
        (hip_nonneg w hw)).1 hone w hw
      have hipz : ip 1 w = 0 := (mul_eq_zero.1 hz).resolve_left (hd w hw).ne'
      have hcov : #(pos w) + #(neg w) = 4 := by
        have huniv : pos w ∪ neg w = univ := eq_univ_of_forall fun i ↦ by
          rcases (w i).trichotomy with h | h | h
          exacts [mem_union_right _ (mem_neg.2 h), absurd h (hall w hw i),
            mem_union_left _ (mem_pos.2 h)]
        rw [← card_union_of_disjoint (disjoint_pos_neg w), huniv, card_univ, Fintype.card_fin]
      rw [ip_one_eq, sub_eq_zero] at hipz
      have : #(pos w) = #(neg w) := by exact_mod_cast hipz
      omega
    have hinj : ∀ v ∈ S, ∀ w ∈ S, pos v = pos w → v = w := by
      intro v hv w hw heq
      funext i
      have h := congrArg (i ∈ ·) heq
      simp only [mem_pos, eq_iff_iff] at h
      rcases (v i).trichotomy with h1 | h1 | h1 <;> rcases (w i).trichotomy with h2 | h2 | h2 <;>
        simp_all
    -- pigeonhole: four distinct 2-subsets land in three complement classes
    obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq (s := S) (n := 4) (by omega)
    obtain ⟨x, hxT, y, hyT, hxy, hpc⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
      (s := T) (t := (univ : Finset (Fin 3))) (f := fun w ↦ pairClass (pos w))
      (by simp [hT]) fun w _ ↦ mem_coe.2 (mem_univ _)
    have hxS : x ∈ S := hTS hxT
    have hyS : y ∈ S := hTS hyT
    exact hint x hxS y hyS hxy <| disjoint_iff_inter_eq_empty.2 <|
      pairClass_eq_disjoint _ _ (hterm0 x hxS) (hterm0 y hyS)
        (fun h ↦ hxy (hinj _ hxS _ hyS h)) hpc
  · -- Case B: some member has a zero coordinate, so its `𝟙`-value is positive
    push Not at hall
    obtain ⟨v₀, hv₀S, z, hv₀z⟩ := hall
    refine (sum_pos' (fun w hw ↦ mul_nonneg (hd w hw).le (hip_nonneg w hw))
      ⟨v₀, hv₀S, mul_pos (hd v₀ hv₀S) ?_⟩).ne' hone
    have hc3 : #(pos v₀) + #(neg v₀) ≤ 3 := by
      rw [← card_union_of_disjoint (disjoint_pos_neg v₀)]
      calc #(pos v₀ ∪ neg v₀) ≤ #(univ.erase z) := card_le_card fun k hk ↦ mem_erase.2
            ⟨by rintro rfl; simp [hv₀z] at hk, mem_univ k⟩
        _ = 3 := by rw [card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
    have := hcard2 v₀ hv₀S
    rw [ip_one_eq, sub_pos]
    exact_mod_cast (by omega : #(neg v₀) < #(pos v₀))

/-- **Anti-domination from balance.** A family of at most five pairwise non-mergeable
comparisons on four atoms, each with a nonempty positive side and balanced by strictly positive
rational weights, contains two comparisons each of whose positive side lies in the other's
negative side. -/
theorem exists_antidominating_pair (hd : ∀ v ∈ S, 0 < d v)
    (hbal : ∀ i, ∑ v ∈ S, d v * (v i : ℚ) = 0) (hpos : ∀ v ∈ S, (posSupport v).Nonempty)
    (hmerge : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Mergeable v w) (hne : S.Nonempty) (hcard : #S ≤ 5) :
    ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ posSupport v ⊆ negSupport w ∧ posSupport w ⊆ negSupport v := by
  have hposne : ∀ v ∈ S, ∃ i, v i = 1 := hpos
  have hcard1 : 1 ≤ #S := card_pos.2 hne
  interval_cases hc : #S
  · exact (core_card_one hd hbal hposne hc).elim
  · exact (core_card_two hd hbal hmerge hc).elim
  · exact (core_card_three hd hbal hmerge hc).elim
  · exact core_card_ge4 hd hbal hposne hmerge (.inl hc)
  · exact core_card_ge4 hd hbal hposne hmerge (.inr hc)

end ComparativeProbability
