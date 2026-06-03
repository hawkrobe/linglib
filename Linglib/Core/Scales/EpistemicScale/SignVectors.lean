import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Balanced sign-vector families on `Fin 4` have an anti-dominating pair

The finite combinatorial core of the `Fin 4` cancellation theorem: any family
of `{-1,0,1}`-valued vectors on four coordinates, each with a positive
coordinate, balanced by strictly positive weights, of size at most `5`, and
pairwise *non-generalized-mergeable* (every pair shares a same-sign
coordinate), contains an **anti-dominating pair** — two members whose positive
supports sit inside each other's negative supports
(`SignVec.exists_antidom_pair`).

Sizes 1–3 fall to coefficient arithmetic.  For sizes 4–5: full-support
families are forced into 2-element positive supports by the `𝟙`-functional and
die by a pigeonhole on the three complementary pairs of 2-subsets; families
with a zero coordinate die through the *s-shape chain* — a singleton-positive
weight-3 member forces a cascade closing into a 3-cycle whose Stiemke witness
is nonnegative on every admissible sign pattern and positive somewhere,
contradicting balance.
-/

open Finset

namespace Core.Scale.SignVec

open Finset

def posSupport (v : Fin 4 → ℚ) : Finset (Fin 4) := Finset.univ.filter (fun i => v i = 1)
def negSupport (v : Fin 4 → ℚ) : Finset (Fin 4) := Finset.univ.filter (fun i => v i = -1)

@[simp] lemma mem_posSupport {v : Fin 4 → ℚ} {i : Fin 4} : i ∈ posSupport v ↔ v i = 1 := by
  simp [posSupport]

@[simp] lemma mem_negSupport {v : Fin 4 → ℚ} {i : Fin 4} : i ∈ negSupport v ↔ v i = -1 := by
  simp [negSupport]

/-! ### Phase 1: balance and the both-signs corollary -/

/-- Coordinatewise balance: `hsum` evaluated at coordinate `i`. -/
private lemma balance_coord (S : Finset (Fin 4 → ℚ)) (d : (Fin 4 → ℚ) → ℚ)
    (hsum : ∑ v ∈ S, d v • v = 0) (i : Fin 4) :
    ∑ v ∈ S, d v * v i = 0 := by
  have := congrFun hsum i
  rw [Finset.sum_apply] at this
  simpa [Pi.smul_apply, smul_eq_mul] using this

/-! ### Sizes 1 and 2 are impossible -/

private lemma core_card_one (S : Finset (Fin 4 → ℚ))
    (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0) (h1 : S.card = 1) : False := by
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
  obtain ⟨i, hi⟩ := hposne v (Finset.mem_singleton_self v)
  have h := balance_coord {v} d hsum i
  rw [Finset.sum_singleton, hi, mul_one] at h
  exact absurd h (ne_of_gt (hd v (Finset.mem_singleton_self v)))

private lemma core_card_two (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)))
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0) (h2 : S.card = 2) : False := by
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp h2
  have hvS : v ∈ ({v, w} : Finset (Fin 4 → ℚ)) := by simp
  have hwS : w ∈ ({v, w} : Finset (Fin 4 → ℚ)) := by simp
  -- pointwise, balance forces `w = -v`
  have hopp : ∀ i, w i = - v i := by
    intro i
    have hbal : d v * v i + d w * w i = 0 := by
      have := balance_coord {v, w} d hsum i
      rwa [Finset.sum_pair hvw] at this
    have hdv := hd v hvS; have hdw := hd w hwS
    rcases hsign v hvS i with h | h | h <;> rcases hsign w hwS i with h' | h' | h' <;>
      rw [h, h'] at hbal ⊢ <;> linarith
  -- so the pair g-merges, contradicting `hnogm`: same-sign coords clash with `w = -v`
  refine hnogm v hvS w hwS hvw ⟨?_, ?_⟩ <;>
    · rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [mem_posSupport, mem_negSupport, hopp i] at hi hi'
      rw [hi] at hi'; norm_num at hi'

/-! ### Weight-4 dichotomy, sharing, and the size-3 case -/

/-- A full-support (weight-4) pair with disjoint positive supports anti-dominates. -/
private lemma wt4_antidom {v w : Fin 4 → ℚ}
    (hv : ∀ i, v i = -1 ∨ v i = 1) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdisj : Disjoint (posSupport v) (posSupport w)) :
    posSupport v ⊆ negSupport w ∧ posSupport w ⊆ negSupport v := by
  constructor
  · intro i hi
    rw [mem_negSupport]
    rcases hw i with h | h
    · exact h
    · exact absurd (mem_posSupport.mpr h) (Finset.disjoint_left.mp hdisj hi)
  · intro i hi
    rw [mem_negSupport]
    rcases hv i with h | h
    · exact h
    · exact absurd hi (Finset.disjoint_left.mp hdisj (mem_posSupport.mpr h))

/-- A non-g-merging pair shares a same-sign coordinate. -/
private lemma share_of_nogm {v w : Fin 4 → ℚ}
    (h : ¬(Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w))) :
    ∃ j, (v j = 1 ∧ w j = 1) ∨ (v j = -1 ∧ w j = -1) := by
  rw [not_and_or] at h
  rcases h with h | h
  · rw [Finset.not_disjoint_iff] at h
    obtain ⟨j, hj1, hj2⟩ := h
    exact ⟨j, Or.inl ⟨mem_posSupport.mp hj1, mem_posSupport.mp hj2⟩⟩
  · rw [Finset.not_disjoint_iff] at h
    obtain ⟨j, hj1, hj2⟩ := h
    exact ⟨j, Or.inr ⟨mem_negSupport.mp hj1, mem_negSupport.mp hj2⟩⟩

/-- Size-3 engine: when two of three members share a same-sign coordinate, balance
    there forces the third member's coefficient to be the sum of theirs. -/
private lemma trio_eq {a b c : Fin 4 → ℚ} {da db dc : ℚ}
    (hda : 0 < da) (hdb : 0 < db) (hdc : 0 < dc)
    (hsc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) {j : Fin 4}
    (hshare : (a j = 1 ∧ b j = 1) ∨ (a j = -1 ∧ b j = -1))
    (hbal : da * a j + db * b j + dc * c j = 0) :
    dc = da + db := by
  rcases hshare with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] at hbal <;>
    rcases hsc j with h | h | h <;> rw [h] at hbal <;> linarith

private lemma core_card_three (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)))
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0) (h3 : S.card = 3) : False := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
  have haS : a ∈ ({a, b, c} : Finset (Fin 4 → ℚ)) := by simp
  have hbS : b ∈ ({a, b, c} : Finset (Fin 4 → ℚ)) := by simp
  have hcS : c ∈ ({a, b, c} : Finset (Fin 4 → ℚ)) := by simp
  have hbal : ∀ i, d a * a i + d b * b i + d c * c i = 0 := by
    intro i
    have h := balance_coord {a, b, c} d hsum i
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton] at h
    linarith
  obtain ⟨j₁, hsh₁⟩ := share_of_nogm (hnogm a haS b hbS hab)
  have e1 : d c = d a + d b :=
    trio_eq (hd a haS) (hd b hbS) (hd c hcS) (hsign c hcS) hsh₁ (hbal j₁)
  obtain ⟨j₂, hsh₂⟩ := share_of_nogm (hnogm a haS c hcS hac)
  have e2 : d b = d a + d c := by
    have hbal' : d a * a j₂ + d c * c j₂ + d b * b j₂ = 0 := by linarith [hbal j₂]
    exact trio_eq (hd a haS) (hd c hcS) (hd b hbS) (hsign b hbS) hsh₂ hbal'
  linarith [hd a haS]

/-! ### A1: members have at most one zero coordinate (weight ≥ 3) -/

/-- Inner product over `Fin 4`. -/
private def ip (v w : Fin 4 → ℚ) : ℚ := ∑ i, v i * w i

/-- Weighted inner products against any fixed vector vanish (balance functional). -/
private lemma ip_functional (S : Finset (Fin 4 → ℚ)) (d : (Fin 4 → ℚ) → ℚ)
    (hsum : ∑ v ∈ S, d v • v = 0) (v : Fin 4 → ℚ) :
    ∑ w ∈ S, d w * ip v w = 0 := by
  calc ∑ w ∈ S, d w * ip v w
      = ∑ i : Fin 4, v i * ∑ w ∈ S, d w * w i := by
        unfold ip
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by ring
    _ = 0 := by simp [balance_coord S d hsum]

/-- Positive and negative supports are disjoint. -/
private lemma disjoint_spos_sneg (w : Fin 4 → ℚ) : Disjoint (posSupport w) (negSupport w) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [mem_posSupport] at hi
  rw [mem_negSupport, hi] at hi'
  norm_num at hi'

/-- The `𝟙`-functional of a sign vector counts positives minus negatives. -/
private lemma ip_one_eq {w : Fin 4 → ℚ} (hw : ∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) :
    ip (fun _ => 1) w = ((posSupport w).card : ℚ) - ((negSupport w).card : ℚ) := by
  unfold ip
  simp only [one_mul]
  have hcov : (Finset.univ : Finset (Fin 4)) =
      (posSupport w ∪ negSupport w) ∪ (Finset.univ \ (posSupport w ∪ negSupport w)) := by
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  rw [hcov, Finset.sum_union Finset.disjoint_sdiff,
    Finset.sum_union (disjoint_spos_sneg w)]
  have h0 : ∑ k ∈ Finset.univ \ (posSupport w ∪ negSupport w), w k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_union, mem_posSupport, mem_negSupport] at hk
    rcases hw k with h | h | h
    · exact absurd h (fun f => hk.2 (Or.inr f))
    · exact h
    · exact absurd h (fun f => hk.2 (Or.inl f))
  have h1 : ∑ k ∈ posSupport w, w k = ((posSupport w).card : ℚ) := by
    rw [Finset.sum_congr rfl (fun k hk => mem_posSupport.mp hk)]
    simp
  have h2 : ∑ k ∈ negSupport w, w k = -((negSupport w).card : ℚ) := by
    rw [Finset.sum_congr rfl (fun k hk => mem_negSupport.mp hk)]
    simp
  rw [h0, h1, h2]
  ring

/-- At most four signed coordinates. -/
private lemma card_spos_add_sneg_le (w : Fin 4 → ℚ) :
    (posSupport w).card + (negSupport w).card ≤ 4 := by
  calc (posSupport w).card + (negSupport w).card
      = (posSupport w ∪ negSupport w).card :=
        (Finset.card_union_of_disjoint (disjoint_spos_sneg w)).symm
    _ ≤ (Finset.univ : Finset (Fin 4)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = 4 := by simp

/-- **A1**: no member of the family has two zero coordinates. -/
private lemma at_most_one_zero (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)))
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0)
    {v : Fin 4 → ℚ} (hvS : v ∈ S) {i₁ i₂ : Fin 4} (hne : i₁ ≠ i₂)
    (hz1 : v i₁ = 0) (hz2 : v i₂ = 0) : False := by
  classical
  set supp := Finset.univ.filter (fun i => v i ≠ 0) with hsupp
  have hsupp_card : supp.card ≤ 2 := by
    have hsub : supp ⊆ Finset.univ \ {i₁, i₂} := by
      intro i hi
      rw [hsupp, Finset.mem_filter] at hi
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ i, fun hmem => ?_⟩
      rcases Finset.mem_insert.mp hmem with rfl | hmem
      · exact hi.2 hz1
      · rw [Finset.mem_singleton] at hmem; subst hmem; exact hi.2 hz2
    calc supp.card ≤ (Finset.univ \ {i₁, i₂}).card := Finset.card_le_card hsub
      _ = 2 := by
          rw [Finset.card_univ_diff, Finset.card_pair hne, Fintype.card_fin]
  -- `ip v v ≥ 1`
  have hterm_nonneg : ∀ i, 0 ≤ v i * v i := fun i => mul_self_nonneg (v i)
  have hvv : 1 ≤ ip v v := by
    obtain ⟨k, hk⟩ := hposne v hvS
    have hk1 : v k * v k = 1 := by rw [hk]; norm_num
    calc (1 : ℚ) = v k * v k := hk1.symm
      _ ≤ ∑ i, v i * v i := Finset.single_le_sum (fun i _ => hterm_nonneg i) (Finset.mem_univ k)
  -- `ip v w ≥ 0` for every other member
  have hge : ∀ w ∈ S, w ≠ v → 0 ≤ ip v w := by
    intro w hwS hwv
    obtain ⟨j, hsh⟩ := share_of_nogm (hnogm v hvS w hwS (Ne.symm hwv))
    have hjsupp : j ∈ supp := by
      rw [hsupp, Finset.mem_filter]
      refine ⟨Finset.mem_univ j, ?_⟩
      rcases hsh with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> norm_num
    have hjterm : v j * w j = 1 := by
      rcases hsh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
    have hip_supp : ip v w = ∑ i ∈ supp, v i * w i := by
      refine (Finset.sum_filter_of_ne fun i _ hne0 => ?_).symm
      intro h0
      exact hne0 (by rw [h0, zero_mul])
    have hbound : ∀ i ∈ supp.erase j, -1 ≤ v i * w i := by
      intro i _
      rcases hsign v hvS i with h | h | h <;> rcases hsign w hwS i with h' | h' | h' <;>
        rw [h, h'] <;> norm_num
    have hcard_erase : (supp.erase j).card ≤ 1 := by
      rw [Finset.card_erase_of_mem hjsupp]; omega
    have hsum_erase : -1 ≤ ∑ i ∈ supp.erase j, v i * w i :=
      calc (-1 : ℚ) ≤ (supp.erase j).card • (-1 : ℚ) := by
            have : ((supp.erase j).card : ℚ) ≤ 1 := by exact_mod_cast hcard_erase
            simp only [nsmul_eq_mul]; linarith
        _ ≤ ∑ i ∈ supp.erase j, v i * w i := Finset.card_nsmul_le_sum _ _ _ hbound
    rw [hip_supp, ← Finset.add_sum_erase _ _ hjsupp, hjterm]
    linarith
  -- conclude: the balance functional is strictly positive
  have h0 := ip_functional S d hsum v
  have hpos : 0 < ∑ w ∈ S, d w * ip v w := by
    apply Finset.sum_pos'
    · intro w hwS
      rcases eq_or_ne w v with rfl | hwv
      · exact mul_nonneg (le_of_lt (hd w hwS)) (by linarith)
      · exact mul_nonneg (le_of_lt (hd w hwS)) (hge w hwS hwv)
    · exact ⟨v, hvS, mul_pos (hd v hvS) (by linarith)⟩
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-! ### The weight-3 singleton-positive kill

A singleton-positive weight-3 member `x` (one `+1`, one `0`, two `-1`s) forces,
via the functional `w ↦ w p + w ζ`, an *s-shape* companion `y₁` (zero at `x`'s
positive coordinate, `-1` at `x`'s zero); `y₁` is again singleton-positive
weight-3, so the forcing iterates.  Pairwise admissibility kills one branch of
the second iterate, pinning the 3-cycle `x, y₁, y₂`, whose Stiemke witness
`w ↦ w p + w i + w ζ - w j` is nonnegative on every admissible sign pattern
and positive at `x` — contradicting balance. -/

private lemma fin4_exhaust : ∀ p ζ i j k : Fin 4, p ≠ ζ → i ≠ p → i ≠ ζ →
    j ≠ p → j ≠ ζ → i ≠ j → k = p ∨ k = ζ ∨ k = i ∨ k = j := by
  decide

private lemma exists_fourth : ∀ p ζ i : Fin 4, p ≠ ζ → i ≠ p → i ≠ ζ →
    ∃ j, j ≠ p ∧ j ≠ ζ ∧ j ≠ i := by
  decide

private lemma spos_singleton {x : Fin 4 → ℚ} {p ζ : Fin 4} (hpζ : p ≠ ζ)
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    posSupport x = {p} := by
  ext k
  simp only [mem_posSupport, Finset.mem_singleton]
  constructor
  · intro hk
    by_contra hkp
    rcases eq_or_ne k ζ with rfl | hkζ
    · rw [hxζ] at hk; norm_num at hk
    · rw [hxn k hkp hkζ] at hk; norm_num at hk
  · rintro rfl; exact hxp

private lemma sneg_pair {x : Fin 4 → ℚ} {p ζ i j : Fin 4}
    (hpζ : p ≠ ζ) (hip : i ≠ p) (hiζ : i ≠ ζ) (hjp : j ≠ p) (hjζ : j ≠ ζ)
    (hij : i ≠ j) (hxp : x p = 1) (hxζ : x ζ = 0)
    (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    negSupport x = {i, j} := by
  ext k
  simp only [mem_negSupport, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hk
    rcases fin4_exhaust p ζ i j k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · rw [hxp] at hk; norm_num at hk
    · rw [hxζ] at hk; norm_num at hk
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact hxn _ hip hiζ
    · exact hxn _ hjp hjζ

/-- Coordinate translations of no-g-merge and no-anti-domination against a
    singleton-positive weight-3 member. -/
private lemma constraints_of_sp3 (S : Finset (Fin 4 → ℚ))
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)))
    (hno : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → posSupport v ⊆ negSupport w → ¬posSupport w ⊆ negSupport v)
    {x w : Fin 4 → ℚ} (hxS : x ∈ S) (hwS : w ∈ S) (hxw : x ≠ w)
    {p ζ i j : Fin 4} (hpζ : p ≠ ζ) (hip : i ≠ p) (hiζ : i ≠ ζ)
    (hjp : j ≠ p) (hjζ : j ≠ ζ) (hij : i ≠ j)
    (hxp : x p = 1) (hxζ : x ζ = 0) (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    (w p = 1 ∨ w i = -1 ∨ w j = -1) ∧ (w p ≠ -1 ∨ w ζ = 1) := by
  have hsx := spos_singleton hpζ hxp hxζ hxn
  have hnx := sneg_pair hpζ hip hiζ hjp hjζ hij hxp hxζ hxn
  constructor
  · by_contra hc
    push_neg at hc
    obtain ⟨h1, h2, h3⟩ := hc
    refine hnogm x hxS w hwS hxw ⟨?_, ?_⟩
    · rw [hsx, Finset.disjoint_singleton_left]
      simp only [mem_posSupport]
      exact h1
    · rw [hnx]
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, mem_negSupport]
      rintro k (rfl | rfl)
      · exact h2
      · exact h3
  · by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    refine hno x hxS w hwS hxw ?_ ?_
    · rw [hsx, Finset.singleton_subset_iff]
      exact mem_negSupport.mpr h1
    · intro k hk
      rw [mem_posSupport] at hk
      rw [hnx]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases fin4_exhaust p ζ i j k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
      · rw [h1] at hk; norm_num at hk
      · exact absurd hk h2
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- Sign-value arithmetic core: under the pair constraints with the pinned
    3-cycle, every admissible sign pattern has nonnegative witness value. -/
private lemma wt3_witness_bound (wp wi wj wz : ℚ)
    (hsp : wp = -1 ∨ wp = 0 ∨ wp = 1) (hsi : wi = -1 ∨ wi = 0 ∨ wi = 1)
    (hsj : wj = -1 ∨ wj = 0 ∨ wj = 1) (hsz : wz = -1 ∨ wz = 0 ∨ wz = 1)
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
    0 ≤ wp + wi + wz - wj := by
  rcases hsp with rfl | rfl | rfl <;> rcases hsi with rfl | rfl | rfl <;>
    rcases hsj with rfl | rfl | rfl <;> rcases hsz with rfl | rfl | rfl <;>
    norm_num at *

/-- A singleton-positive weight-3 member forces an *s-shape* companion: zero at
    the member's positive coordinate, `-1` at its zero coordinate, and a ±1
    split on the remaining two. -/
private lemma s_shape_forcing (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)))
    (hno : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → posSupport v ⊆ negSupport w → ¬posSupport w ⊆ negSupport v)
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0)
    {x : Fin 4 → ℚ} (hxS : x ∈ S) {p ζ : Fin 4} (hpζ : p ≠ ζ)
    (hxp : x p = 1) (hxζ : x ζ = 0)
    (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) :
    ∃ y ∈ S, ∃ i j : Fin 4, i ≠ p ∧ i ≠ ζ ∧ j ≠ p ∧ j ≠ ζ ∧ i ≠ j ∧
      y p = 0 ∧ y ζ = -1 ∧ y i = 1 ∧ y j = -1 := by
  have hsx := spos_singleton hpζ hxp hxζ hxn
  -- the functional `w ↦ w p + w ζ` sums to zero over `S`
  have hF : ∑ w ∈ S, d w * (w p + w ζ) = 0 := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, balance_coord S d hsum p, balance_coord S d hsum ζ, add_zero]
  -- `x`'s term is positive, so some member has `w p + w ζ < 0`
  obtain ⟨y, hyS, hy⟩ : ∃ w ∈ S, w p + w ζ < 0 := by
    by_contra hall
    push_neg at hall
    have hpos : 0 < ∑ w ∈ S, d w * (w p + w ζ) :=
      Finset.sum_pos' (fun w hw => mul_nonneg (le_of_lt (hd w hw)) (hall w hw))
        ⟨x, hxS, by rw [hxp, hxζ]; simpa using hd x hxS⟩
    rw [hF] at hpos
    exact lt_irrefl 0 hpos
  -- pin the shape of `y`: `y p = 0` and `y ζ = -1`
  have hyp : y p = 0 := by
    rcases hsign y hyS p with h | h | h
    · -- `y p = -1` forces `y ζ = 1` by no-anti-domination, making the term 0
      exfalso
      have hxy : x ≠ y := by
        intro he; rw [← he, hxp] at h; norm_num at h
      have hsub : posSupport x ⊆ negSupport y := by
        rw [hsx, Finset.singleton_subset_iff]; exact mem_negSupport.mpr h
      obtain ⟨m, hmy, hmx⟩ := Finset.not_subset.mp (hno x hxS y hyS hxy hsub)
      rw [mem_posSupport] at hmy
      rw [mem_negSupport] at hmx
      have hmp : m ≠ p := by intro he; rw [he, h] at hmy; norm_num at hmy
      have hmζ : m = ζ := by
        by_contra hmζ
        exact hmx (hxn m hmp hmζ)
      rw [hmζ] at hmy
      rw [h, hmy] at hy
      norm_num at hy
    · exact h
    · exfalso
      rcases hsign y hyS ζ with h' | h' | h' <;> rw [h, h'] at hy <;> norm_num at hy
  have hyζ : y ζ = -1 := by
    rcases hsign y hyS ζ with h | h | h
    · exact h
    · exfalso; rw [hyp, h] at hy; norm_num at hy
    · exfalso; rw [hyp, h] at hy; norm_num at hy
  -- `y`'s positive coordinate is off `{p, ζ}`
  obtain ⟨i, hyi⟩ := hposne y hyS
  have hip : i ≠ p := by intro he; rw [he, hyp] at hyi; norm_num at hyi
  have hiζ : i ≠ ζ := by intro he; rw [he, hyζ] at hyi; norm_num at hyi
  -- the fourth coordinate carries `-1`, via no-g-merge with `x`
  obtain ⟨j, hjp, hjζ, hji⟩ := exists_fourth p ζ i hpζ hip hiζ
  have hxy : x ≠ y := by
    intro he; rw [← he, hxp] at hyp; norm_num at hyp
  have hyj : y j = -1 := by
    have hdp : Disjoint (posSupport x) (posSupport y) := by
      rw [hsx, Finset.disjoint_singleton_left]; simp only [mem_posSupport]; rw [hyp]; norm_num
    obtain ⟨m, hmx, hmy⟩ := Finset.not_disjoint_iff.mp
      (fun hdn => hnogm x hxS y hyS hxy ⟨hdp, hdn⟩)
    rw [mem_negSupport] at hmx hmy
    have hmp : m ≠ p := by intro he; rw [he, hxp] at hmx; norm_num at hmx
    have hmζ : m ≠ ζ := by intro he; rw [he, hxζ] at hmx; norm_num at hmx
    have hmi : m ≠ i := by intro he; rw [he, hyi] at hmy; norm_num at hmy
    rcases fin4_exhaust p ζ i j m hpζ hip hiζ hjp hjζ (Ne.symm hji) with rfl | rfl | rfl | rfl
    · exact absurd rfl hmp
    · exact absurd rfl hmζ
    · exact absurd rfl hmi
    · exact hmy
  exact ⟨y, hyS, i, j, hip, hiζ, hjp, hjζ, Ne.symm hji, hyp, hyζ, hyi, hyj⟩

/-- No member is singleton-positive of weight 3: the s-shape chain closes into
    a 3-cycle whose Stiemke witness is nonnegative on all of `S` and positive
    at `x`, contradicting balance. -/
private lemma sp3_kill (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)))
    (hno : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → posSupport v ⊆ negSupport w → ¬posSupport w ⊆ negSupport v)
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0)
    {x : Fin 4 → ℚ} (hxS : x ∈ S) {p ζ : Fin 4} (hpζ : p ≠ ζ)
    (hxp : x p = 1) (hxζ : x ζ = 0)
    (hxn : ∀ k, k ≠ p → k ≠ ζ → x k = -1) : False := by
  obtain ⟨y₁, hy₁S, i, j, hip, hiζ, hjp, hjζ, hij, hy₁p, hy₁ζ, hy₁i, hy₁j⟩ :=
    s_shape_forcing S hsign hposne hnogm hno d hd hsum hxS hpζ hxp hxζ hxn
  -- `y₁` is singleton-positive weight-3 with roles (pos `i`, zero `p`, negs `{j, ζ}`)
  have hy₁n : ∀ k, k ≠ i → k ≠ p → y₁ k = -1 := by
    intro k hki hkp
    rcases fin4_exhaust p ζ i j k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
    · exact absurd rfl hkp
    · exact hy₁ζ
    · exact absurd rfl hki
    · exact hy₁j
  obtain ⟨y₂, hy₂S, a, b, hai, hap, hbi, hbp, hab, hy₂i, hy₂p, hy₂a, hy₂b⟩ :=
    s_shape_forcing S hsign hposne hnogm hno d hd hsum hy₁S hip hy₁i hy₁p hy₁n
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
      have hG : ∑ w ∈ S, d w * (w p + w i + w a - w b) = 0 := by
        simp_rw [mul_sub, mul_add]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          balance_coord S d hsum p, balance_coord S d hsum i, balance_coord S d hsum a,
          balance_coord S d hsum b]
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
      have hterm : ∀ w ∈ S, 0 ≤ w p + w i + w a - w b := by
        intro w hw
        rcases eq_or_ne w x with rfl | hwx
        · rw [hxp, hxζ, hxn i hip hiζ, hxn b hjp hjζ]; norm_num
        rcases eq_or_ne w y₁ with rfl | hwy₁
        · rw [hy₁p, hy₁ζ, hy₁i, hy₁j]; norm_num
        rcases eq_or_ne w y₂ with rfl | hwy₂
        · rw [hy₂p, hy₂i, hy₂a, hy₂b]; norm_num
        -- otherwise: translate the pair constraints and close by sign arithmetic
        have hpos1 : w p = 1 ∨ w i = 1 ∨ w b = 1 ∨ w a = 1 := by
          obtain ⟨k, hk⟩ := hposne w hw
          rcases fin4_exhaust p a i b k hpζ hip hiζ hjp hjζ hij with rfl | rfl | rfl | rfl
          · exact Or.inl hk
          · exact Or.inr (Or.inr (Or.inr hk))
          · exact Or.inr (Or.inl hk)
          · exact Or.inr (Or.inr (Or.inl hk))
        have hamoz : ∀ {k₁ k₂ : Fin 4}, k₁ ≠ k₂ → w k₁ = 0 → w k₂ ≠ 0 :=
          fun hne hz1 hz2 =>
            at_most_one_zero S hsign hposne hnogm d hd hsum hw hne hz1 hz2
        have h2p : w p = 0 → w i ≠ 0 ∧ w b ≠ 0 ∧ w a ≠ 0 := fun hz =>
          ⟨hamoz (Ne.symm hip) hz, hamoz (Ne.symm hjp) hz, hamoz hpζ hz⟩
        have h2i : w i = 0 → w b ≠ 0 ∧ w a ≠ 0 := fun hz =>
          ⟨hamoz hij hz, hamoz hiζ hz⟩
        have h2j : w b = 0 → w a ≠ 0 := fun hz => hamoz hjζ hz
        obtain ⟨hgx, hax⟩ := constraints_of_sp3 S hnogm hno hxS hw (Ne.symm hwx)
          hpζ hip hiζ hjp hjζ hij hxp hxζ hxn
        obtain ⟨hgy1, hay1⟩ := constraints_of_sp3 S hnogm hno hy₁S hw (Ne.symm hwy₁)
          hip (Ne.symm hij) hjp (Ne.symm hiζ) (Ne.symm hpζ) hjζ hy₁i hy₁p hy₁n
        obtain ⟨hgy2, hay2⟩ := constraints_of_sp3 S hnogm hno hy₂S hw (Ne.symm hwy₂)
          (Ne.symm hiζ) hpζ (Ne.symm hip) hjζ (Ne.symm hij) (Ne.symm hjp) hy₂a hy₂i hy₂n
        exact wt3_witness_bound (w p) (w i) (w b) (w a) (hsign w hw p) (hsign w hw i)
          (hsign w hw b) (hsign w hw a) hpos1 h2p h2i h2j hgx hax hgy1 hay1 hgy2 hay2
      have hpos : 0 < ∑ w ∈ S, d w * (w p + w i + w a - w b) :=
        Finset.sum_pos' (fun w hw => mul_nonneg (le_of_lt (hd w hw)) (hterm w hw))
          ⟨x, hxS, by
            rw [hxp, hxζ, hxn i hip hiζ, hxn b hjp hjζ]
            simpa using hd x hxS⟩
      rw [hG] at hpos
      exact lt_irrefl 0 hpos
  · -- `a = j`: `y₂` g-merges with `x` — contradiction
    have hxy₂ : x ≠ y₂ := by
      intro he
      rw [← he, hxp] at hy₂p
      norm_num at hy₂p
    rcases hb with rfl | rfl
    · -- `b = ζ`: `y₂ = (-1@p, 0@i, +1@j, -1@ζ)`
      refine hnogm x hxS y₂ hy₂S hxy₂ ⟨?_, ?_⟩
      · rw [spos_singleton hpζ hxp hxζ hxn, Finset.disjoint_singleton_left]
        simp only [mem_posSupport]
        rw [hy₂p]
        norm_num
      · rw [sneg_pair hpζ hip hiζ hjp hjζ hij hxp hxζ hxn]
        simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, mem_negSupport]
        rintro k (rfl | rfl)
        · rw [hy₂i]; norm_num
        · rw [hy₂a]; norm_num
    · exact hab rfl

/-! ### Sizes 4 and 5 -/

/-- The six 2-element subsets of `Fin 4` split into three complementary pairs;
    `pairClass` names the pair. -/
private def pairClass (P : Finset (Fin 4)) : Fin 3 :=
  if P = {0, 1} ∨ P = {2, 3} then 0 else if P = {0, 2} ∨ P = {1, 3} then 1 else 2

/-- Distinct 2-subsets in the same complement class are complementary, hence disjoint. -/
private lemma pairClass_eq_disjoint : ∀ P Q : Finset (Fin 4),
    P.card = 2 → Q.card = 2 → P ≠ Q → pairClass P = pairClass Q → P ∩ Q = ∅ := by
  decide

private lemma core_card_ge4 (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)))
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0) (hc45 : S.card = 4 ∨ S.card = 5) :
    ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ posSupport v ⊆ negSupport w ∧ posSupport w ⊆ negSupport v := by
  by_contra hno
  push_neg at hno
  -- Every member has at least two positive coordinates: singleton-positive
  -- members die on balance (weight-4 directly, weight-3 via the s-shape chain).
  have hcard2 : ∀ v ∈ S, 2 ≤ (posSupport v).card := by
    intro v hv
    by_contra hlt
    push_neg at hlt
    obtain ⟨k, hk⟩ := hposne v hv
    -- `posSupport v` has one element and contains `k`, so it is `{k}`.
    have hk' : posSupport v = {k} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨mem_posSupport.mpr hk, fun x hx => Finset.card_le_one.mp (by omega) x hx k (mem_posSupport.mpr hk)⟩
    by_cases hzero : ∃ m, v m = 0
    · -- weight-3 singleton-positive: the s-shape chain kill
      obtain ⟨m, hm⟩ := hzero
      have hmk : k ≠ m := by intro he; rw [← he, hk] at hm; norm_num at hm
      have hvn : ∀ l, l ≠ k → l ≠ m → v l = -1 := by
        intro l hlk hlm
        rcases hsign v hv l with h | h | h
        · exact h
        · exact (at_most_one_zero S hsign hposne hnogm d hd hsum hv hlm h hm).elim
        · exfalso
          have hl : l ∈ posSupport v := mem_posSupport.mpr h
          rw [hk', Finset.mem_singleton] at hl
          exact hlk hl
      exact sp3_kill S hsign hposne hnogm hno d hd hsum hv hmk hk hm hvn
    · -- full-support singleton-positive: balance at `k` kills directly
      push_neg at hzero
      have hnok : ∀ w ∈ S, w ≠ v → w k ≠ -1 := by
        intro w hw hwv hwk
        have hsub : posSupport v ⊆ negSupport w := by
          rw [hk', Finset.singleton_subset_iff]; exact mem_negSupport.mpr hwk
        have hnsub := hno v hv w hw (Ne.symm hwv) hsub
        rw [Finset.not_subset] at hnsub
        obtain ⟨m, hmw, hmv⟩ := hnsub
        rw [mem_posSupport] at hmw
        rw [mem_negSupport] at hmv
        have hm1 : v m = 1 := by
          rcases hsign v hv m with h | h | h
          · exact absurd h hmv
          · exact absurd h (hzero m)
          · exact h
        have hmem : m ∈ posSupport v := mem_posSupport.mpr hm1
        rw [hk', Finset.mem_singleton] at hmem
        subst hmem
        rw [hmw] at hwk
        norm_num at hwk
      have hbal := balance_coord S d hsum k
      have hposk : 0 < ∑ w ∈ S, d w * w k := by
        apply Finset.sum_pos'
        · intro w hw
          rcases eq_or_ne w v with rfl | hwv
          · rw [hk, mul_one]
            exact le_of_lt (hd w hw)
          · rcases hsign w hw k with h | h | h
            · exact absurd h (hnok w hw hwv)
            · simp [h]
            · rw [h, mul_one]
              exact le_of_lt (hd w hw)
        · exact ⟨v, hv, by rw [hk, mul_one]; exact hd v hv⟩
      rw [hbal] at hposk
      exact lt_irrefl 0 hposk
  by_cases hall : ∀ v ∈ S, ∀ i : Fin 4, v i ≠ 0
  · -- Case A: every member has full support (weight 4)
    have hsign' : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 1 := by
      intro v hv i
      rcases hsign v hv i with h | h | h
      · exact Or.inl h
      · exact absurd h (hall v hv i)
      · exact Or.inr h
    -- Step 1: positive supports pairwise intersect
    have hint : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Disjoint (posSupport v) (posSupport w) := by
      intro v hv w hw hvw hdisj
      obtain ⟨had1, had2⟩ := wt4_antidom (hsign' v hv) (hsign' w hw) hdisj
      exact hno v hv w hw hvw had1 had2
    -- the 𝟙-functional forces all supports to have exactly 2 elements
    have hterm0 : ∀ w ∈ S, (posSupport w).card = 2 := by
      have hone := ip_functional S d hsum (fun _ => 1)
      have hnn : ∀ w ∈ S, 0 ≤ d w * ip (fun _ => 1) w := by
        intro w hw
        have hcs : (2:ℚ) ≤ ((posSupport w).card : ℚ) := by exact_mod_cast hcard2 w hw
        have hc4 : ((posSupport w).card : ℚ) + ((negSupport w).card : ℚ) ≤ 4 := by
          exact_mod_cast card_spos_add_sneg_le w
        exact mul_nonneg (hd w hw).le (by rw [ip_one_eq (hsign w hw)]; linarith)
      intro w hw
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hone w hw
      have hipz : ip (fun _ => 1) w = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h (ne_of_gt (hd w hw))
        · exact h
      rw [ip_one_eq (hsign w hw)] at hipz
      have hcs : (2:ℚ) ≤ ((posSupport w).card : ℚ) := by exact_mod_cast hcard2 w hw
      have hc4 : ((posSupport w).card : ℚ) + ((negSupport w).card : ℚ) ≤ 4 := by
        exact_mod_cast card_spos_add_sneg_le w
      have : ((posSupport w).card : ℚ) = 2 := by linarith
      exact_mod_cast this
    have hinj : ∀ v ∈ S, ∀ w ∈ S, posSupport v = posSupport w → v = w := by
      intro v hv w hw heq
      funext i
      rcases hsign' v hv i with h | h <;> rcases hsign' w hw i with h' | h' <;>
        rw [h, h']
      · have hni : i ∉ posSupport v := by rw [mem_posSupport, h]; norm_num
        rw [heq, mem_posSupport] at hni
        exact absurd h' hni
      · have hv' : i ∈ posSupport v := mem_posSupport.mpr h
        rw [heq, mem_posSupport, h'] at hv'
        norm_num at hv'
    -- pigeonhole: four distinct 2-subsets land in three complement classes
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (s := S) (n := 4) (by omega)
    obtain ⟨x, hxT, y, hyT, hxy, hpc⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := T) (t := (Finset.univ : Finset (Fin 3))) (f := fun w => pairClass (posSupport w))
        (by simp [hT]) (fun w _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    have hxS : x ∈ S := hTS hxT
    have hyS : y ∈ S := hTS hyT
    have hsne : posSupport x ≠ posSupport y := fun h => hxy (hinj _ hxS _ hyS h)
    have hdisj : posSupport x ∩ posSupport y = ∅ :=
      pairClass_eq_disjoint _ _ (hterm0 x hxS) (hterm0 y hyS) hsne hpc
    exact hint x hxS y hyS hxy (Finset.disjoint_iff_inter_eq_empty.mpr hdisj)
  · -- Case B: some member has a zero coordinate
    push_neg at hall
    obtain ⟨v₀, hv₀S, z, hv₀z⟩ := hall
    have hone := ip_functional S d hsum (fun _ => 1)
    have hposS : 0 < ∑ w ∈ S, d w * ip (fun _ => 1) w := by
      apply Finset.sum_pos'
      · intro w hw
        apply mul_nonneg (le_of_lt (hd w hw))
        rw [ip_one_eq (hsign w hw)]
        have hc2 : (2:ℚ) ≤ ((posSupport w).card : ℚ) := by exact_mod_cast hcard2 w hw
        have hc4 : ((posSupport w).card : ℚ) + ((negSupport w).card : ℚ) ≤ 4 := by
          exact_mod_cast card_spos_add_sneg_le w
        linarith
      · refine ⟨v₀, hv₀S, ?_⟩
        apply mul_pos (hd v₀ hv₀S)
        rw [ip_one_eq (hsign v₀ hv₀S)]
        have hc2 : (2:ℚ) ≤ ((posSupport v₀).card : ℚ) := by exact_mod_cast hcard2 v₀ hv₀S
        have hc3 : (posSupport v₀).card + (negSupport v₀).card ≤ 3 := by
          have hz : z ∉ posSupport v₀ ∪ negSupport v₀ := by
            simp only [Finset.mem_union, mem_posSupport, mem_negSupport, hv₀z]
            norm_num
          calc (posSupport v₀).card + (negSupport v₀).card
              = (posSupport v₀ ∪ negSupport v₀).card :=
                (Finset.card_union_of_disjoint (disjoint_spos_sneg v₀)).symm
            _ ≤ (Finset.univ.erase z).card := Finset.card_le_card
                (fun k hk => Finset.mem_erase.mpr
                  ⟨fun he => hz (he ▸ hk), Finset.mem_univ _⟩)
            _ = 3 := by
                rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ,
                  Fintype.card_fin]
        have hc3' : ((posSupport v₀).card : ℚ) + ((negSupport v₀).card : ℚ) ≤ 3 := by
          exact_mod_cast hc3
        linarith
    rw [hone] at hposS
    exact lt_irrefl 0 hposS

theorem exists_antidom_pair (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hcard : S.card ≤ 5)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (posSupport v) (posSupport w) ∧ Disjoint (negSupport v) (negSupport w)))
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v) (hSne : S.Nonempty)
    (hsum : ∑ v ∈ S, d v • v = 0) :
    ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ posSupport v ⊆ negSupport w ∧ posSupport w ⊆ negSupport v := by
  have hcard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  interval_cases hc : S.card
  · exact (core_card_one S hposne d hd hsum hc).elim
  · exact (core_card_two S hsign hnogm d hd hsum hc).elim
  · exact (core_card_three S hsign hnogm d hd hsum hc).elim
  · exact core_card_ge4 S hsign hposne hnogm d hd hsum (Or.inl hc)
  · exact core_card_ge4 S hsign hposne hnogm d hd hsum (Or.inr hc)



end Core.Scale.SignVec
