import Linglib.Core.Scales.EpistemicScale.Cancellation
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases

/-! # Cancellation for `Fin 4`: the structural merge-reduction proof

Every finitely additive epistemic-comparison system on four worlds satisfies
Scott cancellation (`fa_cancellation_fin4`), hence is representable by a
finitely additive measure (`theorem8a_fin4` — [holliday-icard-2013] Theorem 8).

The proof replaces the former 88-chamber case enumeration with a structural
argument in three layers:

* **Conic Carathéodory** (`EpiCarath.exists_posdep_card_le_five`): a positive
  dependence among vectors of `Fin 4 → ℚ` thins to support `≤ 5`.
* **The finite core** (`core_le5`): a balanced family of pairwise
  non-generalized-mergeable sign vectors of size `≤ 5` contains an
  anti-dominating pair.  Weight-4 families fall to a complement-class
  pigeonhole; families with a zero coordinate fall to the s-shape chain,
  whose forced 3-cycle carries the uniform Stiemke witness `𝟙 - 2·e_c`.
* **Merge reduction** (`merge_to_single`): a valid family whose vector sum is
  a single comparison vector proves that comparison, by a four-rule recursion
  whose stuck case is discharged by the core via `v1_tailored`.

-/

/-! ### Conic Carathéodory pivot over ℚ in dimension 4

A positive dependence among vectors in `Fin 4 → ℚ` can be thinned to one supported
on at most `5` vectors — the conic (Carathéodory) bound `finrank + 1 = 5`.  Strong
induction on the support cardinality; a single linear pivot step strictly shrinks
the positive support each round. -/

open Finset Module

namespace EpiCarath

/-- finrank of `Fin 4 → ℚ` is `4`. -/
private theorem finrank_q4 : finrank ℚ (Fin 4 → ℚ) = 4 := Module.finrank_fin_fun ℚ

/-- **The pivot step.**  Given a positive dependence `c` on `V` together with a *linear
relation* `g` on `V` that is positive somewhere and zero at a marked element `v₀ ∈ V`
with `0 < c v₀`, produce a *strictly smaller* positive support `V'` carrying a positive
dependence, and with `V' ⊆ V`. -/
private theorem pivot
    (V : Finset (Fin 4 → ℚ)) (c : (Fin 4 → ℚ) → ℚ)
    (hpos : ∀ v ∈ V, 0 < c v) (hcsum : ∑ v ∈ V, c v • v = 0)
    (g : (Fin 4 → ℚ) → ℚ) (hgsum : ∑ v ∈ V, g v • v = 0)
    (v₀ : Fin 4 → ℚ) (hv₀ : v₀ ∈ V) (hgv₀ : g v₀ = 0)
    (w : Fin 4 → ℚ) (hw : w ∈ V) (hgw : 0 < g w) :
    ∃ V' ⊆ V, V'.card < V.card ∧ V'.Nonempty ∧
      ∃ d : (Fin 4 → ℚ) → ℚ, (∀ v ∈ V', 0 < d v) ∧ ∑ v ∈ V', d v • v = 0 := by
  classical
  -- The set of vectors where `g` is positive: nonempty (`w`), and excludes `v₀`.
  set P := V.filter (fun v => 0 < g v) with hP
  have hPne : P.Nonempty := ⟨w, mem_filter.2 ⟨hw, hgw⟩⟩
  have hPmem : ∀ {v}, v ∈ P ↔ v ∈ V ∧ 0 < g v := fun {v} => mem_filter
  -- Pivot ratio `t = min_{v ∈ P} c v / g v`, attained at some `v* ∈ P`.
  set t : ℚ := P.inf' hPne (fun v => c v / g v) with ht
  obtain ⟨vstar, hvstarP, hvstar_eq⟩ := Finset.exists_mem_eq_inf' hPne (fun v => c v / g v)
  have hvstarV : vstar ∈ V := (hPmem.1 hvstarP).1
  have hgvstar : 0 < g vstar := (hPmem.1 hvstarP).2
  -- `t > 0`.
  have ht_pos : 0 < t := by
    rw [ht]
    rw [Finset.lt_inf'_iff]
    intro v hv
    exact div_pos (hpos v (hPmem.1 hv).1) (hPmem.1 hv).2
  -- The shifted coefficients.
  set d : (Fin 4 → ℚ) → ℚ := fun v => c v - t * g v with hd
  -- `0 ≤ d v` for every `v ∈ V`.
  have hd_nonneg : ∀ v ∈ V, 0 ≤ d v := by
    intro v hv
    rcases lt_or_ge 0 (g v) with hgvpos | hgvnonpos
    · -- `v ∈ P`, so `t ≤ c v / g v`, hence `t * g v ≤ c v`.
      have hvP : v ∈ P := hPmem.2 ⟨hv, hgvpos⟩
      have hle : t ≤ c v / g v := by rw [ht]; exact Finset.inf'_le _ hvP
      have : t * g v ≤ c v := by rw [le_div_iff₀ hgvpos] at hle; exact hle
      simp only [hd]; linarith
    · -- `g v ≤ 0`, so `t * g v ≤ 0 < c v`.
      have : t * g v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht_pos.le hgvnonpos
      have hcv := hpos v hv
      simp only [hd]; linarith
  -- `d vstar = 0`.
  have hd_vstar : d vstar = 0 := by
    have htv : t = c vstar / g vstar := by rw [ht, hvstar_eq]
    simp only [hd, htv]
    rw [div_mul_cancel₀ _ (ne_of_gt hgvstar), sub_self]
  -- The new positive support.
  set V' := V.filter (fun v => 0 < d v) with hV'
  have hV'sub : V' ⊆ V := filter_subset _ _
  -- `vstar ∉ V'` (since `d vstar = 0`), so `V' ⊆ V.erase vstar`.
  have hvstar_notin : vstar ∉ V' := by
    rw [hV', mem_filter]; rintro ⟨_, h⟩; rw [hd_vstar] at h; exact lt_irrefl _ h
  have hV'_erase : V' ⊆ V.erase vstar := by
    intro v hv
    rw [mem_erase]
    refine ⟨?_, hV'sub hv⟩
    rintro rfl; exact hvstar_notin hv
  have hcard : V'.card < V.card := by
    calc V'.card ≤ (V.erase vstar).card := card_le_card hV'_erase
      _ < V.card := by rw [card_erase_of_mem hvstarV]; exact Nat.pred_lt (card_ne_zero.2 ⟨vstar, hvstarV⟩)
  -- `v₀ ∈ V'`: `d v₀ = c v₀ > 0` since `g v₀ = 0`.
  have hv₀V' : v₀ ∈ V' := by
    rw [hV', mem_filter]
    refine ⟨hv₀, ?_⟩
    simp only [hd, hgv₀, mul_zero, sub_zero]
    exact hpos v₀ hv₀
  -- `∀ v ∈ V', 0 < d v`.
  have hd_pos : ∀ v ∈ V', 0 < d v := fun v hv => (mem_filter.1 hv).2
  -- The zero-sum is preserved: dropped terms have `d v = 0`.
  have hsum' : ∑ v ∈ V', d v • v = 0 := by
    have hsplit : ∑ v ∈ V, d v • v = ∑ v ∈ V', d v • v := by
      rw [hV']
      rw [Finset.sum_filter_of_ne]
      intro v hv hne
      -- `d v • v ≠ 0` and `0 ≤ d v` force `0 < d v`.
      rcases (hd_nonneg v hv).lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd (by rw [← heq, zero_smul] : d v • v = 0) hne
    have hVsum : ∑ v ∈ V, d v • v = 0 := by
      have hstep : ∑ v ∈ V, d v • v = (∑ v ∈ V, c v • v) - t • ∑ v ∈ V, g v • v := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        show (c v - t * g v) • v = c v • v - t • (g v • v)
        rw [sub_smul, mul_smul]
      rw [hstep, hcsum, hgsum, smul_zero, sub_zero]
    rw [← hsplit]; exact hVsum
  exact ⟨V', hV'sub, hcard, ⟨v₀, hv₀V'⟩, d, hd_pos, hsum'⟩

/-- **Conic Carathéodory pivot, dimension 4.**  A positive dependence among finitely
many vectors of `Fin 4 → ℚ` can be thinned to one supported on at most `5` of them. -/
theorem exists_posdep_card_le_five
    (V : Finset (Fin 4 → ℚ)) (c : (Fin 4 → ℚ) → ℚ)
    (hpos : ∀ v ∈ V, 0 < c v) (hne : V.Nonempty)
    (hsum : ∑ v ∈ V, c v • v = 0) :
    ∃ S ⊆ V, S.Nonempty ∧ S.card ≤ 5 ∧
      ∃ d : (Fin 4 → ℚ) → ℚ, (∀ v ∈ S, 0 < d v) ∧ ∑ v ∈ S, d v • v = 0 := by
  classical
  -- Strong induction on the cardinality of the support.
  induction hn : V.card using Nat.strong_induction_on generalizing V c with
  | _ n ih =>
    subst hn
    rcases le_or_gt V.card 5 with hsmall | hbig
    · -- Base case: already small enough.
      exact ⟨V, subset_rfl, hne, hsmall, c, hpos, hsum⟩
    · -- Inductive step: `V.card ≥ 6`, pivot to a strictly smaller support.
      obtain ⟨v₀, hv₀⟩ := hne
      -- `V.erase v₀` has card `> finrank ℚ (Fin 4 → ℚ) = 4`.
      have hcard_erase : finrank ℚ (Fin 4 → ℚ) < (V.erase v₀).card := by
        rw [finrank_q4, card_erase_of_mem hv₀]
        omega
      -- A nontrivial relation on `V.erase v₀`.
      obtain ⟨g₀, hg₀sum, x, hxmem, hxne⟩ :=
        Module.exists_nontrivial_relation_of_finrank_lt_card hcard_erase
      have hx_ne_v₀ : x ≠ v₀ := (mem_erase.1 hxmem).1
      have hxV : x ∈ V := (mem_erase.1 hxmem).2
      -- Extend `g₀` by zero at `v₀`, so the relation lives on all of `V`.
      set g : (Fin 4 → ℚ) → ℚ := fun v => if v = v₀ then 0 else g₀ v with hg
      have hgv₀ : g v₀ = 0 := by simp [hg]
      have hgx : g x = g₀ x := by simp [hg, hx_ne_v₀]
      have hgxne : g x ≠ 0 := by rw [hgx]; exact hxne
      -- The extended relation still sums to zero over `V`.
      have hgsum : ∑ v ∈ V, g v • v = 0 := by
        rw [← Finset.sum_erase_add V _ hv₀, hgv₀, zero_smul, add_zero]
        rw [← hg₀sum]
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [hg]; simp [(mem_erase.1 hv).1]
      -- WLOG `g` is positive somewhere on `V` (negate if necessary).
      rcases hgxne.lt_or_gt with hxneg | hxpos
      · -- `g x < 0`: use `-g`, positive at `x`.
        obtain ⟨V', hV'sub, hV'card, hV'ne, d, hd_pos, hd_sum⟩ :=
          pivot V c hpos hsum (fun v => -g v)
            (by simp only [neg_smul, Finset.sum_neg_distrib, hgsum, neg_zero])
            v₀ hv₀ (by simp [hgv₀]) x hxV (by simpa using hxneg)
        obtain ⟨S, hSV', hSne, hScard, e, he_pos, he_sum⟩ :=
          ih V'.card hV'card V' d hd_pos hV'ne hd_sum rfl
        exact ⟨S, hSV'.trans hV'sub, hSne, hScard, e, he_pos, he_sum⟩
      · -- `g x > 0`: use `g` directly.
        obtain ⟨V', hV'sub, hV'card, hV'ne, d, hd_pos, hd_sum⟩ :=
          pivot V c hpos hsum g hgsum v₀ hv₀ hgv₀ x hxV hxpos
        obtain ⟨S, hSV', hSne, hScard, e, he_pos, he_sum⟩ :=
          ih V'.card hV'card V' d hd_pos hV'ne hd_sum rfl
        exact ⟨S, hSV'.trans hV'sub, hSne, hScard, e, he_pos, he_sum⟩

end EpiCarath


/-! # `core_le5`: balanced no-g-merge sign families have an anti-dominating pair

A self-contained reformulation of the combinatorial crux behind Theorem 8a for
`Fin 4` epistemic-comparison systems (the `v1_tailored` sorry in
`scratch/epi_work.lean`).
-/

open Finset

private def spos (v : Fin 4 → ℚ) : Finset (Fin 4) := Finset.univ.filter (fun i => v i = 1)
private def sneg (v : Fin 4 → ℚ) : Finset (Fin 4) := Finset.univ.filter (fun i => v i = -1)

@[simp] private lemma mem_spos {v : Fin 4 → ℚ} {i : Fin 4} : i ∈ spos v ↔ v i = 1 := by
  simp [spos]

@[simp] private lemma mem_sneg {v : Fin 4 → ℚ} {i : Fin 4} : i ∈ sneg v ↔ v i = -1 := by
  simp [sneg]

/-! ### Phase 1: balance and the both-signs corollary -/

/-- Coordinatewise balance: `hsum` evaluated at coordinate `i`. -/
private lemma balance_coord (S : Finset (Fin 4 → ℚ)) (d : (Fin 4 → ℚ) → ℚ)
    (hsum : ∑ v ∈ S, d v • v = 0) (i : Fin 4) :
    ∑ v ∈ S, d v * v i = 0 := by
  have := congrFun hsum i
  rw [Finset.sum_apply] at this
  simpa [Pi.smul_apply, smul_eq_mul] using this

/-- If a coordinate is hit with `+1` by some member, balance forces a `-1` member. -/
private lemma neg_of_pos (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0) (i : Fin 4)
    (hex : ∃ v ∈ S, v i = 1) : ∃ w ∈ S, w i = -1 := by
  by_contra hno
  push_neg at hno
  -- every term d v * v i ≥ 0, with the witness term strictly > 0 ⟹ sum > 0
  have hbal := balance_coord S d hsum i
  obtain ⟨v₀, hv₀S, hv₀⟩ := hex
  have hpos : 0 < ∑ w ∈ S, d w * w i := by
    apply Finset.sum_pos'
    · intro w hwS
      rcases hsign w hwS i with h | h | h
      · exact absurd h (hno w hwS)
      · simp [h]
      · rw [h, mul_one]; exact le_of_lt (hd w hwS)
    · exact ⟨v₀, hv₀S, by rw [hv₀, mul_one]; exact hd v₀ hv₀S⟩
  rw [hbal] at hpos
  exact lt_irrefl 0 hpos

/-- If a coordinate is hit with `-1` by some member, balance forces a `+1` member. -/
private lemma pos_of_neg (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0) (i : Fin 4)
    (hex : ∃ v ∈ S, v i = -1) : ∃ w ∈ S, w i = 1 := by
  by_contra hno
  push_neg at hno
  have hbal := balance_coord S d hsum i
  obtain ⟨v₀, hv₀S, hv₀⟩ := hex
  have hneg : ∑ w ∈ S, d w * w i < 0 := by
    apply Finset.sum_neg'
    · intro w hwS
      rcases hsign w hwS i with h | h | h
      · rw [h, mul_neg, mul_one]; exact le_of_lt (neg_neg_of_pos (hd w hwS))
      · simp [h]
      · exact absurd h (hno w hwS)
    · exact ⟨v₀, hv₀S, by rw [hv₀, mul_neg, mul_one]; exact neg_neg_of_pos (hd v₀ hv₀S)⟩
  rw [hbal] at hneg
  exact lt_irrefl 0 hneg

/-! ### Sizes 1 and 2 are impossible -/

private lemma core_card_one (S : Finset (Fin 4 → ℚ))
    (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0) (h1 : S.card = 1) : False := by
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
  rw [Finset.sum_singleton] at hsum
  rcases smul_eq_zero.mp hsum with h | h
  · exact absurd h (ne_of_gt (hd v (Finset.mem_singleton_self v)))
  · obtain ⟨i, hi⟩ := hposne v (Finset.mem_singleton_self v)
    rw [h] at hi
    simpa using hi

private lemma core_card_two (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w)))
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0) (h2 : S.card = 2) : False := by
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp h2
  have hvS : v ∈ ({v, w} : Finset (Fin 4 → ℚ)) := by simp
  have hwS : w ∈ ({v, w} : Finset (Fin 4 → ℚ)) := by simp
  have hdv := hd v hvS
  have hdw := hd w hwS
  -- pointwise, balance forces `w = -v`
  have hopp : ∀ i, w i = - v i := by
    intro i
    have hbal : d v * v i + d w * w i = 0 := by
      have := balance_coord {v, w} d hsum i
      rwa [Finset.sum_pair hvw] at this
    rcases hsign v hvS i with h | h | h <;> rcases hsign w hwS i with h' | h' | h' <;>
      rw [h, h'] at hbal ⊢ <;> linarith
  -- so the pair g-merges, contradicting `hnogm`
  refine hnogm v hvS w hwS hvw ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hi'
    rw [mem_spos] at hi hi'
    rw [hopp i, hi] at hi'
    norm_num at hi'
  · rw [Finset.disjoint_left]
    intro i hi hi'
    rw [mem_sneg] at hi hi'
    rw [hopp i, hi] at hi'
    norm_num at hi'

/-! ### Weight-4 dichotomy, sharing, and the size-3 case -/

/-- A full-support (weight-4) pair with disjoint positive supports anti-dominates. -/
private lemma wt4_antidom {v w : Fin 4 → ℚ}
    (hv : ∀ i, v i = -1 ∨ v i = 1) (hw : ∀ i, w i = -1 ∨ w i = 1)
    (hdisj : Disjoint (spos v) (spos w)) :
    spos v ⊆ sneg w ∧ spos w ⊆ sneg v := by
  constructor
  · intro i hi
    rw [mem_sneg]
    rcases hw i with h | h
    · exact h
    · exact absurd (mem_spos.mpr h) (Finset.disjoint_left.mp hdisj hi)
  · intro i hi
    rw [mem_sneg]
    rcases hv i with h | h
    · exact h
    · exact absurd hi (Finset.disjoint_left.mp hdisj (mem_spos.mpr h))

/-- A non-g-merging pair shares a same-sign coordinate. -/
private lemma share_of_nogm {v w : Fin 4 → ℚ}
    (h : ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w))) :
    ∃ j, (v j = 1 ∧ w j = 1) ∨ (v j = -1 ∧ w j = -1) := by
  rw [not_and_or] at h
  rcases h with h | h
  · rw [Finset.not_disjoint_iff] at h
    obtain ⟨j, hj1, hj2⟩ := h
    exact ⟨j, Or.inl ⟨mem_spos.mp hj1, mem_spos.mp hj2⟩⟩
  · rw [Finset.not_disjoint_iff] at h
    obtain ⟨j, hj1, hj2⟩ := h
    exact ⟨j, Or.inr ⟨mem_sneg.mp hj1, mem_sneg.mp hj2⟩⟩

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
      ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w)))
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
  have key : ∑ w ∈ S, d w * ip v w = ∑ i : Fin 4, v i * ∑ w ∈ S, d w * w i := by
    unfold ip
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by ring
  rw [key]
  have hz : ∀ i, ∑ w ∈ S, d w * w i = 0 := balance_coord S d hsum
  simp [hz]

/-- **A1**: no member of the family has two zero coordinates. -/
private lemma at_most_one_zero (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w)))
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
    have hsum_erase : -1 ≤ ∑ i ∈ supp.erase j, v i * w i := by
      have hcq : ((supp.erase j).card : ℚ) ≤ 1 := by exact_mod_cast hcard_erase
      calc (-1 : ℚ) ≤ -((supp.erase j).card : ℚ) := by linarith
        _ = (supp.erase j).card • (-1 : ℚ) := by simp [nsmul_eq_mul]
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
    spos x = {p} := by
  ext k
  simp only [mem_spos, Finset.mem_singleton]
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
    sneg x = {i, j} := by
  ext k
  simp only [mem_sneg, Finset.mem_insert, Finset.mem_singleton]
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
      ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w)))
    (hno : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → spos v ⊆ sneg w → ¬spos w ⊆ sneg v)
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
      simp only [mem_spos]
      exact h1
    · rw [hnx, Finset.disjoint_left]
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [mem_sneg]
      rcases hk with rfl | rfl
      · exact h2
      · exact h3
  · by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    refine hno x hxS w hwS hxw ?_ ?_
    · rw [hsx]
      rintro k hk
      rw [Finset.mem_singleton] at hk
      subst hk
      exact mem_sneg.mpr h1
    · intro k hk
      rw [mem_spos] at hk
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
      ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w)))
    (hno : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → spos v ⊆ sneg w → ¬spos w ⊆ sneg v)
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
    have h1 := balance_coord S d hsum p
    have h2 := balance_coord S d hsum ζ
    calc ∑ w ∈ S, d w * (w p + w ζ)
        = ∑ w ∈ S, (d w * w p + d w * w ζ) := by simp_rw [mul_add]
      _ = (∑ w ∈ S, d w * w p) + ∑ w ∈ S, d w * w ζ := Finset.sum_add_distrib
      _ = 0 := by rw [h1, h2, add_zero]
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
      have hsub : spos x ⊆ sneg y := by
        rw [hsx]
        rintro k hk
        rw [Finset.mem_singleton] at hk
        subst hk
        exact mem_sneg.mpr h
      have hnsub := hno x hxS y hyS hxy hsub
      rw [Finset.not_subset] at hnsub
      obtain ⟨m, hmy, hmx⟩ := hnsub
      rw [mem_spos] at hmy
      rw [mem_sneg] at hmx
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
    have hdp : Disjoint (spos x) (spos y) := by
      rw [hsx, Finset.disjoint_singleton_left]
      simp only [mem_spos]
      rw [hyp]
      norm_num
    have hni : ¬Disjoint (sneg x) (sneg y) :=
      fun hdn => hnogm x hxS y hyS hxy ⟨hdp, hdn⟩
    rw [Finset.not_disjoint_iff] at hni
    obtain ⟨m, hmx, hmy⟩ := hni
    rw [mem_sneg] at hmx hmy
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
      ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w)))
    (hno : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → spos v ⊆ sneg w → ¬spos w ⊆ sneg v)
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
        have h1 := balance_coord S d hsum p
        have h2 := balance_coord S d hsum i
        have h3 := balance_coord S d hsum a
        have h4 := balance_coord S d hsum b
        calc ∑ w ∈ S, d w * (w p + w i + w a - w b)
            = ∑ w ∈ S, (d w * w p + d w * w i + d w * w a - d w * w b) := by
              simp_rw [mul_sub, mul_add]
          _ = 0 := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
                h1, h2, h3, h4]
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
        simp only [mem_spos]
        rw [hy₂p]
        norm_num
      · rw [sneg_pair hpζ hip hiζ hjp hjζ hij hxp hxζ hxn, Finset.disjoint_left]
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        simp only [mem_sneg]
        rcases hk with rfl | rfl
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
      ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w)))
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v)
    (hsum : ∑ v ∈ S, d v • v = 0) (hc45 : S.card = 4 ∨ S.card = 5) :
    ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ spos v ⊆ sneg w ∧ spos w ⊆ sneg v := by
  by_contra hno
  push_neg at hno
  by_cases hall : ∀ v ∈ S, ∀ i : Fin 4, v i ≠ 0
  · -- Case A: every member has full support (weight 4)
    have hsign' : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 1 := by
      intro v hv i
      rcases hsign v hv i with h | h | h
      · exact Or.inl h
      · exact absurd h (hall v hv i)
      · exact Or.inr h
    -- Step 1: positive supports pairwise intersect
    have hint : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬Disjoint (spos v) (spos w) := by
      intro v hv w hw hvw hdisj
      obtain ⟨had1, had2⟩ := wt4_antidom (hsign' v hv) (hsign' w hw) hdisj
      exact hno v hv w hw hvw had1 had2
    -- every positive support has ≥ 2 elements
    have hcard2 : ∀ v ∈ S, 2 ≤ (spos v).card := by
      intro v hv
      obtain ⟨k, hk⟩ := hposne v hv
      have hkmem : k ∈ spos v := mem_spos.mpr hk
      by_contra hlt
      push_neg at hlt
      have h1 : (spos v).card = 1 :=
        le_antisymm (by omega) (Finset.card_pos.mpr ⟨k, hkmem⟩)
      obtain ⟨k', hk'⟩ := Finset.card_eq_one.mp h1
      have hkk : k = k' := by
        rw [hk'] at hkmem; exact Finset.mem_singleton.mp hkmem
      subst hkk
      have hallk : ∀ w ∈ S, w k = 1 := by
        intro w hw
        rcases eq_or_ne w v with rfl | hwv
        · exact hk
        · have hnd := hint v hv w hw (Ne.symm hwv)
          rw [Finset.not_disjoint_iff] at hnd
          obtain ⟨j, hj1, hj2⟩ := hnd
          rw [hk', Finset.mem_singleton] at hj1
          subst hj1
          exact mem_spos.mp hj2
      have hbal := balance_coord S d hsum k
      have hpos : 0 < ∑ w ∈ S, d w * w k := by
        apply Finset.sum_pos
        · intro w hw; rw [hallk w hw, mul_one]; exact hd w hw
        · exact ⟨v, hv⟩
      rw [hbal] at hpos
      exact lt_irrefl 0 hpos
    -- support/cosupport bookkeeping
    have hdisjps : ∀ w : Fin 4 → ℚ, Disjoint (spos w) (sneg w) := by
      intro w
      rw [Finset.disjoint_left]
      intro i hi hi'
      rw [mem_spos] at hi; rw [mem_sneg] at hi'
      rw [hi] at hi'; norm_num at hi'
    have hcover : ∀ w ∈ S, (Finset.univ : Finset (Fin 4)) = spos w ∪ sneg w := by
      intro w hw
      ext i
      simp only [Finset.mem_univ, true_iff, Finset.mem_union, mem_spos, mem_sneg]
      rcases hsign' w hw i with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hip1 : ∀ w ∈ S, ip (fun _ => 1) w
        = ((spos w).card : ℚ) - ((sneg w).card : ℚ) := by
      intro w hw
      unfold ip
      simp only [one_mul]
      rw [show (Finset.univ : Finset (Fin 4)) = spos w ∪ sneg w from hcover w hw,
        Finset.sum_union (hdisjps w)]
      have h1 : ∑ i ∈ spos w, w i = ((spos w).card : ℚ) := by
        rw [Finset.sum_congr rfl (fun i hi => mem_spos.mp hi)]
        simp
      have h2 : ∑ i ∈ sneg w, w i = -((sneg w).card : ℚ) := by
        rw [Finset.sum_congr rfl (fun i hi => mem_sneg.mp hi)]
        simp
      rw [h1, h2]; ring
    have hcard4 : ∀ w ∈ S, ((spos w).card : ℚ) + ((sneg w).card : ℚ) = 4 := by
      intro w hw
      have hn : (spos w).card + (sneg w).card = 4 := by
        rw [← Finset.card_union_of_disjoint (hdisjps w),
          ← (hcover w hw)]
        simp
      exact_mod_cast hn
    -- the 𝟙-functional forces all supports to have exactly 2 elements
    have hone := ip_functional S d hsum (fun _ => 1)
    have hnn : ∀ w ∈ S, 0 ≤ d w * ip (fun _ => 1) w := by
      intro w hw
      have hcs : (2:ℚ) ≤ ((spos w).card : ℚ) := by exact_mod_cast hcard2 w hw
      have hge : (0:ℚ) ≤ ip (fun _ => 1) w := by
        rw [hip1 w hw]
        have := hcard4 w hw
        linarith
      exact mul_nonneg (le_of_lt (hd w hw)) hge
    have hterm0 : ∀ w ∈ S, (spos w).card = 2 := by
      intro w hw
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hone w hw
      have hipz : ip (fun _ => 1) w = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h (ne_of_gt (hd w hw))
        · exact h
      have he1 := hip1 w hw
      have he4 := hcard4 w hw
      have : ((spos w).card : ℚ) = 2 := by linarith
      exact_mod_cast this
    -- distinct members have distinct supports
    have hinj : ∀ v ∈ S, ∀ w ∈ S, spos v = spos w → v = w := by
      intro v hv w hw heq
      funext i
      rcases hsign' v hv i with h | h <;> rcases hsign' w hw i with h' | h' <;>
        rw [h, h']
      · have hni : i ∉ spos v := by rw [mem_spos, h]; norm_num
        rw [heq, mem_spos] at hni
        exact absurd h' hni
      · have hv' : i ∈ spos v := mem_spos.mpr h
        rw [heq, mem_spos, h'] at hv'
        norm_num at hv'
    -- pigeonhole: four distinct 2-subsets land in three complement classes
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (s := S) (n := 4) (by omega)
    obtain ⟨x, hxT, y, hyT, hxy, hpc⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := T) (t := (Finset.univ : Finset (Fin 3))) (f := fun w => pairClass (spos w))
        (by simp [hT]) (fun w _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    have hxS : x ∈ S := hTS hxT
    have hyS : y ∈ S := hTS hyT
    have hsne : spos x ≠ spos y := fun h => hxy (hinj _ hxS _ hyS h)
    have hdisj : spos x ∩ spos y = ∅ :=
      pairClass_eq_disjoint _ _ (hterm0 x hxS) (hterm0 y hyS) hsne hpc
    exact hint x hxS y hyS hxy (Finset.disjoint_iff_inter_eq_empty.mpr hdisj)
  · -- Case B: some member has a zero coordinate
    push_neg at hall
    obtain ⟨v₀, hv₀S, z, hv₀z⟩ := hall
    have hdisjps : ∀ w : Fin 4 → ℚ, Disjoint (spos w) (sneg w) := by
      intro w
      rw [Finset.disjoint_left]
      intro k hk hk'
      rw [mem_spos] at hk
      rw [mem_sneg] at hk'
      rw [hk] at hk'
      norm_num at hk'
    -- every member has at least two positive coordinates
    have hcard2 : ∀ v ∈ S, 2 ≤ (spos v).card := by
      intro v hv
      by_contra hlt
      push_neg at hlt
      obtain ⟨k, hk⟩ := hposne v hv
      have h1 : (spos v).card = 1 :=
        le_antisymm (by omega) (Finset.card_pos.mpr ⟨k, mem_spos.mpr hk⟩)
      obtain ⟨k', hk'⟩ := Finset.card_eq_one.mp h1
      have hkk : k = k' := by
        have hkm := mem_spos.mpr hk
        rw [hk'] at hkm
        exact Finset.mem_singleton.mp hkm
      subst hkk
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
            have hl : l ∈ spos v := mem_spos.mpr h
            rw [hk', Finset.mem_singleton] at hl
            exact hlk hl
        exact sp3_kill S hsign hposne hnogm hno d hd hsum hv hmk hk hm hvn
      · -- full-support singleton-positive: balance at `k` kills directly
        push_neg at hzero
        have hnok : ∀ w ∈ S, w ≠ v → w k ≠ -1 := by
          intro w hw hwv hwk
          have hsub : spos v ⊆ sneg w := by
            rw [hk']
            rintro l hl
            rw [Finset.mem_singleton] at hl
            subst hl
            exact mem_sneg.mpr hwk
          have hnsub := hno v hv w hw (Ne.symm hwv) hsub
          rw [Finset.not_subset] at hnsub
          obtain ⟨m, hmw, hmv⟩ := hnsub
          rw [mem_spos] at hmw
          rw [mem_sneg] at hmv
          have hm1 : v m = 1 := by
            rcases hsign v hv m with h | h | h
            · exact absurd h hmv
            · exact absurd h (hzero m)
            · exact h
          have hmem : m ∈ spos v := mem_spos.mpr hm1
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
    -- the 𝟙-functional is nonnegative termwise and positive at `v₀`
    have hipw : ∀ w ∈ S, ip (fun _ => 1) w
        = ((spos w).card : ℚ) - ((sneg w).card : ℚ) := by
      intro w hw
      unfold ip
      simp only [one_mul]
      have hcov : (Finset.univ : Finset (Fin 4)) =
          (spos w ∪ sneg w) ∪ (Finset.univ \ (spos w ∪ sneg w)) := by
        rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
      rw [hcov, Finset.sum_union Finset.disjoint_sdiff, Finset.sum_union (hdisjps w)]
      have h0 : ∑ k ∈ Finset.univ \ (spos w ∪ sneg w), w k = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_union, mem_spos, mem_sneg] at hk
        rcases hsign w hw k with h | h | h
        · exact absurd h (fun f => hk.2 (Or.inr f))
        · exact h
        · exact absurd h (fun f => hk.2 (Or.inl f))
      have h1 : ∑ k ∈ spos w, w k = ((spos w).card : ℚ) := by
        rw [Finset.sum_congr rfl (fun k hk => mem_spos.mp hk)]
        simp
      have h2 : ∑ k ∈ sneg w, w k = -((sneg w).card : ℚ) := by
        rw [Finset.sum_congr rfl (fun k hk => mem_sneg.mp hk)]
        simp
      rw [h0, h1, h2]
      ring
    have hcsum : ∀ w : Fin 4 → ℚ, (spos w).card + (sneg w).card ≤ 4 := by
      intro w
      calc (spos w).card + (sneg w).card
          = (spos w ∪ sneg w).card := (Finset.card_union_of_disjoint (hdisjps w)).symm
        _ ≤ (Finset.univ : Finset (Fin 4)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = 4 := by simp
    have hone := ip_functional S d hsum (fun _ => 1)
    have hposS : 0 < ∑ w ∈ S, d w * ip (fun _ => 1) w := by
      apply Finset.sum_pos'
      · intro w hw
        apply mul_nonneg (le_of_lt (hd w hw))
        rw [hipw w hw]
        have hc2 : (2:ℚ) ≤ ((spos w).card : ℚ) := by exact_mod_cast hcard2 w hw
        have hc4 : ((spos w).card : ℚ) + ((sneg w).card : ℚ) ≤ 4 := by
          exact_mod_cast hcsum w
        linarith
      · refine ⟨v₀, hv₀S, ?_⟩
        apply mul_pos (hd v₀ hv₀S)
        rw [hipw v₀ hv₀S]
        have hc2 : (2:ℚ) ≤ ((spos v₀).card : ℚ) := by exact_mod_cast hcard2 v₀ hv₀S
        have hc3 : (spos v₀).card + (sneg v₀).card ≤ 3 := by
          have hz : z ∉ spos v₀ ∪ sneg v₀ := by
            simp only [Finset.mem_union, mem_spos, mem_sneg, hv₀z]
            norm_num
          calc (spos v₀).card + (sneg v₀).card
              = (spos v₀ ∪ sneg v₀).card :=
                (Finset.card_union_of_disjoint (hdisjps v₀)).symm
            _ ≤ (Finset.univ.erase z).card := Finset.card_le_card
                (fun k hk => Finset.mem_erase.mpr
                  ⟨fun he => hz (he ▸ hk), Finset.mem_univ _⟩)
            _ = 3 := by
                rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ,
                  Fintype.card_fin]
        have hc3' : ((spos v₀).card : ℚ) + ((sneg v₀).card : ℚ) ≤ 3 := by
          exact_mod_cast hc3
        linarith
    rw [hone] at hposS
    exact lt_irrefl 0 hposS

private theorem core_le5 (S : Finset (Fin 4 → ℚ))
    (hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (hposne : ∀ v ∈ S, ∃ i, v i = 1)
    (hcard : S.card ≤ 5)
    (hnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w)))
    (d : (Fin 4 → ℚ) → ℚ) (hd : ∀ v ∈ S, 0 < d v) (hSne : S.Nonempty)
    (hsum : ∑ v ∈ S, d v • v = 0) :
    ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ spos v ⊆ sneg w ∧ spos w ⊆ sneg v := by
  have hcard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  interval_cases hc : S.card
  · exact (core_card_one S hposne d hd hsum hc).elim
  · exact (core_card_two S hsign hnogm d hd hsum hc).elim
  · exact (core_card_three S hsign hnogm d hd hsum hc).elim
  · exact core_card_ge4 S hsign hposne hnogm d hd hsum (Or.inl hc)
  · exact core_card_ge4 S hsign hposne hnogm d hd hsum (Or.inr hc)


namespace Core.Scale

/-- **Add common context** (from Axiom A + the diff-cancellation): for `C` disjoint
    from both `X` and `Y`, `X ≿ Y ↔ (X ∪ C) ≿ (Y ∪ C)`. -/
lemma ge_union_context {n : ℕ} (sys : EpistemicSystemFA (Fin n)) (X Y C : Set (Fin n))
    (hCX : Disjoint C X) (hCY : Disjoint C Y) :
    sys.ge X Y ↔ sys.ge (X ∪ C) (Y ∪ C) := by
  rw [sys.additive X Y, sys.additive (X ∪ C) (Y ∪ C)]
  have hCXl : ∀ x, x ∈ C → x ∉ X := fun x hx => Set.disjoint_left.mp hCX hx
  have hCYl : ∀ x, x ∈ C → x ∉ Y := fun x hx => Set.disjoint_left.mp hCY hx
  have e1 : (X ∪ C) \ (Y ∪ C) = X \ Y := by
    ext x; simp only [Set.mem_diff, Set.mem_union]
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact ⟨hx, fun h => hn (Or.inl h)⟩
      · exact absurd (Or.inr hx) hn
    · rintro ⟨hxX, hxnY⟩
      exact ⟨Or.inl hxX, fun h => h.elim hxnY (fun hxC => hCXl x hxC hxX)⟩
  have e2 : (Y ∪ C) \ (X ∪ C) = Y \ X := by
    ext x; simp only [Set.mem_diff, Set.mem_union]
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact ⟨hx, fun h => hn (Or.inl h)⟩
      · exact absurd (Or.inr hx) hn
    · rintro ⟨hxY, hxnX⟩
      exact ⟨Or.inl hxY, fun h => h.elim hxnX (fun hxC => hCYl x hxC hxY)⟩
  rw [e1, e2]

/-- **Exchange lemma**: two valid disjoint comparisons merge into their union,
    provided the supports interleave disjointly. Holds in ANY de Finetti order
    (Axiom A twice + transitivity) — this is the derivable width-2 additivity. -/
lemma ge_exchange {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    {A₁ B₁ A₂ B₂ : Set (Fin n)}
    (h1 : sys.ge A₁ B₁) (h2 : sys.ge A₂ B₂)
    (hA₂A₁ : Disjoint A₂ A₁) (hA₂B₁ : Disjoint A₂ B₁) (hB₁B₂ : Disjoint B₁ B₂) :
    sys.ge (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  -- step1: add context A₂ to (A₁ ≿ B₁): A₁∪A₂ ≿ B₁∪A₂
  have step1 : sys.ge (A₁ ∪ A₂) (B₁ ∪ A₂) :=
    (ge_union_context sys A₁ B₁ A₂ hA₂A₁ hA₂B₁).mp h1
  -- step2: add context B₁ to (A₂ ≿ B₂): A₂∪B₁ ≿ B₂∪B₁
  have step2 : sys.ge (A₂ ∪ B₁) (B₂ ∪ B₁) :=
    (ge_union_context sys A₂ B₂ B₁ hA₂B₁.symm hB₁B₂).mp h2
  -- reconcile via commutativity, then transitivity through (B₁ ∪ A₂)
  rw [Set.union_comm A₂ B₁] at step2
  rw [Set.union_comm B₂ B₁] at step2
  exact sys.trans _ _ _ step1 step2

/-- **Generalized merge**: two valid comparisons whose left parts are disjoint and
    whose right parts are disjoint merge into their union — even with pivot overlaps
    (X₁∩Y₂, X₂∩Y₁ ≠ ∅). The width-2 additivity in full generality.
    Derivation: add context `X₂\Y₁` to the first and `Y₁\X₂` to the second, transit
    through `X₂∪Y₁`, then restore the pivot `P = X₂∩Y₁` via Axiom A. -/
lemma ge_generalized_merge {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    {X₁ Y₁ X₂ Y₂ : Set (Fin n)}
    (h1 : sys.ge X₁ Y₁) (h2 : sys.ge X₂ Y₂)
    (hX : Disjoint X₁ X₂) (hY : Disjoint Y₁ Y₂) :
    sys.ge (X₁ ∪ X₂) (Y₁ ∪ Y₂) := by
  have hXl : ∀ x, x ∈ X₁ → x ∉ X₂ := fun x hx => Set.disjoint_left.mp hX hx
  have hYl : ∀ x, x ∈ Y₂ → x ∉ Y₁ := fun x hy2 hy1 => Set.disjoint_left.mp hY hy1 hy2
  -- context C₁ = X₂ \ Y₁ added to (X₁ ≿ Y₁)
  have step1 : sys.ge (X₁ ∪ (X₂ \ Y₁)) (Y₁ ∪ (X₂ \ Y₁)) :=
    (ge_union_context sys X₁ Y₁ (X₂ \ Y₁)
      (Set.disjoint_left.mpr fun x hx hx1 => hXl x hx1 hx.1)
      (Set.disjoint_left.mpr fun x hx hxY1 => hx.2 hxY1)).mp h1
  -- context C₂ = Y₁ \ X₂ added to (X₂ ≿ Y₂)
  have step2 : sys.ge (X₂ ∪ (Y₁ \ X₂)) (Y₂ ∪ (Y₁ \ X₂)) :=
    (ge_union_context sys X₂ Y₂ (Y₁ \ X₂)
      (Set.disjoint_left.mpr fun x hx hx2 => hx.2 hx2)
      (Set.disjoint_left.mpr fun x hx hxY2 => hYl x hxY2 hx.1)).mp h2
  have hmid : Y₁ ∪ (X₂ \ Y₁) = X₂ ∪ (Y₁ \ X₂) := by
    ext x; simp only [Set.mem_union, Set.mem_diff]; tauto
  rw [hmid] at step1
  have htrans : sys.ge (X₁ ∪ (X₂ \ Y₁)) (Y₂ ∪ (Y₁ \ X₂)) := sys.trans _ _ _ step1 step2
  set P : Set (Fin n) := X₂ ∩ Y₁ with hP
  have hLHS : X₁ ∪ (X₂ \ Y₁) = (X₁ ∪ X₂) \ P := by
    ext x
    simp only [Set.mem_union, Set.mem_diff, hP, Set.mem_inter_iff, not_and]
    constructor
    · rintro (hx1 | ⟨hx2, hnY1⟩)
      · exact ⟨Or.inl hx1, fun hx2 _ => hXl x hx1 hx2⟩
      · exact ⟨Or.inr hx2, fun _ hY1 => hnY1 hY1⟩
    · rintro ⟨hx1 | hx2, hn⟩
      · exact Or.inl hx1
      · exact Or.inr ⟨hx2, fun hY1 => hn hx2 hY1⟩
  have hRHS : Y₂ ∪ (Y₁ \ X₂) = (Y₁ ∪ Y₂) \ P := by
    ext x
    simp only [Set.mem_union, Set.mem_diff, hP, Set.mem_inter_iff, not_and]
    constructor
    · rintro (hy2 | ⟨hy1, hnX2⟩)
      · exact ⟨Or.inr hy2, fun _ hY1 => hYl x hy2 hY1⟩
      · exact ⟨Or.inl hy1, fun hX2 _ => hnX2 hX2⟩
    · rintro ⟨hy1 | hy2, hn⟩
      · exact Or.inr ⟨hy1, fun hX2 => hn hX2 hy1⟩
      · exact Or.inl hy2
  rw [hLHS, hRHS] at htrans
  have hPsubX : P ⊆ X₁ ∪ X₂ := Set.inter_subset_left.trans Set.subset_union_right
  have hPsubY : P ⊆ Y₁ ∪ Y₂ := Set.inter_subset_right.trans Set.subset_union_left
  have key := (ge_union_context sys ((X₁ ∪ X₂) \ P) ((Y₁ ∪ Y₂) \ P) P
    (Set.disjoint_left.mpr fun x hxP hxd => hxd.2 hxP)
    (Set.disjoint_left.mpr fun x hxP hxd => hxd.2 hxP)).mp htrans
  rwa [Set.diff_union_of_subset hPsubX, Set.diff_union_of_subset hPsubY] at key

/-- **Mono-domination discharge**: a single valid comparison `X ≿ Y` with `X ⊆ P`
    and `Q ⊆ Y` proves `P ≿ Q` (monotonicity twice + transitivity). Used to discharge
    the merge-to-single target when one family member already dominates it. -/
lemma ge_mono_dominated {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    {X Y P Q : Set (Fin n)} (h : sys.ge X Y) (hXP : X ⊆ P) (hQY : Q ⊆ Y) :
    sys.ge P Q :=
  sys.trans _ _ _ (sys.mono X P hXP) (sys.trans _ _ _ h (sys.mono Q Y hQY))

/-- **Trivial-target discharge**: `P ≿ ∅` always (monotonicity, `∅ ⊆ P`). The
    merge-to-single base case when the target's negative part is empty. -/
lemma ge_empty_target {n : ℕ} (sys : EpistemicSystemFA (Fin n)) (P : Set (Fin n)) :
    sys.ge P ∅ :=
  sys.mono ∅ P (Set.empty_subset P)

/-! ### Merge-to-single infrastructure

A comparison is a pair of disjoint finsets `(pos, neg)`; its integer vector is
`1_pos − 1_neg ∈ {−1,0,1}ⁿ`. `mergeCmp` combines two comparisons whose pos-parts and
neg-parts are disjoint into the disjoint-normal-form of their vector sum. -/

/-- Integer comparison vector of a finset pair. -/
def cmpVec {n : ℕ} (c : Finset (Fin n) × Finset (Fin n)) (i : Fin n) : ℤ :=
  (if i ∈ c.1 then 1 else 0) - (if i ∈ c.2 then 1 else 0)

/-- Merge two comparisons into the disjoint normal form of their vector sum. -/
def mergeCmp {n : ℕ} (c d : Finset (Fin n) × Finset (Fin n)) :
    Finset (Fin n) × Finset (Fin n) :=
  ((c.1 ∪ d.1) \ (c.2 ∪ d.2), (c.2 ∪ d.2) \ (c.1 ∪ d.1))

/-- The merged comparison's vector is the sum of the two vectors, provided pos-parts
    are disjoint and neg-parts are disjoint (so no coordinate doubles). -/
lemma cmpVec_mergeCmp {n : ℕ} (c d : Finset (Fin n) × Finset (Fin n))
    (hpos : Disjoint c.1 d.1) (hneg : Disjoint c.2 d.2) (i : Fin n) :
    cmpVec (mergeCmp c d) i = cmpVec c i + cmpVec d i := by
  have h1 : i ∈ c.1 → i ∉ d.1 := fun h => Finset.disjoint_left.mp hpos h
  have h2 : i ∈ c.2 → i ∉ d.2 := fun h => Finset.disjoint_left.mp hneg h
  by_cases hc1 : i ∈ c.1 <;> by_cases hc2 : i ∈ c.2 <;>
    by_cases hd1 : i ∈ d.1 <;> by_cases hd2 : i ∈ d.2 <;>
    first
      | exact absurd hd1 (h1 hc1)
      | exact absurd hd2 (h2 hc2)
      | (simp only [cmpVec, mergeCmp, Finset.mem_sdiff, Finset.mem_union, hc1, hc2, hd1, hd2,
          true_or, or_true, false_or, or_false, true_and, and_true, false_and, and_false,
          not_true, not_false_iff, if_true, if_false] <;> omega)

/-- `mergeCmp` of two valid comparisons is valid, given the disjointness conditions.
    Uses `ge_generalized_merge` then Axiom A to reach disjoint normal form. -/
lemma mergeCmp_valid {n : ℕ} (sys : EpistemicSystemFA (Fin n))
    {c d : Finset (Fin n) × Finset (Fin n)}
    (hc : sys.ge ↑c.1 ↑c.2) (hd : sys.ge ↑d.1 ↑d.2)
    (hpos : Disjoint c.1 d.1) (hneg : Disjoint c.2 d.2) :
    sys.ge ↑(mergeCmp c d).1 ↑(mergeCmp c d).2 := by
  have hmerge : sys.ge (↑c.1 ∪ ↑d.1) (↑c.2 ∪ ↑d.2) :=
    ge_generalized_merge sys hc hd
      (by rwa [← Finset.disjoint_coe] at hpos)
      (by rwa [← Finset.disjoint_coe] at hneg)
  -- reduce to disjoint form via Axiom A
  rw [sys.additive (↑c.1 ∪ ↑d.1) (↑c.2 ∪ ↑d.2)] at hmerge
  have e1 : (↑c.1 ∪ ↑d.1 : Set (Fin n)) \ (↑c.2 ∪ ↑d.2) = ↑(mergeCmp c d).1 := by
    simp only [mergeCmp, Finset.coe_sdiff, Finset.coe_union]
  have e2 : (↑c.2 ∪ ↑d.2 : Set (Fin n)) \ (↑c.1 ∪ ↑d.1) = ↑(mergeCmp c d).2 := by
    simp only [mergeCmp, Finset.coe_sdiff, Finset.coe_union]
  rwa [e1, e2] at hmerge

/-- Pointwise integer vector-sum of a list of comparisons. -/
def cvSumList {n : ℕ} (L : List (Finset (Fin n) × Finset (Fin n))) (i : Fin n) : ℤ :=
  (L.map (fun c => cmpVec c i)).sum

@[simp] lemma cvSumList_nil {n : ℕ} (i : Fin n) :
    cvSumList ([] : List (Finset (Fin n) × Finset (Fin n))) i = 0 := rfl

@[simp] lemma cvSumList_cons {n : ℕ} (c : Finset (Fin n) × Finset (Fin n))
    (L : List (Finset (Fin n) × Finset (Fin n))) (i : Fin n) :
    cvSumList (c :: L) i = cmpVec c i + cvSumList L i := by
  simp only [cvSumList, List.map_cons, List.sum_cons]

lemma cvSumList_perm {n : ℕ} {L L' : List (Finset (Fin n) × Finset (Fin n))}
    (h : L.Perm L') (i : Fin n) : cvSumList L i = cvSumList L' i := by
  simp only [cvSumList]; exact (h.map _).sum_eq

/-- **Two-member null-forcing**: if two valid disjoint comparisons have vector-sum `≤ 0`
    everywhere with a strict negative coordinate, some atom is null (`ge ∅ {i}`).
    Disjointness forces `A ⊆ D` and `C ⊆ B`, giving `ge C A → ge C B → (Axiom A) ge ∅ (B\C)`
    and symmetrically `ge ∅ (D\A)`; the strict coordinate lies in one of them. -/
lemma null_from_pair (sys : EpistemicSystemFA (Fin 4))
    {A B C D : Finset (Fin 4)}
    (hAB : sys.ge ↑A ↑B) (hCD : sys.ge ↑C ↑D)
    (hABd : Disjoint A B) (hCDd : Disjoint C D)
    (hle : ∀ i, cmpVec (A, B) i + cmpVec (C, D) i ≤ 0)
    (i₀ : Fin 4) (hlt : cmpVec (A, B) i₀ + cmpVec (C, D) i₀ < 0) :
    ∃ i, sys.ge (∅ : Set (Fin 4)) {i} := by
  -- membership facts from disjointness
  have hAnB : ∀ x, x ∈ A → x ∉ B := fun x hx => Finset.disjoint_left.mp hABd hx
  have hCnD : ∀ x, x ∈ C → x ∉ D := fun x hx => Finset.disjoint_left.mp hCDd hx
  -- A ⊆ D and C ⊆ B
  have hAD : A ⊆ D := by
    intro a ha
    by_contra haD
    have := hle a
    simp only [cmpVec, if_pos ha, if_neg (hAnB a ha), if_neg haD, sub_zero] at this
    split_ifs at this <;> omega
  have hCB : C ⊆ B := by
    intro c hc
    by_contra hcB
    have := hle c
    simp only [cmpVec, if_pos hc, if_neg (hCnD c hc), if_neg hcB, sub_zero] at this
    split_ifs at this <;> omega
  -- ge C A, ge C B
  have hCA : sys.ge ↑C ↑A := sys.trans _ _ _ hCD (sys.mono ↑A ↑D (Finset.coe_subset.mpr hAD))
  have hCB_ge : sys.ge ↑C ↑B := sys.trans _ _ _ hCA hAB
  -- Axiom A: ge ∅ (B \ C)
  have hBC : sys.ge (∅ : Set (Fin 4)) ↑(B \ C) := by
    have hax := (sys.additive ↑C ↑B).mp hCB_ge
    have e1 : (↑C : Set (Fin 4)) \ ↑B = ∅ := by
      rw [← Finset.coe_sdiff, Finset.sdiff_eq_empty_iff_subset.mpr hCB, Finset.coe_empty]
    have e2 : (↑B : Set (Fin 4)) \ ↑C = ↑(B \ C) := by rw [Finset.coe_sdiff]
    rwa [e1, e2] at hax
  -- symmetric: ge A D, ge A C, ge A D? -> ge ∅ (D \ A)
  have hAC : sys.ge ↑A ↑C := sys.trans _ _ _ hAB (sys.mono ↑C ↑B (Finset.coe_subset.mpr hCB))
  have hAD_ge : sys.ge ↑A ↑D := sys.trans _ _ _ hAC hCD
  have hDA : sys.ge (∅ : Set (Fin 4)) ↑(D \ A) := by
    have hax := (sys.additive ↑A ↑D).mp hAD_ge
    have e1 : (↑A : Set (Fin 4)) \ ↑D = ∅ := by
      rw [← Finset.coe_sdiff, Finset.sdiff_eq_empty_iff_subset.mpr hAD, Finset.coe_empty]
    have e2 : (↑D : Set (Fin 4)) \ ↑A = ↑(D \ A) := by rw [Finset.coe_sdiff]
    rwa [e1, e2] at hax
  -- strict coordinate i₀ ∈ (B \ C) ∪ (D \ A)
  have hmem : i₀ ∈ B \ C ∨ i₀ ∈ D \ A := by
    simp only [cmpVec] at hlt
    by_cases hiA : i₀ ∈ A <;> by_cases hiB : i₀ ∈ B <;>
      by_cases hiC : i₀ ∈ C <;> by_cases hiD : i₀ ∈ D <;>
      simp only [hiA, hiB, hiC, hiD, if_true, if_false] at hlt <;>
      first
        | omega
        | (rw [Finset.mem_sdiff, Finset.mem_sdiff]; exact Or.inl ⟨hiB, hiC⟩)
        | (rw [Finset.mem_sdiff, Finset.mem_sdiff]; exact Or.inr ⟨hiD, hiA⟩)
  rcases hmem with hm | hm
  · exact ⟨i₀, sys.trans _ _ _ hBC (sys.mono {i₀} ↑(B \ C)
      (by rw [Set.singleton_subset_iff]; exact Finset.mem_coe.mpr hm))⟩
  · exact ⟨i₀, sys.trans _ _ _ hDA (sys.mono {i₀} ↑(D \ A)
      (by rw [Set.singleton_subset_iff]; exact Finset.mem_coe.mpr hm))⟩

/-! ### Bridging comparisons to ℚ sign vectors -/

/-- ℚ-valued sign vector of a comparison. -/
def toQVec (c : Finset (Fin 4) × Finset (Fin 4)) : Fin 4 → ℚ :=
  fun i => (cmpVec c i : ℚ)

lemma toQVec_apply (c : Finset (Fin 4) × Finset (Fin 4)) (k : Fin 4) :
    toQVec c k = (if k ∈ c.1 then (1 : ℚ) else 0) - (if k ∈ c.2 then 1 else 0) := by
  simp only [toQVec, cmpVec]
  split_ifs <;> norm_num

lemma spos_toQVec {c : Finset (Fin 4) × Finset (Fin 4)} (hc : Disjoint c.1 c.2) :
    spos (toQVec c) = c.1 := by
  ext k
  rw [mem_spos, toQVec_apply]
  by_cases h1 : k ∈ c.1 <;> by_cases h2 : k ∈ c.2
  · exact absurd h2 (Finset.disjoint_left.mp hc h1)
  · norm_num [h1, h2]
  · norm_num [h1, h2]
  · norm_num [h1, h2]

lemma sneg_toQVec {c : Finset (Fin 4) × Finset (Fin 4)} (hc : Disjoint c.1 c.2) :
    sneg (toQVec c) = c.2 := by
  ext k
  rw [mem_sneg, toQVec_apply]
  by_cases h1 : k ∈ c.1 <;> by_cases h2 : k ∈ c.2
  · exact absurd h2 (Finset.disjoint_left.mp hc h1)
  · norm_num [h1, h2]
  · norm_num [h1, h2]
  · norm_num [h1, h2]

lemma cmpVec_swap (A B : Finset (Fin 4)) (i : Fin 4) :
    cmpVec (B, A) i = -cmpVec (A, B) i := by
  simp only [cmpVec]
  ring

/-- Comparisons with both parts empty contribute nothing to the vector sum. -/
lemma cvSumList_filter_ne_empty (L : List (Finset (Fin 4) × Finset (Fin 4)))
    (h0 : ∀ c ∈ L, c.1 = ∅ → c.2 = ∅) (i : Fin 4) :
    cvSumList (L.filter (fun c => c.1 ≠ ∅)) i = cvSumList L i := by
  induction L with
  | nil => rfl
  | cons c rest ih =>
    have h0' : ∀ c' ∈ rest, c'.1 = ∅ → c'.2 = ∅ :=
      fun c' hc' => h0 c' (List.mem_cons_of_mem _ hc')
    by_cases hc : c.1 = ∅
    · have hc2 := h0 c (List.mem_cons.mpr (Or.inl rfl)) hc
      rw [List.filter_cons_of_neg (by simp [hc])]
      rw [cvSumList_cons, ih h0']
      have hz : cmpVec c i = 0 := by simp [cmpVec, hc, hc2]
      omega
    · rw [List.filter_cons_of_pos (by simp [hc])]
      rw [cvSumList_cons, cvSumList_cons, ih h0']

/-- **The (V1) consequence** the recursion needs (the combinatorial crux, isolated):
    a "stuck" family — no generalized-mergeable pair, no mono-dominating member,
    summing to `(vpos, vneg)` with `vneg` nonempty — either contains a **null pair**
    (two members whose comparison vectors sum `≤ 0` with a strict negative coordinate)
    or has a member generalized-merged by the reversed target `(vneg, vpos)`.

    This is exactly (V1) applied to `L ∪ {(vneg, vpos)}` (balanced): (V1) yields a
    g-merge or anti-dom pair; an anti-dom pair inside `L` is a null pair, an anti-dom
    pair with the reversed target is mono-domination (excluded), a g-merge pair inside
    `L` is excluded by `hnogm`, leaving a g-merge with the reversed target.
    Verified true for all families (expert proof + exhaustive ≤5-circuit check). -/
lemma v1_tailored (sys : EpistemicSystemFA (Fin 4))
    (L : List (Finset (Fin 4) × Finset (Fin 4)))
    (hdisj : ∀ c ∈ L, Disjoint c.1 c.2)
    (hvalid : ∀ c ∈ L, sys.ge ↑c.1 ↑c.2)
    {vpos vneg : Finset (Fin 4)}
    (hvpvn : Disjoint vpos vneg)
    (hsum : ∀ i, cvSumList L i = cmpVec (vpos, vneg) i)
    (hne : vneg.Nonempty)
    (hnotdom : ∀ c ∈ L, c.1 ⊆ vpos → ¬ vneg ⊆ c.2)
    (hnogm : ¬ ∃ c d rest, L.Perm (c :: d :: rest) ∧ Disjoint c.1 d.1 ∧ Disjoint c.2 d.2) :
    (∃ c ∈ L, ∃ d ∈ L,
        (∀ i, cmpVec (c.1, c.2) i + cmpVec (d.1, d.2) i ≤ 0) ∧
        (∃ i, cmpVec (c.1, c.2) i + cmpVec (d.1, d.2) i < 0))
      ∨ (∃ c ∈ L, Disjoint vneg c.1 ∧ Disjoint vpos c.2) := by
  classical
  -- Step A: a member with empty positive part and nonempty negative part is
  -- itself a null pair
  by_cases hemp : ∃ c ∈ L, c.1 = ∅ ∧ c.2.Nonempty
  · obtain ⟨c, hcL, hc1, k, hk⟩ := hemp
    refine Or.inl ⟨c, hcL, c, hcL, fun i => ?_, k, ?_⟩
    · simp only [cmpVec, hc1, if_neg (Finset.notMem_empty i)]
      split_ifs <;> omega
    · simp only [cmpVec, hc1, if_neg (Finset.notMem_empty k), if_pos hk]
      omega
  -- Step B: the right disjunct as an escape hatch
  by_cases hrd : ∃ c ∈ L, Disjoint vneg c.1 ∧ Disjoint vpos c.2
  · exact Or.inr hrd
  have h0 : ∀ c ∈ L, c.1 = ∅ → c.2 = ∅ := by
    intro c hc h1
    by_contra h2
    exact hemp ⟨c, hc, h1, Finset.nonempty_iff_ne_empty.mpr h2⟩
  -- Step C: the balanced ℚ sign-vector family on `L′ ∪ {reversed target}`
  set L' := L.filter (fun c => c.1 ≠ ∅) with hL'
  set l : List (Fin 4 → ℚ) := ((vneg, vpos) :: L').map toQVec with hl
  set S : Finset (Fin 4 → ℚ) := l.toFinset with hS
  have hfil : ∀ i, cvSumList L' i = cvSumList L i := by
    intro i
    rw [hL']
    exact cvSumList_filter_ne_empty L h0 i
  have hmem_shape : ∀ v ∈ S, ∃ c, (c = (vneg, vpos) ∨ c ∈ L') ∧ toQVec c = v := by
    intro v hv
    rw [hS, List.mem_toFinset, hl, List.mem_map] at hv
    obtain ⟨c, hc, hcv⟩ := hv
    exact ⟨c, List.mem_cons.mp hc, hcv⟩
  have hdisj' : ∀ c, (c = (vneg, vpos) ∨ c ∈ L') → Disjoint c.1 c.2 := by
    rintro c (rfl | hc)
    · exact hvpvn.symm
    · exact hdisj c (List.mem_of_mem_filter hc)
  have hsign : ∀ v ∈ S, ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1 := by
    intro v hv i
    obtain ⟨c, _, rfl⟩ := hmem_shape v hv
    rw [toQVec_apply]
    split_ifs <;> norm_num
  have hposne : ∀ v ∈ S, ∃ i, v i = 1 := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := hmem_shape v hv
    rcases hc with rfl | hc
    · obtain ⟨k, hk⟩ := hne
      refine ⟨k, ?_⟩
      rw [toQVec_apply, if_pos hk, if_neg (Finset.disjoint_right.mp hvpvn hk)]
      norm_num
    · have hcL : c ∈ L := List.mem_of_mem_filter hc
      have hc1 : c.1 ≠ ∅ := by simpa using List.of_mem_filter hc
      obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hc1
      refine ⟨k, ?_⟩
      rw [toQVec_apply, if_pos hk, if_neg (Finset.disjoint_left.mp (hdisj c hcL) hk)]
      norm_num
  have hSne : S.Nonempty := by
    refine ⟨toQVec (vneg, vpos), ?_⟩
    rw [hS, List.mem_toFinset, hl]
    exact List.mem_map.mpr ⟨(vneg, vpos), List.mem_cons.mpr (Or.inl rfl), rfl⟩
  have hdQ : ∀ v ∈ S, 0 < ((l.count v : ℕ) : ℚ) := by
    intro v hv
    rw [hS, List.mem_toFinset] at hv
    exact_mod_cast List.count_pos_iff.mpr hv
  have hbal : ∑ v ∈ S, ((l.count v : ℕ) : ℚ) • v = 0 := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hc := Finset.sum_list_map_count l (fun v => v i)
    rw [hS]
    have he : ∀ v ∈ l.toFinset, ((l.count v : ℕ) : ℚ) * v i = l.count v • v i := by
      intro v _
      rw [nsmul_eq_mul]
    rw [Finset.sum_congr rfl he, ← hc, hl, List.map_map]
    simp only [Function.comp_def, List.map_cons, List.sum_cons]
    have hLs : (L'.map (fun c => toQVec c i)).sum = ((cvSumList L' i : ℤ) : ℚ) := by
      simp only [toQVec, cvSumList]
      rw [Int.cast_list_sum, List.map_map]
      rfl
    rw [hLs, hfil i, hsum i]
    simp only [toQVec]
    rw [cmpVec_swap]
    push_cast
    ring
  -- no-g-merge transfers to the vector family
  have hSnogm : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ¬(Disjoint (spos v) (spos w) ∧ Disjoint (sneg v) (sneg w)) := by
    rintro v hv w hw hvw ⟨hg1, hg2⟩
    obtain ⟨c, hc, rfl⟩ := hmem_shape v hv
    obtain ⟨c', hc', rfl⟩ := hmem_shape w hw
    rw [spos_toQVec (hdisj' c hc), spos_toQVec (hdisj' c' hc')] at hg1
    rw [sneg_toQVec (hdisj' c hc), sneg_toQVec (hdisj' c' hc')] at hg2
    rcases hc with rfl | hc <;> rcases hc' with rfl | hc'
    · exact hvw rfl
    · exact hrd ⟨c', List.mem_of_mem_filter hc', hg1, hg2⟩
    · exact hrd ⟨c, List.mem_of_mem_filter hc, hg1.symm, hg2.symm⟩
    · have hcc' : c ≠ c' := fun he => hvw (by rw [he])
      have hcL : c ∈ L := List.mem_of_mem_filter hc
      have hc'L : c' ∈ L := List.mem_of_mem_filter hc'
      have hp1 := List.perm_cons_erase hcL
      have hc'e : c' ∈ L.erase c := (List.mem_erase_of_ne (Ne.symm hcc')).mpr hc'L
      have hp2 := List.perm_cons_erase hc'e
      exact hnogm ⟨c, c', (L.erase c).erase c',
        hp1.trans (List.Perm.cons c hp2), hg1, hg2⟩
  -- Carathéodory pivot, then the finite core
  obtain ⟨S', hS'S, hS'ne, hS'card, d', hd', hsum'⟩ :=
    EpiCarath.exists_posdep_card_le_five S (fun v => ((l.count v : ℕ) : ℚ)) hdQ hSne hbal
  obtain ⟨v, hvS', w, hwS', hvw, had1, had2⟩ :=
    core_le5 S' (fun v hv => hsign v (hS'S hv)) (fun v hv => hposne v (hS'S hv))
      hS'card (fun v hv w hw => hSnogm v (hS'S hv) w (hS'S hw)) d' hd' hS'ne hsum'
  have hvS : v ∈ S := hS'S hvS'
  have hwS : w ∈ S := hS'S hwS'
  -- vector-level consequences of the anti-dominating pair
  have hps : ∀ i, v i = 1 → w i = -1 := fun i h => mem_sneg.mp (had1 (mem_spos.mpr h))
  have hps' : ∀ i, w i = 1 → v i = -1 := fun i h => mem_sneg.mp (had2 (mem_spos.mpr h))
  have hvle : ∀ i, v i + w i ≤ 0 := by
    intro i
    rcases hsign v hvS i with h1 | h1 | h1 <;> rcases hsign w hwS i with h2 | h2 | h2
    · rw [h1, h2]; norm_num
    · rw [h1, h2]; norm_num
    · rw [h1, h2]; norm_num
    · rw [h1, h2]; norm_num
    · rw [h1, h2]; norm_num
    · -- v = 0, w = 1: anti-domination forces v = -1, contradiction
      have hbad := hps' i h2
      rw [h1] at hbad
      norm_num at hbad
    · rw [h1, h2]; norm_num
    · -- v = 1, w = 0: anti-domination forces w = -1, contradiction
      have hbad := hps i h1
      rw [h2] at hbad
      norm_num at hbad
    · -- v = 1, w = 1: anti-domination forces w = -1, contradiction
      have hbad := hps i h1
      rw [h2] at hbad
      norm_num at hbad
  have hvstrict : ∃ i, v i + w i < 0 := by
    by_contra hall
    push_neg at hall
    have heq : ∀ i, w i = -v i := fun i =>
      le_antisymm (by have := hvle i; linarith) (by have := hall i; linarith)
    refine hSnogm v hvS w hwS hvw ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk'
      rw [mem_spos] at hk hk'
      rw [heq k, hk] at hk'
      norm_num at hk'
    · rw [Finset.disjoint_left]
      intro k hk hk'
      rw [mem_sneg] at hk hk'
      rw [heq k, hk] at hk'
      norm_num at hk'
  -- map the pair back to comparisons
  obtain ⟨c, hc, rfl⟩ := hmem_shape v hvS
  obtain ⟨c', hc', rfl⟩ := hmem_shape w hwS
  rcases hc with rfl | hc <;> rcases hc' with rfl | hc'
  · exact (hvw rfl).elim
  · -- the reversed target anti-dominated by `c'` is mono-domination, excluded
    exfalso
    have h1 : c'.1 ⊆ vpos := by
      have h := had2
      rw [spos_toQVec (hdisj' c' (Or.inr hc')),
        sneg_toQVec (hdisj' _ (Or.inl rfl))] at h
      exact h
    have h2 : vneg ⊆ c'.2 := by
      have h := had1
      rw [spos_toQVec (hdisj' _ (Or.inl rfl)),
        sneg_toQVec (hdisj' c' (Or.inr hc'))] at h
      exact h
    exact hnotdom c' (List.mem_of_mem_filter hc') h1 h2
  · exfalso
    have h1 : c.1 ⊆ vpos := by
      have h := had1
      rw [spos_toQVec (hdisj' c (Or.inr hc)),
        sneg_toQVec (hdisj' _ (Or.inl rfl))] at h
      exact h
    have h2 : vneg ⊆ c.2 := by
      have h := had2
      rw [spos_toQVec (hdisj' _ (Or.inl rfl)),
        sneg_toQVec (hdisj' c (Or.inr hc))] at h
      exact h
    exact hnotdom c (List.mem_of_mem_filter hc) h1 h2
  · -- both from `L`: the null pair
    refine Or.inl ⟨c, List.mem_of_mem_filter hc, c', List.mem_of_mem_filter hc',
      fun i => ?_, ?_⟩
    · have h := hvle i
      simp only [toQVec] at h
      exact_mod_cast h
    · obtain ⟨i, hi⟩ := hvstrict
      refine ⟨i, ?_⟩
      simp only [toQVec] at hi
      exact_mod_cast hi

/-- **Recombine** (case 4 of the merge recursion): if a member `c` is valid, the
    reversed target `r = (vneg, vpos)` generalized-merges `c` (`Disjoint vneg c.1`,
    `Disjoint vpos c.2`), and the residual target `t' = t − cmpVec c` — namely
    `(p, q)` with `p = (vpos \ c.1) ∪ (c.2 \ vneg)`, `q = (vneg \ c.2) ∪ (c.1 \ vpos)`
    — is provable (`ge p q`, the IH), then `ge vpos vneg`. Proved by merging `(p,q)`
    with `c` via `mergeCmp_valid`; the disjoint-normal-form is exactly `(vpos, vneg)`. -/
lemma recombine (sys : EpistemicSystemFA (Fin 4))
    (vpos vneg : Finset (Fin 4)) (c : Finset (Fin 4) × Finset (Fin 4))
    (hcd : Disjoint c.1 c.2) (hvv : Disjoint vpos vneg)
    (hrc1 : Disjoint vneg c.1) (hrc2 : Disjoint vpos c.2)
    (hc : sys.ge ↑c.1 ↑c.2)
    (hX : sys.ge ↑((vpos \ c.1) ∪ (c.2 \ vneg)) ↑((vneg \ c.2) ∪ (c.1 \ vpos))) :
    sys.ge ↑vpos ↑vneg := by
  set p := (vpos \ c.1) ∪ (c.2 \ vneg) with hp
  set q := (vneg \ c.2) ∪ (c.1 \ vpos) with hq
  have dvv : ∀ x, x ∈ vpos → x ∉ vneg := fun x h => Finset.disjoint_left.mp hvv h
  have dvc1 : ∀ x, x ∈ vneg → x ∉ c.1 := fun x h => Finset.disjoint_left.mp hrc1 h
  have dvc2 : ∀ x, x ∈ vpos → x ∉ c.2 := fun x h => Finset.disjoint_left.mp hrc2 h
  have dc : ∀ x, x ∈ c.1 → x ∉ c.2 := fun x h => Finset.disjoint_left.mp hcd h
  have hdp : Disjoint p c.1 := by
    rw [Finset.disjoint_left]; intro x hxp hxc1
    rw [hp, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hxp
    rcases hxp with ⟨_, hn⟩ | ⟨hxc2, _⟩
    · exact hn hxc1
    · exact dc x hxc1 hxc2
  have hdq : Disjoint q c.2 := by
    rw [Finset.disjoint_left]; intro x hxq hxc2
    rw [hq, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at hxq
    rcases hxq with ⟨_, hn⟩ | ⟨hxc1, _⟩
    · exact hn hxc2
    · exact dc x hxc1 hxc2
  have hmerge := mergeCmp_valid sys (c := (p, q)) (d := c) hX hc hdp hdq
  have e1 : (mergeCmp (p, q) c).1 = vpos := by
    apply Finset.ext; intro x
    have h1 := dvv x; have h2 := dvc1 x; have h3 := dvc2 x; have h4 := dc x
    simp only [mergeCmp, hp, hq, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have e2 : (mergeCmp (p, q) c).2 = vneg := by
    apply Finset.ext; intro x
    have h1 := dvv x; have h2 := dvc1 x; have h3 := dvc2 x; have h4 := dc x
    simp only [mergeCmp, hp, hq, Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [e1, e2] at hmerge
  exact hmerge

/-- **Merge-to-single**: on a no-null Fin 4 system, any valid family of disjoint
    comparisons whose vector-sum equals a single comparison vector `(vpos, vneg)`
    proves `vpos ≿ vneg`. Four uniform rules: trivial target (`vneg = ∅`),
    mono-domination, merge a generalizable pair and recurse, or (no g-merge pair)
    `v1_tailored` gives a null pair (→ contradiction via `hnull`) or a member merged
    by the reversed target (→ peel it, recurse, `recombine`). -/
theorem merge_to_single (sys : EpistemicSystemFA (Fin 4))
    (hnull : ∀ i : Fin 4, ¬ sys.ge ∅ {i})
    (L : List (Finset (Fin 4) × Finset (Fin 4)))
    (hdisj : ∀ c ∈ L, Disjoint c.1 c.2)
    (hvalid : ∀ c ∈ L, sys.ge ↑c.1 ↑c.2)
    (vpos vneg : Finset (Fin 4))
    (hvpvn : Disjoint vpos vneg)
    (hsum : ∀ i, cvSumList L i = cmpVec (vpos, vneg) i) :
    sys.ge ↑vpos ↑vneg := by
  by_cases hne : vneg.Nonempty
  · by_cases hdom : ∃ c ∈ L, c.1 ⊆ vpos ∧ vneg ⊆ c.2
    · -- mono-domination discharge
      obtain ⟨c, hcL, hc1, hc2⟩ := hdom
      exact ge_mono_dominated sys (hvalid c hcL)
        (Finset.coe_subset.mpr hc1) (Finset.coe_subset.mpr hc2)
    · -- no mono-dominating member: either a gmerge pair (merge & recurse) or, failing
      -- that, a forced null atom contradicting `hnull`.
      push_neg at hdom
      by_cases hgm : ∃ c d rest, L.Perm (c :: d :: rest) ∧ Disjoint c.1 d.1 ∧ Disjoint c.2 d.2
      case neg =>
        rcases v1_tailored sys L hdisj hvalid hvpvn hsum hne hdom hgm with
          ⟨c, hcL, d, hdL, hle, i0, hlt⟩ | ⟨c, hcL, hrc1, hrc2⟩
        · -- null pair → null atom → contradicts hnull
          obtain ⟨i, hi⟩ := null_from_pair sys (hvalid c hcL) (hvalid d hdL)
            (hdisj c hcL) (hdisj d hdL) hle i0 hlt
          exact absurd hi (hnull i)
        · -- reversed target g-merges `c`: peel `c`, recurse on residual target, recombine
          have hperm := List.perm_cons_erase hcL
          have hsum' : ∀ i, cvSumList (L.erase c) i =
              cmpVec ((vpos \ c.1) ∪ (c.2 \ vneg), (vneg \ c.2) ∪ (c.1 \ vpos)) i := by
            intro i
            have h1 : cvSumList L i = cmpVec c i + cvSumList (L.erase c) i := by
              rw [cvSumList_perm hperm i, cvSumList_cons]
            have he : cvSumList (L.erase c) i = cmpVec (vpos, vneg) i - cmpVec c i := by
              have hh := hsum i; omega
            rw [he]
            have a1 : i ∈ vpos → i ∉ vneg := fun h => Finset.disjoint_left.mp hvpvn h
            have a2 : i ∈ vpos → i ∉ c.2 := fun h => Finset.disjoint_left.mp hrc2 h
            have a3 : i ∈ vneg → i ∉ c.1 := fun h => Finset.disjoint_left.mp hrc1 h
            have a4 : i ∈ c.1 → i ∉ c.2 := fun h => Finset.disjoint_left.mp (hdisj c hcL) h
            simp only [cmpVec, Finset.mem_union, Finset.mem_sdiff]
            by_cases h1v : i ∈ vpos <;> by_cases h2v : i ∈ vneg <;>
              by_cases h3v : i ∈ c.1 <;> by_cases h4v : i ∈ c.2 <;>
              simp_all <;> omega
          have hpq : Disjoint ((vpos \ c.1) ∪ (c.2 \ vneg)) ((vneg \ c.2) ∪ (c.1 \ vpos)) := by
            rw [Finset.disjoint_left]; intro x hxp hxq
            have a1 : x ∈ vpos → x ∉ vneg := fun h => Finset.disjoint_left.mp hvpvn h
            have a4 : x ∈ c.1 → x ∉ c.2 := fun h => Finset.disjoint_left.mp (hdisj c hcL) h
            simp only [Finset.mem_union, Finset.mem_sdiff] at hxp hxq
            tauto
          have hdisj' : ∀ x ∈ L.erase c, Disjoint x.1 x.2 :=
            fun x hx => hdisj x (List.mem_of_mem_erase hx)
          have hvalid' : ∀ x ∈ L.erase c, sys.ge ↑x.1 ↑x.2 :=
            fun x hx => hvalid x (List.mem_of_mem_erase hx)
          have IH := merge_to_single sys hnull (L.erase c) hdisj' hvalid'
            ((vpos \ c.1) ∪ (c.2 \ vneg)) ((vneg \ c.2) ∪ (c.1 \ vpos)) hpq hsum'
          exact recombine sys vpos vneg c (hdisj c hcL) hvpvn hrc1 hrc2 (hvalid c hcL) IH
      obtain ⟨c, d, rest, hperm, hpd, hnd⟩ := hgm
      -- new list: mergeCmp c d :: rest, one shorter
      have hcmem : c ∈ L := hperm.mem_iff.mpr (by simp)
      have hdmem : d ∈ L := hperm.mem_iff.mpr (by simp)
      have hrestsub : ∀ x ∈ rest, x ∈ L := fun x hx => hperm.mem_iff.mpr (by simp [hx])
      have hdisj' : ∀ x ∈ mergeCmp c d :: rest, Disjoint x.1 x.2 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [mergeCmp]; exact disjoint_sdiff_sdiff
        · exact hdisj x (hrestsub x hx)
      have hvalid' : ∀ x ∈ mergeCmp c d :: rest, sys.ge ↑x.1 ↑x.2 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact mergeCmp_valid sys (hvalid c hcmem) (hvalid d hdmem) hpd hnd
        · exact hvalid x (hrestsub x hx)
      have hsum' : ∀ i, cvSumList (mergeCmp c d :: rest) i = cmpVec (vpos, vneg) i := by
        intro i
        rw [cvSumList_cons, cmpVec_mergeCmp c d hpd hnd i, ← hsum i,
            cvSumList_perm hperm i]
        simp only [cvSumList_cons]
        omega
      exact merge_to_single sys hnull (mergeCmp c d :: rest) hdisj' hvalid' vpos vneg hvpvn hsum'
  · -- trivial-target discharge: vneg = ∅
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simpa using ge_empty_target sys (↑vpos)
termination_by L.length
decreasing_by
  all_goals
    have h := hperm.length_eq
    simp only [List.length_cons] at h ⊢
    omega

/-! ### Denominator-clearing infrastructure

To turn a rational-weighted neutral portfolio into an integer-balanced list of unit
comparisons, multiply every weight by the common denominator `D` and replicate each
comparison `wc.weight·D` times. The helpers below compute the vector sum of such a
`flatMap`-of-`replicate` list and recover `D · weightedSum` after casting back to `ℚ`. -/

private lemma cvSumList_flatMap {n : ℕ} {α : Type*} (P : List α)
    (f : α → List (Finset (Fin n) × Finset (Fin n))) (i : Fin n) :
    cvSumList (P.flatMap f) i = (P.map (fun a => cvSumList (f a) i)).sum := by
  induction P with
  | nil => simp [cvSumList]
  | cons a P ih =>
    rw [List.flatMap_cons,
      show cvSumList (f a ++ List.flatMap f P) i
          = cvSumList (f a) i + cvSumList (List.flatMap f P) i by
        simp only [cvSumList, List.map_append, List.sum_append], ih,
      List.map_cons, List.sum_cons]

private lemma cvSumList_replicate {n : ℕ} (m : ℕ) (c : Finset (Fin n) × Finset (Fin n))
    (i : Fin n) : cvSumList (List.replicate m c) i = (m : ℤ) * cmpVec c i := by
  simp only [cvSumList, List.map_replicate, List.sum_replicate, nsmul_eq_mul]

private lemma weight_mul_den (q : ℚ) : q * (q.den : ℚ) = (q.num : ℚ) := by
  have h := Rat.num_div_den q
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [div_eq_iff hd] at h
  exact h.symm

private lemma den_prod_pos (P : List (WComparison 4)) :
    0 < (P.map (fun wc => wc.weight.den)).prod := by
  induction P with
  | nil => simp
  | cons a P ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_pos a.weight.den_pos ih

/-- Casting the integer multiplicities back to `ℚ` recovers `D · weightedSum`. -/
private lemma cleared_sum_eq (P : Portfolio 4) (i : Fin 4) (D : ℕ)
    (mult : WComparison 4 → ℕ)
    (hcast : ∀ wc, List.Mem wc P → ((mult wc : ℤ) : ℚ) = wc.weight * (D : ℚ)) :
    (((P.map (fun wc => (mult wc : ℤ) * cmpVec (wc.left, wc.right) i)).sum : ℤ) : ℚ)
      = (D : ℚ) * P.weightedSum i := by
  rw [Portfolio.weightedSum]
  induction P with
  | nil => simp
  | cons a P ih =>
    have ha : List.Mem a (a :: P) := List.Mem.head P
    have hsub : ∀ wc, List.Mem wc P → ((mult wc : ℤ) : ℚ) = wc.weight * (D : ℚ) :=
      fun wc h => hcast wc (List.Mem.tail a h)
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
    rw [ih hsub, mul_add]
    congr 1
    rw [hcast a ha]
    show a.weight * ↑D * ↑(comparisonVec 4 a.left a.right i)
        = ↑D * (a.weight * ↑(comparisonVec 4 a.left a.right i))
    ring

/-- **Integer-balance bridge**: from a valid neutral portfolio `P` with a member `s`,
    clearing denominators yields a unit-weight list `R` of valid disjoint comparisons
    with `cvSumList R = cmpVec (s.right, s.left)` — the denominator-cleared balanced
    multiset with one copy of `s` removed. -/
theorem exists_balanced_list (sys : EpistemicSystemFA (Fin 4))
    (P : Portfolio 4) (hvalid : P.isValid sys.ge) (hneutral : P.isNeutral)
    (s : WComparison 4) (hsmem : List.Mem s P) :
    ∃ R : List (Finset (Fin 4) × Finset (Fin 4)),
      (∀ c ∈ R, Disjoint c.1 c.2) ∧ (∀ c ∈ R, sys.ge ↑c.1 ↑c.2) ∧
      (∀ i, cvSumList R i = cmpVec (s.right, s.left) i) := by
  set D : ℕ := (P.map (fun wc => wc.weight.den)).prod with hD
  have hDpos : 0 < D := hD ▸ den_prod_pos P
  have hdvd : ∀ wc, List.Mem wc P → wc.weight.den ∣ D := by
    intro wc hwc
    rw [hD]
    exact List.dvd_prod (by simp only [List.mem_map]; exact ⟨wc, hwc, rfl⟩)
  set mult : WComparison 4 → ℕ :=
    fun wc => (wc.weight.num * (D / wc.weight.den : ℕ)).toNat with hmult
  have hcast : ∀ wc, List.Mem wc P → ((mult wc : ℤ) : ℚ) = wc.weight * (D : ℚ) := by
    intro wc hwc
    obtain ⟨k, hk⟩ := hdvd wc hwc
    have hdk : D / wc.weight.den = k := by
      rw [hk]; exact Nat.mul_div_cancel_left k wc.weight.den_pos
    have hnumpos : 0 < wc.weight.num := Rat.num_pos.mpr wc.weight_pos
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h
      · rw [h0, Nat.mul_zero] at hk; omega
      · exact h
    have hmz : 0 ≤ wc.weight.num * (D / wc.weight.den : ℕ) := by
      rw [hdk]; positivity
    rw [hmult]
    simp only
    rw [Int.toNat_of_nonneg hmz, hdk]
    push_cast
    rw [hk]
    push_cast
    rw [← mul_assoc, weight_mul_den]
  have hmultpos : ∀ wc, List.Mem wc P → 1 ≤ mult wc := by
    intro wc hwc
    obtain ⟨k, hk⟩ := hdvd wc hwc
    have hdk : D / wc.weight.den = k := by
      rw [hk]; exact Nat.mul_div_cancel_left k wc.weight.den_pos
    have hnumpos : 0 < wc.weight.num := Rat.num_pos.mpr wc.weight_pos
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h
      · rw [h0, Nat.mul_zero] at hk; omega
      · exact h
    rw [hmult]
    simp only
    rw [hdk]
    have hp : 0 < wc.weight.num * (k : ℤ) := by positivity
    omega
  set Lfull : List (Finset (Fin 4) × Finset (Fin 4)) :=
    P.flatMap (fun wc => List.replicate (mult wc) (wc.left, wc.right)) with hLfull
  have hmemLfull : ∀ c, c ∈ Lfull → ∃ wc, List.Mem wc P ∧ c = (wc.left, wc.right) := by
    intro c hc
    rw [hLfull, List.mem_flatMap] at hc
    obtain ⟨wc, hwc, hc⟩ := hc
    exact ⟨wc, hwc, List.eq_of_mem_replicate hc⟩
  have hLdisj : ∀ c ∈ Lfull, Disjoint c.1 c.2 := by
    intro c hc
    obtain ⟨wc, _, rfl⟩ := hmemLfull c hc
    exact wc.disjoint
  have hLvalid : ∀ c ∈ Lfull, sys.ge ↑c.1 ↑c.2 := by
    intro c hc
    obtain ⟨wc, hwc, rfl⟩ := hmemLfull c hc
    exact hvalid wc hwc
  have hLsum : ∀ i, cvSumList Lfull i = 0 := by
    intro i
    have hstep : cvSumList Lfull i =
        (P.map (fun wc => (mult wc : ℤ) * cmpVec (wc.left, wc.right) i)).sum := by
      rw [hLfull, cvSumList_flatMap]
      congr 1
      apply List.map_congr_left
      intro wc _
      rw [cvSumList_replicate]
    have hcastsum : ((cvSumList Lfull i : ℤ) : ℚ) = (D : ℚ) * P.weightedSum i := by
      rw [hstep]; exact cleared_sum_eq P i D mult hcast
    have hzero : ((cvSumList Lfull i : ℤ) : ℚ) = 0 := by
      rw [hcastsum, hneutral i, mul_zero]
    exact_mod_cast hzero
  have hsLfull : (s.left, s.right) ∈ Lfull := by
    rw [hLfull, List.mem_flatMap]
    exact ⟨s, hsmem, List.mem_replicate.mpr ⟨by have := hmultpos s hsmem; omega, rfl⟩⟩
  refine ⟨Lfull.erase (s.left, s.right), ?_, ?_, ?_⟩
  · intro c hc
    exact hLdisj c (List.mem_of_mem_erase hc)
  · intro c hc
    exact hLvalid c (List.mem_of_mem_erase hc)
  · intro i
    have hperm := List.perm_cons_erase hsLfull
    have h1 : cvSumList Lfull i
        = cmpVec (s.left, s.right) i + cvSumList (Lfull.erase (s.left, s.right)) i := by
      rw [cvSumList_perm hperm i, cvSumList_cons]
    have h2 : cvSumList (Lfull.erase (s.left, s.right)) i = - cmpVec (s.left, s.right) i := by
      have := hLsum i; omega
    rw [h2]
    simp only [cmpVec]
    split_ifs <;> omega

/-- **No-null case** of Theorem 8a (Fin 4): when no atom is null, every valid neutral
    portfolio is non-strict, via the merge reduction `merge_to_single`. -/
theorem no_null_cancellation (sys : EpistemicSystemFA (Fin 4))
    (hnull : ∀ i : Fin 4, ¬ sys.ge ∅ {i}) :
    Cancellation 4 sys.ge := by
  intro P hvalid hneutral hstrict
  obtain ⟨s, hsmem, hsstrict⟩ := hstrict
  apply hsstrict
  obtain ⟨R, hRdisj, hRvalid, hRsum⟩ := exists_balanced_list sys P hvalid hneutral s hsmem
  exact merge_to_single sys hnull R hRdisj hRvalid s.right s.left s.disjoint.symm hRsum

/-- **Theorem 8a (Fin 4), structural**: every FA system on `Fin 4` satisfies
    cancellation. Null cases reduce to `Fin 3` (existing `null_elem_reduce` machinery);
    the no-null case is the merge reduction `no_null_cancellation`. Replaces the
    88-chamber `fa_cancellation_fin4`. -/
theorem fa_cancellation_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    Cancellation 4 sys.ge := by
  by_cases h0 : sys.ge ∅ {(0 : Fin 4)}
  · exact fa_cancellation_fin4_null0 sys h0 (by
      by_contra hall; push_neg at hall
      exact not_all_null_fin4 sys h0 (hall 0) (hall 1) (hall 2))
  · by_cases h1 : sys.ge ∅ {(1 : Fin 4)}
    · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 1) sys
        (null_elem_reduce (transportFA (Equiv.swap 0 1) sys)
          ((perm_null_convert _ _ 0 1 (by decide)).mpr h1)
          ⟨0, fun h => h0 ((perm_null_convert _ _ 1 0 (by decide)).mp h)⟩
          (fun sys' => theorem8a_fin3 sys'))
      exact representable_implies_cancellation sys m hm
    · by_cases h2 : sys.ge ∅ {(2 : Fin 4)}
      · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 2) sys
          (null_elem_reduce (transportFA (Equiv.swap 0 2) sys)
            ((perm_null_convert _ _ 0 2 (by decide)).mpr h2)
            ⟨0, fun h => h1 ((perm_null_convert _ _ 1 1 (by decide)).mp h)⟩
            (fun sys' => theorem8a_fin3 sys'))
        exact representable_implies_cancellation sys m hm
      · by_cases h3 : sys.ge ∅ {(3 : Fin 4)}
        · obtain ⟨m, hm⟩ := perm_repr (Equiv.swap 0 3) sys
            (null_elem_reduce (transportFA (Equiv.swap 0 3) sys)
              ((perm_null_convert _ _ 0 3 (by decide)).mpr h3)
              ⟨0, fun h => h1 ((perm_null_convert _ _ 1 1 (by decide)).mp h)⟩
              (fun sys' => theorem8a_fin3 sys'))
          exact representable_implies_cancellation sys m hm
        · exact no_null_cancellation sys (fun i => by fin_cases i <;> assumption)


/-- **Theorem 8a for Fin 4**: every FA system on 4 elements is representable.
    Via Scott cancellation — see `Cancellation.lean` for the framework. -/
theorem theorem8a_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  cancellation_implies_representable sys (fa_cancellation_fin4 sys)

end Core.Scale
