import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith

/-! # Conic Carathéodory: thinning positive dependences

A *positive dependence* on a finite set of vectors — strictly positive weights
summing the vectors to zero — can be thinned to one supported on at most
`finrank + 1` of them.  This is the conic counterpart of Carathéodory's
theorem, proved by strong induction on the support cardinality with a single
linear pivot step that strictly shrinks the positive support each round.

## Main declarations

* `Caratheodory.exists_posdep_card_le_finrank_add_one` — the general bound
  over a linearly ordered field.
* `Caratheodory.exists_posdep_card_le_five` — the specialisation to
  `Fin 4 → ℚ` (bound `5`) consumed by the `Fin 4` cancellation proof.
-/

open Finset Module

namespace Caratheodory

variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E] [Module.Finite K E]

omit [Module.Finite K E] in
/-- **The pivot step.**  Given a positive dependence `c` on `s` together with a *linear
relation* `g` on `s` that is positive somewhere and zero at a marked element `v₀ ∈ s`
with `0 < c v₀`, produce a *strictly smaller* positive support `s'` carrying a positive
dependence, and with `s' ⊆ s`. -/
private theorem pivot (s : Finset E) (c : E → K)
    (hpos : ∀ v ∈ s, 0 < c v) (hcsum : ∑ v ∈ s, c v • v = 0)
    (g : E → K) (hgsum : ∑ v ∈ s, g v • v = 0)
    (v₀ : E) (hv₀ : v₀ ∈ s) (hgv₀ : g v₀ = 0)
    (w : E) (hw : w ∈ s) (hgw : 0 < g w) :
    ∃ s' ⊆ s, s'.card < s.card ∧ s'.Nonempty ∧
      ∃ d : E → K, (∀ v ∈ s', 0 < d v) ∧ ∑ v ∈ s', d v • v = 0 := by
  classical
  -- The set of vectors where `g` is positive: nonempty (`w`), and excludes `v₀`.
  set P := s.filter (fun v => 0 < g v)
  have hPne : P.Nonempty := ⟨w, mem_filter.2 ⟨hw, hgw⟩⟩
  have hPmem : ∀ {v}, v ∈ P ↔ v ∈ s ∧ 0 < g v := fun {v} => mem_filter
  -- Pivot ratio `t = min_{v ∈ P} c v / g v`, attained at some `v* ∈ P`.
  set t : K := P.inf' hPne (fun v => c v / g v) with ht
  obtain ⟨vstar, hvstarP, hvstar_eq⟩ := Finset.exists_mem_eq_inf' hPne (fun v => c v / g v)
  have hvstarV : vstar ∈ s := (hPmem.1 hvstarP).1
  have hgvstar : 0 < g vstar := (hPmem.1 hvstarP).2
  -- `t > 0`.
  have ht_pos : 0 < t := by
    rw [ht, Finset.lt_inf'_iff]
    exact fun v hv => div_pos (hpos v (hPmem.1 hv).1) (hPmem.1 hv).2
  -- The shifted coefficients.
  set d : E → K := fun v => c v - t * g v with hd
  -- `0 ≤ d v` for every `v ∈ s`.
  have hd_nonneg : ∀ v ∈ s, 0 ≤ d v := by
    intro v hv
    simp only [hd]
    rcases lt_or_ge 0 (g v) with hgvpos | hgvnonpos
    · -- `v ∈ P`, so `t ≤ c v / g v`, hence `t * g v ≤ c v`.
      have hle : t ≤ c v / g v := ht ▸ Finset.inf'_le _ (hPmem.2 ⟨hv, hgvpos⟩)
      rw [le_div_iff₀ hgvpos] at hle
      linarith
    · -- `g v ≤ 0`, so `t * g v ≤ 0 < c v`.
      have := mul_nonpos_of_nonneg_of_nonpos ht_pos.le hgvnonpos
      linarith [hpos v hv]
  -- `d vstar = 0`.
  have hd_vstar : d vstar = 0 := by
    simp only [hd, ht ▸ hvstar_eq]
    rw [div_mul_cancel₀ _ (ne_of_gt hgvstar), sub_self]
  -- The new positive support.
  set s' := s.filter (fun v => 0 < d v) with hs'
  have hs'sub : s' ⊆ s := filter_subset _ _
  -- `s'` omits `vstar` (where `d vstar = 0`), so it is a strict subset of `s`.
  have hs'_erase : s' ⊆ s.erase vstar := fun v hv => mem_erase.2
    ⟨fun h => hd_vstar.not_gt (h ▸ (mem_filter.1 hv).2), hs'sub hv⟩
  have hcard : s'.card < s.card :=
    card_lt_card (ssubset_iff_exists_subset_erase.2 ⟨vstar, hvstarV, hs'_erase⟩)
  -- `v₀ ∈ s'`: `d v₀ = c v₀ > 0` since `g v₀ = 0`.
  have hv₀s' : v₀ ∈ s' := by
    rw [hs', mem_filter]
    refine ⟨hv₀, ?_⟩
    simp only [hd, hgv₀, mul_zero, sub_zero]
    exact hpos v₀ hv₀
  -- `∀ v ∈ s', 0 < d v`.
  have hd_pos : ∀ v ∈ s', 0 < d v := fun v hv => (mem_filter.1 hv).2
  -- The zero-sum is preserved: dropped terms have `d v = 0`.
  have hsum' : ∑ v ∈ s', d v • v = 0 := by
    rw [hs', Finset.sum_filter_of_ne fun v hv hne => (hd_nonneg v hv).lt_or_eq.resolve_right
      fun heq => hne (by rw [← heq, zero_smul])]
    simp only [hd, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
      hcsum, hgsum, smul_zero, sub_zero]
  exact ⟨s', hs'sub, hcard, ⟨v₀, hv₀s'⟩, d, hd_pos, hsum'⟩

/-- **Conic Carathéodory.**  A positive dependence among finitely many vectors of a
finite-dimensional space over a linearly ordered field can be thinned to one
supported on at most `finrank + 1` of them. -/
theorem exists_posdep_card_le_finrank_add_one
    (s : Finset E) (c : E → K)
    (hpos : ∀ v ∈ s, 0 < c v) (hne : s.Nonempty)
    (hsum : ∑ v ∈ s, c v • v = 0) :
    ∃ t ⊆ s, t.Nonempty ∧ t.card ≤ finrank K E + 1 ∧
      ∃ d : E → K, (∀ v ∈ t, 0 < d v) ∧ ∑ v ∈ t, d v • v = 0 := by
  classical
  -- Strong induction on the cardinality of the support.
  induction hn : s.card using Nat.strong_induction_on generalizing s c with
  | _ n ih =>
    subst hn
    rcases le_or_gt s.card (finrank K E + 1) with hsmall | hbig
    · -- Base case: already small enough.
      exact ⟨s, subset_rfl, hne, hsmall, c, hpos, hsum⟩
    · -- Inductive step: pivot to a strictly smaller support.
      obtain ⟨v₀, hv₀⟩ := hne
      have hcard_erase : finrank K E < (s.erase v₀).card := by
        rw [card_erase_of_mem hv₀]
        omega
      -- A nontrivial relation on `s.erase v₀`.
      obtain ⟨g₀, hg₀sum, x, hxmem, hxne⟩ :=
        Module.exists_nontrivial_relation_of_finrank_lt_card hcard_erase
      have hx_ne_v₀ : x ≠ v₀ := (mem_erase.1 hxmem).1
      have hxV : x ∈ s := (mem_erase.1 hxmem).2
      -- Extend `g₀` by zero at `v₀`, so the relation lives on all of `s`.
      set g : E → K := fun v => if v = v₀ then 0 else g₀ v with hg
      have hgv₀ : g v₀ = 0 := by simp [hg]
      have hgxne : g x ≠ 0 := by simpa [hg, hx_ne_v₀] using hxne
      -- The extended relation still sums to zero over `s`.
      have hgsum : ∑ v ∈ s, g v • v = 0 := by
        rw [← Finset.sum_erase_add s _ hv₀, hgv₀, zero_smul, add_zero, ← hg₀sum]
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [hg]; simp [(mem_erase.1 hv).1]
      -- WLOG `g` is positive somewhere on `s` (negate if necessary).
      obtain ⟨g', hg'sum, hg'v₀, hg'x⟩ :
          ∃ g' : E → K, ∑ v ∈ s, g' v • v = 0 ∧ g' v₀ = 0 ∧ 0 < g' x := by
        rcases hgxne.lt_or_gt with hxneg | hxpos
        · exact ⟨fun v => -g v,
            by simp only [neg_smul, Finset.sum_neg_distrib, hgsum, neg_zero],
            by simp [hgv₀], by simpa using hxneg⟩
        · exact ⟨g, hgsum, hgv₀, hxpos⟩
      obtain ⟨s', hs'sub, hs'card, hs'ne, d, hd_pos, hd_sum⟩ :=
        pivot s c hpos hsum g' hg'sum v₀ hv₀ hg'v₀ x hxV hg'x
      obtain ⟨t, hts', htne, htcard, e, he_pos, he_sum⟩ :=
        ih s'.card hs'card s' d hd_pos hs'ne hd_sum rfl
      exact ⟨t, hts'.trans hs'sub, htne, htcard, e, he_pos, he_sum⟩

/-- Conic Carathéodory for `Fin 4 → ℚ`: a positive dependence thins to support `≤ 5`. -/
theorem exists_posdep_card_le_five
    (V : Finset (Fin 4 → ℚ)) (c : (Fin 4 → ℚ) → ℚ)
    (hpos : ∀ v ∈ V, 0 < c v) (hne : V.Nonempty)
    (hsum : ∑ v ∈ V, c v • v = 0) :
    ∃ S ⊆ V, S.Nonempty ∧ S.card ≤ 5 ∧
      ∃ d : (Fin 4 → ℚ) → ℚ, (∀ v ∈ S, 0 < d v) ∧ ∑ v ∈ S, d v • v = 0 := by
  simpa [Module.finrank_fin_fun] using
    exists_posdep_card_le_finrank_add_one V c hpos hne hsum

end Caratheodory
