import Linglib.Core.Data.Multiset.Dominates
import Mathlib.Data.Fintype.BigOperators

/-!
# Informativity profiles

The combinatorial shadow of a finite Boolean RSA model: for a meaning `sem : C → Finset T`
assigning each choice its extension, the profile of a state is the multiset of extension
sizes of the choices true there, and the fibre profile keeps the choices heard as a given
form under `obs : C → O`. The classical speaker's masses are ratios of inverse-power sums
over these multisets (`Linglib.Pragmatics.RSA.Classical`), so preference certificates are
`Multiset.StrictDominates` facts and pinned-rationality comparisons are ℕ inequalities.

## Main definitions

* `RSA.profile`, `RSA.fiberProfile`, `RSA.restProfile` — extension-size multisets.
* `RSA.pooledDivPowSum` — the ℕ-cleared production mass of a choice pooled over its true
  states.

## Main results

* `RSA.invPowSum_odds_lt_of_prodMul_strictDominates` — strict dominance of fibre-by-rest
  products decides the odds comparison uniformly in the exponent.
-/

open scoped ENNReal

namespace RSA

variable {T C O : Type*} [Fintype C] [DecidableEq T] (sem : C → Finset T)

/-- The choices true at a state. -/
def trueChoices (t : T) : Finset C := Finset.univ.filter (t ∈ sem ·)

/-- The informativity profile: extension sizes of the true choices. -/
def profile (t : T) : Multiset ℕ := (trueChoices sem t).val.map fun c => (sem c).card

variable [DecidableEq O] (obs : C → O)

/-- The profile restricted to choices heard as `o`. -/
def fiberProfile (o : O) (t : T) : Multiset ℕ :=
  ((trueChoices sem t).filter (obs · = o)).val.map fun c => (sem c).card

/-- The profile of true choices heard otherwise. -/
def restProfile (o : O) (t : T) : Multiset ℕ :=
  ((trueChoices sem t).filter (obs · ≠ o)).val.map fun c => (sem c).card

theorem profile_eq_fiberProfile_add_restProfile (o : O) (t : T) :
    profile sem t = fiberProfile sem obs o t + restProfile sem obs o t := by
  rw [fiberProfile, restProfile, ← Multiset.map_add, profile]
  congr 1
  rw [Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]

theorem zero_notMem_profile (t : T) : 0 ∉ profile sem t := by
  simp only [profile, Multiset.mem_map, not_exists, not_and]
  intro c hc hcard
  rw [Finset.mem_val, trueChoices, Finset.mem_filter] at hc
  exact Finset.card_ne_zero_of_mem hc.2 hcard

theorem zero_notMem_fiberProfile (o : O) (t : T) : 0 ∉ fiberProfile sem obs o t := fun h =>
  zero_notMem_profile sem t
    (profile_eq_fiberProfile_add_restProfile sem obs o t ▸ Multiset.mem_add.mpr (Or.inl h))

theorem zero_notMem_restProfile (o : O) (t : T) : 0 ∉ restProfile sem obs o t := fun h =>
  zero_notMem_profile sem t
    (profile_eq_fiberProfile_add_restProfile sem obs o t ▸ Multiset.mem_add.mpr (Or.inr h))

/-- A nonempty fibre profile exhibits an `o`-shaped true choice — certificates carry their
own truth witnesses. -/
theorem exists_of_fiberProfile_ne_zero {o : O} {t : T} (h : fiberProfile sem obs o t ≠ 0) :
    ∃ c, obs c = o ∧ t ∈ sem c := by
  rw [fiberProfile, ne_eq, Multiset.map_eq_zero, Finset.val_eq_zero, ← ne_eq,
    ← Finset.nonempty_iff_ne_empty] at h
  obtain ⟨c, hc⟩ := h
  rw [Finset.mem_filter, trueChoices, Finset.mem_filter] at hc
  exact ⟨c, hc.2, hc.1.2⟩

theorem profile_ne_zero (hsem : ∀ t, ∃ c, t ∈ sem c) (t : T) : profile sem t ≠ 0 := by
  obtain ⟨c, hc⟩ := hsem t
  intro h
  rw [profile, Multiset.map_eq_zero, Finset.val_eq_zero] at h
  exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩) (h ▸ Finset.notMem_empty c)

/-- The certificate closes the odds comparison: strict domination of the fibre-by-rest cross
products decides it uniformly in the rationality (the shared fibre-by-fibre terms cancel). -/
theorem invPowSum_odds_lt_of_prodMul_strictDominates {α : ℝ} (hα : 0 < α) {o : O} {t₁ t₂ : T}
    (hcert : ((fiberProfile sem obs o t₂).prodMul (restProfile sem obs o t₁)).StrictDominates
      ((fiberProfile sem obs o t₁).prodMul (restProfile sem obs o t₂))) :
    ((fiberProfile sem obs o t₁).invPowSum α).toReal * ((profile sem t₂).invPowSum α).toReal
      < ((fiberProfile sem obs o t₂).invPowSum α).toReal
          * ((profile sem t₁).invPowSum α).toReal := by
  have hWne : ∀ t, (fiberProfile sem obs o t).invPowSum α ≠ ∞ := fun t =>
    Multiset.invPowSum_ne_top hα.le (zero_notMem_fiberProfile sem obs o t)
  have hodds : (fiberProfile sem obs o t₁).invPowSum α * (restProfile sem obs o t₂).invPowSum α
      < (fiberProfile sem obs o t₂).invPowSum α * (restProfile sem obs o t₁).invPowSum α := by
    rw [← Multiset.invPowSum_prodMul hα.le, ← Multiset.invPowSum_prodMul hα.le]
    exact hcert.invPowSum_lt hα
      (Multiset.zero_notMem_prodMul (zero_notMem_fiberProfile sem obs o t₁)
        (zero_notMem_restProfile sem obs o t₂))
  rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul,
    ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (hWne t₁)
        (Multiset.invPowSum_ne_top hα.le (zero_notMem_profile sem t₂)))
      (ENNReal.mul_ne_top (hWne t₂)
        (Multiset.invPowSum_ne_top hα.le (zero_notMem_profile sem t₁))),
    profile_eq_fiberProfile_add_restProfile sem obs o t₁,
    profile_eq_fiberProfile_add_restProfile sem obs o t₂, Multiset.invPowSum_add,
    Multiset.invPowSum_add, mul_add, mul_add, mul_comm ((fiberProfile sem obs o t₂).invPowSum α)]
  exact ENNReal.add_lt_add_left (ENNReal.mul_ne_top (hWne t₁) (hWne t₂)) hodds

variable [Fintype T]

/-- The ℕ-cleared production mass of a choice, pooled over its true states: its
common-denominator weight times, per true state, the product of the other states' cleared
partition sums. Pooled evaluation-register hypotheses compare these. -/
def pooledDivPowSum (D k : ℕ) (c : C) : ℕ :=
  (D / (sem c).card) ^ k
    * ∑ t ∈ sem c, ∏ t' ∈ Finset.univ.erase t, (profile sem t').divPowSum D k

theorem pooledDivPowSum_eq_sum (D k : ℕ) (c : C) :
    pooledDivPowSum sem D k c
      = ∑ t : T, if t ∈ sem c then
          (D / (sem c).card) ^ k * ∏ t' ∈ Finset.univ.erase t, (profile sem t').divPowSum D k
        else 0 := by
  rw [pooledDivPowSum, Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]

end RSA
