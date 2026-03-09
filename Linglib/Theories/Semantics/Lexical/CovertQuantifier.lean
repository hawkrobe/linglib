import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

/-!
# Covert Quantifier — Shared GEN/HAB Infrastructure

@cite{krifka-etal-1995} @cite{carlson-1977}

GEN (over situations) and HAB (over occasions) are both covert quantifiers
with identical formal structure: universal quantification over a restricted
domain, with a threshold-based alternative that eliminates the hidden
restriction parameter.

This module captures the shared structure parametrically, so that
`traditionalGEN` and `traditionalHAB` are both instances.
-/

namespace Semantics.Lexical.CovertQuantifier

variable {D : Type}

/-- A covert quantifier: `∀d ∈ domain. restriction(d) → scope(d)`.
GEN instantiates with `D = Situation`, `restriction = normal ∧ restrictor`.
HAB instantiates with `D = Occasion`, `restriction = characteristic`. -/
def covertQ (domain : List D) (restriction : D → Bool) (scope : D → Bool) : Bool :=
  domain.all λ d => !restriction d || scope d

/-- Dual formulation: no counterexample exists. -/
def covertQ_dual (domain : List D) (restriction : D → Bool) (scope : D → Bool) : Bool :=
  !domain.any λ d => restriction d && !scope d

/-- The two formulations are equivalent (De Morgan). -/
theorem covertQ_equiv (domain : List D) (restriction : D → Bool) (scope : D → Bool) :
    covertQ domain restriction scope = covertQ_dual domain restriction scope := by
  simp only [covertQ, covertQ_dual, List.all_eq_not_any_not]
  congr 1
  induction domain with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.any_cons]
    rw [ih]
    cases restriction d <;> cases scope d <;> rfl

/-- Measure: proportion of restriction-satisfying cases where scope holds. -/
def measure (domain : List D) (restriction : D → Bool) (scope : D → Bool) : ℚ :=
  let restricted := domain.filter restriction
  let satisfied := restricted.filter scope
  if restricted.length = 0 then 0
  else (satisfied.length : ℚ) / (restricted.length : ℚ)

/-- Threshold-based alternative: measure > θ. -/
def thresholdQ (domain : List D) (restriction : D → Bool)
    (scope : D → Bool) (θ : ℚ) : Bool :=
  measure domain restriction scope > θ

/-- Measure is non-negative. -/
theorem measure_nonneg (domain : List D) (restriction : D → Bool) (scope : D → Bool) :
    measure domain restriction scope ≥ 0 := by
  simp only [measure]
  by_cases h : (domain.filter restriction).length = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _

/-- Measure is at most 1 (when restriction domain is non-empty). -/
theorem measure_le_one (domain : List D) (restriction : D → Bool) (scope : D → Bool)
    (hNonEmpty : (domain.filter restriction).length > 0) :
    measure domain restriction scope ≤ 1 := by
  simp only [measure]
  have hPos : (domain.filter restriction).length ≠ 0 := Nat.pos_iff_ne_zero.mp hNonEmpty
  simp only [hPos, ↓reduceIte]
  have hLenLe : (List.filter scope (List.filter restriction domain)).length ≤
                (List.filter restriction domain).length :=
    List.length_filter_le _ _
  have hDenom : (0 : ℚ) < ↑(List.filter restriction domain).length := by
    rw [Nat.cast_pos]; exact hNonEmpty
  calc (↑(List.filter scope (List.filter restriction domain)).length : ℚ) /
         ↑(List.filter restriction domain).length
       ≤ ↑(List.filter restriction domain).length /
         ↑(List.filter restriction domain).length := by
           apply div_le_div_of_nonneg_right
           · exact Nat.cast_le.mpr hLenLe
           · exact le_of_lt hDenom
     _ = 1 := div_self (ne_of_gt hDenom)

/-- Any covert quantifier configuration can be matched by threshold semantics.

    Note: this is a *degeneracy* result — the existential threshold is either -1
    (if Q holds) or 1 (if Q fails). It shows eliminability in principle, not that
    the threshold is informative. The RSA treatment adds substance by making the
    threshold uncertain and pragmatically inferred. -/
theorem reduces_to_threshold (domain : List D)
    (restriction : D → Bool) (scope : D → Bool)
    (hNonEmpty : (domain.filter restriction).length > 0) :
    ∃ θ : ℚ, covertQ domain restriction scope =
             thresholdQ domain restriction scope θ := by
  let m := measure domain restriction scope
  by_cases hQ : covertQ domain restriction scope
  · -- Q = true: pick θ = -1
    use -1
    simp only [thresholdQ, hQ]
    have hNonneg := measure_nonneg domain restriction scope
    symm; rw [decide_eq_true_iff]
    have h : (-1 : ℚ) < 0 := by decide
    linarith
  · -- Q = false: pick θ = 1
    use 1
    simp only [thresholdQ]
    have hLe := measure_le_one domain restriction scope hNonEmpty
    have hNotQ : covertQ domain restriction scope = false := by
      simp only [Bool.eq_false_iff]; exact hQ
    simp only [hNotQ]
    symm; rw [decide_eq_false_iff_not]
    intro hContra; linarith

end Semantics.Lexical.CovertQuantifier
