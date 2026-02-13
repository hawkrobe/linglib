import Linglib.Theories.TruthConditional.Sentence.Tense.TemporalConnectives
import Linglib.Fragments.English.TemporalExpressions

/-!
# Temporal Connective Truth-Condition Examples

Concrete scenarios verifying that the Anscombe and Rett formalizations
produce correct truth-value judgments for the scenario types in
Rett (2020) Table 1.

Each scenario defines a main eventuality (ME) and an embedded eventuality (EE)
as intervals over ℕ, then verifies that `Anscombe.before`/`after` and
`Rett.before`/`after` return the expected truth values.

## Scenarios (ℕ time points)

| # | ME       | EE                   | Connective | Result |
|---|----------|----------------------|------------|--------|
| 1 | point(1) | stative [5,10]       | before     | True   |
| 2 | point(12)| stative [5,10]       | after      | True   |
| 3 | point(1) | accomplishment [3,8] | before     | True   |
| 4 | point(12)| accomplishment [3,8] | after      | True   |
| 5 | point(7) | stative [5,10]       | before     | False  |
| 6 | point(7) | stative [5,10]       | after      | False  |

## References

- Rett, J. (2020). Eliminating EARLIEST. *Sinn und Bedeutung* 24, Table 1.
-/

namespace Phenomena.TemporalConnectives.Examples

open TruthConditional.Core.Time
open TruthConditional.Core.Time.Interval
open TruthConditional.Sentence.Tense.TemporalConnectives

-- ============================================================================
-- § 1: Concrete Intervals
-- ============================================================================

/-- ME: "John left" — punctual event at time 1 (early). -/
def me_early : Interval ℕ := Interval.point 1

/-- ME: "John left" — punctual event at time 12 (late). -/
def me_late : Interval ℕ := Interval.point 12

/-- ME: punctual event at time 7 (inside the stative EE). -/
def me_inside : Interval ℕ := Interval.point 7

/-- EE: "she was president" — stative, running [5, 10]. -/
def ee_stative : Interval ℕ :=
  { start := 5, finish := 10, valid := by omega }

/-- EE: "she climbed the mountain" — accomplishment, [3, 8]. -/
def ee_accomplishment : Interval ℕ :=
  { start := 3, finish := 8, valid := by omega }

-- Sentence denotations
abbrev A_early := accomplishmentDenotation me_early
abbrev A_late := accomplishmentDenotation me_late
abbrev A_inside := accomplishmentDenotation me_inside
abbrev B_stative := stativeDenotation ee_stative
abbrev B_telic := accomplishmentDenotation ee_accomplishment

/-- Rewriting lemma: membership in timeTrace of our stative denotation. -/
private theorem mem_tt_stative {t : ℕ} :
    t ∈ timeTrace B_stative ↔ 5 ≤ t ∧ t ≤ 10 := by
  rw [timeTrace_stativeDenotation]
  simp [contains, ee_stative]

/-- Rewriting lemma: membership in timeTrace of our telic denotation. -/
private theorem mem_tt_telic {t : ℕ} :
    t ∈ timeTrace B_telic ↔ 3 ≤ t ∧ t ≤ 8 := by
  rw [timeTrace_accomplishmentDenotation]
  simp [contains, ee_accomplishment]

/-- Rewriting lemma: membership in timeTrace of early ME. -/
private theorem mem_tt_early {t : ℕ} :
    t ∈ timeTrace A_early ↔ t = 1 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_early, Interval.point, Set.mem_setOf_eq]
  omega

/-- Rewriting lemma: membership in timeTrace of late ME. -/
private theorem mem_tt_late {t : ℕ} :
    t ∈ timeTrace A_late ↔ t = 12 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_late, Interval.point, Set.mem_setOf_eq]
  omega

/-- Rewriting lemma: membership in timeTrace of inside ME. -/
private theorem mem_tt_inside {t : ℕ} :
    t ∈ timeTrace A_inside ↔ t = 7 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_inside, Interval.point, Set.mem_setOf_eq]
  omega

-- ============================================================================
-- § 2: Scenario 1 — ME(1) before stative EE[5,10]
-- ============================================================================

/-- "John left₁ before she was president₅₋₁₀" — True under Anscombe.
    Witness: t = 1 ∈ ME, and 1 < all t' ∈ [5, 10]. -/
theorem scenario1_anscombe : Anscombe.before A_early B_stative := by
  refine ⟨1, mem_tt_early.mpr rfl, ?_⟩
  intro t' ht'
  exact Nat.lt_of_lt_of_le (by omega) (mem_tt_stative.mp ht').1

/-- "John left₁ before she was president₅₋₁₀" — True under Rett.
    Witness: t = 1, m = 5 (the GLB of [5, 10] on the ≺ scale). -/
theorem scenario1_rett : Rett.before A_early B_stative := by
  refine ⟨1, mem_tt_early.mpr rfl, 5, ⟨mem_tt_stative.mpr ⟨le_refl _, by omega⟩, ?_⟩, by omega⟩
  intro x' hx' hne
  have ⟨h1, _⟩ := mem_tt_stative.mp hx'
  omega

-- ============================================================================
-- § 3: Scenario 2 — ME(12) after stative EE[5,10]
-- ============================================================================

/-- "John left₁₂ after she was president₅₋₁₀" — True under Anscombe.
    Witness: t = 12, t' = 5 (any point in EE suffices). -/
theorem scenario2_anscombe : Anscombe.after A_late B_stative := by
  exact ⟨12, mem_tt_late.mpr rfl, 5, mem_tt_stative.mpr ⟨le_refl _, by omega⟩, by omega⟩

/-- "John left₁₂ after she was president₅₋₁₀" — True under Rett.
    Witness: t = 12, m = 10 (the LUB of [5, 10] on the ≻ scale). -/
theorem scenario2_rett : Rett.after A_late B_stative := by
  refine ⟨12, mem_tt_late.mpr rfl, 10, ⟨mem_tt_stative.mpr ⟨by omega, le_refl _⟩, ?_⟩, by omega⟩
  intro x' hx' hne
  have ⟨_, h2⟩ := mem_tt_stative.mp hx'
  omega

-- ============================================================================
-- § 4: Scenario 3 — ME(1) before accomplishment EE[3,8]
-- ============================================================================

/-- "John met Mary₁ before she climbed the mountain₃₋₈" — True under Anscombe.
    Witness: t = 1, and 1 < all t' in [3, 8]. -/
theorem scenario3_anscombe : Anscombe.before A_early B_telic := by
  refine ⟨1, mem_tt_early.mpr rfl, ?_⟩
  intro t' ht'
  have ⟨h1, _⟩ := mem_tt_telic.mp ht'
  omega

/-- "John met Mary₁ before she climbed the mountain₃₋₈" — True under Rett.
    Witness: t = 1, m = 3 (the GLB of [3, 8] on the ≺ scale). -/
theorem scenario3_rett : Rett.before A_early B_telic := by
  refine ⟨1, mem_tt_early.mpr rfl, 3, ⟨mem_tt_telic.mpr ⟨le_refl _, by omega⟩, ?_⟩, by omega⟩
  intro x' hx' hne
  have ⟨h1, _⟩ := mem_tt_telic.mp hx'
  omega

-- ============================================================================
-- § 5: Scenario 4 — ME(12) after accomplishment EE[3,8]
-- ============================================================================

/-- "John met Mary₁₂ after she climbed the mountain₃₋₈" — True under Anscombe.
    Witness: t = 12, t' = 3. -/
theorem scenario4_anscombe : Anscombe.after A_late B_telic := by
  exact ⟨12, mem_tt_late.mpr rfl, 3, mem_tt_telic.mpr ⟨le_refl _, by omega⟩, by omega⟩

/-- "John met Mary₁₂ after she climbed the mountain₃₋₈" — True under Rett.
    Witness: t = 12, m = 8 (the LUB of [3, 8] on the ≻ scale). -/
theorem scenario4_rett : Rett.after A_late B_telic := by
  refine ⟨12, mem_tt_late.mpr rfl, 8, ⟨mem_tt_telic.mpr ⟨by omega, le_refl _⟩, ?_⟩, by omega⟩
  intro x' hx' hne
  have ⟨_, h2⟩ := mem_tt_telic.mp hx'
  omega

-- ============================================================================
-- § 6: Negative scenarios — ME inside EE
-- ============================================================================

/-- "John left₇ before she was president₅₋₁₀" — False under Anscombe.
    Any witness t from ME (t=7) fails: t'=7 ∈ EE and ¬(7 < 7). -/
theorem scenario5_anscombe_false : ¬ Anscombe.before A_inside B_stative := by
  intro ⟨t, ht, hall⟩
  have := mem_tt_inside.mp ht
  subst this
  have h7 := hall 7 (mem_tt_stative.mpr ⟨by omega, by omega⟩)
  omega

/-- "John left₇ after she was president₅₋₁₀" — False under Rett.
    The max on the ≻ scale is 10, and ¬(7 > 10). -/
theorem scenario6_rett_false : ¬ Rett.after A_inside B_stative := by
  intro ⟨t, ht, m, ⟨hm_mem, hm_max⟩, hgt⟩
  have := mem_tt_inside.mp ht
  subst this
  have ⟨hm_lo, hm_hi⟩ := mem_tt_stative.mp hm_mem
  -- 7 > m means m < 7. But m must be maximal on ≻: ∀ x' ≠ m, m > x'.
  -- If m < 10, then 10 ∈ [5,10] and 10 ≠ m, so m > 10 — contradiction.
  -- If m = 10, then 7 > 10 is false.
  by_cases hm10 : m = 10
  · omega
  · have h10 := hm_max 10 (mem_tt_stative.mpr ⟨by omega, le_refl _⟩) (Ne.symm hm10)
    omega

-- ============================================================================
-- § 7: Theory Agreement on Concrete Scenarios
-- ============================================================================

/-- Both theories agree on scenario 1 (ME before stative EE). -/
theorem scenario1_agree : Anscombe.before A_early B_stative ∧
    Rett.before A_early B_stative :=
  ⟨scenario1_anscombe, scenario1_rett⟩

/-- Both theories agree on scenario 2 (ME after stative EE). -/
theorem scenario2_agree : Anscombe.after A_late B_stative ∧
    Rett.after A_late B_stative :=
  ⟨scenario2_anscombe, scenario2_rett⟩

/-- Both theories agree on scenario 3 (ME before accomplishment EE). -/
theorem scenario3_agree : Anscombe.before A_early B_telic ∧
    Rett.before A_early B_telic :=
  ⟨scenario3_anscombe, scenario3_rett⟩

/-- Both theories agree on scenario 4 (ME after accomplishment EE). -/
theorem scenario4_agree : Anscombe.after A_late B_telic ∧
    Rett.after A_late B_telic :=
  ⟨scenario4_anscombe, scenario4_rett⟩

-- ============================================================================
-- § 8: INCHOAT / COMPLET on Concrete Data
-- ============================================================================

/-- INCHOAT of "she was president₅₋₁₀" = {point(5)}.
    Verifies that inchoative coercion extracts the onset. -/
theorem inchoat_stative_ee :
    INCHOAT B_stative = { j | j = Interval.point 5 } :=
  inchoat_bridges_inception ee_stative

/-- COMPLET of "she climbed the mountain₃₋₈" = {point(8)}.
    Verifies that completive coercion extracts the telos. -/
theorem complet_telic_ee :
    COMPLET B_telic = { j | j = Interval.point 8 } :=
  complet_bridges_cessation ee_accomplishment

end Phenomena.TemporalConnectives.Examples
