import Linglib.Theories.Semantics.Tense.TemporalConnectives
import Linglib.Fragments.English.TemporalExpressions

/-!
# Temporal Connective Truth-Condition Examples

Concrete scenarios verifying that the Anscombe, Rett, and Karttunen
formalizations produce correct truth-value judgments.

Scenarios 1–6 verify Rett (2020) Table 1 for *before*/*after*.
Scenarios 7–10 verify Heinämäki (1974) Chs. 6, 8, 9 for *since*, *by*, *till*.

## Scenarios (ℕ time points)

| # | ME           | EE                   | Connective | Result |
|---|--------------|----------------------|------------|--------|
| 1 | point(1)     | stative [5,10]       | before     | True   |
| 2 | point(12)    | stative [5,10]       | after      | True   |
| 3 | point(1)     | accomplishment [3,8] | before     | True   |
| 4 | point(12)    | accomplishment [3,8] | after      | True   |
| 5 | point(7)     | stative [5,10]       | before     | False  |
| 6 | point(7)     | stative [5,10]       | after      | False  |
| 7 | stative[5,10]| point(5)             | since      | True   |
| 8 | point(1)     | point(3)             | by         | True   |
| 9 | point(3)     | point(3)             | by         | True   |
| 9'| point(3)     | point(3)             | before     | False  |
|10 | stative[5,10]| point(5)             | till       | True   |

## References

- Rett, J. (2020). Eliminating EARLIEST. *Sinn und Bedeutung* 24, Table 1.
- Heinämäki, O. (1974). *Semantics of English temporal connectives*. PhD.
-/

namespace Phenomena.TemporalConnectives.Examples

open Core.Time
open Core.Time.Interval
open Semantics.Tense.TemporalConnectives

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

-- ============================================================================
-- § 9: *Since*, *By*, *Till* on Concrete Data (Heinämäki 1974)
-- ============================================================================

/-- ME: stative [5, 10] — "He has been happy." -/
abbrev A_stative := stativeDenotation ee_stative

/-- EE: punctual event at time 5 — "she arrived." -/
def ee_onset : Interval ℕ := Interval.point 5
abbrev B_onset := accomplishmentDenotation ee_onset

/-- Rewriting lemma: membership in timeTrace of onset EE. -/
private theorem mem_tt_onset {t : ℕ} :
    t ∈ timeTrace B_onset ↔ t = 5 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, ee_onset, Interval.point, Set.mem_setOf_eq]
  omega

/-- ME: punctual event at time 3 — "arrived at 3pm" (for *by* coincidence case). -/
def me_at_deadline : Interval ℕ := Interval.point 3
abbrev A_at_deadline := accomplishmentDenotation me_at_deadline

/-- EE: punctual event at time 3 — "3pm" (deadline). -/
def ee_deadline : Interval ℕ := Interval.point 3
abbrev B_deadline := accomplishmentDenotation ee_deadline

/-- Rewriting lemma: membership in timeTrace of the at-deadline ME. -/
private theorem mem_tt_at_deadline {t : ℕ} :
    t ∈ timeTrace A_at_deadline ↔ t = 3 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, me_at_deadline, Interval.point, Set.mem_setOf_eq]
  omega

/-- Rewriting lemma: membership in timeTrace of the deadline EE. -/
private theorem mem_tt_deadline {t : ℕ} :
    t ∈ timeTrace B_deadline ↔ t = 3 := by
  rw [timeTrace_accomplishmentDenotation]
  simp only [contains, ee_deadline, Interval.point, Set.mem_setOf_eq]
  omega

/-- "He has been happy₅₋₁₀ since she arrived₅" — True under `Karttunen.since`.
    Witness: t = 5 ∈ B, and ∀t' ∈ A (i.e., 5 ≤ t' ≤ 10), 5 ≤ t'. -/
theorem scenario_since : Karttunen.since A_stative B_onset := by
  refine ⟨5, mem_tt_onset.mpr rfl, ?_⟩
  intro t' ht'
  exact (mem_tt_stative.mp ht').1

/-- *Since* is veridical for its complement in scenario: she arrived. -/
theorem scenario_since_veridical :
    Karttunen.since A_stative B_onset → ∃ t, t ∈ timeTrace B_onset :=
  since_veridical_complement _ _

/-- "He arrived₁ by 3pm₃" — True under `Karttunen.by_`.
    Witness: t = 1 ∈ A, and ∀t' ∈ B (t' = 3), 1 ≤ 3. -/
theorem scenario_by_strict : Karttunen.by_ A_early B_deadline := by
  refine ⟨1, mem_tt_early.mpr rfl, ?_⟩
  intro t' ht'; have := mem_tt_deadline.mp ht'; omega

/-- "He arrived₃ by 3pm₃" — True under `Karttunen.by_`.
    Witness: t = 3 ∈ A, 3 ≤ 3 (coincidence allowed). -/
theorem scenario_by_coincidence : Karttunen.by_ A_at_deadline B_deadline := by
  refine ⟨3, mem_tt_at_deadline.mpr rfl, ?_⟩
  intro t' ht'; have := mem_tt_deadline.mp ht'; omega

/-- "He arrived₃ before 3pm₃" — FALSE under `Anscombe.before`.
    Need 3 < 3, which fails. Shows *by* ⊋ *before*. -/
theorem scenario_before_coincidence_false :
    ¬ Anscombe.before A_at_deadline B_deadline := by
  intro ⟨t, ht, hall⟩
  have ht3 := mem_tt_at_deadline.mp ht
  have hlt := hall 3 (mem_tt_deadline.mpr rfl)
  omega

/-- *By* but not *before* on the same scenario: demonstrates the strict
    weakening from `before_implies_by`. -/
theorem by_without_before :
    Karttunen.by_ A_at_deadline B_deadline ∧
    ¬ Anscombe.before A_at_deadline B_deadline :=
  ⟨scenario_by_coincidence, scenario_before_coincidence_false⟩

/-- "He slept₅₋₁₀ till she arrived₅" — True under `Karttunen.till`.
    Witness: t = 5 ∈ both time traces (overlap). -/
theorem scenario_till : Karttunen.till A_stative B_onset := by
  exact ⟨5, mem_tt_stative.mpr ⟨le_refl _, by omega⟩, mem_tt_onset.mpr rfl⟩

/-- *Till* agrees with *until* on the same scenario (definitional). -/
theorem till_matches_until_scenario :
    Karttunen.till A_stative B_onset ↔ Karttunen.until A_stative B_onset :=
  till_iff_until _ _

end Phenomena.TemporalConnectives.Examples
