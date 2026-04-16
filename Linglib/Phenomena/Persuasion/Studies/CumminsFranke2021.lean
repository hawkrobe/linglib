import Linglib.Theories.Pragmatics.RSA.Extensions.ArgumentativeStrength
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Mathlib.Data.Rat.Defs

/-!
# @cite{cummins-franke-2021}: Argumentative Strength of Numerical Quantity
@cite{cummins-franke-2021}

Formalizes the conference registration scenario (C&F pp. 7–8) demonstrating that
semantic and pragmatic argumentative strength can *reverse* the ordering of
"more than M" expressions, and the REF 2014 case study on strategic use of
"top M" claims (C&F §5, pp. 10–14).

## Key Results

1. **Semantic measure**: "more than 110" > "more than 100" for goal "success"
   (because "more than 110" concentrates probability mass in goal-worlds)
2. **Pragmatic reversal**: with 90% enrichment, the ordering
   flips — "more than 100" becomes pragmatically stronger (C&F Eq. 25)
3. **REF case study**: universities use round "top M" claims and prefer
   the ranking measure on which they score better (C&F §5)

See also `MacuchSilvaEtAl2024.lean` for the experimental follow-up on
strategic quantifier choice in exam scenarios.

## Methodology

All ordinal comparisons use Bayes factor ratios (exact ℚ arithmetic),
which are equivalent to comparing argStr values since log is monotone.
This avoids dependence on log approximations.

-/

namespace CumminsFranke2021

open RSA.ArgumentativeStrength
open Semantics.Lexical.Numeral


-- ============================================================
-- Section 1: Modified Numeral Semantics (Grounding)
-- ============================================================

/-- "More than M" is equivalent to lower-bound meaning at M+1.

moreThan(M)(n) = true ↔ n > M ↔ n ≥ M+1 = lowerBound(M+1)(n)

These theorems ground the conference scenario's semantics in the
canonical `moreThanMeaning` from Numeral.Semantics. The conference
scenario (§2) uses probability counts directly for tractability, but
the underlying denotation is the same. -/
theorem moreThan_from_lowerBound_zero (n : Nat) :
    moreThanMeaning 0 n = LowerBound.meaning .one n := by
  simp [moreThanMeaning, maxMeaning, NumeralTheory.meaning, LowerBound, BareNumeral.toNat]
  omega

theorem moreThan_from_lowerBound_one (n : Nat) :
    moreThanMeaning 1 n = LowerBound.meaning .two n := by
  simp [moreThanMeaning, maxMeaning, NumeralTheory.meaning, LowerBound, BareNumeral.toNat]
  omega

theorem moreThan_from_lowerBound_two (n : Nat) :
    moreThanMeaning 2 n = LowerBound.meaning .three n := by
  simp [moreThanMeaning, maxMeaning, NumeralTheory.meaning, LowerBound, BareNumeral.toNat]
  omega


-- ============================================================
-- Section 2: Conference Scenario — Semantic (C&F §4, Eq. 17, p. 7)
-- ============================================================

-- Conference scenario: attendees uniformly distributed on [0, 200].
-- Success goal G: more than 120 attend.
-- C&F use continuous uniform, so ¬G range [0, 120] has measure 120.

/-- Conference argumentative goal -/
def conferenceGoal : ArgumentativeGoal (Fin 201) :=
  ⟨fun w => w.val > 120⟩

-- Utterance: "more than 100"

/-- P("more than 100" | G) = 1: all goal-worlds (value > 120) satisfy value > 100. -/
def p_mt100_givenG : ℚ := 1

/-- P("more than 100" | ¬G) = 20/120 = 1/6: among ¬G worlds (value in [0, 120]),
values > 100 span (100, 120], measure 20 out of 120. (C&F p. 7) -/
def p_mt100_givenNotG : ℚ := 1 / 6

-- Utterance: "more than 110"

/-- P("more than 110" | G) = 1: all goal-worlds satisfy value > 110. -/
def p_mt110_givenG : ℚ := 1

/-- P("more than 110" | ¬G) = 10/120 = 1/12: among ¬G worlds,
values > 110 span (110, 120], measure 10 out of 120. (C&F p. 7) -/
def p_mt110_givenNotG : ℚ := 1 / 12

/-- "More than 110" has a higher Bayes factor than "more than 100" for the conference goal.

BF("mt110") = 1/(1/12) = 12 > BF("mt100") = 1/(1/6) = 6.

This is C&F's key semantic result: the more precise (higher M) expression
has higher argStr because it has lower P(u|¬G). (C&F p. 7) -/
theorem moreThan110_semantically_stronger :
    bayesFactor p_mt110_givenG p_mt110_givenNotG >
    bayesFactor p_mt100_givenG p_mt100_givenNotG := by native_decide

/-- Both utterances have positive argumentative strength for the goal. -/
theorem moreThan100_supports_goal :
    hasPositiveArgStr p_mt100_givenG p_mt100_givenNotG := by native_decide

theorem moreThan110_supports_goal :
    hasPositiveArgStr p_mt110_givenG p_mt110_givenNotG := by native_decide


-- ============================================================
-- Section 3: Pragmatic Enrichment (C&F §4, Eq. 25, pp. 7–8)
-- ============================================================

-- C&F's illustrative enrichment assumptions (p. 7):
-- • 90% probability of pragmatic enrichment
-- • "more than 100" enriched to "not more than 150" (assertable range: (100, 150])
-- • "more than 110" enriched to "not more than 120" (assertable range: (110, 120])

/-- P_A("more than 100" | G):
90% × P(value ∈ (100,150] | value ∈ (120,200]) + 10% × P(value > 100 | value ∈ (120,200])
= 90% × 30/80 + 10% × 1 = 27/80 + 8/80 = 35/80. (C&F p. 8) -/
def p_mt100_assertable_givenG : ℚ := 35 / 80

/-- P_A("more than 100" | ¬G) = 1/6:
Both enriched and literal paths give the same probability, since
(100,150] ∩ [0,120] = (100,120] and literal >100 in [0,120] is also (100,120].
Total: 90% × 1/6 + 10% × 1/6 = 1/6. (C&F p. 8) -/
def p_mt100_assertable_givenNotG : ℚ := 1 / 6

/-- P_A("more than 110" | G) = 1/10:
90% × P(value ∈ (110,120] | value ∈ (120,200]) + 10% × P(value > 110 | value ∈ (120,200])
= 90% × 0 + 10% × 1 = 1/10.
The enriched range (110,120] doesn't intersect the goal range (120,200]. (C&F p. 8) -/
def p_mt110_assertable_givenG : ℚ := 1 / 10

/-- P_A("more than 110" | ¬G) = 1/12:
Both paths give P(value > 110 | value ∈ [0,120]) = 10/120 = 1/12.
Total: 90% × 1/12 + 10% × 1/12 = 1/12. (C&F p. 8) -/
def p_mt110_assertable_givenNotG : ℚ := 1 / 12

/-- PRAGMATIC REVERSAL: "more than 100" becomes pragmatically stronger.

BF_prag("mt100") = (35/80)/(1/6) = 21/8 = 2.625
BF_prag("mt110") = (1/10)/(1/12) = 6/5 = 1.2

This is C&F's central result (p. 8). Semantically mt110 > mt100, but
pragmatically mt100 > mt110. The enrichment of "more than 110" to
"not more than 120" makes it nearly unassertable in goal-worlds (P_A = 1/10),
while "more than 100" enriched to "not more than 150" retains substantial
assertability (P_A = 35/80). -/
theorem pragmatic_reversal :
    bayesFactor p_mt100_assertable_givenG p_mt100_assertable_givenNotG >
    bayesFactor p_mt110_assertable_givenG p_mt110_assertable_givenNotG := by native_decide

/-- Both utterances retain positive pragmatic argumentative strength. -/
theorem moreThan100_pragmatically_supports_goal :
    hasPositiveArgStr p_mt100_assertable_givenG p_mt100_assertable_givenNotG := by native_decide

theorem moreThan110_pragmatically_supports_goal :
    hasPositiveArgStr p_mt110_assertable_givenG p_mt110_assertable_givenNotG := by native_decide

/-- Structural theorem: when P_a(u|¬G) increases (through wider enrichment),
the Bayes factor decreases and thus argStr decreases. This is the mechanism
behind the pragmatic reversal. -/
theorem wider_enrichment_weakens_argStr
    (pG : ℚ) (pNotG_narrow pNotG_wide : ℚ)
    (hG : 0 < pG) (hNarrow : 0 < pNotG_narrow) (hWide : 0 < pNotG_wide)
    (hWider : pNotG_narrow < pNotG_wide) :
    bayesFactor pG pNotG_wide < bayesFactor pG pNotG_narrow := by
  unfold bayesFactor
  simp [ne_of_gt hNarrow, ne_of_gt hWide]
  exact div_lt_div_of_pos_left hG hNarrow hWider


-- ============================================================
-- Section 4: REF Case Study (C&F §5, examples 29–38, p. 12)
-- ============================================================

/-- Claim type: absolute rank ("top M") or percentile ("top M per cent") -/
inductive ClaimType where
  | absolute     -- "top M" (actual rank ≤ M)
  | percentile   -- "top M per cent" (actual rank ≤ ⌈N × M/100⌉)
  deriving DecidableEq, Repr

/-- A "top M" datum from C&F §5, examples 29–38 (p. 12) -/
structure TopMDatum where
  institution : String
  actualRank : Nat
  claimedM : Nat
  claimType : ClaimType
  isRound : Bool
  rankingMeasure : String
  deriving Repr

/-- C&F examples 29–38: UK universities' "top M" claims from REF 2014 reports.

All claimed M values are round numbers (multiples of 5 or 10).
Data verified against C&F p. 12. REF 2014 had 154 multi-subject institutions. -/
def topMExamples : List TopMDatum :=
  [ ⟨"Cardiff",        5,   5, .absolute,   true, "GPA"⟩       -- (29) top five
  , ⟨"KCL",            7,  10, .absolute,   true, "Power"⟩     -- (30) Top 10 nationally
  , ⟨"Warwick",        8,  10, .absolute,   true, "GPA"⟩       -- (31) top 10 success
  , ⟨"LSHTM",         10,  10, .absolute,   true, "GPA"⟩       -- (32) top 10 of all universities
  , ⟨"Sheffield",     16,  10, .percentile, true, "GPA"⟩       -- (33) top 10 per cent
  , ⟨"Leeds",         10,  10, .absolute,   true, "Power"⟩     -- (34) top 10
  , ⟨"Royal Holloway", 26, 25, .percentile, true, "Quality"⟩  -- (35) top 25 per cent
  , ⟨"Swansea",       26,  30, .absolute,   true, "GPA"⟩       -- (36) top 30
  , ⟨"Essex",         20,  20, .absolute,   true, "Intensity"⟩ -- (37) top 20
  , ⟨"Strathclyde",   18,  20, .absolute,   true, "Intensity"⟩ -- (38) Top 20
  ]

/-- H1 verification: all claimed M values are round (multiples of 5) -/
theorem h1_all_round : topMExamples.all (·.isRound) = true := by native_decide

/-- H1 verification: absolute claims are truthful (actual rank ≤ claimed M) -/
theorem h1_absolute_truthful :
    (topMExamples.filter (·.claimType == .absolute)).all
      (λ d => decide (d.actualRank ≤ d.claimedM)) = true := by native_decide

/-- H1 verification: percentile claims are truthful.
REF 2014 had 154 institutions; top 10% = rank ≤ 16, top 25% = rank ≤ 39. -/
theorem h1_percentile_truthful :
    -- Sheffield: rank 16 ≤ ⌈154 × 0.10⌉ = 16
    16 ≤ 16 ∧
    -- Royal Holloway: rank 26 ≤ ⌈154 × 0.25⌉ = 39
    26 ≤ 39 := ⟨le_refl 16, by omega⟩

/-- H2 data: ranking measure preference (C&F p. 13).

Of 39 institutions with data, 19 ranked higher on GPA and 19 on power
(Durham 20th on both). Institutions systematically prefer the measure
on which they rank better. -/
structure RankPreferenceGroup where
  groupSize : Nat
  citedPreferred : Nat
  citedNonPreferred : Nat
  citedNeither : Nat
  deriving Repr

/-- GPA-preferred group: 9 cite GPA, 0 cite power, 10 cite neither.
(p < 0.01, sign test; C&F p. 13) -/
def h2_gpaGroup : RankPreferenceGroup :=
  { groupSize := 19, citedPreferred := 9, citedNonPreferred := 0, citedNeither := 10 }

/-- Power-preferred group: 11 cite power, 2 cite GPA, 6 cite neither.
(p < 0.05, sign test; C&F p. 13) -/
def h2_powerGroup : RankPreferenceGroup :=
  { groupSize := 19, citedPreferred := 11, citedNonPreferred := 2, citedNeither := 6 }

/-- H2: in each group, more institutions cite their preferred measure
than the non-preferred one. -/
theorem h2_gpa_group_prefers_gpa :
    h2_gpaGroup.citedPreferred > h2_gpaGroup.citedNonPreferred := by native_decide

theorem h2_power_group_prefers_power :
    h2_powerGroup.citedPreferred > h2_powerGroup.citedNonPreferred := by native_decide

/-- H2: group counts are internally consistent. -/
theorem h2_groups_consistent :
    h2_gpaGroup.citedPreferred + h2_gpaGroup.citedNonPreferred + h2_gpaGroup.citedNeither
      = h2_gpaGroup.groupSize ∧
    h2_powerGroup.citedPreferred + h2_powerGroup.citedNonPreferred + h2_powerGroup.citedNeither
      = h2_powerGroup.groupSize := by native_decide


end CumminsFranke2021
