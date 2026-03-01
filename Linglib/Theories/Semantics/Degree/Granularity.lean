import Mathlib.Order.Basic
import Linglib.Core.Scales.Scale
import Linglib.Core.Scales.Roundness

/-!
# Granularity-Sensitive Degree Semantics @cite{thomas-deo-2020}

Thomas, W. & Deo, A. (2020). The interaction of *just* with modified
scalar predicates. *Sinn und Bedeutung* 24, vol. 2, pp. 354–372.

## Overview

A granularity level maps each degree on a scale to an interval of width
2ε (the "grain"). Equatives use the infimum of this interval as the
standard; comparatives use the supremum. This creates an **entailment
reversal**: finer granularity strengthens equatives but weakens
comparatives.

This reversal explains why approximative *just* yields different readings:
- *just as tall as* ≈ "exactly" (negative component vacuous)
- *just taller than* ≈ "barely" (negative component substantive)

## Discretization

The paper works on dense scales with strict > and finite contextual
granularity sets 𝒢. We discretize to ℕ with ≥ for equatives and >
for comparatives. This preserves the structural properties (entailment
reversal, vacuity/substantivity of *just*'s negative component) and
enables the stronger result `approxJust_comp_exact`: on ℕ, "just
taller" forces degree = d_c + 1 (the minimal comparative excess).

On a dense scale, `approxJust` must quantify over a finite 𝒢 to
remain satisfiable for comparatives; quantifying over all ε > 0 makes
it unsatisfiable. On ℕ, the gap between ε = 0 and ε = 1 provides a
natural stopping point.

## Definitions

1. `GranLevel` — grain size ε on ℕ, with `LinearOrder` and `OrderBot`
2. `eqAtGran` / `compAtGran` — granularity-sensitive degree morphology
3. `approxJust` — approximative *just* (paper eq. 44)
4. `roundnessToGrain` — numeral roundness → grain size (Krifka 2007)

## References

- Sauerland, U. & Stateva, P. (2007). Scalar vs. epistemic vagueness.
- Krifka, M. (2007). Approximate interpretation of number words.
-/

namespace Semantics.Degree.Granularity

-- ════════════════════════════════════════════════════
-- § 1. Granularity Levels
-- ════════════════════════════════════════════════════

/-- A granularity level with grain size ε.
    The identity partition (each cell a singleton) has ε = 0.
    Coarser levels have larger ε, yielding wider intervals. -/
structure GranLevel where
  ε : Nat
  deriving Repr, DecidableEq, BEq

/-- The finest granularity: each degree maps to itself (ε = 0). -/
def GranLevel.finest : GranLevel := ⟨0⟩

instance : LinearOrder GranLevel :=
  LinearOrder.lift' GranLevel.ε (fun a b h => by cases a; cases b; exact congrArg _ h)

/-- The finest level is ≤ all levels. -/
theorem GranLevel.finest_le (g : GranLevel) : GranLevel.finest ≤ g :=
  Nat.zero_le g.ε

instance : OrderBot GranLevel where
  bot := .finest
  bot_le := GranLevel.finest_le

-- ════════════════════════════════════════════════════
-- § 2. Granularity-Sensitive Degree Morphology
-- ════════════════════════════════════════════════════

/-- Equative at granularity g: "as Adj as d_c" at grain ε.
    True iff μ(x) ≥ d_c − ε, reformulated as μ_x + ε ≥ d_c
    to avoid ℕ subtraction truncation.

    Paper eq. (45): ⟦as...as d_c⟧^g = λGλx.∃d[d > inf(g(d_c)) ∧ G(d)(x)].
    On ℕ, strict > at inf becomes ≥ at the same point, recovering the
    standard equative (≥) at ε = 0. -/
def eqAtGran (g : GranLevel) (μ_x d_c : Nat) : Prop :=
  μ_x + g.ε ≥ d_c

/-- Comparative at granularity g: "Adj-er than d_c" at grain ε.
    True iff μ(x) exceeds d_c + ε: the subject must surpass even the
    upper end of the granularity interval around d_c.

    Paper eq. (49): ⟦er/more than d_c⟧^g = λGλx.∃d[d > sup(g(d_c)) ∧ G(d)(x)]. -/
def compAtGran (g : GranLevel) (μ_x d_c : Nat) : Prop :=
  μ_x > d_c + g.ε

-- ════════════════════════════════════════════════════
-- § 3. Recovery of Standard Semantics
-- ════════════════════════════════════════════════════

/-- At finest granularity, the equative is the standard ≥ comparison. -/
theorem eq_finest_iff (μ_x d_c : Nat) :
    eqAtGran .finest μ_x d_c ↔ μ_x ≥ d_c := by
  simp [eqAtGran, GranLevel.finest]

/-- At finest granularity, the comparative is the standard > comparison. -/
theorem comp_finest_iff (μ_x d_c : Nat) :
    compAtGran .finest μ_x d_c ↔ μ_x > d_c := by
  simp [compAtGran, GranLevel.finest]

-- ════════════════════════════════════════════════════
-- § 4. Entailment Reversal
-- ════════════════════════════════════════════════════

/-! ### The central observation

Equatives and comparatives have **opposite monotonicity** in granularity:
- **Equatives**: finer grain → higher threshold → *stronger* claim
- **Comparatives**: finer grain → lower excess → *weaker* claim

Entailment flows in opposite directions:
- Equative: fine ⊢ coarse  (`IsUpwardMonotone`)
- Comparative: coarse ⊢ fine  (`IsDownwardMonotone`) -/

/-- Equatives: finer granularity entails coarser granularity. -/
theorem eq_fine_entails_coarse (g₁ g₂ : GranLevel)
    (hfine : g₁.ε ≤ g₂.ε) (μ_x d_c : Nat)
    (h : eqAtGran g₁ μ_x d_c) : eqAtGran g₂ μ_x d_c := by
  unfold eqAtGran at *; omega

/-- Comparatives: coarser granularity entails finer granularity. -/
theorem comp_coarse_entails_fine (g₁ g₂ : GranLevel)
    (hfine : g₁.ε ≤ g₂.ε) (μ_x d_c : Nat)
    (h : compAtGran g₂ μ_x d_c) : compAtGran g₁ μ_x d_c := by
  unfold compAtGran at *; omega

-- § 4a. Monotonicity via Core.Scale infrastructure

open Core.Scale in
/-- Equatives are upward monotone in granularity: larger ε (coarser grain)
    yields a weaker (more easily satisfied) equative claim. -/
theorem eqAtGran_upwardMono (d_c : Nat) :
    IsUpwardMonotone (fun g : GranLevel => fun μ_x : Nat => eqAtGran g μ_x d_c) :=
  fun g₁ g₂ hle μ_x h => eq_fine_entails_coarse g₁ g₂ hle μ_x d_c h

open Core.Scale in
/-- Comparatives are downward monotone in granularity: larger ε (coarser grain)
    yields a stronger (harder to satisfy) comparative claim. -/
theorem compAtGran_downwardMono (d_c : Nat) :
    IsDownwardMonotone (fun g : GranLevel => fun μ_x : Nat => compAtGran g μ_x d_c) :=
  fun g₁ g₂ hle μ_x h => comp_coarse_entails_fine g₁ g₂ hle μ_x d_c h

-- ════════════════════════════════════════════════════
-- § 5. Approximative *just*
-- ════════════════════════════════════════════════════

/-- Propositional strength: p at g₁ is at least as strong as p at g₂
    iff g₁-truth entails g₂-truth for all degree assignments. -/
def atLeastAsStrong (p : GranLevel → Nat → Nat → Prop)
    (g₁ g₂ : GranLevel) : Prop :=
  ∀ μ_x d_c, p g₁ μ_x d_c → p g₂ μ_x d_c

/-- Approximative *just* (paper eq. 44).
    Positive component: the prejacent holds at finest granularity.
    Negative component: at every granularity level where the prejacent
    holds, the finest-grain version is at least as strong.

    The paper restricts the negative component to a contextually available
    finite set 𝒢. Our version quantifies over all `GranLevel`s, yielding
    a strictly stronger condition. On ℕ, this is satisfiable (for
    comparatives, μ_x = d_c + 1 is the unique witness; see
    `approxJust_comp_exact`). On dense scales, quantifying over all ε > 0
    makes the comparative case unsatisfiable — hence the paper's
    restriction to finite 𝒢. -/
def approxJust (p : GranLevel → Nat → Nat → Prop)
    (μ_x d_c : Nat) : Prop :=
  p .finest μ_x d_c ∧
  ∀ g : GranLevel, p g μ_x d_c → atLeastAsStrong p .finest g

-- ════════════════════════════════════════════════════
-- § 6. Equative: Negative Component is Vacuous
-- ════════════════════════════════════════════════════

/-- The finest equative is at least as strong as any equative. -/
theorem eq_finest_strongest (g : GranLevel) :
    atLeastAsStrong eqAtGran .finest g :=
  fun μ_x d_c h => eq_fine_entails_coarse .finest g (Nat.zero_le _) μ_x d_c h

/-- *Just* applied to an equative reduces to the equative at finest grain.
    The negative component is vacuous because the finest equative is already
    the strongest — "just as tall as" ≈ "exactly as tall as". -/
theorem just_eq_reduces (μ_x d_c : Nat) :
    approxJust eqAtGran μ_x d_c ↔ eqAtGran .finest μ_x d_c := by
  constructor
  · exact fun ⟨h, _⟩ => h
  · intro h; exact ⟨h, fun _ _ => eq_finest_strongest _⟩

-- ════════════════════════════════════════════════════
-- § 7. Comparative: Negative Component is Substantive
-- ════════════════════════════════════════════════════

/-- The finest comparative is NOT at least as strong as any strictly
    coarser comparative: witness (μ_x, d_c) = (1, 0). -/
theorem comp_finest_not_strongest (g : GranLevel) (hcoarser : 0 < g.ε) :
    ¬ atLeastAsStrong compAtGran .finest g := by
  intro hstr
  have h1 : compAtGran .finest 1 0 := by simp [compAtGran, GranLevel.finest]
  have h2 := hstr 1 0 h1
  unfold compAtGran at h2
  omega

/-- *Just* applied to a comparative forces the comparative to be false
    at every strictly coarser granularity level.
    "Just taller than d_c" entails "not much taller than d_c". -/
theorem just_comp_rules_out_coarser (g : GranLevel) (hcoarser : 0 < g.ε)
    (μ_x d_c : Nat) (hjust : approxJust compAtGran μ_x d_c) :
    ¬ compAtGran g μ_x d_c := by
  intro hg
  exact comp_finest_not_strongest g hcoarser (hjust.2 g hg)

/-- On ℕ, *just* + comparative forces the degree to be exactly 1 above
    the standard. "Just taller than d_c" means μ_x = d_c + 1 — the
    minimal comparative excess. This is the paper's strongest discrete
    prediction, combining:
    - Positive component: μ_x > d_c (from `comp_finest_iff`)
    - Negative at ε = 1: ¬(μ_x > d_c + 1), so μ_x ≤ d_c + 1 -/
theorem approxJust_comp_exact (μ_x d_c : Nat)
    (hjust : approxJust compAtGran μ_x d_c) : μ_x = d_c + 1 := by
  have hpos := hjust.1
  have hneg := just_comp_rules_out_coarser ⟨1⟩ (show (0 : Nat) < 1 by omega) μ_x d_c hjust
  simp only [compAtGran, GranLevel.finest] at hpos hneg
  omega

-- ════════════════════════════════════════════════════
-- § 8. Concrete Verification
-- ════════════════════════════════════════════════════

/-- Heights equal (both 170): "just as tall as" holds. -/
example : approxJust eqAtGran 170 170 :=
  (just_eq_reduces 170 170).mpr (by simp [eqAtGran, GranLevel.finest])

/-- Fafen 171, Siri 170: comparative true at finest grain. -/
example : compAtGran .finest 171 170 := by simp [compAtGran, GranLevel.finest]

/-- Fafen 171, Siri 170: comparative false at grain ε = 5. -/
example : ¬ compAtGran ⟨5⟩ 171 170 := by simp [compAtGran]

/-- Fafen 171, Siri 170: "just" forces exactly 1 above. -/
example (hjust : approxJust compAtGran 171 170) : 171 = 170 + 1 :=
  approxJust_comp_exact 171 170 hjust

-- ════════════════════════════════════════════════════
-- § 9. Roundness → Granularity Bridge
-- ════════════════════════════════════════════════════

open Core.Roundness in
/-- Map numeral roundness grades to default granularity levels.
    Rounder numerals evoke coarser granularity (Krifka 2007):
    "just over 100" (ε = 10) conveys less proximity than
    "just over 31" (ε = 0). -/
def roundnessToGrain (grade : RoundnessGrade) : GranLevel :=
  match grade with
  | .high     => ⟨10⟩
  | .moderate => ⟨5⟩
  | .low      => ⟨2⟩
  | .none     => ⟨0⟩

/-- Roundness grade is monotone in grain size. -/
theorem rounder_means_coarser :
    (roundnessToGrain .none).ε ≤ (roundnessToGrain .low).ε ∧
    (roundnessToGrain .low).ε ≤ (roundnessToGrain .moderate).ε ∧
    (roundnessToGrain .moderate).ε ≤ (roundnessToGrain .high).ε := by
  simp [roundnessToGrain]

/-- "Just over 31 minutes" conveys greater proximity than "just over 30
    minutes": 31 (non-round) evokes finer granularity than 30 (round). -/
theorem just_over_31_finer_than_30 :
    (roundnessToGrain (Core.Roundness.roundnessGrade 31)).ε <
    (roundnessToGrain (Core.Roundness.roundnessGrade 30)).ε := by native_decide

end Semantics.Degree.Granularity
