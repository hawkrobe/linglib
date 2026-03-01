import Linglib.Core.Scales.Roundness

/-!
# Granularity-Sensitive Degree Semantics @cite{thomas-deo-2020}

Thomas, W. & Deo, A. (2020). The interaction of *just* with modified
scalar predicates. *Sinn und Bedeutung* 24, pp. 360–377.

## Overview

A granularity level maps each degree on a scale to an interval of width
2ε (the "grain"). Equatives use the infimum of this interval as the
standard; comparatives use the supremum. This creates an **entailment
reversal**: finer granularity strengthens equatives but weakens
comparatives.

This reversal explains why approximative *just* yields different readings:
- *just as tall as* ≈ "exactly" (negative component vacuous)
- *just taller than* ≈ "barely" (negative component substantive)

## Definitions

1. `GranLevel` — grain size ε on ℕ
2. `eqAtGran` / `compAtGran` — granularity-sensitive degree morphology
3. `approxJust` — approximative *just* (eq. 44)
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

instance : LE GranLevel where le g₁ g₂ := g₁.ε ≤ g₂.ε
instance : LT GranLevel where lt g₁ g₂ := g₁.ε < g₂.ε

/-- The finest level is ≤ all levels. -/
theorem GranLevel.finest_le (g : GranLevel) : GranLevel.finest ≤ g :=
  Nat.zero_le g.ε

-- ════════════════════════════════════════════════════
-- § 2. Granularity-Sensitive Degree Morphology
-- ════════════════════════════════════════════════════

/-- Equative at granularity g: "as Adj as d_c" at grain ε.
    True iff μ(x) ≥ d_c − ε, reformulated as μ_x + ε ≥ d_c
    to avoid ℕ subtraction truncation. (eq. 39) -/
def eqAtGran (g : GranLevel) (μ_x d_c : Nat) : Prop :=
  μ_x + g.ε ≥ d_c

/-- Comparative at granularity g: "Adj-er than d_c" at grain ε.
    True iff μ(x) exceeds d_c + ε: the subject must surpass even the
    upper end of the granularity interval around d_c. (eq. 42) -/
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
- Equative: fine ⊢ coarse
- Comparative: coarse ⊢ fine -/

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

-- ════════════════════════════════════════════════════
-- § 5. Approximative *just*
-- ════════════════════════════════════════════════════

/-- Propositional strength: p at g₁ is at least as strong as p at g₂
    iff g₁-truth entails g₂-truth for all degree assignments. -/
def atLeastAsStrong (p : GranLevel → Nat → Nat → Prop)
    (g₁ g₂ : GranLevel) : Prop :=
  ∀ μ_x d_c, p g₁ μ_x d_c → p g₂ μ_x d_c

/-- Approximative *just* (eq. 44).
    Positive component: the prejacent holds at finest granularity.
    Negative component: at every granularity level where the prejacent
    holds, the finest-grain version is at least as strong. -/
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
