import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Linglib.Theories.Pragmatics.NeoGricean.NegationScope

/-!
# @cite{scontras-pearl-2021}: Quantifier Scope Ambiguity @cite{scontras-pearl-2021} @cite{musolino-lidz-2003}
@cite{horn-1972} @cite{kennedy-2015} @cite{partee-1987} @cite{musolino-2004}

"When pragmatics matters more for truth-value judgments:
An investigation of quantifier scope ambiguity"
*Glossa* 6(1): 110.

Scope truth conditions for scopally ambiguous sentences. S&P is a modeling paper —
it explains endorsement patterns from @cite{musolino-lidz-2003} and others via RSA,
rather than reporting new experiments.

## Sections

### §1. Every-not (n=2)
- `JumpOutcome`: 0, 1, or 2 horses jumped
- `ScopeReading`: surface (∀>¬) vs inverse (¬>∀)
- `scopeTruth`: truth conditions for "every horse didn't jump"

### §2. Two-not (n=4)
- `JumpOutcome4`: 0–4 horses jumped
- `NumeralReading`: exact (=2) vs at-least (≥2)
- `twoNotTruth`: truth conditions for "two horses didn't jump" (eq 6)

-/

namespace Phenomena.Quantification.Studies.ScontrasPearl2021

-- ============================================================================
-- §1. Every-Not (n=2)
-- ============================================================================

/-- How many horses jumped (out of 2). -/
inductive JumpOutcome where
  | zero   -- 0 horses jumped
  | one    -- 1 horse jumped
  | two    -- 2 horses jumped (all)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Scope configuration for "every...not". -/
inductive ScopeReading where
  | surface  -- ∀>¬: "For every horse, it didn't jump"
  | inverse  -- ¬>∀: "Not every horse jumped"
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Truth conditions for "Every horse didn't jump" under each scope reading. -/
def scopeTruth : ScopeReading → JumpOutcome → Bool
  | .surface, .zero => true   -- ∀x.¬jump(x): none jumped
  | .surface, .one  => false  -- ∀x.¬jump(x): one jumped, so false
  | .surface, .two  => false  -- ∀x.¬jump(x): all jumped, so false
  | .inverse, .zero => true   -- ¬∀x.jump(x): none jumped, so not all
  | .inverse, .one  => true   -- ¬∀x.jump(x): one jumped, not all
  | .inverse, .two  => false  -- ¬∀x.jump(x): all jumped, so false

/-- Scope truth table correctness. -/
theorem surface_scope_truth :
    scopeTruth .surface .zero = true ∧
    scopeTruth .surface .one = false ∧
    scopeTruth .surface .two = false := ⟨rfl, rfl, rfl⟩

theorem inverse_scope_truth :
    scopeTruth .inverse .zero = true ∧
    scopeTruth .inverse .one = true ∧
    scopeTruth .inverse .two = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §2. Two-Not (n=4)
-- ============================================================================

/-- How many horses jumped (out of 4). -/
inductive JumpOutcome4 where
  | w0  -- 0 horses jumped
  | w1  -- 1 horse jumped
  | w2  -- 2 horses jumped
  | w3  -- 3 horses jumped
  | w4  -- 4 horses jumped (all)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert JumpOutcome4 to natural number. -/
def JumpOutcome4.toNat : JumpOutcome4 → Nat
  | .w0 => 0 | .w1 => 1 | .w2 => 2 | .w3 => 3 | .w4 => 4

/-- Numeral reading: does "two" mean exactly 2 or at least 2? -/
inductive NumeralReading where
  | exact    -- "two" = exactly 2 (@cite{kennedy-2015})
  | atLeast  -- "two" = at least 2 (@cite{horn-1972})
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Truth conditions for "two horses didn't jump" with n=4 horses (eq 6).

    Parameterized by numeral reading and scope configuration.

    Surface scope (two > not): "There are two horses that didn't jump"
    - Exact: exactly 2 didn't jump → exactly 2 jumped → w=2
    - At-least: at least 2 didn't jump → at most 2 jumped → w ∈ {0,1,2}

    Inverse scope (not > two): "It's not the case that two horses jumped"
    - Exact: ¬(exactly 2 jumped) → w ≠ 2 → w ∈ {0,1,3,4}
    - At-least: ¬(at least 2 jumped) → fewer than 2 jumped → w ∈ {0,1} -/
def twoNotTruth : NumeralReading → ScopeReading → JumpOutcome4 → Bool
  -- Exact, surface: exactly 2 horses didn't jump → exactly 2 jumped
  | .exact, .surface, .w2 => true
  | .exact, .surface, _   => false
  -- Exact, inverse: ¬(exactly 2 jumped)
  | .exact, .inverse, .w2 => false
  | .exact, .inverse, _   => true
  -- At-least, surface: ≥2 didn't jump → ≤2 jumped
  | .atLeast, .surface, .w0 => true
  | .atLeast, .surface, .w1 => true
  | .atLeast, .surface, .w2 => true
  | .atLeast, .surface, _   => false
  -- At-least, inverse: ¬(≥2 jumped) → <2 jumped
  | .atLeast, .inverse, .w0 => true
  | .atLeast, .inverse, .w1 => true
  | .atLeast, .inverse, _   => false

/-- In the 1-of-2 context (n=2, numeral=2), "two horses didn't jump" reduces
    to "every horse didn't jump" because the numeral saturates the domain.
    The every-not model's `scopeTruth` thus covers the 1-of-2 two-not case
    (paper §4.2): exact and at-least have the same extension when n = numeral.

    This theorem documents the `scopeTruth` values that serve as the shared
    baseline. The interesting divergence only appears in the 2-of-4 context
    where n > numeral (see `exact_atleast_diverge_2of4`). -/
theorem every_not_covers_1of2 :
    scopeTruth .surface .zero = true ∧
    scopeTruth .surface .one = false ∧
    scopeTruth .surface .two = false ∧
    scopeTruth .inverse .zero = true ∧
    scopeTruth .inverse .one = true ∧
    scopeTruth .inverse .two = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The two numeral theories diverge in the 2-of-4 context (n=4).
    Surface scope: exact → {w2}, at-least → {w0,w1,w2}
    Inverse scope: exact → {w0,w1,w3,w4}, at-least → {w0,w1} -/
theorem exact_atleast_diverge_2of4 :
    -- Surface scope: exact excludes w0,w1 but at-least includes them
    twoNotTruth .exact .surface .w0 = false ∧
    twoNotTruth .atLeast .surface .w0 = true ∧
    twoNotTruth .exact .surface .w1 = false ∧
    twoNotTruth .atLeast .surface .w1 = true ∧
    -- Inverse scope: exact includes w3,w4 but at-least excludes them
    twoNotTruth .exact .inverse .w3 = true ∧
    twoNotTruth .atLeast .inverse .w3 = false ∧
    twoNotTruth .exact .inverse .w4 = true ∧
    twoNotTruth .atLeast .inverse .w4 = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §3. Scope Entailment Asymmetry (@cite{musolino-lidz-2003}, pp. 288–289)
-- ============================================================================

/-- For universals, surface scope (∀>¬: none jumped) ENTAILS inverse scope
    (¬>∀: not all jumped). If no horse jumped, then trivially not every horse
    jumped. This means no truth-value judgment context can diagnose the
    isomorphism effect for universals: whenever surface is true, inverse
    is automatically true too. -/
theorem universal_surface_entails_inverse :
    ∀ w, scopeTruth .surface w = true → scopeTruth .inverse w = true := by
  intro w; cases w <;> simp [scopeTruth]

/-- The entailment is strict: inverse does NOT entail surface.
    At w=1 (one horse jumped), inverse scope is true (not all jumped)
    but surface scope is false (not none jumped). -/
theorem universal_inverse_not_entails_surface :
    ∃ w, scopeTruth .inverse w = true ∧ scopeTruth .surface w = false :=
  ⟨.one, rfl, rfl⟩

/-- For exact numerals, surface scope does NOT entail inverse scope.
    At w=2 (exactly 2 jumped out of 4), surface is true (exactly 2 didn't)
    but inverse is false (it IS the case that exactly 2 jumped).
    This independence is what makes numerals diagnostic for the isomorphism
    effect. -/
theorem numeral_surface_not_entails_inverse :
    ∃ w, twoNotTruth .exact .surface w = true ∧
         twoNotTruth .exact .inverse w = false :=
  ⟨.w2, rfl, rfl⟩

/-- Inverse scope also does not entail surface for exact numerals.
    At w=0 (none jumped), inverse is true (¬(exactly 2 jumped)) but
    surface is false (not exactly 2 didn't jump, since all 4 didn't). -/
theorem numeral_inverse_not_entails_surface :
    ∃ w, twoNotTruth .exact .inverse w = true ∧
         twoNotTruth .exact .surface w = false :=
  ⟨.w0, rfl, rfl⟩

-- ============================================================================
-- §4. @cite{musolino-lidz-2003} Experimental Data
-- ============================================================================

/-- Acceptance rate from a truth-value judgment experiment. -/
structure AcceptanceRate where
  accepted : Nat
  total : Nat
  deriving Repr

/-- Experiment 2, matched condition: isomorphic reading (two > not) true.
    "Two N didn't V" — context makes surface scope true, inverse false.
    Adults accept readily when the isomorphic reading works → 100%. -/
def ml2003_exp2_matched : AcceptanceRate := ⟨40, 40⟩

/-- Experiment 2, unmatched condition: non-isomorphic reading (not > two) true.
    "Two N didn't V" — context makes only inverse scope true.
    Adults show isomorphism effect (surface scope preference) → 27.5%.
    This is the key datum that @cite{scontras-pearl-2021}'s RSA model explains. -/
def ml2003_exp2_unmatched : AcceptanceRate := ⟨11, 40⟩

/-- Experiment 3: same as Exp 2 unmatched but preceded by an affirmative
    statement (e.g., "Two frogs jumped... but two frogs didn't jump").
    Affirmative context rescues non-isomorphic (inverse scope) access → 92.5%.
    Modeled by @cite{scontras-pearl-2021}'s `supportiveCfg`. -/
def ml2003_exp3_affirmative : AcceptanceRate := ⟨37, 40⟩

-- ============================================================================
-- §5. Numeral Semantics Grounding
-- ============================================================================

/-! Connects S&P's `twoNotTruth` truth conditions to linglib's numeral
semantics infrastructure (`maxMeaning` in `Numeral.Semantics`).

The truth conditions in the data file are grounded in `maxMeaning`:
- Exact surface: "exactly 2 didn't jump" = `maxMeaning.eq 2 (4 - w)`
- Exact inverse: "¬(exactly 2 jumped)" = `!(maxMeaning.eq 2 w)`
- At-least surface: "≥2 didn't jump" = `maxMeaning.ge 2 (4 - w)`
- At-least inverse: "¬(≥2 jumped)" = `!(maxMeaning.ge 2 w)`

Convergent evidence for exact semantics from @cite{kennedy-2015}
(de-Fregean semantics where bare numerals mean =n) and @cite{musolino-2004}
(acquisition data — children reject "two" at w=3).
-/

open Semantics.Lexical.Numeral (maxMeaning OrderingRel)

/-- Exact surface: "exactly two didn't jump" (out of 4) ↔ exactly two jumped.
    Matches `maxMeaning.eq 2` applied to the complement count (4 - w). -/
theorem twoNotExact_surface_matches_maxMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .exact .surface w = maxMeaning .eq 2 (4 - w.toNat) := by
  intro w; cases w <;> rfl

/-- Exact inverse: "¬(exactly two jumped)" ↔ `!(maxMeaning.eq 2 w)`. -/
theorem twoNotExact_inverse_matches_maxMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .exact .inverse w = !(maxMeaning .eq 2 w.toNat) := by
  intro w; cases w <;> rfl

/-- At-least surface: "at least two didn't jump" ↔ at most two jumped.
    Matches `maxMeaning.ge 2` applied to the complement count. -/
theorem twoNotAtLeast_surface_matches_maxMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .atLeast .surface w = maxMeaning .ge 2 (4 - w.toNat) := by
  intro w; cases w <;> rfl

/-- At-least inverse: "¬(at least two jumped)" ↔ `!(maxMeaning.ge 2 w)`. -/
theorem twoNotAtLeast_inverse_matches_maxMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .atLeast .inverse w = !(maxMeaning .ge 2 w.toNat) := by
  intro w; cases w <;> rfl

/-- The negation-scope asymmetry collapses under exact semantics:
    internal and external negation of "three" give the same result. -/
theorem exact_collapses_negation_scope :
    NeoGricean.negatedMeaning Semantics.Lexical.Numeral.Exact .three .internal 4 =
    NeoGricean.negatedMeaning Semantics.Lexical.Numeral.Exact .three .external 4 := by
  native_decide

/-- Lower-bound semantics preserves the negation-scope distinction. -/
theorem lowerBound_preserves_negation_scope :
    NeoGricean.negatedMeaning Semantics.Lexical.Numeral.LowerBound .three .internal 4 ≠
    NeoGricean.negatedMeaning Semantics.Lexical.Numeral.LowerBound .three .external 4 := by
  native_decide

/-- @cite{kennedy-2015}'s resolution: exact meaning is basic, lower-bound is derived
    via type-shift. Both meanings are grammatically available. -/
theorem typeshift_resolves_tension :
    Semantics.Lexical.Numeral.typeLower (maxMeaning .eq) 4 2 2 =
    maxMeaning .ge 2 2 := by native_decide

end Phenomena.Quantification.Studies.ScontrasPearl2021
