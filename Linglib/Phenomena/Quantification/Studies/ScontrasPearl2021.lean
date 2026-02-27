/-!
# Scontras & Pearl (2021): Quantifier Scope Ambiguity @cite{scontras-pearl-2021}

"When pragmatics matters more for truth-value judgments:
An investigation of quantifier scope ambiguity"
*Glossa* 6(1): 110.

Scope truth conditions for scopally ambiguous sentences. S&P is a modeling paper —
it explains endorsement patterns from Musolino & Lidz (2003) and others via RSA,
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

## References

- Scontras, G. & Pearl, L. (2021). When pragmatics matters more for
  truth-value judgments. *Glossa* 6(1): 110.
- Musolino, J. & Lidz, J. (2003). The scope of isomorphism.
  *Journal of Child Language* 30: 915–950.
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
  | exact    -- "two" = exactly 2 (Kennedy 2015)
  | atLeast  -- "two" = at least 2 (Horn 1972)
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

/-- In the 1-of-2 context (n=2), both numeral readings give truth conditions
    identical to `scopeTruth`. With only 2 horses, "exactly 2" and "at least 2"
    have the same extension over {0, 1, 2}, so the choice of numeral semantics
    is immaterial. The every-not model's `scopeTruth` thus covers the 1-of-2
    two-not case (paper §4.2, p. 25). -/
theorem exact_atleast_agree_1of2 :
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

end Phenomena.Quantification.Studies.ScontrasPearl2021
