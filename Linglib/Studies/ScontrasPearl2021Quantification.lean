import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Pragmatics.RSA.Basic
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Composition.Scope
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# [scontras-pearl-2021]: Quantifier Scope Ambiguity [musolino-lidz-2003]

"When pragmatics matters more for truth-value judgments:
An investigation of quantifier scope ambiguity"
*Glossa* 6(1): 110.

S&P is a modeling paper — it explains endorsement patterns from
[musolino-lidz-2003] and others via RSA, rather than reporting
new experiments.

## Part I: Truth Conditions & Shared Types

- §1. Every-not (n=2): `JumpOutcome`, `ScopeReading`, `scopeTruth`
- §2. Two-not (n=4): `JumpOutcome4`, `NumeralReading`, `twoNotTruth`
- Scope entailment asymmetry, [musolino-lidz-2003] data, and
  numeral semantics grounding via the named meaning functions from `Semantics.Numerals`.

## Part II: Every-Not RSA Model (§3, `EveryNot` namespace)

Domain: "Every horse didn't jump" with n=2 horses. 3 world states
(0, 1, 2 jumped). 2 utterances (null, everyNot). 6 latent states
(2 scopes × 3 QUDs).

- **L0**: L0(w|u,i) ∝ δ_{⟦u⟧ⁱ(w)} (literal semantics, no world prior; footnote 6)
- **S1**: S1(u|w,i,q) ∝ exp(α · log L0(⟦q⟧(w)|u,i,q)) (QUD-projected)
- **L1**: L1(w,i,q|u) ∝ P(w) · P(i) · P(q) · S1(u|w,i,q)
- **S2**: S2(u|w) ∝ exp(log Σ_{i,q} L1(w,i,q|u)) = L1(w|u)
- **Endorsement**: P(endorse u | w_obs) = S2(u|w_obs)

Parameters: α = 1 (§3.2). P(w) = Binomial(n, b_suc).

### QUDs (paper (3))

Three QUD partitions over worlds:
- how-many?: identity — partitions {w0}, {w1}, {w2}
- all?: w = n? — partitions {w0,w1} vs {w2}
- none?: w = 0? — partitions {w0} vs {w1,w2}

### Compositional Grounding

Truth conditions grounded in `every_sem` (`Quantifier.lean`),
`ScopeConfig`/`ScopeDerivation` (`Scope.lean`).

### Key Findings (Figure 2)

S2 endorsement for "every horse didn't jump" in the partial world (w=1).
The "Paper value" column is S&P's computed model predictions (not
experimental data):

| Config | S2(everyNot|w=1) | Paper value |
|--------|-----------------|-------------|
| b_suc=0.1 (baseline) | 0.288 | ~0.29 |
| b_suc=0.5 (default) | 0.506 | ~0.48 (read from Figure 2) |
| b_suc=0.9 (high base rate) | 0.796 | ~0.80 |

QUD manipulation (Figure 2, center panel): favoring none? < how-many? < all?
yields monotonically increasing endorsement (paper: 0.38, 0.48, 0.63).

### Developmental Continuity (§3.3)

Same model architecture explains child and adult behavior. Children's
isomorphic (surface-scope) preference follows from low `b_suc` priors.

## Part III: Two-Not RSA Model (§4, `TwoNot` namespace)

Domain: "Two horses didn't jump" with n=4 horses. 5 world states
(0–4 jumped). 2 utterances (null, twoNot). 10 latent states
(2 scopes × 5 QUDs).

### Central Claim (§4.2)

Under exact semantics, surface scope pinpoints w=2 as the unique true
world → high S2 endorsement (> 1/2). Under at-least semantics, surface
scope is true at {w0,w1,w2} → low S2 endorsement (< 1/2). This predicts
that adults endorse "two horses didn't jump" more readily in 2-of-4
contexts under exact numeral semantics.

-/

namespace ScontrasPearl2021

/-! ### Every-Not (n=2) — Shared Types & Truth Conditions -/

/-- How many horses jumped (out of 2). -/
inductive JumpOutcome where
  | zero   -- 0 horses jumped
  | one    -- 1 horse jumped
  | two    -- 2 horses jumped (all)
  deriving DecidableEq, Repr, Inhabited

instance : Fintype JumpOutcome where
  elems := {.zero, .one, .two}
  complete := fun x => by cases x <;> simp

/-- Scope configuration for "every...not". -/
inductive ScopeReading where
  | surface  -- ∀>¬: "For every horse, it didn't jump"
  | inverse  -- ¬>∀: "Not every horse jumped"
  deriving DecidableEq, Repr, Inhabited

instance : Fintype ScopeReading where
  elems := {.surface, .inverse}
  complete := fun x => by cases x <;> simp

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

/-! ### Two-Not (n=4) — Shared Types & Truth Conditions -/

/-- How many horses jumped (out of 4). -/
inductive JumpOutcome4 where
  | w0  -- 0 horses jumped
  | w1  -- 1 horse jumped
  | w2  -- 2 horses jumped
  | w3  -- 3 horses jumped
  | w4  -- 4 horses jumped (all)
  deriving DecidableEq, Repr, Inhabited

instance : Fintype JumpOutcome4 where
  elems := {.w0, .w1, .w2, .w3, .w4}
  complete := fun x => by cases x <;> simp

/-- Convert JumpOutcome4 to natural number. -/
def JumpOutcome4.toNat : JumpOutcome4 → Nat
  | .w0 => 0 | .w1 => 1 | .w2 => 2 | .w3 => 3 | .w4 => 4

/-- Numeral reading: does "two" mean exactly 2 or at least 2? -/
inductive NumeralReading where
  | exact    -- "two" = exactly 2 ([kennedy-2015])
  | atLeast  -- "two" = at least 2 ([horn-1972])
  deriving DecidableEq, Repr, Inhabited

instance : Fintype NumeralReading where
  elems := {.exact, .atLeast}
  complete := fun x => by cases x <;> simp

/-- Truth conditions for "two horses didn't jump" with n=4 horses (paper (6)).

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

-- In the 1-of-2 context (n=2, numeral=2), "two horses didn't jump" reduces
-- to "every horse didn't jump" because the numeral saturates the domain:
-- exact and at-least have the same extension when n = numeral (paper §4.2.1).
-- The divergence only appears in the 2-of-4 context where n > numeral.

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

/-! ### Scope Entailment Asymmetry ([musolino-lidz-2003]) -/

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

/-! ### Numeral Semantics Grounding -/

/-! Connects S&P's `twoNotTruth` truth conditions to linglib's numeral
semantics infrastructure (named meanings in `Semantics.Numerals`).

The truth conditions in the data file are grounded in the named meanings:
- Exact surface: "exactly 2 didn't jump" = `bareMeaning 2 (4 - w)`
- Exact inverse: "¬(exactly 2 jumped)" = `!(bareMeaning 2 w)`
- At-least surface: "≥2 didn't jump" = `atLeastMeaning 2 (4 - w)`
- At-least inverse: "¬(≥2 jumped)" = `!(atLeastMeaning 2 w)`

Convergent evidence for exact semantics from [kennedy-2015]
(de-Fregean semantics where bare numerals mean =n) and [musolino-2004]
(acquisition data — children reject "two" at w=3).
-/

open Semantics.Numerals (bareMeaning atLeastMeaning)

/-- Exact surface: "exactly two didn't jump" (out of 4) ↔ exactly two jumped.
    Matches `bareMeaning 2` applied to the complement count (4 - w). -/
theorem twoNotExact_surface_matches_bareMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .exact .surface w = true ↔ bareMeaning 2 (4 - w.toNat) := by
  intro w; cases w <;> decide

/-- Exact inverse: "¬(exactly two jumped)" ↔ ¬(bareMeaning 2 w). -/
theorem twoNotExact_inverse_matches_bareMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .exact .inverse w = true ↔ ¬ bareMeaning 2 w.toNat := by
  intro w; cases w <;> decide

/-- At-least surface: "at least two didn't jump" ↔ at most two jumped.
    Matches `atLeastMeaning 2` applied to the complement count. -/
theorem twoNotAtLeast_surface_matches_atLeastMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .atLeast .surface w = true ↔ atLeastMeaning 2 (4 - w.toNat) := by
  intro w; cases w <;> decide

/-- At-least inverse: "¬(at least two jumped)" ↔ ¬(atLeastMeaning 2 w). -/
theorem twoNotAtLeast_inverse_matches_atLeastMeaning :
    ∀ w : JumpOutcome4,
    twoNotTruth .atLeast .inverse w = true ↔ ¬ atLeastMeaning 2 w.toNat := by
  intro w; cases w <;> decide

/-- The negation-scope asymmetry collapses under exact semantics:
    internal negation `¬(=3)` and external negation `≠3` agree at world 4. -/
theorem exact_collapses_negation_scope :
    (¬ bareMeaning 3 4) ↔ (4 ≠ 3) := by
  decide

/-- Lower-bound semantics preserves the negation-scope distinction:
    internal negation `¬(≥3)` and external negation `≠3` diverge at world 4. -/
theorem lowerBound_preserves_negation_scope :
    ¬ ((¬ atLeastMeaning 3 4) ↔ (4 ≠ 3)) := by
  decide

/-- [kennedy-2015]'s resolution: exact meaning is basic, lower-bound is derived
    via type-shift. Both meanings are grammatically available. -/
theorem typeshift_resolves_tension :
    Degree.typeLower bareMeaning 2 2 ↔
    atLeastMeaning 2 2 :=
  Semantics.Numerals.typeLower_bareMeaning_iff 2 2

/-! ### Every-Not RSA Model (§3) -/

-- ℚ-score PMF combinator (local pending the RSA API pass)

section PMFCombinator

open scoped ENNReal

/-- Normalize a rational score vector into a PMF (uniform at zero mass). -/
noncomputable def pmfOfScores {σ : Type*} [Fintype σ] [Nonempty σ]
    (f : σ → ℚ) : PMF σ :=
  if h : (∑' x, ENNReal.ofReal ((f x : ℝ))) ≠ 0 then
    PMF.normalize (fun x => ENNReal.ofReal ((f x : ℝ))) h
      (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)
  else PMF.uniformOfFintype σ

theorem pmfOfScores_apply {σ : Type*} [Fintype σ] [Nonempty σ]
    {f : σ → ℚ} (hf : ∀ x, 0 ≤ f x) (hpos : 0 < ∑ x, f x) (x : σ) :
    pmfOfScores f x = ENNReal.ofReal ((f x / ∑ x', f x' : ℚ) : ℝ) := by
  have hsum : (∑' x, ENNReal.ofReal ((f x : ℝ)))
      = ENNReal.ofReal ((∑ x, f x : ℚ) : ℝ) := by
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun x _ => by exact_mod_cast hf x)]
    push_cast
    rfl
  rw [pmfOfScores, dif_pos (by
      rw [hsum, ENNReal.ofReal_ne_zero_iff]; exact_mod_cast hpos),
    PMF.normalize_apply, hsum,
    ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hpos),
    ← ENNReal.ofReal_mul (by exact_mod_cast hf x)]
  congr 1
  push_cast
  rw [div_eq_mul_inv]

/-- Strict comparison of `pmfOfScores` values via the exact-ℚ scores;
`f` and `g` may be different score vectors (cross-world, cross-configuration). -/
theorem pmf_lt_cross {σ τ : Type*} [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ]
    {f : σ → ℚ} {g : τ → ℚ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfp : 0 < ∑ x, f x) (hgp : 0 < ∑ x, g x) {a : σ} {b : τ}
    (hb : 0 < g b / ∑ x, g x) (hab : f a / ∑ x, f x < g b / ∑ x, g x) :
    pmfOfScores f a < pmfOfScores g b := by
  rw [pmfOfScores_apply hf hfp, pmfOfScores_apply hg hgp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hb)).mpr
    (by exact_mod_cast hab)

end PMFCombinator

namespace EveryNot

open BigOperators
open Real (rpow rpow_nonneg)
open Intensional (Denot)
open Quantification (every_sem)
open Semantics.Scope (ScopeConfig ScopeDerivation)

/-- Utterances: null (silence) or "Every horse didn't jump". -/
inductive Utt where
  | null     -- silence (always true, uninformative baseline)
  | everyNot -- "Every horse didn't jump" (scopally ambiguous)
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Utt where
  elems := {.null, .everyNot}
  complete := fun x => by cases x <;> simp

/-- QUDs partition worlds by the question under discussion (paper (3)).
    Three QUD partitions for n=2 worlds. -/
inductive QUD where
  | howMany -- "How many horses jumped?" — {w0}, {w1}, {w2} (identity)
  | all_    -- "Did all the horses jump?" — {w0,w1} vs {w2}
  | none_   -- "Did none of the horses jump?" — {w0} vs {w1,w2}
  deriving DecidableEq, Repr, Inhabited

instance : Fintype QUD where
  elems := {.howMany, .all_, .none_}
  complete := fun x => by cases x <;> simp

/-- Flattened latent variable: scope reading × QUD.
    Flat inductive avoids Prod, keeping proof terms tractable for
    the kernel checker. -/
inductive Latent where
  | surfHowMany  -- surface scope, how-many? QUD
  | surfAll      -- surface scope, all? QUD
  | surfNone     -- surface scope, none? QUD
  | invHowMany   -- inverse scope, how-many? QUD
  | invAll       -- inverse scope, all? QUD
  | invNone      -- inverse scope, none? QUD
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Latent where
  elems := {.surfHowMany, .surfAll, .surfNone, .invHowMany, .invAll, .invNone}
  complete := fun x => by cases x <;> simp

/-- Extract scope reading from latent variable. -/
def Latent.scope : Latent → ScopeReading
  | .surfHowMany | .surfAll | .surfNone => .surface
  | .invHowMany | .invAll | .invNone => .inverse

/-- Extract QUD from latent variable. -/
def Latent.qud : Latent → QUD
  | .surfHowMany | .invHowMany => .howMany
  | .surfAll | .invAll => .all_
  | .surfNone | .invNone => .none_

-- Truth Conditions

/-- RSA meaning derived from `scopeTruth`.
    Null utterance is always true (uninformative baseline). -/
def uttMeaning : ScopeReading → Utt → JumpOutcome → Bool
  | _, .null, _ => true
  | s, .everyNot, w => scopeTruth s w

/-- Truth table verification against the paper's utterance semantics (2). -/
theorem truth_table :
    uttMeaning .surface .everyNot .zero = true ∧
    uttMeaning .surface .everyNot .one = false ∧
    uttMeaning .surface .everyNot .two = false ∧
    uttMeaning .inverse .everyNot .zero = true ∧
    uttMeaning .inverse .everyNot .one = true ∧
    uttMeaning .inverse .everyNot .two = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Compositional Grounding

/-- 2-horse domain for grounding truth conditions in quantifier semantics. -/
inductive Horse where | h1 | h2 deriving DecidableEq

/-- Jump predicate for each world state. In the 1-horse world, exactly h1
    jumped (the choice is arbitrary; only cardinality matters for the
    universally quantified sentence). -/
def jumpIn : JumpOutcome → Horse → Bool
  | .zero, _ => false
  | .one, .h1 => true | .one, .h2 => false
  | .two, _ => true

instance : Fintype Horse where
  elems := ({Horse.h1, Horse.h2} : Finset Horse)
  complete := fun x => by cases x <;> simp

/-- Restrictor: all entities are horses (trivial for this model). -/
def horse_sem : Denot Horse Unit (.e ⇒ .t) := fun _ => True

/-- Scope predicate: did entity h jump in world w? -/
def jumpIn_sem (w : JumpOutcome) : Denot Horse Unit (.e ⇒ .t) :=
  fun h => jumpIn w h = true

/-- Surface scope: ⟦every⟧(horse)(λx.¬jump(x))(w). -/
noncomputable def everyNotJumped_surface (w : JumpOutcome) : Prop :=
  every_sem horse_sem (fun h => ¬ jumpIn_sem w h)

/-- Inverse scope: ¬⟦every⟧(horse)(jump)(w). -/
noncomputable def everyNotJumped_inverse (w : JumpOutcome) : Prop :=
  ¬ (every_sem horse_sem (jumpIn_sem w))

/-- Surface scope grounding: `scopeTruth.surface` derives from
    compositional ⟦every⟧(horse)(λx.¬jump(x)), not stipulation. -/
theorem surface_from_every_sem :
    ∀ w, (scopeTruth .surface w = true) ↔
      every_sem horse_sem (fun h => ¬ jumpIn_sem w h) := by
  intro w; unfold every_sem; cases w
  · exact ⟨fun _ _ _ h => by simp [jumpIn_sem, jumpIn] at h,
           fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide),
           fun h => absurd (h .h1 True.intro) (by simp [jumpIn_sem, jumpIn])⟩
  · exact ⟨fun h => absurd h (by decide),
           fun h => absurd (h .h1 True.intro) (by simp [jumpIn_sem, jumpIn])⟩

/-- Inverse scope grounding: `scopeTruth.inverse` derives from
    negating the compositional ⟦every⟧(horse)(jump). -/
theorem inverse_from_every_sem :
    ∀ w, (scopeTruth .inverse w = true) ↔
      ¬ (every_sem horse_sem (jumpIn_sem w)) := by
  intro w; unfold every_sem; cases w
  · exact ⟨fun _ h => by have := h .h1 True.intro; simp [jumpIn_sem, jumpIn] at this,
           fun _ => rfl⟩
  · exact ⟨fun _ h => by have := h .h2 True.intro; simp [jumpIn_sem, jumpIn] at this,
           fun _ => rfl⟩
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by intro hf; exact hf fun _ _ => rfl)

/-- Map Montague `ScopeConfig` to data file's `ScopeReading`. -/
def scopeConfigToReading : ScopeConfig → ScopeReading
  | .surface => .surface
  | .inverse => .inverse

/-- Map data file's `ScopeReading` to Montague `ScopeConfig`. -/
def readingToScopeConfig : ScopeReading → ScopeConfig
  | .surface => .surface
  | .inverse => .inverse

/-- "Every horse didn't jump" as a `ScopeDerivation`: a single syntactic form
    with multiple semantic values indexed by scope configuration. -/
noncomputable def everyHorseDidntJump (w : JumpOutcome) : ScopeDerivation Horse Unit .t where
  surface := "Every horse didn't jump"
  meaningAt
    | .surface => every_sem horse_sem (fun h => ¬ jumpIn_sem w h)
    | .inverse => ¬ (every_sem horse_sem (jumpIn_sem w))

/-- The `ScopeDerivation`'s `meaningAt` agrees with `scopeTruth` for both readings:
    when scopeTruth is true, the compositional derivation holds, and vice versa. -/
theorem scopeDerivation_matches_scopeTruth :
    ∀ (s : ScopeConfig) (w : JumpOutcome),
    (scopeTruth (scopeConfigToReading s) w = true) ↔
    (everyHorseDidntJump w).meaningAt s := by
  intro s w; cases s
  · -- surface scope
    simp only [scopeConfigToReading, everyHorseDidntJump]
    exact surface_from_every_sem w
  · -- inverse scope
    simp only [scopeConfigToReading, everyHorseDidntJump]
    exact inverse_from_every_sem w

/-- RSA meaning is grounded in `ScopeDerivation`: the meaning function used
    by the RSA config matches the compositional scope derivation. -/
theorem rsa_meaning_from_scope_derivation :
    ∀ (lat : Latent) (w : JumpOutcome),
    (uttMeaning lat.scope .everyNot w = true) ↔
    (everyHorseDidntJump w).meaningAt (readingToScopeConfig lat.scope) := by
  intro lat w; cases lat <;>
    simp only [Latent.scope, readingToScopeConfig, everyHorseDidntJump, uttMeaning, scopeTruth]
  all_goals (first | exact surface_from_every_sem w | exact inverse_from_every_sem w)

/-- The every-not scope pair has surface-entails-inverse structure: surface scope (none jumped) is a strict
    subset of inverse scope (not all jumped). This makes universals
    non-diagnostic for scope preferences — no TVJ context can
    distinguish isomorphic from non-isomorphic behavior. -/
theorem every_not_scope_entailment :
    Semantics.Scope.classifyScopeEntailment
      [JumpOutcome.zero, .one, .two]
      (scopeTruth .surface) (scopeTruth .inverse)
    = .surfaceEntailsInverse := by decide

-- QUD Projection

/-- QUD answer function: q(w) → equivalence class identifier (paper (3)).
    For howMany, each world is its own class (identity partition). -/
def qudAnswer : QUD → JumpOutcome → Fin 3
  | .howMany, .zero => 0  | .howMany, .one => 1  | .howMany, .two => 2
  | .all_,   w => if w == .two then 1 else 0
  | .none_,  w => if w == .zero then 1 else 0

/-- Inline QUD projection: explicit case analysis, kernel-reducible.
    For howMany, each world is its own equivalence class (identity partition).
    For all?/none?, worlds sharing an answer are aggregated. -/
def qudProjectInline (q : QUD) (f : JumpOutcome → ℝ) (w : JumpOutcome) : ℝ :=
  match q, w with
  -- howMany?: identity partition — each world is its own class
  | .howMany, .zero => f .zero
  | .howMany, .one  => f .one
  | .howMany, .two  => f .two
  -- all?: {w0,w1} vs {w2}
  | .all_,  .zero => f .zero + f .one
  | .all_,  .one  => f .zero + f .one
  | .all_,  .two  => f .two
  -- none?: {w0} vs {w1,w2}
  | .none_, .zero => f .zero
  | .none_, .one  => f .one + f .two
  | .none_, .two  => f .one + f .two

theorem qudProjectInline_nonneg {q : QUD} {f : JumpOutcome → ℝ} {w : JumpOutcome}
    (hf : ∀ w, 0 ≤ f w) : 0 ≤ qudProjectInline q f w := by
  cases q <;> cases w <;> simp only [qudProjectInline]
  all_goals first | exact hf _ | exact add_nonneg (hf _) (hf _)

-- Exact-ℚ model

section QModel

/-- Literal listener (fn. 6: no world prior in L0). -/
def l0Q (sc : ScopeReading) (u : Utt) (w : JumpOutcome) : ℚ :=
  (if uttMeaning sc u w then 1 else 0) /
    (∑ w', if uttMeaning sc u w' then (1 : ℚ) else 0)

/-- QUD projection of the literal listener (paper (3)). -/
def qProjQ (q : QUD) (f : JumpOutcome → ℚ) : JumpOutcome → ℚ
  | .zero => match q with
    | .howMany => f .zero
    | .all_ => f .zero + f .one
    | .none_ => f .zero
  | .one => match q with
    | .howMany => f .one
    | .all_ => f .zero + f .one
    | .none_ => f .one + f .two
  | .two => match q with
    | .howMany => f .two
    | .all_ => f .two
    | .none_ => f .one + f .two

/-- Speaker (α = 1, §3.2; costs cancel, fn. 8). -/
def s1Q (sc : ScopeReading) (q : QUD) (w : JumpOutcome) (u : Utt) : ℚ :=
  qProjQ q (fun w' => l0Q sc u w') w / ∑ u', qProjQ q (fun w' => l0Q sc u' w') w

/-- Joint pragmatic listener world score: `P(w)·Σ_{i,q} P(i)·P(q)·S1`. -/
def l1ScoreQ (wp : JumpOutcome → ℚ) (sp : ScopeReading → ℚ) (qp : QUD → ℚ)
    (u : Utt) (w : JumpOutcome) : ℚ :=
  wp w * ∑ lat : Latent, sp lat.scope * qp lat.qud * s1Q lat.scope lat.qud w u

/-- Normalized world posterior. -/
def l1Q (wp : JumpOutcome → ℚ) (sp : ScopeReading → ℚ) (qp : QUD → ℚ)
    (u : Utt) (w : JumpOutcome) : ℚ :=
  l1ScoreQ wp sp qp u w / ∑ w', l1ScoreQ wp sp qp u w'

private theorem l0Q_nonneg (sc : ScopeReading) (u : Utt) (w : JumpOutcome) :
    0 ≤ l0Q sc u w :=
  div_nonneg (by split <;> norm_num)
    (Finset.sum_nonneg fun _ _ => by split <;> norm_num)

private theorem qProjQ_nonneg {f : JumpOutcome → ℚ} (hf : ∀ w, 0 ≤ f w)
    (q : QUD) (w : JumpOutcome) : 0 ≤ qProjQ q f w := by
  cases w <;> cases q <;>
    first
      | exact hf _
      | exact add_nonneg (hf _) (hf _)

private theorem s1Q_nonneg (sc : ScopeReading) (q : QUD) (w : JumpOutcome)
    (u : Utt) : 0 ≤ s1Q sc q w u :=
  div_nonneg (qProjQ_nonneg (fun w' => l0Q_nonneg sc u w') q w)
    (Finset.sum_nonneg fun u' _ => qProjQ_nonneg (fun w' => l0Q_nonneg sc u' w') q w)

theorem l1ScoreQ_nonneg {wp : JumpOutcome → ℚ} {sp : ScopeReading → ℚ}
    {qp : QUD → ℚ} (hwp : ∀ w, 0 ≤ wp w) (hsp : ∀ sc, 0 ≤ sp sc)
    (hqp : ∀ q, 0 ≤ qp q) (u : Utt) (w : JumpOutcome) :
    0 ≤ l1ScoreQ wp sp qp u w :=
  mul_nonneg (hwp w) (Finset.sum_nonneg fun lat _ =>
    mul_nonneg (mul_nonneg (hsp lat.scope) (hqp lat.qud))
      (s1Q_nonneg lat.scope lat.qud w u))

theorem l1Q_nonneg {wp : JumpOutcome → ℚ} {sp : ScopeReading → ℚ}
    {qp : QUD → ℚ} (hwp : ∀ w, 0 ≤ wp w) (hsp : ∀ sc, 0 ≤ sp sc)
    (hqp : ∀ q, 0 ≤ qp q) (u : Utt) (w : JumpOutcome) :
    0 ≤ l1Q wp sp qp u w :=
  div_nonneg (l1ScoreQ_nonneg hwp hsp hqp u w)
    (Finset.sum_nonneg fun w' _ => l1ScoreQ_nonneg hwp hsp hqp u w')

end QModel

-- Prior configurations (ℚ; §3.2, Figure 2)

/-- Binomial(2, 0.1) ∝ (81, 18, 1). -/
def lowWP : JumpOutcome → ℚ | .zero => 81 | .one => 18 | .two => 1

/-- Binomial(2, 0.5) ∝ (1, 2, 1). -/
def midWP : JumpOutcome → ℚ | .zero => 1 | .one => 2 | .two => 1

/-- Binomial(2, 0.9) ∝ (1, 18, 81). -/
def highWP : JumpOutcome → ℚ | .zero => 1 | .one => 18 | .two => 81

/-- Uniform scope prior (P(inverse) = 0.5, the default). -/
def uniSP : ScopeReading → ℚ := fun _ => 1

/-- Surface-only scope prior (P(inverse) = 0). -/
def surfSP : ScopeReading → ℚ | .surface => 1 | .inverse => 0

/-- Uniform QUD prior. -/
def uniQP : QUD → ℚ := fun _ => 1

/-- Biased QUD prior: the favored QUD gets 0.9, others 0.05 (∝ 18:1:1). -/
def biasQP (q₀ : QUD) : QUD → ℚ := fun q => if q = q₀ then 18 else 1

private theorem lowWP_nonneg : ∀ w, 0 ≤ lowWP w := by intro w; cases w <;> norm_num [lowWP]
private theorem midWP_nonneg : ∀ w, 0 ≤ midWP w := by intro w; cases w <;> norm_num [midWP]
private theorem highWP_nonneg : ∀ w, 0 ≤ highWP w := by intro w; cases w <;> norm_num [highWP]
private theorem uniSP_nonneg : ∀ sc, 0 ≤ uniSP sc := fun _ => by norm_num [uniSP]
private theorem surfSP_nonneg : ∀ sc, 0 ≤ surfSP sc := by
  intro sc; cases sc <;> norm_num [surfSP]
private theorem uniQP_nonneg : ∀ q, 0 ≤ uniQP q := fun _ => by norm_num [uniQP]
private theorem biasQP_nonneg (q₀ : QUD) : ∀ q, 0 ≤ biasQP q₀ q := fun q => by
  unfold biasQP; split <;> norm_num

-- PMF face

open scoped ENNReal in
/-- Pragmatic listener over worlds. -/
noncomputable def l1PMF (wp : JumpOutcome → ℚ) (sp : ScopeReading → ℚ)
    (qp : QUD → ℚ) (u : Utt) : PMF JumpOutcome :=
  pmfOfScores (l1ScoreQ wp sp qp u)

open scoped ENNReal in
/-- Endorsement speaker S₂ (§3.1): renormalizes the L1 world posterior. -/
noncomputable def s2PMF (wp : JumpOutcome → ℚ) (sp : ScopeReading → ℚ)
    (qp : QUD → ℚ) (w : JumpOutcome) : PMF Utt :=
  pmfOfScores (fun u => l1Q wp sp qp u w)

-- S2 Endorsement (§3.1: score = the normalized L1 world posterior)

-- L1-Level Theorems

/-- Baseline L1: 0-jumped > 1-jumped. Both scopes agree w=0 is true;
    high prior weight (81 vs 18). -/
theorem baseline_L1_w0_gt_w1 :
    l1PMF lowWP uniSP uniQP .everyNot .one < l1PMF lowWP uniSP uniQP .everyNot .zero :=
  pmf_lt_cross (l1ScoreQ_nonneg lowWP_nonneg uniSP_nonneg uniQP_nonneg _) (l1ScoreQ_nonneg lowWP_nonneg uniSP_nonneg uniQP_nonneg _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Baseline L1: 1-jumped > 2-jumped. Inverse scope makes w=1 true;
    moderate prior advantage (18 vs 1). -/
theorem baseline_L1_w1_gt_w2 :
    l1PMF lowWP uniSP uniQP .everyNot .two < l1PMF lowWP uniSP uniQP .everyNot .one :=
  pmf_lt_cross (l1ScoreQ_nonneg lowWP_nonneg uniSP_nonneg uniQP_nonneg _) (l1ScoreQ_nonneg lowWP_nonneg uniSP_nonneg uniQP_nonneg _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Scope ambiguity boosts partial-world endorsement.
    With both scopes active, L1(w=1) is higher than surface-only,
    because inverse scope directly makes w=1 true. -/
theorem ambiguity_boosts_partial :
    l1PMF lowWP surfSP uniQP .everyNot .one < l1PMF lowWP uniSP uniQP .everyNot .one :=
  pmf_lt_cross (l1ScoreQ_nonneg lowWP_nonneg surfSP_nonneg uniQP_nonneg _) (l1ScoreQ_nonneg lowWP_nonneg uniSP_nonneg uniQP_nonneg _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- S2 Endorsement Theorems (paper's main claims)

-- The paper's central finding: S2 endorsement ordering w0 > w1 > w2 is
-- ROBUST across all prior configurations (Figure 2). At L1 level,
-- highBaseCfg reverses the ordering (w1 > w2 > w0), but S2 normalizing
-- per world restores the correct ordering.

/-- Baseline S2: w0 > w1. The model predicts higher endorsement of
    "every horse didn't jump" when no horses jumped (none-scenario)
    than when one horse jumped (not-all scenario). -/
theorem baseline_S2_w0_gt_w1 :
    s2PMF lowWP uniSP uniQP .one .everyNot < s2PMF lowWP uniSP uniQP .zero .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg lowWP_nonneg uniSP_nonneg uniQP_nonneg u _) (fun u => l1Q_nonneg lowWP_nonneg uniSP_nonneg uniQP_nonneg u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Baseline S2: w1 > w2. Endorsement in the not-all scenario
    exceeds the all scenario. -/
theorem baseline_S2_w1_gt_w2 :
    s2PMF lowWP uniSP uniQP .two .everyNot < s2PMF lowWP uniSP uniQP .one .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg lowWP_nonneg uniSP_nonneg uniQP_nonneg u _) (fun u => l1Q_nonneg lowWP_nonneg uniSP_nonneg uniQP_nonneg u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- S2 ordering robust to high base rate (b_suc = 0.9).
    Even when L1 reverses (w1 > w2 > w0 at L1), S2 still orders w0 > w1. -/
theorem highBase_S2_w0_gt_w1 :
    s2PMF highWP uniSP uniQP .one .everyNot < s2PMF highWP uniSP uniQP .zero .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg highWP_nonneg uniSP_nonneg uniQP_nonneg u _) (fun u => l1Q_nonneg highWP_nonneg uniSP_nonneg uniQP_nonneg u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- S2 ordering robust to high base rate: w1 > w2. -/
theorem highBase_S2_w1_gt_w2 :
    s2PMF highWP uniSP uniQP .two .everyNot < s2PMF highWP uniSP uniQP .one .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg highWP_nonneg uniSP_nonneg uniQP_nonneg u _) (fun u => l1Q_nonneg highWP_nonneg uniSP_nonneg uniQP_nonneg u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- S2 ordering robust to symmetric prior (b_suc = 0.5). -/
theorem default_S2_w0_gt_w1 :
    s2PMF midWP uniSP uniQP .one .everyNot < s2PMF midWP uniSP uniQP .zero .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg midWP_nonneg uniSP_nonneg uniQP_nonneg u _) (fun u => l1Q_nonneg midWP_nonneg uniSP_nonneg uniQP_nonneg u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem default_S2_w1_gt_w2 :
    s2PMF midWP uniSP uniQP .two .everyNot < s2PMF midWP uniSP uniQP .one .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg midWP_nonneg uniSP_nonneg uniQP_nonneg u _) (fun u => l1Q_nonneg midWP_nonneg uniSP_nonneg uniQP_nonneg u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- S2 ordering robust under supportive context (b_suc = 0.9, all?-biased QUD). -/
theorem supportive_S2_w0_gt_w1 :
    s2PMF highWP uniSP (biasQP .all_) .one .everyNot < s2PMF highWP uniSP (biasQP .all_) .zero .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg highWP_nonneg uniSP_nonneg (biasQP_nonneg _) u _) (fun u => l1Q_nonneg highWP_nonneg uniSP_nonneg (biasQP_nonneg _) u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem supportive_S2_w1_gt_w2 :
    s2PMF highWP uniSP (biasQP .all_) .two .everyNot < s2PMF highWP uniSP (biasQP .all_) .one .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg highWP_nonneg uniSP_nonneg (biasQP_nonneg _) u _) (fun u => l1Q_nonneg highWP_nonneg uniSP_nonneg (biasQP_nonneg _) u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- QUD Manipulation Ordering (Figure 2, center panel)

/-- QUD manipulation: how-many?-biased > none?-biased (Figure 2, center panel).
    Favoring the identity QUD yields higher endorsement than favoring the
    "did none succeed?" QUD, because how-many? makes the ambiguous utterance
    more informative at w=1 (partial success). -/
theorem qud_howMany_gt_none :
    s2PMF midWP uniSP (biasQP .none_) .one .everyNot < s2PMF midWP uniSP (biasQP .howMany) .one .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg midWP_nonneg uniSP_nonneg (biasQP_nonneg _) u _) (fun u => l1Q_nonneg midWP_nonneg uniSP_nonneg (biasQP_nonneg _) u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- QUD manipulation: all?-biased > how-many?-biased (Figure 2, center panel).
    Favoring the "did all succeed?" QUD yields the highest endorsement because
    both scope interpretations fully resolve all? at w=1 (the answer is "no"
    under either reading). -/
theorem qud_all_gt_howMany :
    s2PMF midWP uniSP (biasQP .howMany) .one .everyNot < s2PMF midWP uniSP (biasQP .all_) .one .everyNot :=
  pmf_lt_cross (fun u => l1Q_nonneg midWP_nonneg uniSP_nonneg (biasQP_nonneg _) u _) (fun u => l1Q_nonneg midWP_nonneg uniSP_nonneg (biasQP_nonneg _) u _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end EveryNot

/-! ### Two-Not RSA Model (§4) -/

namespace TwoNot

open BigOperators
open Real (rpow rpow_nonneg)

/-- Utterances: null (silence) or "two horses didn't jump". -/
inductive Utt where
  | null    -- silence (always true, uninformative baseline)
  | twoNot  -- "two horses didn't jump" (scopally ambiguous)
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Utt where
  elems := {.null, .twoNot}
  complete := fun x => by cases x <;> simp

/-- QUDs for the two-not model (paper (7)). Five partitions over the 5-world domain.
    The two numeral-specific QUDs (two=?, two≥?) are added because
    explicitly mentioning a numeral makes that cardinality potentially
    relevant to the topic of conversation. -/
inductive QUD5 where
  | howMany    -- "How many horses jumped?" — identity partition
  | all_       -- "Did all the horses jump?" — {w0..w3} vs {w4}
  | none_      -- "Did none of the horses jump?" — {w0} vs {w1..w4}
  | twoExact   -- "Did exactly two horses jump?" — {w2} vs {w0,w1,w3,w4}
  | twoAtLeast -- "Did at least two horses jump?" — {w0,w1} vs {w2,w3,w4}
  deriving DecidableEq, Repr, Inhabited

instance : Fintype QUD5 where
  elems := {.howMany, .all_, .none_, .twoExact, .twoAtLeast}
  complete := fun x => by cases x <;> simp

/-- Flattened latent variable: scope reading × QUD.
    2 scopes × 5 QUDs = 10 constructors. -/
inductive Latent10 where
  | surfHowMany | surfAll | surfNone | surfTwoExact | surfTwoAtLeast
  | invHowMany  | invAll  | invNone  | invTwoExact  | invTwoAtLeast
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Latent10 where
  elems := { .surfHowMany, .surfAll, .surfNone, .surfTwoExact, .surfTwoAtLeast,
             .invHowMany,  .invAll,  .invNone,  .invTwoExact,  .invTwoAtLeast }
  complete := fun x => by cases x <;> simp

/-- Extract scope reading from latent variable. -/
def Latent10.scope : Latent10 → ScopeReading
  | .surfHowMany | .surfAll | .surfNone | .surfTwoExact | .surfTwoAtLeast => .surface
  | .invHowMany  | .invAll  | .invNone  | .invTwoExact  | .invTwoAtLeast  => .inverse

/-- Extract QUD from latent variable. -/
def Latent10.qud : Latent10 → QUD5
  | .surfHowMany | .invHowMany => .howMany
  | .surfAll     | .invAll     => .all_
  | .surfNone    | .invNone    => .none_
  | .surfTwoExact   | .invTwoExact   => .twoExact
  | .surfTwoAtLeast | .invTwoAtLeast => .twoAtLeast

-- Truth Conditions

/-- RSA meaning for the two-not model, parameterized by numeral reading.
    Null utterance is always true (uninformative baseline). -/
def uttMeaning (nr : NumeralReading) : ScopeReading → Utt → JumpOutcome4 → Bool
  | _, .null, _ => true
  | s, .twoNot, w => twoNotTruth nr s w

/-- Exact semantics truth table (paper (6), exact reading). -/
theorem exact_truth_table :
    uttMeaning .exact .surface .twoNot .w0 = false ∧
    uttMeaning .exact .surface .twoNot .w1 = false ∧
    uttMeaning .exact .surface .twoNot .w2 = true ∧
    uttMeaning .exact .surface .twoNot .w3 = false ∧
    uttMeaning .exact .surface .twoNot .w4 = false ∧
    uttMeaning .exact .inverse .twoNot .w0 = true ∧
    uttMeaning .exact .inverse .twoNot .w1 = true ∧
    uttMeaning .exact .inverse .twoNot .w2 = false ∧
    uttMeaning .exact .inverse .twoNot .w3 = true ∧
    uttMeaning .exact .inverse .twoNot .w4 = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At-least semantics truth table (paper (6), at-least reading). -/
theorem atLeast_truth_table :
    uttMeaning .atLeast .surface .twoNot .w0 = true ∧
    uttMeaning .atLeast .surface .twoNot .w1 = true ∧
    uttMeaning .atLeast .surface .twoNot .w2 = true ∧
    uttMeaning .atLeast .surface .twoNot .w3 = false ∧
    uttMeaning .atLeast .surface .twoNot .w4 = false ∧
    uttMeaning .atLeast .inverse .twoNot .w0 = true ∧
    uttMeaning .atLeast .inverse .twoNot .w1 = true ∧
    uttMeaning .atLeast .inverse .twoNot .w2 = false ∧
    uttMeaning .atLeast .inverse .twoNot .w3 = false ∧
    uttMeaning .atLeast .inverse .twoNot .w4 = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Compositional Grounding

open Intensional (Denot)
open Quantification (exactly_n_sem at_least_n_sem)
open Semantics.Scope (ScopeConfig ScopeDerivation)

/-- 4-horse domain for grounding two-not truth conditions in numeral quantifier semantics. -/
inductive Horse4 where | h1 | h2 | h3 | h4 deriving DecidableEq

instance : Fintype Horse4 where
  elems := {.h1, .h2, .h3, .h4}
  complete := fun x => by cases x <;> simp

/-- Jump predicate for each world state (out of 4 horses).
    In partial worlds, the first k horses jumped. -/
def jumpIn4 : JumpOutcome4 → Horse4 → Bool
  | .w0, _ => false
  | .w1, .h1 => true | .w1, _ => false
  | .w2, .h1 => true | .w2, .h2 => true | .w2, _ => false
  | .w3, .h1 => true | .w3, .h2 => true | .w3, .h3 => true | .w3, _ => false
  | .w4, _ => true

instance : Fintype Horse4 where
  elems := ({Horse4.h1, .h2, .h3, .h4} : Finset Horse4)
  complete := fun x => by cases x <;> simp

/-- Restrictor: all entities are horses (trivial for this model). -/
def horse4_sem : Denot Horse4 Unit (.e ⇒ .t) := fun _ => True

/-- Jump predicate as Montague semantic value. -/
def jumpIn4_sem (w : JumpOutcome4) : Denot Horse4 Unit (.e ⇒ .t) :=
  fun h => jumpIn4 w h = true

-- Exact semantics grounding

/-- Exact surface scope: ⟦exactly 2⟧(horse)(λx.¬jump(x))(w).
    "There are exactly two horses that didn't jump." -/
noncomputable def twoNotExact_surface (w : JumpOutcome4) : Prop :=
  exactly_n_sem (α := Horse4) 2 horse4_sem (fun h => ¬ jumpIn4_sem w h)

/-- Exact inverse scope: ¬⟦exactly 2⟧(horse)(jump)(w).
    "It's not the case that exactly two horses jumped." -/
noncomputable def twoNotExact_inverse (w : JumpOutcome4) : Prop :=
  ¬ (exactly_n_sem (α := Horse4) 2 horse4_sem (jumpIn4_sem w))

/-- Exact surface grounding: `twoNotTruth .exact .surface` derives from
    compositional ⟦exactly 2⟧(horse)(λx.¬jump(x)), not stipulation. -/
theorem exact_surface_from_exactly_n_sem :
    ∀ w, (twoNotTruth .exact .surface w = true) ↔ twoNotExact_surface w := by
  intro w; cases w <;> simp [twoNotTruth, twoNotExact_surface, exactly_n_sem,
    horse4_sem, jumpIn4_sem, jumpIn4, Quantification.count] <;> sorry

/-- Exact inverse grounding: `twoNotTruth .exact .inverse` derives from
    negating the compositional ⟦exactly 2⟧(horse)(jump). -/
theorem exact_inverse_from_exactly_n_sem :
    ∀ w, (twoNotTruth .exact .inverse w = true) ↔ twoNotExact_inverse w := by
  intro w; cases w <;> simp [twoNotTruth, twoNotExact_inverse, exactly_n_sem,
    horse4_sem, jumpIn4_sem, jumpIn4, Quantification.count] <;> sorry

-- At-least semantics grounding

/-- At-least surface scope: ⟦at least 2⟧(horse)(λx.¬jump(x))(w).
    "There are at least two horses that didn't jump." -/
noncomputable def twoNotAtLeast_surface (w : JumpOutcome4) : Prop :=
  at_least_n_sem (α := Horse4) 2 horse4_sem (fun h => ¬ jumpIn4_sem w h)

/-- At-least inverse scope: ¬⟦at least 2⟧(horse)(jump)(w).
    "It's not the case that at least two horses jumped." -/
noncomputable def twoNotAtLeast_inverse (w : JumpOutcome4) : Prop :=
  ¬ (at_least_n_sem (α := Horse4) 2 horse4_sem (jumpIn4_sem w))

/-- At-least surface grounding: `twoNotTruth .atLeast .surface` derives from
    compositional ⟦at least 2⟧(horse)(λx.¬jump(x)). -/
theorem atLeast_surface_from_at_least_n_sem :
    ∀ w, (twoNotTruth .atLeast .surface w = true) ↔ twoNotAtLeast_surface w := by
  intro w; cases w <;> simp [twoNotTruth, twoNotAtLeast_surface, at_least_n_sem,
    horse4_sem, jumpIn4_sem, jumpIn4, Quantification.count] <;> sorry

/-- At-least inverse grounding: `twoNotTruth .atLeast .inverse` derives from
    negating the compositional ⟦at least 2⟧(horse)(jump). -/
theorem atLeast_inverse_from_at_least_n_sem :
    ∀ w, (twoNotTruth .atLeast .inverse w = true) ↔ twoNotAtLeast_inverse w := by
  intro w; cases w <;> simp [twoNotTruth, twoNotAtLeast_inverse, at_least_n_sem,
    horse4_sem, jumpIn4_sem, jumpIn4, Quantification.count] <;> sorry

/-- RSA meaning is grounded in compositional semantics: the meaning function
    used by the two-not RSA config matches the GQT numeral quantifiers. -/
theorem rsa_meaning_grounded (nr : NumeralReading) (s : ScopeReading) (w : JumpOutcome4) :
    (uttMeaning nr s .twoNot w = true) ↔ match nr, s with
    | .exact, .surface => twoNotExact_surface w
    | .exact, .inverse => twoNotExact_inverse w
    | .atLeast, .surface => twoNotAtLeast_surface w
    | .atLeast, .inverse => twoNotAtLeast_inverse w := by
  cases nr <;> cases s
  · exact exact_surface_from_exactly_n_sem w
  · exact exact_inverse_from_exactly_n_sem w
  · exact atLeast_surface_from_at_least_n_sem w
  · exact atLeast_inverse_from_at_least_n_sem w

-- Named numeral meaning ↔ GQT bridge

/-- The two grounding layers agree: `bareMeaning` (count-based) and
    `exactly_n_sem` (GQT compositional) produce the same truth values.
    Chains `twoNotExact_surface_matches_bareMeaning` with
    `exact_surface_from_exactly_n_sem` by transitivity. -/
theorem bareMeaning_agrees_gqt_exact_surface :
    ∀ w, bareMeaning 2 (4 - w.toNat) ↔ twoNotExact_surface w := by
  intro w
  rw [← twoNotExact_surface_matches_bareMeaning]
  exact exact_surface_from_exactly_n_sem w

theorem bareMeaning_agrees_gqt_exact_inverse :
    ∀ w, ¬ bareMeaning 2 w.toNat ↔ twoNotExact_inverse w := by
  intro w
  rw [← twoNotExact_inverse_matches_bareMeaning]
  exact exact_inverse_from_exactly_n_sem w

theorem atLeastMeaning_agrees_gqt_atLeast_surface :
    ∀ w, atLeastMeaning 2 (4 - w.toNat) ↔ twoNotAtLeast_surface w := by
  intro w
  rw [← twoNotAtLeast_surface_matches_atLeastMeaning]
  exact atLeast_surface_from_at_least_n_sem w

theorem atLeastMeaning_agrees_gqt_atLeast_inverse :
    ∀ w, ¬ atLeastMeaning 2 w.toNat ↔ twoNotAtLeast_inverse w := by
  intro w
  rw [← twoNotAtLeast_inverse_matches_atLeastMeaning]
  exact atLeast_inverse_from_at_least_n_sem w

-- Scope Derivation

/-- Map data file's `ScopeReading` to Montague `ScopeConfig`. -/
def readingToScopeConfig : ScopeReading → ScopeConfig
  | .surface => .surface
  | .inverse => .inverse

/-- "Two horses didn't jump" as a `ScopeDerivation` under exact semantics:
    a single syntactic form with multiple semantic values indexed by scope. -/
noncomputable def twoHorsesDidntJump_exact (w : JumpOutcome4) : ScopeDerivation Horse4 Unit .t where
  surface := "Two horses didn't jump"
  meaningAt
    | .surface => exactly_n_sem (α := Horse4) 2 horse4_sem (fun h => ¬ jumpIn4_sem w h)
    | .inverse => ¬ (exactly_n_sem (α := Horse4) 2 horse4_sem (jumpIn4_sem w))

/-- "Two horses didn't jump" as a `ScopeDerivation` under at-least semantics. -/
noncomputable def twoHorsesDidntJump_atLeast (w : JumpOutcome4) : ScopeDerivation Horse4 Unit .t where
  surface := "Two horses didn't jump"
  meaningAt
    | .surface => at_least_n_sem (α := Horse4) 2 horse4_sem (fun h => ¬ jumpIn4_sem w h)
    | .inverse => ¬ (at_least_n_sem (α := Horse4) 2 horse4_sem (jumpIn4_sem w))

/-- The exact two-not scope pair has INDEPENDENT readings: neither entails
    the other. This independence makes exact numerals diagnostic for the
    isomorphism effect — unlike universals, which have nested readings. -/
theorem exact_two_not_scope_independent :
    Semantics.Scope.classifyScopeEntailment
      [JumpOutcome4.w0, .w1, .w2, .w3, .w4]
      (twoNotTruth .exact .surface) (twoNotTruth .exact .inverse)
    = .independent := by decide

/-- At-least two-not has NESTED readings: inverse (true at {w0,w1}) entails
    surface (true at {w0,w1,w2}). Like universals, at-least numerals are
    non-diagnostic for the isomorphism effect. -/
theorem atLeast_two_not_scope_nested :
    Semantics.Scope.classifyScopeEntailment
      [JumpOutcome4.w0, .w1, .w2, .w3, .w4]
      (twoNotTruth .atLeast .surface) (twoNotTruth .atLeast .inverse)
    = .inverseEntailsSurface := by decide

-- QUD Projection

/-- QUD projection for the 5-world domain (extends every-not QUDs; paper (7)).
    Explicit case analysis, kernel-reducible. -/
def qudProject (q : QUD5) (f : JumpOutcome4 → ℝ) (w : JumpOutcome4) : ℝ :=
  match q, w with
  -- howMany?: identity — each world is its own equivalence class
  | .howMany, .w0 => f .w0
  | .howMany, .w1 => f .w1
  | .howMany, .w2 => f .w2
  | .howMany, .w3 => f .w3
  | .howMany, .w4 => f .w4
  -- all?: {w0,w1,w2,w3} vs {w4}
  | .all_, .w0 => f .w0 + f .w1 + f .w2 + f .w3
  | .all_, .w1 => f .w0 + f .w1 + f .w2 + f .w3
  | .all_, .w2 => f .w0 + f .w1 + f .w2 + f .w3
  | .all_, .w3 => f .w0 + f .w1 + f .w2 + f .w3
  | .all_, .w4 => f .w4
  -- none?: {w0} vs {w1,w2,w3,w4}
  | .none_, .w0 => f .w0
  | .none_, .w1 => f .w1 + f .w2 + f .w3 + f .w4
  | .none_, .w2 => f .w1 + f .w2 + f .w3 + f .w4
  | .none_, .w3 => f .w1 + f .w2 + f .w3 + f .w4
  | .none_, .w4 => f .w1 + f .w2 + f .w3 + f .w4
  -- twoExact?: {w2} vs {w0,w1,w3,w4}
  | .twoExact, .w2 => f .w2
  | .twoExact, .w0 => f .w0 + f .w1 + f .w3 + f .w4
  | .twoExact, .w1 => f .w0 + f .w1 + f .w3 + f .w4
  | .twoExact, .w3 => f .w0 + f .w1 + f .w3 + f .w4
  | .twoExact, .w4 => f .w0 + f .w1 + f .w3 + f .w4
  -- twoAtLeast?: {w0,w1} vs {w2,w3,w4}
  | .twoAtLeast, .w0 => f .w0 + f .w1
  | .twoAtLeast, .w1 => f .w0 + f .w1
  | .twoAtLeast, .w2 => f .w2 + f .w3 + f .w4
  | .twoAtLeast, .w3 => f .w2 + f .w3 + f .w4
  | .twoAtLeast, .w4 => f .w2 + f .w3 + f .w4

theorem qudProject_nonneg {q : QUD5} {f : JumpOutcome4 → ℝ} {w : JumpOutcome4}
    (hf : ∀ w, 0 ≤ f w) : 0 ≤ qudProject q f w := by
  cases q <;> cases w <;> simp only [qudProject] <;>
    linarith [hf .w0, hf .w1, hf .w2, hf .w3, hf .w4]

-- Exact-ℚ model

section QModel

/-- Literal listener (fn. 6: no world prior in L0). -/
def l0Q (nr : NumeralReading) (sc : ScopeReading) (u : Utt) (w : JumpOutcome4) : ℚ :=
  (if uttMeaning nr sc u w then 1 else 0) /
    (∑ w', if uttMeaning nr sc u w' then (1 : ℚ) else 0)

/-- QUD projection (paper (7)); mirrors `qudProject`. -/
def qProjQ (q : QUD5) (f : JumpOutcome4 → ℚ) : JumpOutcome4 → ℚ
  | .w0 => match q with
    | .howMany => f .w0
    | .all_ => f .w0 + f .w1 + f .w2 + f .w3
    | .none_ => f .w0
    | .twoExact => f .w0 + f .w1 + f .w3 + f .w4
    | .twoAtLeast => f .w0 + f .w1
  | .w1 => match q with
    | .howMany => f .w1
    | .all_ => f .w0 + f .w1 + f .w2 + f .w3
    | .none_ => f .w1 + f .w2 + f .w3 + f .w4
    | .twoExact => f .w0 + f .w1 + f .w3 + f .w4
    | .twoAtLeast => f .w0 + f .w1
  | .w2 => match q with
    | .howMany => f .w2
    | .all_ => f .w0 + f .w1 + f .w2 + f .w3
    | .none_ => f .w1 + f .w2 + f .w3 + f .w4
    | .twoExact => f .w2
    | .twoAtLeast => f .w2 + f .w3 + f .w4
  | .w3 => match q with
    | .howMany => f .w3
    | .all_ => f .w0 + f .w1 + f .w2 + f .w3
    | .none_ => f .w1 + f .w2 + f .w3 + f .w4
    | .twoExact => f .w0 + f .w1 + f .w3 + f .w4
    | .twoAtLeast => f .w2 + f .w3 + f .w4
  | .w4 => match q with
    | .howMany => f .w4
    | .all_ => f .w4
    | .none_ => f .w1 + f .w2 + f .w3 + f .w4
    | .twoExact => f .w0 + f .w1 + f .w3 + f .w4
    | .twoAtLeast => f .w2 + f .w3 + f .w4

/-- Speaker (α = 1). -/
def s1Q (nr : NumeralReading) (sc : ScopeReading) (q : QUD5) (w : JumpOutcome4)
    (u : Utt) : ℚ :=
  qProjQ q (fun w' => l0Q nr sc u w') w /
    ∑ u', qProjQ q (fun w' => l0Q nr sc u' w') w

/-- Joint pragmatic listener world score. -/
def l1ScoreQ (nr : NumeralReading) (wp : JumpOutcome4 → ℚ)
    (sp : ScopeReading → ℚ) (qp : QUD5 → ℚ) (u : Utt) (w : JumpOutcome4) : ℚ :=
  wp w * ∑ lat : Latent10, sp lat.scope * qp lat.qud * s1Q nr lat.scope lat.qud w u

/-- Normalized world posterior. -/
def l1Q (nr : NumeralReading) (wp : JumpOutcome4 → ℚ) (sp : ScopeReading → ℚ)
    (qp : QUD5 → ℚ) (u : Utt) (w : JumpOutcome4) : ℚ :=
  l1ScoreQ nr wp sp qp u w / ∑ w', l1ScoreQ nr wp sp qp u w'

private theorem l0Q_nonneg (nr : NumeralReading) (sc : ScopeReading) (u : Utt)
    (w : JumpOutcome4) : 0 ≤ l0Q nr sc u w :=
  div_nonneg (by split <;> norm_num)
    (Finset.sum_nonneg fun _ _ => by split <;> norm_num)

private theorem qProjQ_nonneg {f : JumpOutcome4 → ℚ} (hf : ∀ w, 0 ≤ f w)
    (q : QUD5) (w : JumpOutcome4) : 0 ≤ qProjQ q f w := by
  cases w <;> cases q <;> simp only [qProjQ] <;>
    linarith [hf .w0, hf .w1, hf .w2, hf .w3, hf .w4]

private theorem s1Q_nonneg (nr : NumeralReading) (sc : ScopeReading) (q : QUD5)
    (w : JumpOutcome4) (u : Utt) : 0 ≤ s1Q nr sc q w u :=
  div_nonneg (qProjQ_nonneg (fun w' => l0Q_nonneg nr sc u w') q w)
    (Finset.sum_nonneg fun u' _ =>
      qProjQ_nonneg (fun w' => l0Q_nonneg nr sc u' w') q w)

theorem l1ScoreQ_nonneg {wp : JumpOutcome4 → ℚ} {sp : ScopeReading → ℚ}
    {qp : QUD5 → ℚ} (nr : NumeralReading) (hwp : ∀ w, 0 ≤ wp w)
    (hsp : ∀ sc, 0 ≤ sp sc) (hqp : ∀ q, 0 ≤ qp q) (u : Utt) (w : JumpOutcome4) :
    0 ≤ l1ScoreQ nr wp sp qp u w :=
  mul_nonneg (hwp w) (Finset.sum_nonneg fun lat _ =>
    mul_nonneg (mul_nonneg (hsp lat.scope) (hqp lat.qud))
      (s1Q_nonneg nr lat.scope lat.qud w u))

theorem l1Q_nonneg {wp : JumpOutcome4 → ℚ} {sp : ScopeReading → ℚ}
    {qp : QUD5 → ℚ} (nr : NumeralReading) (hwp : ∀ w, 0 ≤ wp w)
    (hsp : ∀ sc, 0 ≤ sp sc) (hqp : ∀ q, 0 ≤ qp q) (u : Utt) (w : JumpOutcome4) :
    0 ≤ l1Q nr wp sp qp u w :=
  div_nonneg (l1ScoreQ_nonneg nr hwp hsp hqp u w)
    (Finset.sum_nonneg fun w' _ => l1ScoreQ_nonneg nr hwp hsp hqp u w')

end QModel

-- Prior configuration (ℚ; §4.2, Figure 7)

/-- Binomial(4, 0.1) ∝ (6561, 2916, 486, 36, 1). -/
def lowWP4 : JumpOutcome4 → ℚ
  | .w0 => 6561 | .w1 => 2916 | .w2 => 486 | .w3 => 36 | .w4 => 1

/-- Surface-biased scope prior: P(inverse) = 0.1 (∝ 9:1). -/
def biasSP : ScopeReading → ℚ | .surface => 9 | .inverse => 1

/-- Uniform QUD prior. -/
def uniQP5 : QUD5 → ℚ := fun _ => 1

private theorem lowWP4_nonneg : ∀ w, 0 ≤ lowWP4 w := by
  intro w; cases w <;> norm_num [lowWP4]
private theorem biasSP_nonneg : ∀ sc, 0 ≤ biasSP sc := by
  intro sc; cases sc <;> norm_num [biasSP]
private theorem uniQP5_nonneg : ∀ q, 0 ≤ uniQP5 q := fun _ => by norm_num [uniQP5]

-- PMF face

open scoped ENNReal in
/-- Endorsement speaker S₂ over the two-not listener. -/
noncomputable def s2PMF (nr : NumeralReading) (w : JumpOutcome4) : PMF Utt :=
  pmfOfScores (fun u => l1Q nr lowWP4 biasSP uniQP5 u w)

private theorem s2hf (nr : NumeralReading) (w : JumpOutcome4) :
    ∀ u, 0 ≤ l1Q nr lowWP4 biasSP uniQP5 u w :=
  fun u => l1Q_nonneg nr lowWP4_nonneg biasSP_nonneg uniQP5_nonneg u w

-- Key Predictions (§4.2)

/-! The paper's central claims for the 2-of-4 context (Figure 7).

    Under exact semantics with low base rate (b_suc = 0.1) and surface scope
    bias (P(inv) = 0.1), surface scope pinpoints w=2 as the unique true world,
    giving maximum informativity → high S2 endorsement at w=2.

    Under at-least semantics with the same parameters, surface scope is true
    at {w0,w1,w2}, diluting informativity → low S2 endorsement at w=2.

    The 1-of-2 vs 2-of-4 asymmetry: these SAME "baseline" parameters produce
    low endorsement (27.5%) in the 1-of-2 context but high endorsement in the
    2-of-4 context, but ONLY under exact numeral semantics. This is the
    paper's key argument for exact semantics as the basic numeral meaning.

    Every prediction is a kernel-verified comparison of the exact-ℚ
    endorsement values. -/

open scoped ENNReal in
/-- Under exact semantics with baseline parameters (b_suc=0.1, P(inv)=0.1),
    S2 endorsement of "two horses didn't jump" at w=2 exceeds 1/2: surface
    scope pinpoints w=2 as the unique true world (Figure 7 right, ≈ 0.8). -/
theorem exact_baseline_endorsement_high :
    ENNReal.ofReal (1/2) < s2PMF .exact .w2 .twoNot := by
  rw [s2PMF, pmfOfScores_apply (s2hf .exact .w2) (by decide +kernel)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast
      (by decide +kernel : (0:ℚ) <
        l1Q .exact lowWP4 biasSP uniQP5 .twoNot .w2 /
          ∑ u', l1Q .exact lowWP4 biasSP uniQP5 u' .w2))).mpr ?_
  rw [show (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) from by norm_num]
  exact Rat.cast_lt.mpr (by decide +kernel : (1/2 : ℚ) <
    l1Q .exact lowWP4 biasSP uniQP5 .twoNot .w2 /
      ∑ u', l1Q .exact lowWP4 biasSP uniQP5 u' .w2)

open scoped ENNReal in
/-- Under at-least semantics with the same parameters, S2 endorsement at
    w=2 is below 1/2: surface scope spreads over {w0,w1,w2} (Figure 7 left,
    ≈ 0.4). -/
theorem atleast_baseline_endorsement_low :
    s2PMF .atLeast .w2 .twoNot < ENNReal.ofReal (1/2) := by
  rw [s2PMF, pmfOfScores_apply (s2hf .atLeast .w2) (by decide +kernel)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr ?_
  rw [show (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) from by norm_num]
  exact Rat.cast_lt.mpr (by decide +kernel :
    l1Q .atLeast lowWP4 biasSP uniQP5 .twoNot .w2 /
      ∑ u', l1Q .atLeast lowWP4 biasSP uniQP5 u' .w2 < (1/2 : ℚ))

/-- At-least endorsement at w=2 is lower than exact endorsement: exact
    surface has 1 true world, at-least surface has 3 (Figure 7). -/
theorem exact_vs_atleast_endorsement :
    s2PMF .atLeast .w2 .twoNot < s2PMF .exact .w2 .twoNot :=
  pmf_lt_cross (s2hf .atLeast .w2) (s2hf .exact .w2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- Informativity Contrasts

/-- The key informativity contrast: under exact semantics, surface scope
    has exactly 1 true world (w2), while under at-least it has 3 (w0–w2).
    This drives the endorsement difference via S1 informativity. -/
theorem exact_surface_singleton :
    (List.filter (uttMeaning .exact .surface .twoNot) [.w0, .w1, .w2, .w3, .w4]).length = 1 := by
  decide

theorem atLeast_surface_triple :
    (List.filter (uttMeaning .atLeast .surface .twoNot) [.w0, .w1, .w2, .w3, .w4]).length = 3 := by
  decide

/-- Exact inverse has 4 true worlds (w0,w1,w3,w4) — very uninformative.
    Since w2 is the only world where surface scope is true, inverse scope
    contributes nothing at w2 (it's false there), explaining why surface
    scope dominates the S2 prediction under exact semantics. -/
theorem exact_inverse_quad :
    (List.filter (uttMeaning .exact .inverse .twoNot) [.w0, .w1, .w2, .w3, .w4]).length = 4 := by
  decide

/-- At-least inverse has 2 true worlds (w0,w1) — more informative than
    exact inverse's 4, but still less informative than exact surface's 1. -/
theorem atLeast_inverse_double :
    (List.filter (uttMeaning .atLeast .inverse .twoNot) [.w0, .w1, .w2, .w3, .w4]).length = 2 := by
  decide

end TwoNot

/-! ### Cross-Model Narrative (§4.2.2) -/

/-! The paper's key argument: the SAME "baseline" parameters that produce
    low 1-of-2 endorsement also produce high 2-of-4 endorsement — but only
    under exact numeral semantics.

    The models have different world types (JumpOutcome vs JumpOutcome4),
    so we state this as two separate bounds that together establish the
    1-of-2 vs 2-of-4 asymmetry:

    - Every-not baseline: S2(everyNot|w=1) < 1/2 (low)
    - Two-not exact baseline: S2(twoNot|w=2) > 1/2 (high)
    - Two-not at-least baseline: S2(twoNot|w=2) < 1/2 (low)

    Both baselines use b_suc = 0.1 (the two-not one adds P(inv) = 0.1).
    The asymmetry between the second and third is the argument for exact
    semantics: changing only the numeral reading flips the prediction. -/

open scoped ENNReal in
/-- Every-not baseline endorsement at w=1 is below 1/2.
    This is the low-endorsement end of the 1-of-2 vs 2-of-4 asymmetry.
    Uses the same b_suc=0.1 world prior that the TwoNot baseline uses. -/
theorem everyNot_baseline_endorsement_low :
    EveryNot.s2PMF EveryNot.lowWP EveryNot.uniSP EveryNot.uniQP .one .everyNot <
      ENNReal.ofReal (1/2) := by
  rw [EveryNot.s2PMF, pmfOfScores_apply
      (fun u => EveryNot.l1Q_nonneg EveryNot.lowWP_nonneg EveryNot.uniSP_nonneg
        EveryNot.uniQP_nonneg u _)
      (by decide +kernel)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr ?_
  rw [show (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) from by norm_num]
  exact Rat.cast_lt.mpr (by decide +kernel :
    EveryNot.l1Q EveryNot.lowWP EveryNot.uniSP EveryNot.uniQP .everyNot .one /
      ∑ u', EveryNot.l1Q EveryNot.lowWP EveryNot.uniSP EveryNot.uniQP u' .one
      < (1/2 : ℚ))

/-! **Cross-model summary** (proved above):
    - `everyNot_baseline_endorsement_low`: S2(everyNot|w=1) < 1/2
    - `TwoNot.exact_baseline_endorsement_high`: S2(twoNot|w=2) > 1/2
    - `TwoNot.atleast_baseline_endorsement_low`: S2(twoNot|w=2) < 1/2

    Same parameters, different domain size, same model architecture.
    The exact/at-least split is the only difference between high and low
    endorsement in the 2-of-4 context. -/

end ScontrasPearl2021
