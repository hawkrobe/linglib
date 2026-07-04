import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Core.Probability.Scores
import Linglib.Pragmatics.RSA.Operators
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Composition.Scope

/-!
# [scontras-pearl-2021]: quantifier scope ambiguity in truth-value judgments

"When pragmatics matters more for truth-value judgments: An investigation
of quantifier scope ambiguity", *Glossa* 6(1): 110. A modeling paper: RSA
with lifted scope and QUD variables explains the endorsement patterns of
[musolino-lidz-2003] and successors, separating pragmatic factors (world
and QUD priors) from grammatical processing (scope access).

Two models, each in its own namespace and each with two faces — an
exact-ℚ≥0 kernel face at the paper's parameters and a general-α
structural face on `RSA`/`PMF.posterior` operators:

- `EveryNot`: "Every horse didn't jump", n = 2 (3 worlds × 2 utterances ×
  2 scopes × 3 QUDs; paper §3).
- `TwoNot`: "Two horses didn't jump", n = 4, parameterized by numeral
  reading (exact vs at-least; paper §4).

## Main results

* `EveryNot.s2_ordering_*`: endorsement orders w0 > w1 > w2 across all
  Figure 2 prior configurations (endorsement at w=1: .29 at b_suc = 0.1,
  .80 at b_suc = 0.9).
* `EveryNot.s2_qud_ordering`: favoring none? < how-many? < all?
  monotonically increases endorsement (.38 < .48 < .63; the adult pattern
  of the paper's Figure 4).
* `EveryNot.baseline_L1_zero_gt_one` / `_one_gt_two`: the baseline L₁
  ordering for every α > 0.
* `EveryNot.S1g_all_qud_scope_invariant`: under the all? QUD the speaker
  is scope-invariant — the structural mechanism of pragmatic dominance.
* `TwoNot.exact_baseline_endorsement_high` / `atleast_baseline_endorsement_low`
  / `exact_vs_atleast_endorsement`: the 1-of-2 vs 2-of-4 asymmetry flips
  with the numeral reading (Figure 7) — the paper's argument that exact
  numeral semantics is basic.
* `TwoNot.L0_exact_gt_atLeast_at_w2`: the L0 concentration contrast
  driving that asymmetry, for every α.
* `every_not_scope_entailment` / `exact_two_not_scope_independent`:
  universals have nested scope readings, exact numerals independent ones —
  why numerals are diagnostic for isomorphism.

## Implementation notes

Truth conditions are grounded compositionally (`every_sem`,
`ScopeDerivation`) and in the named numeral meanings of
`Semantics.Numerals`. The kernel faces use `PMF.ofScores` over ℚ≥0 score
chains at α = 1 (§3.2; costs cancel, fn. 8) with L0 taking no world prior
(fn. 6); the structural faces are parametric in α (the
parametric-prior layer is TODO). Developmental claim
(§3.3): children and adults differ only in these parameter values.

## TODO

General-α, parametric-prior versions of the QUD ordering and of the
exact-vs-at-least endorsement divergence (their α = 1 instances at the
paper's parameters are kernel-proved), together with the parametric prior
layer (`PMF.binomial` world prior, weighted scope/QUD priors) and the
general S2 they require; the emergent b_suc-monotonicity of endorsement
as a limit statement.
-/

open scoped NNRat NNReal ENNReal

namespace ScontrasPearl2021

/-! ### Shared domain: every-not (n = 2) -/

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

/-! ### Shared domain: two-not (n = 4) -/

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

/-! ### Scope-entailment asymmetry ([musolino-lidz-2003]) -/

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

/-! ### Numeral-semantics grounding -/

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

/-! ## The every-not model (§3) -/

namespace EveryNot

open BigOperators
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

/-! ### Truth conditions and compositional grounding -/

/-- RSA meaning derived from `scopeTruth`.
    Null utterance is always true (uninformative baseline). -/
def uttMeaning : ScopeReading → Utt → JumpOutcome → Bool
  | _, .null, _ => true
  | s, .everyNot, w => scopeTruth s w

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

/-- The every-not scope pair has surface-entails-inverse structure,
making universals non-diagnostic for scope preferences: no truth-value
judgment context can distinguish isomorphic from non-isomorphic
behavior. -/
theorem every_not_scope_entailment :
    Semantics.Scope.classifyScopeEntailment
      [JumpOutcome.zero, .one, .two]
      (scopeTruth .surface) (scopeTruth .inverse)
    = .surfaceEntailsInverse := by decide

/-! ### The kernel face: exact-ℚ scores at the paper parameters -/

/-- Literal listener (fn. 6: no world prior in L0). -/
def l0Score (sc : ScopeReading) (u : Utt) (w : JumpOutcome) : ℚ≥0 :=
  (if uttMeaning sc u w then 1 else 0) /
    (∑ w', if uttMeaning sc u w' then (1 : ℚ≥0) else 0)

/-- QUD projection (paper (3)): sums `f` over the QUD cell of the world.
Polymorphic over the value monoid — instantiated at ℚ≥0 by the kernel face
and at ℝ≥0∞ by the structural face. -/
def qProj {M : Type*} [Add M] (q : QUD) (f : JumpOutcome → M) : JumpOutcome → M
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
def s1Score (sc : ScopeReading) (q : QUD) (w : JumpOutcome) : Utt → ℚ≥0 :=
  PMF.normalizeScores fun u => qProj q (fun w' => l0Score sc u w') w

/-- Joint pragmatic-listener world score: `P(w)·Σ_{i,q} P(i)·P(q)·S1`. -/
def l1Score (wp : JumpOutcome → ℚ≥0) (sp : ScopeReading → ℚ≥0) (qp : QUD → ℚ≥0)
    (u : Utt) (w : JumpOutcome) : ℚ≥0 :=
  wp w * ∑ lat : Latent, sp lat.scope * qp lat.qud * s1Score lat.scope lat.qud w u

/-- Normalized world posterior. -/
def l1Post (wp : JumpOutcome → ℚ≥0) (sp : ScopeReading → ℚ≥0) (qp : QUD → ℚ≥0)
    (u : Utt) : JumpOutcome → ℚ≥0 :=
  PMF.normalizeScores (l1Score wp sp qp u)

/-- Binomial(2, 0.1) ∝ (81, 18, 1). -/
def lowWP : JumpOutcome → ℚ≥0 | .zero => 81 | .one => 18 | .two => 1

/-- Binomial(2, 0.5) ∝ (1, 2, 1). -/
def midWP : JumpOutcome → ℚ≥0 | .zero => 1 | .one => 2 | .two => 1

/-- Binomial(2, 0.9) ∝ (1, 18, 81). -/
def highWP : JumpOutcome → ℚ≥0 | .zero => 1 | .one => 18 | .two => 81

/-- Uniform scope prior (P(inverse) = 0.5, the default). -/
def uniSP : ScopeReading → ℚ≥0 := fun _ => 1

/-- Surface-only scope prior (P(inverse) = 0). -/
def surfSP : ScopeReading → ℚ≥0 | .surface => 1 | .inverse => 0

/-- Uniform QUD prior. -/
def uniQP : QUD → ℚ≥0 := fun _ => 1

/-- Biased QUD prior: the favored QUD gets 0.9, others 0.05 (∝ 18:1:1). -/
def biasQP (q₀ : QUD) : QUD → ℚ≥0 := fun q => if q = q₀ then 18 else 1

/-- Pragmatic listener over worlds. -/
noncomputable def l1 (wp : JumpOutcome → ℚ≥0) (sp : ScopeReading → ℚ≥0)
    (qp : QUD → ℚ≥0) (u : Utt) : PMF JumpOutcome :=
  .ofScores .uniform (l1Score wp sp qp u)

/-- Endorsement speaker S₂ (§3.1): the L1 world posterior renormalized per
world. -/
noncomputable def s2 (wp : JumpOutcome → ℚ≥0) (sp : ScopeReading → ℚ≥0)
    (qp : QUD → ℚ≥0) (w : JumpOutcome) : PMF Utt :=
  .ofScores .uniform fun u => l1Post wp sp qp u w

/-! ### L₁ predictions -/

/-- Baseline L₁ (b_suc = 0.1) ranks the worlds w0 > w1 > w2: both scopes
verify w0 (prior 81), only inverse verifies w1 (prior 18), neither
verifies w2. -/
theorem baseline_l1_ordering :
    l1 lowWP uniSP uniQP .everyNot .two < l1 lowWP uniSP uniQP .everyNot .one ∧
    l1 lowWP uniSP uniQP .everyNot .one < l1 lowWP uniSP uniQP .everyNot .zero :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-- Scope ambiguity boosts the partial world: with both scopes active,
L₁(w=1) exceeds its surface-only value (inverse scope verifies w=1). -/
theorem ambiguity_boosts_partial :
    l1 lowWP surfSP uniQP .everyNot .one < l1 lowWP uniSP uniQP .everyNot .one :=
  PMF.ofScores_lt_cross _ _ (by decide +kernel)

/-! ### S₂ endorsement predictions

The endorsement ordering w0 > w1 > w2 is robust across all Figure 2
configurations (even where L₁ itself reverses, as under b_suc = 0.9:
per-world renormalization restores it). Each ordering is two cross-world
comparisons of the endorsement distribution. -/

/-- Baseline (b_suc = 0.1): endorsement orders w0 > w1 > w2. -/
theorem s2_ordering_baseline :
    s2 lowWP uniSP uniQP .two .everyNot < s2 lowWP uniSP uniQP .one .everyNot ∧
    s2 lowWP uniSP uniQP .one .everyNot < s2 lowWP uniSP uniQP .zero .everyNot :=
  ⟨PMF.ofScores_lt_cross _ _ (by decide +kernel),
    PMF.ofScores_lt_cross _ _ (by decide +kernel)⟩

/-- Default (b_suc = 0.5): same ordering. -/
theorem s2_ordering_default :
    s2 midWP uniSP uniQP .two .everyNot < s2 midWP uniSP uniQP .one .everyNot ∧
    s2 midWP uniSP uniQP .one .everyNot < s2 midWP uniSP uniQP .zero .everyNot :=
  ⟨PMF.ofScores_lt_cross _ _ (by decide +kernel),
    PMF.ofScores_lt_cross _ _ (by decide +kernel)⟩

/-- High base rate (b_suc = 0.9): same ordering, though L₁ reverses. -/
theorem s2_ordering_highBase :
    s2 highWP uniSP uniQP .two .everyNot < s2 highWP uniSP uniQP .one .everyNot ∧
    s2 highWP uniSP uniQP .one .everyNot < s2 highWP uniSP uniQP .zero .everyNot :=
  ⟨PMF.ofScores_lt_cross _ _ (by decide +kernel),
    PMF.ofScores_lt_cross _ _ (by decide +kernel)⟩

/-- Supportive context (b_suc = 0.9, all?-biased QUD): same ordering. -/
theorem s2_ordering_supportive :
    s2 highWP uniSP (biasQP .all_) .two .everyNot <
      s2 highWP uniSP (biasQP .all_) .one .everyNot ∧
    s2 highWP uniSP (biasQP .all_) .one .everyNot <
      s2 highWP uniSP (biasQP .all_) .zero .everyNot :=
  ⟨PMF.ofScores_lt_cross _ _ (by decide +kernel),
    PMF.ofScores_lt_cross _ _ (by decide +kernel)⟩

/-- QUD manipulation (Figure 2, center panel): endorsement at the partial
world increases none? < how-many? < all? (paper values .38 < .48 < .63) —
all? is fully resolved by either scope, so favoring it makes the ambiguous
utterance maximally useful. Matches the adult data of Song et al. 2021
reproduced as the paper's Figure 4. -/
theorem s2_qud_ordering :
    s2 midWP uniSP (biasQP .none_) .one .everyNot <
      s2 midWP uniSP (biasQP .howMany) .one .everyNot ∧
    s2 midWP uniSP (biasQP .howMany) .one .everyNot <
      s2 midWP uniSP (biasQP .all_) .one .everyNot :=
  ⟨PMF.ofScores_lt_cross _ _ (by decide +kernel),
    PMF.ofScores_lt_cross _ _ (by decide +kernel)⟩

/-! ### The structural face: general α

The same model on the `RSA` operator face, parametric in the rationality
α and the prior parameters — the general theorems the kernel instances
above sample. -/

/-! #### The uniform world prior -/

/-- Uniform world prior (`worldPriorAt` below is the paper-faithful
parametric version). -/
noncomputable def worldPrior : PMF JumpOutcome := PMF.uniformOfFintype JumpOutcome

theorem worldPrior_ne_zero (w : JumpOutcome) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

/-! #### L0 as `RSA.L0OfBoolMeaning`

`uttMeaning lat.scope u w` is `Bool`-valued, so L0 is uniform on the
extension. Each scope reading induces its own L0 distribution (the meaning
function's first argument is `ScopeReading`, not just `Utt`). -/

/-- Extension of `uttMeaning s u`: the worlds where `u` is true under scope `s`. -/
abbrev extension (s : ScopeReading) (u : Utt) : Finset JumpOutcome :=
  RSA.extensionOf (uttMeaning s) u

theorem extension_nonempty (s : ScopeReading) (u : Utt) : (extension s u).Nonempty := by
  -- `.zero` is true under every (s, u) pair: null is universally true, and
  -- both surface and inverse readings of everyNot are true at `.zero`.
  refine ⟨.zero, ?_⟩
  rw [RSA.mem_extensionOf]
  cases s <;> cases u <;> rfl

/-- Literal listener: uniform on the extension of `uttMeaning lat.scope u`. -/
noncomputable def L0 (s : ScopeReading) (u : Utt) : PMF JumpOutcome :=
  RSA.L0OfBoolMeaning (uttMeaning s) u (extension_nonempty s u)

@[simp] theorem mem_support_L0_iff (s : ScopeReading) (u : Utt) (w : JumpOutcome) :
    w ∈ (L0 s u).support ↔ uttMeaning s u w = true :=
  RSA.mem_support_L0OfBoolMeaning_iff _ _

theorem L0_apply_of_true {s : ScopeReading} {u : Utt} {w : JumpOutcome}
    (h : uttMeaning s u w = true) :
    L0 s u w = ((extension s u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem L0_apply_of_false {s : ScopeReading} {u : Utt} {w : JumpOutcome}
    (h : uttMeaning s u w ≠ true) :
    L0 s u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

/-! #### QUD projection facts on ℝ≥0∞ -/

/-- The projection at `w` under QUD `q` is bounded above by the total mass
of `f` (a finite sum of pieces of `Σ f`). Used to discharge `≠ ∞`. -/
theorem qudProjectE_ne_top {q : QUD} {f : JumpOutcome → ℝ≥0∞} {w : JumpOutcome}
    (hf : ∀ w, f w ≠ ∞) : qProj q f w ≠ ∞ := by
  cases q <;> cases w <;> simp only [qProj] <;>
    first
    | exact hf _
    | exact ENNReal.add_ne_top.mpr ⟨hf _, hf _⟩

/-- The projection of L0 includes the mass at `w` itself (since `w` is in
its own equivalence class for every QUD). Used to derive positivity of the
rpow speaker score at the witness world. -/
theorem qudProjectE_self_ge {q : QUD} {f : JumpOutcome → ℝ≥0∞} (w : JumpOutcome) :
    f w ≤ qProj q f w := by
  cases q <;> cases w <;> simp only [qProj] <;>
    first
    | exact le_refl _
    | exact le_self_add
    | exact le_add_self

/-- If L0 is non-zero at `w`, the QUD-projected sum is non-zero at `w`. -/
theorem qudProjectE_ne_zero_of_self {q : QUD} {f : JumpOutcome → ℝ≥0∞} {w : JumpOutcome}
    (h : f w ≠ 0) : qProj q f w ≠ 0 := by
  intro hp
  exact h (le_antisymm (hp ▸ qudProjectE_self_ge w) zero_le)

/-! #### S1g — speaker conditional on (latent, world)

`S1g lat w u ∝ (qProj lat.qud (L0 lat.scope u) w)^α`. The cover witness
is the `null` utterance: its L0 is uniform on `Finset.univ`, so the projection
is positive at every `w` (every QUD class contains some world where `null`'s
L0 is positive — and `null`'s L0 is positive everywhere). -/

/-- The unnormalised score: `(qProj lat.qud (L0 lat.scope u) w)^α`. -/
noncomputable def s1Weight (α : ℝ) (lat : Latent) (w : JumpOutcome) (u : Utt) : ℝ≥0∞ :=
  (qProj lat.qud (fun w' => L0 lat.scope u w') w) ^ α

theorem L0_null_ne_zero (s : ScopeReading) (w : JumpOutcome) :
    L0 s .null w ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_L0_iff]
  cases s <;> rfl

theorem s1Weight_null_ne_zero {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) :
    s1Weight α lat w .null ≠ 0 := by
  refine (not_congr (ENNReal.rpow_eq_zero_iff_of_pos hα)).mpr ?_
  exact qudProjectE_ne_zero_of_self (L0_null_ne_zero _ _)

theorem L0_ne_top (s : ScopeReading) (u : Utt) (w : JumpOutcome) : L0 s u w ≠ ∞ :=
  PMF.apply_ne_top _ _

theorem s1Weight_ne_top {α : ℝ} (hα : 0 ≤ α) (lat : Latent) (w : JumpOutcome) (u : Utt) :
    s1Weight α lat w u ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg hα (qudProjectE_ne_top (L0_ne_top _ _))

theorem s1Weight_tsum_ne_zero {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) :
    ∑' u, s1Weight α lat w u ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.null, s1Weight_null_ne_zero hα lat w⟩

theorem s1Weight_tsum_ne_top {α : ℝ} (hα : 0 ≤ α) (lat : Latent) (w : JumpOutcome) :
    ∑' u, s1Weight α lat w u ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun u => s1Weight_ne_top hα lat w u

/-- Pragmatic speaker conditioned on (latent, world). -/
noncomputable def S1g {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) : PMF Utt :=
  PMF.normalize (s1Weight α lat w) (s1Weight_tsum_ne_zero hα lat w)
    (s1Weight_tsum_ne_top hα.le lat w)

theorem mem_support_S1g_iff {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) (u : Utt) :
    u ∈ (S1g hα lat w).support ↔ s1Weight α lat w u ≠ 0 := by
  rw [S1g, PMF.mem_support_normalize_iff]

theorem S1g_null_ne_zero {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) :
    S1g hα lat w .null ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_S1g_iff]
  exact s1Weight_null_ne_zero hα lat w

/-! #### Marginal speaker — `PMF.bind` over the latent prior

The product latent is `scope × QUD` (flattened to `Latent`). `PMF.bind`
against a `latentPrior : PMF Latent` is mathlib's idiom for marginalising
over a chained random variable — exactly what's needed here. -/

/-- Speaker marginalised over latent state. -/
noncomputable def marginalSpeaker {α : ℝ} (hα : 0 < α) (latentPrior : PMF Latent)
    (w : JumpOutcome) : PMF Utt :=
  latentPrior.bind (fun lat => S1g hα lat w)

/-- The cover witness lifts to the marginal speaker: if any latent has
positive prior mass and S1g is non-zero on `null`, the marginal speaker is
non-zero on `null`. Used to discharge `marginal ≠ 0` for L1 at `u = null`. -/
theorem marginalSpeaker_null_ne_zero {α : ℝ} (hα : 0 < α)
    {latentPrior : PMF Latent} {lat : Latent} (hlat : latentPrior lat ≠ 0)
    (w : JumpOutcome) :
    marginalSpeaker hα latentPrior w .null ≠ 0 := by
  unfold marginalSpeaker
  rw [PMF.bind_apply]
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨lat, mul_ne_zero hlat ?_⟩
  exact S1g_null_ne_zero hα lat w

/-! #### L1 — Bayesian inversion via `PMF.posterior` -/

theorem L1_marginal_null_ne_zero {α : ℝ} (hα : 0 < α)
    {latentPrior : PMF Latent} {lat : Latent} (hlat : latentPrior lat ≠ 0) :
    PMF.marginal (marginalSpeaker hα latentPrior) worldPrior Utt.null ≠ 0 :=
  PMF.marginal_ne_zero _ worldPrior Utt.null
    (worldPrior_ne_zero .zero) (marginalSpeaker_null_ne_zero hα hlat .zero)

/-- The everyNot utterance also has L1-marginal cover: at world `.zero`,
both scope readings make `everyNot` true, so L0 puts positive mass there,
S1g(everyNot|lat,.zero) > 0 for every lat (since qudProject ≥ L0(.zero) > 0),
and the marginal speaker is positive on everyNot at `.zero`. -/
theorem marginalSpeaker_everyNot_at_zero_ne_zero {α : ℝ} (hα : 0 < α)
    {latentPrior : PMF Latent} {lat : Latent} (hlat : latentPrior lat ≠ 0) :
    marginalSpeaker hα latentPrior .zero .everyNot ≠ 0 := by
  unfold marginalSpeaker
  rw [PMF.bind_apply]
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨lat, mul_ne_zero hlat ?_⟩
  rw [← PMF.mem_support_iff, S1g, PMF.mem_support_normalize_iff]
  refine (not_congr (ENNReal.rpow_eq_zero_iff_of_pos hα)).mpr ?_
  refine qudProjectE_ne_zero_of_self ?_
  rw [← PMF.mem_support_iff, mem_support_L0_iff]
  cases lat.scope <;> rfl

theorem L1_marginal_everyNot_ne_zero {α : ℝ} (hα : 0 < α)
    {latentPrior : PMF Latent} {lat : Latent} (hlat : latentPrior lat ≠ 0) :
    PMF.marginal (marginalSpeaker hα latentPrior) worldPrior Utt.everyNot ≠ 0 :=
  PMF.marginal_ne_zero _ worldPrior Utt.everyNot
    (worldPrior_ne_zero .zero) (marginalSpeaker_everyNot_at_zero_ne_zero hα hlat)

/-- Pragmatic listener: `PMF.posterior` of the latent-marginalised speaker
against the world prior. The "L1 = Bayesian inversion" claim is true by
construction (`PMF.posterior` IS Bayes' rule). -/
noncomputable def L1 {α : ℝ} (hα : 0 < α) (latentPrior : PMF Latent) (u : Utt)
    (hMarg : PMF.marginal (marginalSpeaker hα latentPrior) worldPrior u ≠ 0) :
    PMF JumpOutcome :=
  PMF.posterior (marginalSpeaker hα latentPrior) worldPrior u hMarg

theorem mem_support_L1_iff {α : ℝ} (hα : 0 < α) (latentPrior : PMF Latent) (u : Utt)
    (hMarg : PMF.marginal (marginalSpeaker hα latentPrior) worldPrior u ≠ 0)
    (w : JumpOutcome) :
    w ∈ (L1 hα latentPrior u hMarg).support ↔
      worldPrior w ≠ 0 ∧ marginalSpeaker hα latentPrior w u ≠ 0 :=
  PMF.mem_support_posterior_iff _ _ _ _ _

/-! #### The general-α baseline orderings

General-α companions of `baseline_l1_ordering`: the L₁ orderings hold for
every α > 0 and any `latentPrior` with positive mass everywhere. The
structural shell: `posterior_lt_iff_kernel_lt_of_uniform` cancels the L1
marginal and the uniform world prior, `PMF.bind_lt_bind` reduces the
marginal speaker to per-latent S1g comparisons, and each latent case is a
vacuous zero, an equality of score functions, or rpow monotonicity. -/

/-- Surface-scope-favored latent prior: every latent has positive mass.
Used as the default `latentPrior` for the findings below. -/
noncomputable def uniformLatentPrior : PMF Latent := PMF.uniformOfFintype Latent

theorem uniformLatentPrior_ne_zero (lat : Latent) : uniformLatentPrior lat ≠ 0 :=
  (uniformLatentPrior.mem_support_iff lat).mp (PMF.mem_support_uniformOfFintype lat)

/-- `extension X .null = Finset.univ` for both scopes — `null` is true everywhere.
Structurally generic: constructs cover witnesses for universal-extension
utterances. -/
theorem extension_null_eq_univ (s : ScopeReading) :
    extension s .null = Finset.univ := by
  ext w; simp [extension, RSA.mem_extensionOf]; cases s <;> cases w <;> rfl

/-! L0 values at each (scope, utterance, world) — the leaves every
comparison below reduces to. -/

private lemma L0_null_apply (sc : ScopeReading) (w : JumpOutcome) :
    L0 sc .null w = (3 : ℝ≥0∞)⁻¹ := by
  rw [L0_apply_of_true (by cases sc <;> rfl), extension_null_eq_univ]; rfl

private lemma L0_surf_en : ∀ w, L0 .surface .everyNot w =
    if w = .zero then 1 else 0
  | .zero => by
      rw [L0_apply_of_true (by decide),
        show extension .surface .everyNot = {JumpOutcome.zero} from rfl]
      simp
  | .one => L0_apply_of_false (by decide)
  | .two => L0_apply_of_false (by decide)

private lemma L0_inv_en : ∀ w, L0 .inverse .everyNot w =
    if w = .two then 0 else (2 : ℝ≥0∞)⁻¹
  | .zero => by
      rw [L0_apply_of_true (by decide), show extension .inverse .everyNot
        = {JumpOutcome.zero, JumpOutcome.one} from rfl]
      rfl
  | .one => by
      rw [L0_apply_of_true (by decide), show extension .inverse .everyNot
        = {JumpOutcome.zero, JumpOutcome.one} from rfl]
      rfl
  | .two => L0_apply_of_false (by decide)

/-- At `.surfHowMany`, surface scope makes `.everyNot` false at `.one`, so
the speaker score vanishes there but not at `.zero`. -/
theorem S1g_surfHowMany_strict {α : ℝ} (hα : 0 < α) :
    S1g hα .surfHowMany .one .everyNot < S1g hα .surfHowMany .zero .everyNot := by
  apply PMF.normalize_lt_of_apply_zero_pos
  · show (qProj .howMany (fun w' => L0 .surface .everyNot w') .one) ^ α = 0
    simp [qProj, L0_surf_en, ENNReal.zero_rpow_of_pos hα]
  · show (qProj .howMany (fun w' => L0 .surface .everyNot w') .zero) ^ α ≠ 0
    simp [qProj, L0_surf_en]

/-- Same shape at `.surfNone`: the none? projection at `.one` is
`L0 .one + L0 .two = 0`. -/
theorem S1g_surfNone_strict {α : ℝ} (hα : 0 < α) :
    S1g hα .surfNone .one .everyNot < S1g hα .surfNone .zero .everyNot := by
  apply PMF.normalize_lt_of_apply_zero_pos
  · show (qProj .none_ (fun w' => L0 .surface .everyNot w') .one) ^ α = 0
    simp [qProj, L0_surf_en, ENNReal.zero_rpow_of_pos hα]
  · show (qProj .none_ (fun w' => L0 .surface .everyNot w') .zero) ^ α ≠ 0
    simp [qProj, L0_surf_en]

/-- Per-latent comparison for the w0-vs-w1 ordering: no latent gives
`.everyNot` more mass at `.one` than at `.zero`, strictly less at
`.surfHowMany`. Each case is a vacuous zero, an equality of score
functions, or `≤` of projections lifted through rpow. -/
theorem S1g_zero_gt_one_for_some_latent {α : ℝ} (hα : 0 < α) :
    (∀ lat, S1g hα lat .one .everyNot ≤ S1g hα lat .zero .everyNot) ∧
    S1g hα .surfHowMany .one .everyNot < S1g hα .surfHowMany .zero .everyNot := by
  refine ⟨?_, S1g_surfHowMany_strict hα⟩
  have h_eq_via : ∀ (lat : Latent),
      (∀ u, s1Weight α lat .one u = s1Weight α lat .zero u) →
      S1g hα lat .one .everyNot ≤ S1g hα lat .zero .everyNot := fun lat hScore =>
    le_of_eq <| PMF.normalize_eq_of_apply_eq_and_sum_eq _ _ _ _ _ _ _
      (hScore .everyNot) (tsum_congr hScore)
  intro lat
  cases lat
  case surfHowMany => exact (S1g_surfHowMany_strict hα).le
  case surfNone => exact (S1g_surfNone_strict hα).le
  case surfAll => exact h_eq_via _ fun u => rfl
  case invAll => exact h_eq_via _ fun u => rfl
  case invHowMany =>
    refine h_eq_via _ fun u => ?_
    show (qProj .howMany (fun w' => L0 .inverse u w') .one) ^ α =
         (qProj .howMany (fun w' => L0 .inverse u w') .zero) ^ α
    cases u <;> simp [qProj, L0_null_apply, L0_inv_en]
  case invNone =>
    apply PMF.normalize_le_of_apply_eq_and_sum_ge
    · show (qProj .none_ (fun w' => L0 .inverse .everyNot w') .one) ^ α =
           (qProj .none_ (fun w' => L0 .inverse .everyNot w') .zero) ^ α
      simp [qProj, L0_inv_en]
    · refine ENNReal.tsum_le_tsum fun u => ?_
      refine ENNReal.rpow_le_rpow ?_ hα.le
      show qProj .none_ (fun w' => L0 .inverse u w') .zero ≤
           qProj .none_ (fun w' => L0 .inverse u w') .one
      cases u <;> simp [qProj, L0_null_apply, L0_inv_en] <;>
        exact le_self_add

/-- Baseline L1 ordering `L1(zero | everyNot) > L1(one | everyNot)` for
every α > 0: cancel the marginal and the uniform world prior, then compare
the marginal speakers per latent. -/
theorem baseline_L1_zero_gt_one {α : ℝ} (hα : 0 < α) :
    (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .zero >
      (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .one := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  obtain ⟨h_le, h_strict⟩ := S1g_zero_gt_one_for_some_latent hα
  exact PMF.bind_lt_bind uniformLatentPrior _ _ Utt.everyNot
    (uniformLatentPrior_ne_zero .surfHowMany) h_le h_strict

/-- At `.invHowMany`, inverse scope makes `.everyNot` false at `.two`, so
the speaker score vanishes there but not at `.one`. -/
theorem S1g_invHowMany_strict_one_two {α : ℝ} (hα : 0 < α) :
    S1g hα .invHowMany .two .everyNot < S1g hα .invHowMany .one .everyNot := by
  apply PMF.normalize_lt_of_apply_zero_pos
  · show (qProj .howMany (fun w' => L0 .inverse .everyNot w') .two) ^ α = 0
    simp [qProj, L0_inv_en, ENNReal.zero_rpow_of_pos hα]
  · show (qProj .howMany (fun w' => L0 .inverse .everyNot w') .one) ^ α ≠ 0
    simp [qProj, L0_inv_en]

/-- Per-latent comparison for the w1-vs-w2 ordering: five cases are
vacuous zeros at `.two`, `.invNone` is an equality. -/
theorem S1g_one_gt_two_for_some_latent {α : ℝ} (hα : 0 < α) :
    (∀ lat, S1g hα lat .two .everyNot ≤ S1g hα lat .one .everyNot) ∧
    S1g hα .invHowMany .two .everyNot < S1g hα .invHowMany .one .everyNot := by
  refine ⟨?_, S1g_invHowMany_strict_one_two hα⟩
  have h_zero_le : ∀ (lat : Latent),
      s1Weight α lat .two .everyNot = 0 →
      S1g hα lat .two .everyNot ≤ S1g hα lat .one .everyNot := fun lat hScore => by
    have h0 : S1g hα lat .two .everyNot = 0 := by
      rw [S1g, PMF.normalize_apply, hScore, zero_mul]
    rw [h0]; exact bot_le
  have h_eq_via : ∀ (lat : Latent),
      (∀ u, s1Weight α lat .two u = s1Weight α lat .one u) →
      S1g hα lat .two .everyNot ≤ S1g hα lat .one .everyNot := fun lat hScore =>
    le_of_eq <| PMF.normalize_eq_of_apply_eq_and_sum_eq _ _ _ _ _ _ _
      (hScore .everyNot) (tsum_congr hScore)
  intro lat
  cases lat
  case invHowMany => exact (S1g_invHowMany_strict_one_two hα).le
  case invNone =>
    refine h_eq_via _ fun u => ?_
    show (qProj .none_ (fun w' => L0 .inverse u w') .two) ^ α =
         (qProj .none_ (fun w' => L0 .inverse u w') .one) ^ α
    rfl
  all_goals refine h_zero_le _ ?_
  all_goals simp [s1Weight, Latent.qud, Latent.scope, qProj, L0_surf_en,
    L0_inv_en, ENNReal.zero_rpow_of_pos hα]

/-- Baseline L1 ordering `L1(one | everyNot) > L1(two | everyNot)` for
every α > 0. Same discharge as `baseline_L1_zero_gt_one`. -/
theorem baseline_L1_one_gt_two {α : ℝ} (hα : 0 < α) :
    (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .one >
      (L1 hα uniformLatentPrior .everyNot
        (L1_marginal_everyNot_ne_zero hα (uniformLatentPrior_ne_zero .surfHowMany))) .two := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  obtain ⟨h_le, h_strict⟩ := S1g_one_gt_two_for_some_latent hα
  exact PMF.bind_lt_bind uniformLatentPrior _ _ Utt.everyNot
    (uniformLatentPrior_ne_zero .invHowMany) h_le h_strict

/-! #### Scope collapse under QUD = all? (paper §3.2, restated §5.1)

The paper's central explanatory move (p. 17, 29-30): when QUD = `all?` is
favored, BOTH scope readings of "every horse didn't jump" answer the QUD
identically with "no, not all succeeded". This collapses the scope distinction
at the speaker layer — the structural mechanism behind pragmatic
dominance (the scope prior becoming nearly irrelevant).

Formalized at three layers: `qProj .all_` is scope-independent at
every utterance and world; hence `S1g hα .surfAll = S1g hα .invAll` as
PMFs; hence the surface/inverse all?-latents contribute interchangeably
to the marginal speaker. -/

/-- Under QUD = all?, the projected L0 mass is scope-invariant at every
utterance and world: the raw L0s differ (surface concentrates on `.zero`,
inverse splits over `.zero, .one`) but the all?-cell sums agree. -/
theorem qProj_all_scope_invariant (u : Utt) (w : JumpOutcome) :
    qProj .all_ (fun w' => L0 .surface u w') w =
      qProj .all_ (fun w' => L0 .inverse u w') w := by
  cases u <;> cases w <;>
    simp [qProj, L0_null_apply, L0_surf_en, L0_inv_en,
      ENNReal.inv_two_add_inv_two]

/-- Under QUD = `all?`, the speaker `S1g` is identical for surface
and inverse scope readings (at every world).

Direct corollary of the L0 invariance lifted through `PMF.normalize`: the score functions
are pointwise equal (since `s1Weight` only depends on `lat.qud` and `lat.scope`
through `qProj` which collapses the scope distinction), so the
normalized PMFs are equal. -/
theorem S1g_all_qud_scope_invariant {α : ℝ} (hα : 0 < α) (w : JumpOutcome) :
    S1g hα .surfAll w = S1g hα .invAll w := by
  -- Both are PMF.normalize of s1Weight; show s1Weight is pointwise equal across u.
  have h_score_eq : ∀ u, s1Weight α .surfAll w u = s1Weight α .invAll w u := fun u => by
    show (qProj .all_ (fun w' => L0 .surface u w') w) ^ α =
         (qProj .all_ (fun w' => L0 .inverse u w') w) ^ α
    rw [qProj_all_scope_invariant]
  ext u
  show PMF.normalize (s1Weight α .surfAll w) _ _ u =
       PMF.normalize (s1Weight α .invAll w) _ _ u
  exact PMF.normalize_eq_of_apply_eq_and_sum_eq _ _ _ _ _ _ _
    (h_score_eq u) (tsum_congr h_score_eq)

/-! #### Scope-prior irrelevance under QUD = all?

The headline structural consequence of the speaker collapse: when the latent prior is split
between `.surfAll` and `.invAll`, the contribution of these two latents to
`marginalSpeaker` depends only on the SUM of their prior weights, not the
individual values. Direct corollary of `S1g_all_qud_scope_invariant`
+ ENNReal distributivity (`add_mul`).

This is the structural mechanism behind the pragmatic-dominance claim:
shifting prior mass between `.invAll` and `.surfAll` doesn't change the
all?-QUD speaker behavior. -/

/-- Under QUD = `all?`, the `.surfAll` and `.invAll`
contributions to `marginalSpeaker` combine as a single sum-weighted term —
their individual prior weights don't matter, only the total.

Proof: `S1g_all_qud_scope_invariant` + ENNReal `add_mul`. -/
theorem marginalSpeaker_surfAll_invAll_combine {α : ℝ} (hα : 0 < α)
    (latentPrior : PMF Latent) (w : JumpOutcome) (u : Utt) :
    latentPrior .surfAll * S1g hα .surfAll w u +
        latentPrior .invAll * S1g hα .invAll w u =
      (latentPrior .surfAll + latentPrior .invAll) * S1g hα .surfAll w u := by
  rw [← S1g_all_qud_scope_invariant hα w, ← add_mul]

/-! #### The general-α QUD ordering (open)

The kernel-checked `s2_qud_ordering` above proves Figure 2's center panel
at the paper's exact parameters (α = 1, b_suc = 0.5, 18:1 QUD bias). The
general-α, parametric-prior statement — endorsement at `.one` ordered
across `qudPriorAt` values favoring none? < how-many? < all? — remains
open: the scope-collapse theorems above supply the all?-latent structure,
but the cross-prior comparison needs ENNReal arithmetic on the closed-form
chain (module-docstring TODO).

A related non-theorem, worth recording: endorsement monotonicity in
`b_suc` (Figure 2, left) is NOT factor-wise — `worldPriorAt b_suc .one`
equals `2·b_suc·(1 − b_suc)`, symmetric in `b_suc ↔ 1 − b_suc` and peaked
at 1/2 — so the observed monotone endorsement (.29/.50/.80) is an emergent
property of the full chain: as `b_suc → 1` the utterance gains
informativity at `.one` by ruling out the high-prior `.two`. Any
formalization must go through the full chain, e.g. as a limit statement. -/

end EveryNot

/-! ## The two-not model (§4) -/

namespace TwoNot

open BigOperators

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

/-! ### Truth conditions and compositional grounding -/

/-- RSA meaning for the two-not model, parameterized by numeral reading.
    Null utterance is always true (uninformative baseline). -/
def uttMeaning (nr : NumeralReading) : ScopeReading → Utt → JumpOutcome4 → Bool
  | _, .null, _ => true
  | s, .twoNot, w => twoNotTruth nr s w

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

/-- Restrictor: all entities are horses (trivial for this model). -/
def horse4_sem : Denot Horse4 Unit (.e ⇒ .t) := fun _ => True

/-- Jump predicate as Montague semantic value. -/
def jumpIn4_sem (w : JumpOutcome4) : Denot Horse4 Unit (.e ⇒ .t) :=
  fun h => jumpIn4 w h = true

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
noncomputable def twoHorsesDidntJump_atLeast (w : JumpOutcome4) :
    ScopeDerivation Horse4 Unit .t where
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

/-! ### The kernel face: exact-ℚ scores at the paper parameters -/

/-- Literal listener (fn. 6: no world prior in L0). -/
def l0Score (nr : NumeralReading) (sc : ScopeReading) (u : Utt)
    (w : JumpOutcome4) : ℚ≥0 :=
  (if uttMeaning nr sc u w then 1 else 0) /
    (∑ w', if uttMeaning nr sc u w' then (1 : ℚ≥0) else 0)

/-- QUD projection (paper (7)). -/
def qProj (q : QUD5) (f : JumpOutcome4 → ℚ≥0) (w : JumpOutcome4) : ℚ≥0 :=
  match q with
  | .howMany => f w
  | .all_ => match w with
    | .w4 => f .w4
    | _ => f .w0 + f .w1 + f .w2 + f .w3
  | .none_ => match w with
    | .w0 => f .w0
    | _ => f .w1 + f .w2 + f .w3 + f .w4
  | .twoExact => match w with
    | .w2 => f .w2
    | _ => f .w0 + f .w1 + f .w3 + f .w4
  | .twoAtLeast => match w with
    | .w2 | .w3 | .w4 => f .w2 + f .w3 + f .w4
    | _ => f .w0 + f .w1

/-- Speaker (α = 1; costs cancel). -/
def s1Score (nr : NumeralReading) (sc : ScopeReading) (q : QUD5)
    (w : JumpOutcome4) : Utt → ℚ≥0 :=
  PMF.normalizeScores fun u => qProj q (fun w' => l0Score nr sc u w') w

/-- Joint pragmatic-listener world score. -/
def l1Score (nr : NumeralReading) (wp : JumpOutcome4 → ℚ≥0)
    (sp : ScopeReading → ℚ≥0) (qp : QUD5 → ℚ≥0) (u : Utt)
    (w : JumpOutcome4) : ℚ≥0 :=
  wp w * ∑ lat : Latent10, sp lat.scope * qp lat.qud * s1Score nr lat.scope lat.qud w u

/-- Normalized world posterior. -/
def l1Post (nr : NumeralReading) (wp : JumpOutcome4 → ℚ≥0)
    (sp : ScopeReading → ℚ≥0) (qp : QUD5 → ℚ≥0) (u : Utt) :
    JumpOutcome4 → ℚ≥0 :=
  PMF.normalizeScores (l1Score nr wp sp qp u)

/-- Binomial(4, 0.1) ∝ (6561, 2916, 486, 36, 1). -/
def lowWP4 : JumpOutcome4 → ℚ≥0
  | .w0 => 6561 | .w1 => 2916 | .w2 => 486 | .w3 => 36 | .w4 => 1

/-- Surface-biased scope prior: P(inverse) = 0.1 (∝ 9:1). -/
def biasSP : ScopeReading → ℚ≥0 | .surface => 9 | .inverse => 1

/-- Uniform QUD prior. -/
def uniQP5 : QUD5 → ℚ≥0 := fun _ => 1

/-- Endorsement speaker S₂ over the two-not listener (baseline priors:
b_suc = 0.1, P(inverse) = 0.1, uniform QUDs). -/
noncomputable def s2 (nr : NumeralReading) (w : JumpOutcome4) : PMF Utt :=
  .ofScores .uniform fun u => l1Post nr lowWP4 biasSP uniQP5 u w

/-! ### Endorsement predictions (§4.2, Figure 7)

Under exact semantics, surface scope pinpoints w=2 as the unique true
world, so baseline endorsement at w=2 is high; under at-least semantics it
spreads over {w0,w1,w2} and endorsement is low. The same baseline that
gives low 1-of-2 endorsement gives high 2-of-4 endorsement only under
exact semantics — the paper's argument for exact numeral meanings. -/

/-- Exact semantics: baseline S₂ endorsement at w=2 exceeds 1/2
(Figure 7 right, ≈ .8). -/
theorem exact_baseline_endorsement_high : (((1/2 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < s2 .exact .w2 .twoNot :=
  PMF.ratCast_lt_ofScores _ (by decide +kernel)

/-- At-least semantics: baseline S₂ endorsement at w=2 is below 1/2
(Figure 7 left, ≈ .4). -/
theorem atleast_baseline_endorsement_low : s2 .atLeast .w2 .twoNot < (((1/2 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofScores_lt_ratCast _ (by decide +kernel)

/-- Exact endorsement at w=2 exceeds at-least endorsement: one true
surface world versus three. -/
theorem exact_vs_atleast_endorsement : s2 .atLeast .w2 .twoNot < s2 .exact .w2 .twoNot :=
  PMF.ofScores_lt_cross _ _ (by decide +kernel)

/-! ### Informativity contrasts -/

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

/-! ### The structural face: exact-vs-at-least necessity (§4.2.2)

The paper's strongest contribution to the numeral-semantics literature:

> "the current model requires one more ingredient to account for the 1-of-2
> vs 2-of-4 difference in adult behavior: an exact semantics for utterances
> with numerals (in contrast to an at-least semantics; for discussion, see
> e.g. Geurts 2006; Breheny 2008)."

Figure 7 (paper p.27) shows the contrast explicitly: under exact semantics
the surface scope of `twoNot` pinpoints `w=2` as the unique true world →
high S2 endorsement; under at-least semantics the surface scope is true at
multiple worlds {w0, w1, w2} → S2 dilutes across 3 worlds → low endorsement.

The paper's core empirical move: only with exact semantics can the model
reproduce adult endorsement-rate divergence between EveryNot (1-of-2) and
TwoNot (2-of-4).

This section proves the structural foundation: at w=2, the surface-scope
`twoNot` L0 mass is strictly higher under exact semantics than under
at-least semantics (a singleton extension {w2} versus {w0, w1, w2}). The
endorsement difference proved on the kernel face above
(`exact_vs_atleast_endorsement` and the two threshold theorems) inherits
from this concentration. -/

/-! #### Extension of `twoNot` under each numeral reading -/

/-- Extension of `uttMeaning nr s u`: worlds where `u` is true under
numeral reading `nr` and scope `s`. -/
abbrev extension4 (nr : NumeralReading) (s : ScopeReading) (u : TwoNot.Utt) :
    Finset JumpOutcome4 :=
  RSA.extensionOf (TwoNot.uttMeaning nr s) u

/-- Under exact semantics, surface `twoNot` extension is the singleton `{w2}`
(only "exactly 2 didn't jump" is true when exactly 2 jumped). -/
theorem extension4_exact_surface_twoNot :
    extension4 .exact .surface .twoNot = {JumpOutcome4.w2} := rfl

/-- Under at-least semantics, surface `twoNot` extension is `{w0, w1, w2}`
(at least 2 didn't jump iff at most 2 jumped). -/
theorem extension4_atLeast_surface_twoNot :
    extension4 .atLeast .surface .twoNot =
      {JumpOutcome4.w0, JumpOutcome4.w1, JumpOutcome4.w2} := rfl

theorem extension4_nonempty (nr : NumeralReading) (s : ScopeReading) (u : TwoNot.Utt) :
    (extension4 nr s u).Nonempty := by
  -- For `null`: w0 always works (null is universally true).
  -- For `twoNot`: case split — exact surface is true ONLY at w2; other cases have w0.
  cases u
  case null => exact ⟨.w0, by rw [RSA.mem_extensionOf]; cases nr <;> cases s <;> rfl⟩
  case twoNot =>
    cases nr <;> cases s
    case exact.surface => exact ⟨.w2, by rw [RSA.mem_extensionOf]; rfl⟩
    case exact.inverse => exact ⟨.w0, by rw [RSA.mem_extensionOf]; rfl⟩
    case atLeast.surface => exact ⟨.w0, by rw [RSA.mem_extensionOf]; rfl⟩
    case atLeast.inverse => exact ⟨.w0, by rw [RSA.mem_extensionOf]; rfl⟩

/-! #### L0 (literal listener) for the TwoNot model

Parameterized on numeral reading `nr` (exact vs at-least), determining the
extension's cardinality. -/

/-- TwoNot literal listener: uniform on extension under given numeral reading. -/
noncomputable def L0_4 (nr : NumeralReading) (s : ScopeReading) (u : TwoNot.Utt) :
    PMF JumpOutcome4 :=
  RSA.L0OfBoolMeaning (TwoNot.uttMeaning nr s) u (extension4_nonempty nr s u)

theorem L0_4_apply_of_true {nr : NumeralReading} {s : ScopeReading} {u : TwoNot.Utt}
    {w : JumpOutcome4} (h : TwoNot.uttMeaning nr s u w = true) :
    L0_4 nr s u w = ((extension4 nr s u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem L0_4_apply_of_false {nr : NumeralReading} {s : ScopeReading} {u : TwoNot.Utt}
    {w : JumpOutcome4} (h : TwoNot.uttMeaning nr s u w ≠ true) :
    L0_4 nr s u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

/-! #### The L0 concentration contrast

At world `w2` (2 of 4 jumped), surface scope `twoNot` L0 mass is strictly
higher under exact than under at-least — because the extension cardinality
shrinks from 3 to 1. The S2 endorsement difference inherits from this. -/

/-- The structural foundation of the exact-semantics necessity claim:
at world `w2`, surface-scope `twoNot` L0 is strictly higher under EXACT
semantics (1) than under AT-LEAST semantics (1/3).

Proof: extension cardinality is 1 (exact) vs 3 (at-least); uniform-on-extension
gives 1/1 = 1 vs 1/3.

This single L0 fact propagates to S2 endorsement: under exact, S2 puts more
mass on `.twoNot` at w=2 (informative utterance pinpoints the world);
under at-least, the L0 dilutes across 3 worlds → less informative → lower
S2 endorsement. The structural mechanism behind paper's Figure 7. -/
theorem L0_exact_gt_atLeast_at_w2 :
    L0_4 .atLeast .surface .twoNot .w2 < L0_4 .exact .surface .twoNot .w2 := by
  rw [L0_4_apply_of_true (by decide : TwoNot.uttMeaning .exact .surface .twoNot .w2 = true),
      L0_4_apply_of_true (by decide : TwoNot.uttMeaning .atLeast .surface .twoNot .w2 = true),
      extension4_exact_surface_twoNot, extension4_atLeast_surface_twoNot]
  -- Goal: ((Finset.card {w0, w1, w2} : ℕ) : ℝ≥0∞)⁻¹ < ((Finset.card {w2} : ℕ) : ℝ≥0∞)⁻¹
  -- = (3 : ℝ≥0∞)⁻¹ < (1 : ℝ≥0∞)⁻¹ = 1
  show ((3 : ℕ) : ℝ≥0∞)⁻¹ < ((1 : ℕ) : ℝ≥0∞)⁻¹
  rw [Nat.cast_one, Nat.cast_ofNat, inv_one]
  exact ENNReal.inv_lt_one.mpr (by norm_num)

/-! #### Vacuous-zero contrast at the divergence worlds

The other side of the exact-vs-at-least divergence: at worlds w0 and w1
(where 0 or 1 horses jumped), surface-scope `twoNot` is FALSE under exact
("not exactly 2 didn't jump") but TRUE under at-least ("at least 2 didn't
jump"). So L0 mass under exact at these worlds is 0; L0 mass under at-least
is 1/3 (positive).

This is the "dilution" mechanism: at-least's broader extension means L0
mass spreads to "wrong" worlds. -/

/-- At worlds w0 and w1, exact L0 is zero (surface twoNot false), at-least
L0 is positive (surface twoNot true). -/
theorem L0_exact_zero_atLeast_pos_at_w0 :
    L0_4 .exact .surface .twoNot .w0 = 0 ∧ L0_4 .atLeast .surface .twoNot .w0 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · exact L0_4_apply_of_false (by decide : TwoNot.uttMeaning .exact .surface .twoNot .w0 ≠ true)
  · rw [L0_4_apply_of_true (by decide : TwoNot.uttMeaning .atLeast .surface .twoNot .w0 = true),
        extension4_atLeast_surface_twoNot]
    -- Goal: ((Finset.card {w0, w1, w2} : ℕ) : ℝ≥0∞)⁻¹ ≠ 0
    -- = (3 : ℝ≥0∞)⁻¹ ≠ 0; true since 3 ≠ ⊤
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-! The full endorsement-rate divergence at the paper's parameters is
proved on the kernel face above (`exact_baseline_endorsement_high`,
`atleast_baseline_endorsement_low`, `exact_vs_atleast_endorsement`); a
general-α propagation of the L0 concentration through the 5-world ×
10-latent chain remains open (module-docstring TODO). -/

end TwoNot

/-! ### The cross-model asymmetry (§4.2.2)

The paper's key argument: the SAME "baseline" parameters that produce
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

/-- Every-not baseline endorsement at w=1 is below 1/2: the low end of the
1-of-2 vs 2-of-4 asymmetry, with the same b_suc = 0.1 world prior as the
two-not baseline. -/
theorem everyNot_baseline_endorsement_low :
    EveryNot.s2 EveryNot.lowWP EveryNot.uniSP EveryNot.uniQP .one .everyNot <
      (((1/2 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofScores_lt_ratCast _ (by decide +kernel)

end ScontrasPearl2021
