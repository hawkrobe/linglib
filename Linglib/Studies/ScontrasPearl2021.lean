import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Core.Probability.Scores
import Linglib.Pragmatics.RSA.Operators
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Composition.Scope

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

- `l0Score`: L0(w|u,i) ∝ δ_{⟦u⟧ⁱ(w)} (literal semantics, no world prior; fn. 6)
- `s1Score`: S1(u|w,i,q) ∝ exp(α · log L0(⟦q⟧(w)|u,i,q)) (QUD-projected)
- `l1Score`/`l1`: L1(w,i,q|u) ∝ P(w) · P(i) · P(q) · S1(u|w,i,q)
- `s2`: S2(u|w) ∝ Σ_{i,q} L1(w,i,q|u), the endorsement probability at the
  observed world

Parameters: α = 1 (§3.2). P(w) = Binomial(n, b_suc).

### QUDs (paper (3))

Three QUD partitions over worlds:
- how-many?: identity — partitions {w0}, {w1}, {w2}
- all?: w = n? — partitions {w0,w1} vs {w2}
- none?: w = 0? — partitions {w0} vs {w1,w2}

### Compositional Grounding

Truth conditions grounded in `every_sem` (`Quantifier.lean`),
`ScopeConfig`/`ScopeDerivation` (`Scope.lean`).

### Key findings (Figure 2)

`s2_ordering_*`: the endorsement ordering w0 > w1 > w2 across all prior
configurations (paper's Figure 2 endorsement at w=1: .29 at b_suc = 0.1,
.80 at b_suc = 0.9). `s2_qud_ordering`: favoring none? < how-many? < all?
monotonically increases endorsement (paper: .38 < .48 < .63; the adult
pattern of the paper's Figure 4).

### The structural face

Each model also carries its general-α operator-face formalization
(`RSA.L0OfBoolMeaning`, `PMF.posterior`, `PMF.binomial` priors): the
baseline L₁ orderings for every α > 0, the scope-collapse theorems under
the all? QUD (`S1g_all_qud_scope_invariant` — the paper's pragmatic-
dominance mechanism), and the exact-vs-at-least L0 concentration contrast
that drives §4.2.2.

## TODO

General-α, parametric-prior versions of the QUD-ordering and of the
exact-vs-at-least endorsement divergence (their α = 1 instances at the
paper's parameters are kernel-proved); the emergent b_suc-monotonicity of
endorsement as a limit statement.

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

open scoped NNRat NNReal ENNReal

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

/-- The every-not scope pair has surface-entails-inverse structure:
surface scope (none jumped) is a strict
    subset of inverse scope (not all jumped). This makes universals
    non-diagnostic for scope preferences — no TVJ context can
    distinguish isomorphic from non-isomorphic behavior. -/
theorem every_not_scope_entailment :
    Semantics.Scope.classifyScopeEntailment
      [JumpOutcome.zero, .one, .two]
      (scopeTruth .surface) (scopeTruth .inverse)
    = .surfaceEntailsInverse := by decide

-- QUD Projection

-- Exact-ℚ model

/-- Literal listener (fn. 6: no world prior in L0). -/
def l0Score (sc : ScopeReading) (u : Utt) (w : JumpOutcome) : ℚ≥0 :=
  (if uttMeaning sc u w then 1 else 0) /
    (∑ w', if uttMeaning sc u w' then (1 : ℚ≥0) else 0)

/-- QUD projection of the literal listener (paper (3)). -/
def qProj (q : QUD) (f : JumpOutcome → ℚ≥0) : JumpOutcome → ℚ≥0
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

-- Prior configurations (ℚ; §3.2, Figure 2)

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


open scoped ENNReal NNReal
open ScontrasPearl2021 ScontrasPearl2021.EveryNot

/-! ### World prior — uniform on `JumpOutcome` -/

noncomputable def worldPrior : PMF JumpOutcome := PMF.uniformOfFintype JumpOutcome

theorem worldPrior_ne_zero (w : JumpOutcome) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

/-! ### L0 — literal listener as `RSA.L0OfBoolMeaning`

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

/-! ### QUD projection (ENNReal version)

ENNReal lift of `qudProjectInline`: sums L0 mass over the equivalence class
of `w` under QUD `q`. Returns `ℝ≥0∞` so that the rpow speaker score lives
in `ℝ≥0∞` end-to-end. -/

/-- QUD projection on `ℝ≥0∞`-valued functions. -/
noncomputable def qudProjectE (q : QUD) (f : JumpOutcome → ℝ≥0∞) (w : JumpOutcome) : ℝ≥0∞ :=
  match q, w with
  | .howMany, .zero => f .zero
  | .howMany, .one  => f .one
  | .howMany, .two  => f .two
  | .all_,    .zero => f .zero + f .one
  | .all_,    .one  => f .zero + f .one
  | .all_,    .two  => f .two
  | .none_,   .zero => f .zero
  | .none_,   .one  => f .one + f .two
  | .none_,   .two  => f .one + f .two

/-- The projection at `w` under QUD `q` is bounded above by the total mass
of `f` (a finite sum of pieces of `Σ f`). Used to discharge `≠ ∞`. -/
theorem qudProjectE_ne_top {q : QUD} {f : JumpOutcome → ℝ≥0∞} {w : JumpOutcome}
    (hf : ∀ w, f w ≠ ∞) : qudProjectE q f w ≠ ∞ := by
  cases q <;> cases w <;> simp only [qudProjectE] <;>
    first
    | exact hf _
    | exact ENNReal.add_ne_top.mpr ⟨hf _, hf _⟩

/-- The projection of L0 includes the mass at `w` itself (since `w` is in
its own equivalence class for every QUD). Used to derive positivity of the
rpow speaker score at the witness world. -/
theorem qudProjectE_self_ge {q : QUD} {f : JumpOutcome → ℝ≥0∞} (w : JumpOutcome) :
    f w ≤ qudProjectE q f w := by
  cases q <;> cases w <;> simp only [qudProjectE] <;>
    first
    | exact le_refl _
    | exact le_self_add
    | exact le_add_self

/-- If L0 is non-zero at `w`, the QUD-projected sum is non-zero at `w`. -/
theorem qudProjectE_ne_zero_of_self {q : QUD} {f : JumpOutcome → ℝ≥0∞} {w : JumpOutcome}
    (h : f w ≠ 0) : qudProjectE q f w ≠ 0 := by
  intro hp
  exact h (le_antisymm (hp ▸ qudProjectE_self_ge w) zero_le)

/-! ### S1g — speaker conditional on (latent, world)

`S1g lat w u ∝ (qudProjectE lat.qud (L0 lat.scope u) w)^α`. The cover witness
is the `null` utterance: its L0 is uniform on `Finset.univ`, so the projection
is positive at every `w` (every QUD class contains some world where `null`'s
L0 is positive — and `null`'s L0 is positive everywhere). -/

/-- The unnormalised score: `(qudProjectE lat.qud (L0 lat.scope u) w)^α`. -/
noncomputable def s1Weight (α : ℝ) (lat : Latent) (w : JumpOutcome) (u : Utt) : ℝ≥0∞ :=
  (qudProjectE lat.qud (fun w' => L0 lat.scope u w') w) ^ α

theorem L0_null_ne_zero (s : ScopeReading) (w : JumpOutcome) :
    L0 s .null w ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_L0_iff]
  cases s <;> rfl

theorem s1Score_null_ne_zero {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) :
    s1Weight α lat w .null ≠ 0 := by
  refine (not_congr (ENNReal.rpow_eq_zero_iff_of_pos hα)).mpr ?_
  exact qudProjectE_ne_zero_of_self (L0_null_ne_zero _ _)

theorem L0_ne_top (s : ScopeReading) (u : Utt) (w : JumpOutcome) : L0 s u w ≠ ∞ :=
  PMF.apply_ne_top _ _

theorem s1Score_ne_top {α : ℝ} (hα : 0 ≤ α) (lat : Latent) (w : JumpOutcome) (u : Utt) :
    s1Weight α lat w u ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg hα (qudProjectE_ne_top (L0_ne_top _ _))

theorem s1Score_tsum_ne_zero {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) :
    ∑' u, s1Weight α lat w u ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.null, s1Score_null_ne_zero hα lat w⟩

theorem s1Score_tsum_ne_top {α : ℝ} (hα : 0 ≤ α) (lat : Latent) (w : JumpOutcome) :
    ∑' u, s1Weight α lat w u ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun u => s1Score_ne_top hα lat w u

/-- Pragmatic speaker conditioned on (latent, world). -/
noncomputable def S1g {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) : PMF Utt :=
  PMF.normalize (s1Weight α lat w) (s1Score_tsum_ne_zero hα lat w)
    (s1Score_tsum_ne_top hα.le lat w)

theorem mem_support_S1g_iff {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) (u : Utt) :
    u ∈ (S1g hα lat w).support ↔ s1Weight α lat w u ≠ 0 := by
  rw [S1g, PMF.mem_support_normalize_iff]

theorem S1g_null_ne_zero {α : ℝ} (hα : 0 < α) (lat : Latent) (w : JumpOutcome) :
    S1g hα lat w .null ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_S1g_iff]
  exact s1Score_null_ne_zero hα lat w

/-! ### Marginal speaker — `PMF.bind` over the latent prior

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

/-! ### L1 — Bayesian inversion via `PMF.posterior` -/

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

/-! ### Findings — paper's S2 endorsement orderings

The paper's central claims (Figure 2) are S2 endorsement orderings at the
partial world `.one`, robust across prior configurations. Each is an L1
inequality discharged via the Bayes identity (S2(u|w) ∝ L1(w|u) over u).

Proved below for every α > 0 via the structural shell; the α = 1
instances at the paper's exact priors are the kernel-checked
`s2_ordering_*` theorems above. -/


/-! ### Baseline (b_suc = 0.1, uniform scope and QUD)

General-α companions of `baseline_l1_ordering` above. Take any
`latentPrior` with positive mass everywhere — the uniform on `Latent`
works. -/

/-- Surface-scope-favored latent prior: every latent has positive mass.
Used as the default `latentPrior` for the findings below. -/
noncomputable def uniformLatentPrior : PMF Latent := PMF.uniformOfFintype Latent

theorem uniformLatentPrior_ne_zero (lat : Latent) : uniformLatentPrior lat ≠ 0 :=
  (uniformLatentPrior.mem_support_iff lat).mp (PMF.mem_support_uniformOfFintype lat)

/-! ### Structural-shell decomposition

The two baseline findings below admit a clean structural decomposition:

  `posterior_lt_iff_score_lt` cancels the L1 marginal denominator, reducing
  to a `worldPrior · marginalSpeaker` score comparison. `worldPrior` is
  uniform, so it cancels via `mul_lt_mul_iff_right`. The remainder is a
  pure `marginalSpeaker` comparison — itself a `PMF.bind` over the latent
  prior, decomposable per-latent via `marginal_lt_marginal`.

The per-latent comparison is the natural "leaf" obligation: a finite
case-bash over `Latent` that compares S1g speaker outputs at the two
worlds being contrasted. It bottoms out in `ENNReal.rpow_lt_rpow` (rpow
is strictly increasing in its base) — *structural* but specific to the
S1g internals. -/

/-! ### Per-latent leaf computations

The structural shell reduces the headline to per-latent S1g comparisons.
For each latent, both sides are `(qudProjectE q (L0 s .everyNot) w)^α / Z(lat, w)`
with `Z` and the projection depending only on `lat` and `w`. The pointwise
comparison breaks into 6 cases over `Latent`, each computable from the
truth table of `uttMeaning` plus rpow monotonicity.

In the strict-witness case (`.surfHowMany`) at world `.one`, surface
scope makes `.everyNot` false, the L0 numerator is zero, and the speaker
score collapses; the remaining cases collapse to equalities or to
`(1/3)^α < (2/3)^α` monotonicity. -/

/-- The strict-witness case: at `.surfHowMany`, surface scope makes
`.everyNot` false at world `.one`, so the speaker score is zero. -/
theorem S1g_surfHowMany_strict {α : ℝ} (hα : 0 < α) :
    S1g hα .surfHowMany .one .everyNot < S1g hα .surfHowMany .zero .everyNot := by
  apply PMF.normalize_lt_of_apply_zero_pos
  · -- LHS score = 0: qudProjectE .howMany at .one = L0 .surface .everyNot .one = 0
    show (qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .one) ^ α = 0
    rw [show qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .one
            = L0 .surface .everyNot .one from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- RHS score ≠ 0: qudProjectE .howMany at .zero = L0 .surface .everyNot .zero = 1
    show (qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .zero) ^ α ≠ 0
    rw [show qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .zero
            = L0 .surface .everyNot .zero from rfl,
        L0_apply_of_true (by decide : uttMeaning .surface .everyNot .zero = true),
        show extension .surface .everyNot = {JumpOutcome.zero} from rfl]
    simp

/-- Companion vacuous-zero strict case at `.surfNone`: same shape as
`.surfHowMany`. Surface scope makes `.everyNot` false at `.one`, and the
QUD .none_ doesn't help — its projection at `.one` is `L0 .one + L0 .two = 0`. -/
theorem S1g_surfNone_strict {α : ℝ} (hα : 0 < α) :
    S1g hα .surfNone .one .everyNot < S1g hα .surfNone .zero .everyNot := by
  apply PMF.normalize_lt_of_apply_zero_pos
  · -- LHS score = 0: qudProjectE .none_ at .one = L0 .one + L0 .two = 0 + 0 = 0
    show (qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .one) ^ α = 0
    rw [show qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .one
            = L0 .surface .everyNot .one + L0 .surface .everyNot .two from rfl,
        L0_apply_of_false (by decide : uttMeaning .surface .everyNot .one ≠ true),
        L0_apply_of_false (by decide : uttMeaning .surface .everyNot .two ≠ true), add_zero]
    exact ENNReal.zero_rpow_of_pos hα
  · -- RHS score ≠ 0: at .zero, qudProjectE .none_ = L0 .zero ≠ 0
    show (qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .zero) ^ α ≠ 0
    rw [show qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .zero
            = L0 .surface .everyNot .zero from rfl,
        L0_apply_of_true (by decide : uttMeaning .surface .everyNot .zero = true),
        show extension .surface .everyNot = {JumpOutcome.zero} from rfl]
    simp

/-- Per-latent comparison: at every latent, the S1g speaker assigns no more
mass to `.everyNot` at world `.one` than at world `.zero`, with strict
preference at `.surfHowMany`.

Per-latent breakdown:
- `.surfHowMany`, `.surfNone` (vacuous-zero): LHS = 0, ≤ via `le_of_lt` from
  the strict witnesses `S1g_surfHowMany_strict` / `S1g_surfNone_strict`.
- `.surfAll`, `.invHowMany`, `.invAll` (equality): both sides have the same
  numerator AND same partition function (verified by symmetric structure).
- `.invNone` (strict via rpow monotonicity): `(1/3)^α < (2/3)^α` makes the
  partition function smaller at `.zero`, so the quotient is larger.

The 4 remaining cases are mechanical computation but require ENNReal
arithmetic infrastructure (or a `pmf_score_compare` tactic). -/
theorem S1g_zero_gt_one_for_some_latent {α : ℝ} (hα : 0 < α) :
    (∀ lat, S1g hα lat .one .everyNot ≤ S1g hα lat .zero .everyNot) ∧
    S1g hα .surfHowMany .one .everyNot < S1g hα .surfHowMany .zero .everyNot := by
  refine ⟨?_, S1g_surfHowMany_strict hα⟩
  -- Helper: equality cases reduce to "score functions are equal pointwise"
  have h_eq_via : ∀ (lat : Latent),
      (∀ u, s1Weight α lat .one u = s1Weight α lat .zero u) →
      S1g hα lat .one .everyNot ≤ S1g hα lat .zero .everyNot := fun lat hScore =>
    le_of_eq <| PMF.normalize_eq_of_apply_eq_and_sum_eq _ _ _ _ _ _ _
      (hScore .everyNot) (tsum_congr hScore)
  intro lat
  cases lat
  · exact (S1g_surfHowMany_strict hα).le  -- surfHowMany: vacuous-zero LHS
  · -- surfAll: scores equal at .one and .zero (qudProjectE .all_ groups {.zero, .one})
    refine h_eq_via .surfAll fun u => ?_
    show (qudProjectE .all_ (fun w' => L0 .surface u w') .one) ^ α =
         (qudProjectE .all_ (fun w' => L0 .surface u w') .zero) ^ α
    rfl
  · exact (S1g_surfNone_strict hα).le  -- surfNone: vacuous-zero LHS
  · -- invHowMany: scores equal at .one and .zero because L0 .inverse u is symmetric
    -- between .zero and .one for all u (uttMeaning .inverse u .zero = uttMeaning .inverse u .one)
    refine h_eq_via .invHowMany fun u => ?_
    show (qudProjectE .howMany (fun w' => L0 .inverse u w') .one) ^ α =
         (qudProjectE .howMany (fun w' => L0 .inverse u w') .zero) ^ α
    -- qudProjectE .howMany is identity, so need L0 .inverse u .one = L0 .inverse u .zero
    have hL0_eq : L0 .inverse u .one = L0 .inverse u .zero := by
      cases u
      · -- u = .null: both true (L0 = 1/3)
        rw [L0_apply_of_true (by decide), L0_apply_of_true (by decide)]
      · -- u = .everyNot: both true under .inverse (L0 = 1/2)
        rw [L0_apply_of_true (by decide), L0_apply_of_true (by decide)]
    show L0 .inverse u .one ^ α = L0 .inverse u .zero ^ α
    rw [hL0_eq]
  · -- invAll: scores equal at .one and .zero (same QUD groups {.zero, .one})
    refine h_eq_via .invAll fun u => ?_
    show (qudProjectE .all_ (fun w' => L0 .inverse u w') .one) ^ α =
         (qudProjectE .all_ (fun w' => L0 .inverse u w') .zero) ^ α
    rfl
  · -- invNone: numerators equal at .everyNot, partition larger at .one
    apply PMF.normalize_le_of_apply_eq_and_sum_ge
    · -- Numerator equality at .everyNot:
      -- qudProjectE .none_ (L0 .inverse .everyNot) .one = L0 .one + L0 .two = L0 .one + 0 = L0 .one
      -- qudProjectE .none_ (L0 .inverse .everyNot) .zero = L0 .zero
      -- L0 .inverse .everyNot .zero = L0 .inverse .everyNot .one (both =((extension).card)⁻¹)
      have h_two : L0 .inverse .everyNot .two = 0 := L0_apply_of_false (by decide)
      have h_eq_zero_one : L0 .inverse .everyNot .zero = L0 .inverse .everyNot .one := by
        rw [L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .zero = true),
            L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .one = true)]
      show (L0 .inverse .everyNot .one + L0 .inverse .everyNot .two) ^ α =
           L0 .inverse .everyNot .zero ^ α
      rw [h_two, add_zero, h_eq_zero_one]
    · -- Partition sum monotonicity: per-u, qudProj at .zero ≤ qudProj at .one
      apply ENNReal.tsum_le_tsum
      intro u
      cases u
      · -- u = .null: qudProj at .zero = L0 .zero; at .one = L0 .one + L0 .two
        -- L0 .inverse .null = uniform (all true), so L0 .zero = L0 .one = L0 .two = 1/3
        -- So L0 .zero ≤ L0 .one + L0 .two via le_add_right + h_eq
        show L0 .inverse .null .zero ^ α ≤
             (L0 .inverse .null .one + L0 .inverse .null .two) ^ α
        have h_zero_le_one : L0 .inverse .null .zero ≤ L0 .inverse .null .one := by
          rw [L0_apply_of_true (by decide : uttMeaning .inverse .null .zero = true),
              L0_apply_of_true (by decide : uttMeaning .inverse .null .one = true)]
        apply ENNReal.rpow_le_rpow _ hα.le
        exact h_zero_le_one.trans le_self_add
      · -- u = .everyNot: qudProj at .zero = L0 .zero;
        -- at .one = L0 .one + L0 .two = L0 .one + 0 = L0 .one = L0 .zero
        show L0 .inverse .everyNot .zero ^ α ≤
             (L0 .inverse .everyNot .one + L0 .inverse .everyNot .two) ^ α
        have h_two : L0 .inverse .everyNot .two = 0 := L0_apply_of_false (by decide)
        have h_eq : L0 .inverse .everyNot .zero = L0 .inverse .everyNot .one := by
          rw [L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .zero = true),
              L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .one = true)]
        rw [h_two, add_zero, h_eq]

/-- Baseline L1 ordering at the partial world: `L1(zero | everyNot) > L1(one | everyNot)`.
Both scopes agree `.zero` is true; only inverse scope makes `.one` true.

**Structural discharge** (2 lemma applications, post-API extension):
1. `posterior_lt_iff_kernel_lt_of_uniform`: cancels L1 marginal AND uniform world prior.
2. `PMF.bind_lt_bind`: reduces marginalSpeaker = bind to per-latent comparison.

The pre-API-extension version of this proof took 4 explicit rewrite steps;
the cancellation lemmas collapse it to two single-line tactics. -/
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

/-- Strict-witness case for the .one-vs-.two ordering: at `.invHowMany`,
inverse scope makes `.everyNot` false at `.two` (only `.zero` and `.one`
are in extension), so the speaker score at `.two` is zero. -/
theorem S1g_invHowMany_strict_one_two {α : ℝ} (hα : 0 < α) :
    S1g hα .invHowMany .two .everyNot < S1g hα .invHowMany .one .everyNot := by
  apply PMF.normalize_lt_of_apply_zero_pos
  · -- LHS score = 0: L0 .inverse .everyNot .two = 0 (.two ∉ extension {.zero, .one})
    show (qudProjectE .howMany (fun w' => L0 .inverse .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .howMany (fun w' => L0 .inverse .everyNot w') .two
            = L0 .inverse .everyNot .two from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- RHS score ≠ 0: L0 .inverse .everyNot .one ≠ 0 (.one ∈ extension)
    show (qudProjectE .howMany (fun w' => L0 .inverse .everyNot w') .one) ^ α ≠ 0
    rw [show qudProjectE .howMany (fun w' => L0 .inverse .everyNot w') .one
            = L0 .inverse .everyNot .one from rfl,
        L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .one = true)]
    -- L0 = ((extension .inverse .everyNot).card)⁻¹ ≠ 0
    rw [show extension .inverse .everyNot = {JumpOutcome.zero, JumpOutcome.one} from rfl]
    simp

/-- Per-latent comparison: at every latent, the S1g speaker assigns no more
mass to `.everyNot` at world `.two` than at world `.one`. Strict witness at
`.invHowMany`.

5 of 6 cases are vacuous-zero (LHS = 0 because `.two ∉ extension` for both
scopes — surface scope: extension = {.zero}; inverse scope: extension = {.zero, .one}).
The remaining case (.invNone) is an equality. -/
theorem S1g_one_gt_two_for_some_latent {α : ℝ} (hα : 0 < α) :
    (∀ lat, S1g hα lat .two .everyNot ≤ S1g hα lat .one .everyNot) ∧
    S1g hα .invHowMany .two .everyNot < S1g hα .invHowMany .one .everyNot := by
  refine ⟨?_, S1g_invHowMany_strict_one_two hα⟩
  -- Helper for vacuous-zero cases: if score at .two is 0, S1g is 0 ≤ X
  have h_zero_le : ∀ (lat : Latent),
      s1Weight α lat .two .everyNot = 0 →
      S1g hα lat .two .everyNot ≤ S1g hα lat .one .everyNot := by
    intro lat hScore
    have : S1g hα lat .two .everyNot = 0 := by
      rw [S1g, PMF.normalize_apply, hScore, zero_mul]
    rw [this]; exact zero_le
  -- Helper for equality cases (parallel to S1g_zero_gt_one)
  have h_eq_via : ∀ (lat : Latent),
      (∀ u, s1Weight α lat .two u = s1Weight α lat .one u) →
      S1g hα lat .two .everyNot ≤ S1g hα lat .one .everyNot := fun lat hScore =>
    le_of_eq <| PMF.normalize_eq_of_apply_eq_and_sum_eq _ _ _ _ _ _ _
      (hScore .everyNot) (tsum_congr hScore)
  intro lat
  cases lat
  · -- surfHowMany: vacuous-zero (L0 .surface .everyNot .two = 0)
    refine h_zero_le .surfHowMany ?_
    show (qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .howMany (fun w' => L0 .surface .everyNot w') .two
            = L0 .surface .everyNot .two from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- surfAll: vacuous-zero (qudProjectE .all_ at .two = L0 .two = 0 for surface .everyNot)
    refine h_zero_le .surfAll ?_
    show (qudProjectE .all_ (fun w' => L0 .surface .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .all_ (fun w' => L0 .surface .everyNot w') .two
            = L0 .surface .everyNot .two from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- surfNone: vacuous-zero (qudProjectE .none_ at .two = L0 .one + L0 .two = 0 + 0)
    refine h_zero_le .surfNone ?_
    show (qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .none_ (fun w' => L0 .surface .everyNot w') .two
            = L0 .surface .everyNot .one + L0 .surface .everyNot .two from rfl,
        L0_apply_of_false (by decide), L0_apply_of_false (by decide), add_zero]
    exact ENNReal.zero_rpow_of_pos hα
  · exact (S1g_invHowMany_strict_one_two hα).le  -- invHowMany: strict, take .le
  · -- invAll: vacuous-zero (qudProjectE .all_ at .two = L0 .two = 0 for inverse .everyNot)
    refine h_zero_le .invAll ?_
    show (qudProjectE .all_ (fun w' => L0 .inverse .everyNot w') .two) ^ α = 0
    rw [show qudProjectE .all_ (fun w' => L0 .inverse .everyNot w') .two
            = L0 .inverse .everyNot .two from rfl,
        L0_apply_of_false (by decide)]
    exact ENNReal.zero_rpow_of_pos hα
  · -- invNone: equality
    -- (qudProjectE .none_ at .two = L0 .one + L0 .two = same at .one)
    refine h_eq_via .invNone fun u => ?_
    show (qudProjectE .none_ (fun w' => L0 .inverse u w') .two) ^ α =
         (qudProjectE .none_ (fun w' => L0 .inverse u w') .one) ^ α
    rfl

/-- Baseline L1 ordering: `L1(one | everyNot) > L1(two | everyNot)`.
Inverse scope makes `.one` true; neither scope makes `.two` true.

Same 2-lemma discharge as `baseline_L1_zero_gt_one`. -/
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


/-! ### Paper-faithful parametric priors

The §1-§7 above use a *uniform* `worldPrior` and *uniform* `latentPrior` —
a simplification not matching the paper. This section adds the paper-faithful
**parameterized** versions and the **S2 layer** (which §1-§7 omits entirely
despite the paper p.15 stating S2 is the layer that maps to truth-value
judgments).

Paper-faithful parameters (paper p.15-16):
- `b_suc ∈ (0, 1)` — per-horse success rate; `worldPrior = binomial(2, b_suc)`
- `p_all ∈ (0, 1)` — favored-QUD weight; uniform over the other two
- `p_inv ∈ (0, 1)` — favored-scope weight (inverse); 1 - p_inv on surface
- Default: `b_suc = 0.5`, `p_all = 1/3`, `p_inv = 0.5`

At `b_suc = 0.5`: binomial(2, 0.5) = (1/4, 1/2, 1/4) — NOT uniform (1/3, 1/3, 1/3).
The §1 `worldPrior := PMF.uniformOfFintype` is a paper-fidelity bug; §1-§7's
findings are thus at the SIMPLIFIED uniform world prior, not the paper's.

This section follows mathlib's pattern for parameterized PMF families: real-
valued parameters with explicit `0 < · < 1` hypotheses (cf. `PMF.binomial`'s
`unitInterval`-typed parameter). All construction goes through mathlib's
`PMF.normalize` with the Fintype-shape `tsum_ne_zero_iff` (witness form)
and `tsum_ne_top_of_fintype` discharges. -/

/-! #### World prior — binomial in `b_suc` (via mathlib `PMF.binomial`)

Uses mathlib's `PMF.binomial` (
discipline; see `project_pmf_check_mathlib_first.md`). The previous version
hand-rolled a 3-case `worldPriorENN` + `PMF.normalize` construction,
duplicating mathlib's `Mathlib.Probability.ProbabilityMassFunction.Binomial`. -/

/-- Identification of `JumpOutcome` with `Fin 3` (number of horses succeeding,
out of 2). Required to lift `PMF.binomial _ _ 2 : PMF (Fin 3)` to `PMF JumpOutcome`. -/
def JumpOutcome.equivFin3 : JumpOutcome ≃ Fin 3 where
  toFun
    | .zero => 0
    | .one => 1
    | .two => 2
  invFun
    | ⟨0, _⟩ => .zero
    | ⟨1, _⟩ => .one
    | ⟨2, _⟩ => .two
  left_inv := fun w => by cases w <;> rfl
  right_inv := fun ⟨n, h⟩ => by interval_cases n <;> rfl

/-- Binomial world prior, parameterized on per-horse success rate `b_suc : ℝ≥0`.
Paper-faithful (vs the §1 uniform simplification). Wraps mathlib's `PMF.binomial`
with the `JumpOutcome ≃ Fin 3` identification.

Allows `b_suc = 0` and `b_suc = 1` (degenerate Diracs at `.zero` / `.two`
respectively); paper's range is `[0.1, 0.9]` but no positivity-strict bound
needed for the construction itself. -/
noncomputable def worldPriorAt (b_suc : ℝ≥0) (h_le_one : b_suc ≤ 1) :
    PMF JumpOutcome :=
  (PMF.binomial b_suc h_le_one 2).map JumpOutcome.equivFin3.symm

/-! #### QUD prior — favored-QUD weight `p_all` -/

/-- Unnormalized QUD weights with `p_all` favoring the `all?` QUD. -/
noncomputable def qudPriorENN (p_all : ℝ) : QUD → ℝ≥0∞
  | .all_ => ENNReal.ofReal p_all
  | .howMany => ENNReal.ofReal ((1 - p_all) / 2)
  | .none_ => ENNReal.ofReal ((1 - p_all) / 2)

theorem qudPriorENN_finite (p_all : ℝ) (q : QUD) : qudPriorENN p_all q ≠ ⊤ := by
  cases q <;> exact ENNReal.ofReal_ne_top

theorem qudPriorENN_all_pos {p_all : ℝ} (h_lo : 0 < p_all) :
    qudPriorENN p_all .all_ ≠ 0 := by
  show ENNReal.ofReal p_all ≠ 0
  rw [ENNReal.ofReal_ne_zero_iff]; exact h_lo

/-- QUD prior, parameterized on favored-QUD weight `p_all`.
Only `0 < p_all` is needed for positivity; `p_all ≤ 1` doesn't appear in the
proof (the unfavored components use `(1 - p_all)/2` but their positivity
isn't required for this construction — only the witness `.all_` is). -/
noncomputable def qudPriorAt (p_all : ℝ) (h_lo : 0 < p_all) :
    PMF QUD :=
  PMF.normalize (qudPriorENN p_all)
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.all_, qudPriorENN_all_pos h_lo⟩)
    (ENNReal.tsum_ne_top_of_fintype (qudPriorENN_finite p_all))

/-! #### Scope prior — `p_inv` favors inverse, `1 - p_inv` favors surface -/

/-- Unnormalized scope weights. -/
noncomputable def scopePriorENN (p_inv : ℝ) : ScopeReading → ℝ≥0∞
  | .inverse => ENNReal.ofReal p_inv
  | .surface => ENNReal.ofReal (1 - p_inv)

theorem scopePriorENN_finite (p_inv : ℝ) (s : ScopeReading) :
    scopePriorENN p_inv s ≠ ⊤ := by
  cases s <;> exact ENNReal.ofReal_ne_top

theorem scopePriorENN_inverse_pos {p_inv : ℝ} (h_lo : 0 < p_inv) :
    scopePriorENN p_inv .inverse ≠ 0 := by
  show ENNReal.ofReal p_inv ≠ 0
  rw [ENNReal.ofReal_ne_zero_iff]; exact h_lo

/-- Scope prior, parameterized on inverse-scope weight `p_inv`.
Only `0 < p_inv` is needed for positivity (witness `.inverse`); `p_inv ≤ 1`
unused in this construction. -/
noncomputable def scopePriorAt (p_inv : ℝ) (h_lo : 0 < p_inv) :
    PMF ScopeReading :=
  PMF.normalize (scopePriorENN p_inv)
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.inverse, scopePriorENN_inverse_pos h_lo⟩)
    (ENNReal.tsum_ne_top_of_fintype (scopePriorENN_finite p_inv))

/-! #### Latent prior — independent product `scopePrior × qudPrior` -/

/-- Unnormalized latent weight as the per-component product. -/
noncomputable def latentPriorENN (p_inv p_all : ℝ) : Latent → ℝ≥0∞
  | .surfHowMany => scopePriorENN p_inv .surface * qudPriorENN p_all .howMany
  | .surfAll => scopePriorENN p_inv .surface * qudPriorENN p_all .all_
  | .surfNone => scopePriorENN p_inv .surface * qudPriorENN p_all .none_
  | .invHowMany => scopePriorENN p_inv .inverse * qudPriorENN p_all .howMany
  | .invAll => scopePriorENN p_inv .inverse * qudPriorENN p_all .all_
  | .invNone => scopePriorENN p_inv .inverse * qudPriorENN p_all .none_

theorem latentPriorENN_finite (p_inv p_all : ℝ) (lat : Latent) :
    latentPriorENN p_inv p_all lat ≠ ⊤ := by
  cases lat <;> exact ENNReal.mul_ne_top
    (scopePriorENN_finite _ _) (qudPriorENN_finite _ _)

theorem latentPriorENN_invAll_pos {p_inv p_all : ℝ}
    (h_inv : 0 < p_inv) (h_all : 0 < p_all) :
    latentPriorENN p_inv p_all .invAll ≠ 0 :=
  mul_ne_zero (scopePriorENN_inverse_pos h_inv) (qudPriorENN_all_pos h_all)

/-- Latent prior, parameterized on `(p_inv, p_all)` as the independent product
of `scopePriorAt p_inv × qudPriorAt p_all`. Only the per-component lower
bounds (`h_inv_lo`, `h_all_lo`) are needed (witness `.invAll`); upper bounds
unused. -/
noncomputable def latentPriorAt (p_inv p_all : ℝ)
    (h_inv_lo : 0 < p_inv) (h_all_lo : 0 < p_all) : PMF Latent :=
  PMF.normalize (latentPriorENN p_inv p_all)
    (ENNReal.summable.tsum_ne_zero_iff.mpr
      ⟨.invAll, latentPriorENN_invAll_pos h_inv_lo h_all_lo⟩)
    (ENNReal.tsum_ne_top_of_fintype (latentPriorENN_finite p_inv p_all))

/-! #### L1 — paper-faithful Bayesian inversion (parameterized prior)

This is the paper's L1 (marginalized over `(i, q)`) under the parameterized
priors. The §6 `L1` uses the §1 uniform `worldPrior`; this version uses
`worldPriorAt b_suc` and `latentPriorAt p_inv p_all`.

Note on naming: the paper's joint L1 is `PMF (Latent × JumpOutcome)`; this
file's L1 is the world marginal `PMF JumpOutcome` — the variable that S2
consumes. -/

/-- Paper-faithful pragmatic listener (world marginal of joint L1). -/
noncomputable def L1At {α : ℝ} (hα : 0 < α)
    (worldPrior : PMF JumpOutcome) (latentPrior : PMF Latent) (u : Utt)
    (hMarg : PMF.marginal (marginalSpeaker hα latentPrior) worldPrior u ≠ 0) :
    PMF JumpOutcome :=
  PMF.posterior (marginalSpeaker hα latentPrior) worldPrior u hMarg

/-! #### S2 — production speaker for truth-value judgment (paper p.15)

`P_S2(u | w) ∝ exp(log Σ_{i,q} P_L1(w, i, q | u))`. Since `Σ_{i,q} P_L1 = L1_marginal`
(the file's `L1At`), this is `S2(u | w) ∝ L1At u w` — re-normalize the L1 values
across u for each fixed w.

Cover witness for the normalization: `.null` is universally applicable, so
`L1At _ .null _ w ≠ 0` for every `w` with positive `worldPrior` mass. We
encode this via the `dite` pattern: `S2Score = L1At u h w` if h holds, else 0.

Implementation note: this S2 is paper-specific (intersective truth-value-judgment
production), not a generic RSA layer — keep in study file rather than
promoting to `Pragmatics/RSA/`. -/

/-- The unnormalized S2 score at `(w, u)`: the L1 posterior at `w` given `u`,
or 0 if the L1 marginal at `u` is degenerate. -/
noncomputable def S2Score {α : ℝ} (hα : 0 < α)
    (worldPrior : PMF JumpOutcome) (latentPrior : PMF Latent)
    (w : JumpOutcome) (u : Utt) : ℝ≥0∞ :=
  if h : PMF.marginal (marginalSpeaker hα latentPrior) worldPrior u ≠ 0
  then L1At hα worldPrior latentPrior u h w
  else 0

theorem S2Score_finite {α : ℝ} (hα : 0 < α)
    (worldPrior : PMF JumpOutcome) (latentPrior : PMF Latent)
    (w : JumpOutcome) (u : Utt) :
    S2Score hα worldPrior latentPrior w u ≠ ⊤ := by
  unfold S2Score
  split <;> [exact PMF.apply_ne_top _ _; exact ENNReal.zero_ne_top]

/-! Production speaker S2: for each world `w`, `S2 w` is a `PMF Utt` distributed
proportional to `L1At u w` over `u`.

The cover witness for `S2`'s normalization comes from `u = .null` at any
world `w` with positive prior mass: `null` is universally true, so
`marginalSpeaker hα latentPrior w .null > 0` (via `S1g_null_ne_zero`),
giving `marginal κ μ .null > 0` and thus `L1At hα _ _ .null h w > 0`.

For brevity (and since we don't yet have the full positivity machinery for
`L1At` at general parameter values), `S2` is stated with explicit positivity
hypotheses rather than self-discharging. -/

/-- Production speaker for truth-value judgment (paper p.15).

The positivity hypothesis `h_score_pos` is per-world; in practice it is
discharged via the `.null`-utterance cover witness (always applies, so the
L1 marginal at `.null` is positive at every world with positive prior). -/
noncomputable def S2 {α : ℝ} (hα : 0 < α)
    (worldPrior : PMF JumpOutcome) (latentPrior : PMF Latent)
    (w : JumpOutcome)
    (h_score_pos : ∑' u, S2Score hα worldPrior latentPrior w u ≠ 0) :
    PMF Utt :=
  PMF.normalize (S2Score hα worldPrior latentPrior w) h_score_pos
    (ENNReal.tsum_ne_top_of_fintype (S2Score_finite hα worldPrior latentPrior w))

/-! ### structural scope-collapse under QUD = all? (paper §3.2 last paragraph; restated §5.1)

The paper's central explanatory move (p. 17, 29-30): when QUD = `all?` is
favored, BOTH scope readings of "every horse didn't jump" answer the QUD
identically with "no, not all succeeded". This collapses the scope distinction
at the speaker layer — the structural mechanism behind pragmatic
dominance (the scope prior becoming nearly irrelevant).

Formalized at three layers: `qudProjectE .all_` is scope-independent at
every utterance and world; hence `S1g hα .surfAll = S1g hα .invAll` as
PMFs; hence the surface/inverse all?-latents contribute interchangeably
to the marginal speaker. -/

/-- `extension X .null = Finset.univ` for both scopes — `null` is true everywhere.
Structurally generic: constructs cover witnesses for universal-extension
utterances. -/
theorem extension_null_eq_univ (s : ScopeReading) :
    extension s .null = Finset.univ := by
  ext w; simp [extension, RSA.mem_extensionOf]; cases s <;> cases w <;> rfl

/-- Under QUD = all?, the projected L0 mass is the same for surface
and inverse scope readings of any utterance, at every world.

Two cases by utterance:
- `u = .null`: L0 distributions are pointwise equal (both uniform on Finset.univ
  since extension of null = univ for both scopes).
- `u = .everyNot`: L0 distributions DIFFER pointwise (surface puts all mass on
  `.zero`; inverse splits between `.zero` and `.one`). But QUD `.all_` partitions
  worlds as {.zero, .one} vs {.two}, summing surface's (1, 0) → 1 and inverse's
  (1/2, 1/2) → 1 in the first cell. Equal projected behavior despite different
  raw L0. -/
theorem qudProjectE_all_scope_invariant (u : Utt) (w : JumpOutcome) :
    qudProjectE .all_ (fun w' => L0 .surface u w') w =
      qudProjectE .all_ (fun w' => L0 .inverse u w') w := by
  cases u
  case null =>
    -- L0 .surface .null = L0 .inverse .null pointwise (both uniform on univ).
    have h_eq : ∀ w', L0 .surface .null w' = L0 .inverse .null w' := fun w' => by
      rw [L0_apply_of_true (by cases w' <;> rfl), L0_apply_of_true (by cases w' <;> rfl),
          extension_null_eq_univ .surface, extension_null_eq_univ .inverse]
    cases w <;> simp only [qudProjectE, h_eq]
  case everyNot =>
    -- Surface: L0 .zero = 1, L0 .one = L0 .two = 0 (extension = {.zero}, card 1).
    -- Inverse: L0 .zero = L0 .one = 1/2, L0 .two = 0 (extension = {.zero, .one}, card 2).
    -- QUD .all_ at .zero/.one sums L0 .zero + L0 .one;
    -- QUD .all_ at .two = L0 .two.
    have h_surf_zero : L0 .surface .everyNot .zero = 1 := by
      rw [L0_apply_of_true (by decide : uttMeaning .surface .everyNot .zero = true),
          show extension .surface .everyNot = {JumpOutcome.zero} from rfl,
          Finset.card_singleton, Nat.cast_one, inv_one]
    have h_surf_one : L0 .surface .everyNot .one = 0 :=
      L0_apply_of_false (by decide : uttMeaning .surface .everyNot .one ≠ true)
    have h_surf_two : L0 .surface .everyNot .two = 0 :=
      L0_apply_of_false (by decide : uttMeaning .surface .everyNot .two ≠ true)
    have h_inv_zero : L0 .inverse .everyNot .zero = (2 : ℝ≥0∞)⁻¹ := by
      rw [L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .zero = true),
          show extension .inverse .everyNot = {JumpOutcome.zero, JumpOutcome.one} from rfl]
      rfl
    have h_inv_one : L0 .inverse .everyNot .one = (2 : ℝ≥0∞)⁻¹ := by
      rw [L0_apply_of_true (by decide : uttMeaning .inverse .everyNot .one = true),
          show extension .inverse .everyNot = {JumpOutcome.zero, JumpOutcome.one} from rfl]
      rfl
    have h_inv_two : L0 .inverse .everyNot .two = 0 :=
      L0_apply_of_false (by decide : uttMeaning .inverse .everyNot .two ≠ true)
    have h_zero_one_eq :
        L0 .surface .everyNot .zero + L0 .surface .everyNot .one =
          L0 .inverse .everyNot .zero + L0 .inverse .everyNot .one := by
      rw [h_surf_zero, h_surf_one, h_inv_zero, h_inv_one, add_zero,
          ENNReal.inv_two_add_inv_two]
    cases w <;> simp only [qudProjectE]
    · exact h_zero_one_eq
    · exact h_zero_one_eq
    · rw [h_surf_two, h_inv_two]

/-- Under QUD = `all?`, the speaker `S1g` is identical for surface
and inverse scope readings (at every world).

Direct corollary of the L0 invariance lifted through `PMF.normalize`: the score functions
are pointwise equal (since `s1Weight` only depends on `lat.qud` and `lat.scope`
through `qudProjectE` which collapses the scope distinction), so the
normalized PMFs are equal. -/
theorem S1g_all_qud_scope_invariant {α : ℝ} (hα : 0 < α) (w : JumpOutcome) :
    S1g hα .surfAll w = S1g hα .invAll w := by
  -- Both are PMF.normalize of s1Weight; show s1Weight is pointwise equal across u.
  have h_score_eq : ∀ u, s1Weight α .surfAll w u = s1Weight α .invAll w u := fun u => by
    show (qudProjectE .all_ (fun w' => L0 .surface u w') w) ^ α =
         (qudProjectE .all_ (fun w' => L0 .inverse u w') w) ^ α
    rw [qudProjectE_all_scope_invariant]
  ext u
  show PMF.normalize (s1Weight α .surfAll w) _ _ u =
       PMF.normalize (s1Weight α .invAll w) _ _ u
  exact PMF.normalize_eq_of_apply_eq_and_sum_eq _ _ _ _ _ _ _
    (h_score_eq u) (tsum_congr h_score_eq)

/-! ### Scope-prior irrelevance under QUD = all?

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

/-! ### The general-α QUD ordering (open)

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

/-! ### Two-Not RSA Model (§4) -/

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
    uttMeaning .exact .inverse .twoNot .w4 = true := by decide

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
    uttMeaning .atLeast .inverse .twoNot .w4 = false := by decide

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

/-- Restrictor: all entities are horses (trivial for this model). -/
def horse4_sem : Denot Horse4 Unit (.e ⇒ .t) := fun _ => True

/-- Jump predicate as Montague semantic value. -/
def jumpIn4_sem (w : JumpOutcome4) : Denot Horse4 Unit (.e ⇒ .t) :=
  fun h => jumpIn4 w h = true

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

-- QUD Projection

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

-- Prior configuration (ℚ; §4.2, Figure 7)

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
theorem D6_L0_exact_gt_atLeast_at_w2 :
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
theorem D6_L0_exact_zero_atLeast_pos_at_w0 :
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

/-- Every-not baseline endorsement at w=1 is below 1/2: the low end of the
1-of-2 vs 2-of-4 asymmetry, with the same b_suc = 0.1 world prior as the
two-not baseline. -/
theorem everyNot_baseline_endorsement_low :
    EveryNot.s2 EveryNot.lowWP EveryNot.uniSP EveryNot.uniQP .one .everyNot <
      (((1/2 : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
  PMF.ofScores_lt_ratCast _ (by decide +kernel)



end ScontrasPearl2021
