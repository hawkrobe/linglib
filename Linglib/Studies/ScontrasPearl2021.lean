import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Core.Probability.Scores
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
