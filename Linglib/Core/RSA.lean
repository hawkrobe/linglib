/-
# Linglib.Core.RSA

Core RSA (Rational Speech Acts) infrastructure.

## Architecture

RSA is parameterized by:
1. **Score type** (ℚ for exact proofs, Float for empirical work)
2. **RSAScenario** structure (unified interface replacing FiniteSemanticBackend)

### Key Types

- `RSAScore`: Typeclass for score arithmetic (ℚ, Float)
- `RSAScenario Score`: Unified interface for RSA computation
- `ParametricRSAScenario Score`: For lifted-variable RSA (scope ambiguity)

### RSA Model

RSA models communication as recursive reasoning between speakers and listeners:
- L0: Literal interpretation (semantic denotation)
- S1: Pragmatic speaker (chooses utterances to maximize informativity)
- L1: Pragmatic listener (reasons about what speaker meant)

Reference: Frank & Goodman (2012), Goodman & Frank (2016)
-/

import Mathlib.Data.Rat.Defs

-- ============================================================================
-- RSAScore Typeclass
-- ============================================================================

/--
What RSA computation needs from a score type.

Provides basic arithmetic operations for probability-like quantities.
Implemented by `ℚ` (exact rational arithmetic) and `Float`.
-/
class RSAScore (α : Type) where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α
  /-- Division, returning None if denominator is zero -/
  div : α → α → Option α
  /-- Less-than comparison -/
  lt : α → α → Bool

namespace RSAScore

variable {α : Type} [RSAScore α]

/-- Greater-than in terms of less-than -/
def gt (x y : α) : Bool := lt y x

/-- Greater-than-or-equal -/
def ge (x y : α) : Bool := !lt x y

/-- Less-than-or-equal -/
def le (x y : α) : Bool := !lt y x

end RSAScore

-- ============================================================================
-- RSAScore Instances
-- ============================================================================

/-- RSAScore instance for ℚ (exact rational arithmetic) -/
instance : RSAScore ℚ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  div a b := if b ≠ 0 then some (a / b) else none
  lt a b := decide (a < b)

instance : RSAScore Float where
  zero := 0.0
  one := 1.0
  add := (· + ·)
  mul := (· * ·)
  div a b := if b > 0.0 then some (a / b) else none
  lt := (· < ·)

-- ============================================================================
-- RSAScenario: Unified Interface
-- ============================================================================

/--
RSA scenario: the unified interface for all RSA computation.

Replaces the old `FiniteSemanticBackend`. Parametric over score type.

## Fields

- `φ`: Agreement function (meaning). For Boolean semantics, use `RSAScenario.ofBool`.
- `prior`: Prior distribution over worlds (default: uniform)
- `α`: Rationality parameter (default: 1)

## Usage

```lean
def myScenario : ExactRSAScenario :=
  RSAScenario.ofBool [.some_, .all_] [.w0, .w1, .w2] mySatisfies
```
-/
structure RSAScenario (Score : Type) [RSAScore Score] where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of possible worlds -/
  World : Type
  /-- Agreement function: how well does utterance describe world? -/
  φ : Utterance → World → Score
  /-- Enumeration of all utterances -/
  utterances : List Utterance
  /-- Enumeration of all worlds -/
  worlds : List World
  /-- Prior distribution over worlds (default: uniform) -/
  prior : World → Score := fun _ => RSAScore.one
  /-- Rationality parameter (default: 1) -/
  α : Score := RSAScore.one
  /-- BEq instance for utterances -/
  [uttBEq : BEq Utterance]
  /-- BEq instance for worlds -/
  [worldBEq : BEq World]

attribute [instance] RSAScenario.uttBEq RSAScenario.worldBEq

/-- RSAScenario with exact rational arithmetic (for proofs) -/
abbrev ExactRSAScenario := RSAScenario ℚ

/-- RSAScenario with floating point (for empirical/LLM work) -/
abbrev SoftRSAScenario := RSAScenario Float

-- ============================================================================
-- Boolean Semantics Helper
-- ============================================================================

/-- Convert Bool to any RSAScore (for building scenarios from Boolean meanings) -/
def boolToScore {Score : Type} [RSAScore Score] (b : Bool) : Score :=
  if b then RSAScore.one else RSAScore.zero

/--
Build RSAScenario from a Boolean satisfaction relation.

This is the primary way to create scenarios from classical semantics.
The φ function becomes an indicator function: 1 if true, 0 if false.

## Example

```lean
def scalarScenario : ExactRSAScenario :=
  RSAScenario.ofBool [.some_, .all_] [.w0, .w1, .w2, .w3] scalarSatisfies
```
-/
def RSAScenario.ofBool {Utterance World : Type} [BEq Utterance] [BEq World]
    (utterances : List Utterance) (worlds : List World)
    (satisfies : World → Utterance → Bool) : ExactRSAScenario where
  Utterance := Utterance
  World := World
  φ u w := boolToScore (satisfies w u)
  utterances := utterances
  worlds := worlds

/-- Property: a scenario has Boolean semantics (φ only returns 0 or 1) -/
def RSAScenario.isBoolean {Score : Type} [RSAScore Score] (S : RSAScenario Score) : Prop :=
  ∀ u w, S.φ u w = RSAScore.zero ∨ S.φ u w = RSAScore.one

-- ============================================================================
-- RSA Computations
-- ============================================================================

namespace RSA

variable {Score : Type} [RSAScore Score]

/-- Sum a list of scores -/
def sumScores (scores : List Score) : Score :=
  scores.foldl RSAScore.add RSAScore.zero

/-- Look up score in distribution -/
def getScore {α : Type} [BEq α] (dist : List (α × Score)) (x : α) : Score :=
  match dist.find? (·.1 == x) with
  | some (_, s) => s
  | none => RSAScore.zero

/-- Normalize a distribution (divide each score by total) -/
def normalize {α : Type} (dist : List (α × Score)) : List (α × Score) :=
  let total := sumScores (dist.map (·.2))
  dist.map fun (x, s) =>
    (x, (RSAScore.div s total).getD RSAScore.zero)

-- ============================================================================
-- L0: Literal Listener
-- ============================================================================

/--
L0: Literal listener distribution.

P(w | u) ∝ P(w) · φ(u, w)

The literal listener updates prior beliefs by the meaning function,
uniformly distributing probability over worlds where utterance is true
(for Boolean semantics) or proportionally to φ (for graded semantics).
-/
def L0 {Score : Type} [RSAScore Score] (S : RSAScenario Score) (u : S.Utterance) : List (S.World × Score) :=
  let scores := S.worlds.map fun w => (w, RSAScore.mul (S.prior w) (S.φ u w))
  normalize scores

-- ============================================================================
-- S1: Pragmatic Speaker
-- ============================================================================

/--
S1: Pragmatic speaker distribution.

P(u | w) ∝ L0(w | u)^α

The speaker chooses utterances proportional to how well L0 recovers
the intended world. For α=1 (default), this is just L0(w|u) normalized.

More informative (less ambiguous) utterances are preferred.
-/
def S1 {Score : Type} [RSAScore Score] (S : RSAScenario Score) (w : S.World) : List (S.Utterance × Score) :=
  let scores := S.utterances.map fun u => (u, getScore (L0 S u) w)
  normalize scores

-- ============================================================================
-- L1: Pragmatic Listener
-- ============================================================================

/--
L1: Pragmatic listener distribution.

P(w | u) ∝ P(w) · S1(u | w)

The pragmatic listener reasons about what world would make a rational
speaker choose this utterance.
-/
def L1 {Score : Type} [RSAScore Score] (S : RSAScenario Score) (u : S.Utterance) : List (S.World × Score) :=
  let scores := S.worlds.map fun w => (w, RSAScore.mul (S.prior w) (getScore (S1 S w) u))
  normalize scores

-- ============================================================================
-- Convenience Probability Accessors
-- ============================================================================

/-- Get L0 probability for a specific world -/
def L0_prob {Score : Type} [RSAScore Score] (S : RSAScenario Score) (u : S.Utterance) (w : S.World) : Score :=
  getScore (L0 S u) w

/-- Get S1 probability for a specific utterance -/
def S1_prob {Score : Type} [RSAScore Score] (S : RSAScenario Score) (w : S.World) (u : S.Utterance) : Score :=
  getScore (S1 S w) u

/-- Get L1 probability for a specific world -/
def L1_prob {Score : Type} [RSAScore Score] (S : RSAScenario Score) (u : S.Utterance) (w : S.World) : Score :=
  getScore (L1 S u) w

-- ============================================================================
-- Legacy Helpers (for backward compatibility during migration)
-- ============================================================================

/-- Count worlds compatible with an utterance (for Boolean scenarios) -/
def compatibleCount (S : RSAScenario ℚ) (u : S.Utterance) : Nat :=
  (S.worlds.filter fun w => S.φ u w > 0).length

/-- Informativity of an utterance = 1 / (compatible worlds) -/
def informativity (S : RSAScenario ℚ) (u : S.Utterance) : ℚ :=
  let n := compatibleCount S u
  if n > 0 then 1 / n else 0

end RSA

-- ============================================================================
-- ParametricRSAScenario (for Lifted-Variable RSA)
-- ============================================================================

namespace ParametricRSA

/--
RSA scenario with an interpretation parameter.

Supports "lifted-variable" RSA models where:
- **Interp** represents different ways to interpret an utterance
  (e.g., scope readings: surface vs inverse)
- **φ** is parameterized by interpretation

## Example: Scope Ambiguity

"Every horse didn't jump"
- Interp = {surface, inverse}
- φ surface u w = ∀x.¬jump(x) in w
- φ inverse u w = ¬∀x.jump(x) in w

Reference: Scontras & Pearl (2021)
-/
structure ParametricRSAScenario (Score : Type) [RSAScore Score] where
  Utterance : Type
  World : Type
  Interp : Type
  /-- Parameterized agreement function -/
  φ : Interp → Utterance → World → Score
  utterances : List Utterance
  worlds : List World
  interps : List Interp
  /-- Prior over worlds -/
  prior : World → Score := fun _ => RSAScore.one
  /-- Prior over interpretations -/
  interpPrior : Interp → Score := fun _ => RSAScore.one
  /-- Rationality parameter -/
  α : Score := RSAScore.one
  [uttBEq : BEq Utterance]
  [worldBEq : BEq World]
  [interpBEq : BEq Interp]

attribute [instance] ParametricRSAScenario.uttBEq ParametricRSAScenario.worldBEq ParametricRSAScenario.interpBEq

/-- Exact parametric scenario -/
abbrev ExactParametricRSAScenario := ParametricRSAScenario ℚ

variable {Score : Type} [RSAScore Score]

-- ============================================================================
-- Parametric L0, S1, L1
-- ============================================================================

/--
L0 given a fixed interpretation.

P(w | u, i) ∝ P(w) · φ(i, u, w)
-/
def L0 (S : ParametricRSAScenario Score) (i : S.Interp) (u : S.Utterance) : List (S.World × Score) :=
  let scores := S.worlds.map fun w => (w, RSAScore.mul (S.prior w) (S.φ i u w))
  RSA.normalize scores

/--
S1 given a fixed interpretation.

P(u | w, i) ∝ L0(w | u, i)
-/
def S1 (S : ParametricRSAScenario Score) (i : S.Interp) (w : S.World) : List (S.Utterance × Score) :=
  let scores := S.utterances.map fun u => (u, RSA.getScore (L0 S i u) w)
  RSA.normalize scores

/--
L1 joint distribution over (World × Interp).

P(w, i | u) ∝ P(w) · P(i) · S1(u | w, i)

Returns unnormalized scores over all (world, interpretation) pairs.
-/
def L1_joint (S : ParametricRSAScenario Score) (u : S.Utterance) : List ((S.World × S.Interp) × Score) :=
  let pairs := S.worlds.flatMap fun w => S.interps.map fun i => (w, i)
  let scores := pairs.map fun (w, i) =>
    let priorScore := RSAScore.mul (S.prior w) (S.interpPrior i)
    let s1Score := RSA.getScore (S1 S i w) u
    ((w, i), RSAScore.mul priorScore s1Score)
  RSA.normalize scores

/--
L1 marginal over worlds.

P(w | u) = Σ_i P(w, i | u)
-/
def L1_world (S : ParametricRSAScenario Score) (u : S.Utterance) : List (S.World × Score) :=
  let joint := L1_joint S u
  S.worlds.map fun w =>
    let wScores := joint.filter (·.1.1 == w) |>.map (·.2)
    (w, RSA.sumScores wScores)

/--
L1 marginal over interpretations.

P(i | u) = Σ_w P(w, i | u)
-/
def L1_interp (S : ParametricRSAScenario Score) (u : S.Utterance) : List (S.Interp × Score) :=
  let joint := L1_joint S u
  S.interps.map fun i =>
    let iScores := joint.filter (·.1.2 == i) |>.map (·.2)
    (i, RSA.sumScores iScores)

-- ============================================================================
-- Boolean Semantics Helper
-- ============================================================================

/--
Build ParametricRSAScenario from a Boolean satisfaction relation.
-/
def ParametricRSAScenario.ofBool {Utterance World Interp : Type}
    [BEq Utterance] [BEq World] [BEq Interp]
    (utterances : List Utterance) (worlds : List World) (interps : List Interp)
    (satisfies : Interp → World → Utterance → Bool) : ExactParametricRSAScenario where
  Utterance := Utterance
  World := World
  Interp := Interp
  φ i u w := boolToScore (satisfies i w u)
  utterances := utterances
  worlds := worlds
  interps := interps

-- ============================================================================
-- Legacy Helpers
-- ============================================================================

/-- Count worlds compatible with utterance under interpretation -/
def compatibleCount (S : ParametricRSAScenario ℚ)
    (i : S.Interp) (u : S.Utterance) : Nat :=
  (S.worlds.filter fun w => S.φ i u w > 0).length

/-- Informativity under interpretation -/
def informativity (S : ParametricRSAScenario ℚ)
    (i : S.Interp) (u : S.Utterance) : ℚ :=
  let n := compatibleCount S i u
  if n > 0 then 1 / n else 0

end ParametricRSA

-- ============================================================================
-- Generic Theorems (examples, can be instantiated for specific scenarios)
-- ============================================================================

namespace RSA

/--
L0 assigns zero probability to worlds where utterance has zero φ.
-/
theorem L0_zero_when_false {Score : Type} [RSAScore Score]
    (S : RSAScenario Score) (u : S.Utterance) (w : S.World)
    (hfalse : S.φ u w = RSAScore.zero) :
    ∀ p, (w, p) ∈ (L0 S u) → p = RSAScore.zero := by
  intro p hmem
  sorry -- Technical proof about normalization

/--
S1 assigns zero probability to utterances with zero φ at the world.
-/
theorem S1_zero_when_false {Score : Type} [RSAScore Score]
    (S : RSAScenario Score) (w : S.World) (u : S.Utterance)
    (hfalse : S.φ u w = RSAScore.zero) :
    S1_prob S w u = RSAScore.zero := by
  sorry -- Technical proof

end RSA
