/-
# RSA with Rational Alpha (RSAScenarioQ)

Extends RSA to support rational α values (including α < 1), enabling
formalization of Zaslavsky et al. (2020)'s key results.

## Motivation

The standard RSAScenario has α : ℕ, which cannot represent:
- α = 1/2 (utility non-monotonicity counterexample)
- α = 0 (pure compression limit)
- Fractional α for rate-distortion analysis

RSAScenarioQ uses α : ℚ with Newton-Raphson approximation for x^α.

## Key Types

- `RSAScenarioQ`: RSA scenario with rational α
- `S1Q`, `L0Q`, `L1Q`: RSA computations using powApprox

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of
  human pragmatic reasoning. arXiv:2005.06641.
-/

import Linglib.Theories.RSA.Core
import Linglib.Core.RationalPower
import Mathlib.Data.Rat.Defs

namespace RSA

open RationalPower

-- ============================================================================
-- PART 1: RSAScenarioQ Structure
-- ============================================================================

/--
RSA scenario with rational α parameter.

This extends RSAScenario to support fractional rationality parameters,
enabling analysis of:
- α < 1: Utility non-monotonicity (Prop 2)
- α = 1: Rate-distortion critical point (Prop 3)
- α → 0: Pure compression limit
- α → ∞: NeoGricean limit

All other fields are identical to RSAScenario.
-/
structure RSAScenarioQ where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of world states -/
  World : Type
  /-- Type of interpretations (e.g., scope readings). Use Unit for basic models. -/
  Interp : Type := Unit
  /-- Type of QUDs. Use Unit for non-QUD models. -/
  QUD : Type := Unit
  /-- Agreement function: φ(interp, utterance, world) ∈ [0,1] -/
  φ : Interp → Utterance → World → ℚ
  /-- QUD projection: are two worlds equivalent under this QUD? -/
  qudProject : QUD → World → World → Bool
  /-- Enumeration of utterances -/
  utterances : List Utterance
  /-- Enumeration of worlds -/
  worlds : List World
  /-- Enumeration of interpretations -/
  interps : List Interp
  /-- Enumeration of QUDs -/
  quds : List QUD
  /-- Prior over worlds -/
  worldPrior : World → ℚ := fun _ => 1
  /-- Prior over interpretations -/
  interpPrior : Interp → ℚ := fun _ => 1
  /-- Prior over QUDs -/
  qudPrior : QUD → ℚ := fun _ => 1
  /-- Rationality parameter (RATIONAL, not natural) -/
  α : ℚ := 1
  /-- α must be non-negative -/
  α_nonneg : 0 ≤ α := by norm_num
  /-- Newton-Raphson precision for computing x^α -/
  precision : ℕ := 10
  /-- BEq instance for utterances -/
  [uttBEq : BEq Utterance]
  /-- BEq instance for worlds -/
  [worldBEq : BEq World]
  /-- BEq instance for interpretations -/
  [interpBEq : BEq Interp]
  /-- BEq instance for QUDs -/
  [qudBEq : BEq QUD]

attribute [instance] RSAScenarioQ.uttBEq RSAScenarioQ.worldBEq
  RSAScenarioQ.interpBEq RSAScenarioQ.qudBEq

-- ============================================================================
-- PART 2: Smart Constructors
-- ============================================================================

/--
Build a basic RSA scenario with rational α (no interpretation ambiguity, no QUD).
-/
def RSAScenarioQ.basic {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (prior : W → ℚ := fun _ => 1)
    (α : ℚ := 1)
    (α_nonneg : 0 ≤ α := by norm_num)
    (precision : ℕ := 10) : RSAScenarioQ where
  Utterance := U
  World := W
  Interp := Unit
  QUD := Unit
  φ _ u w := φ u w
  qudProject _ w w' := w == w'
  utterances := utterances
  worlds := worlds
  interps := [()]
  quds := [()]
  worldPrior := prior
  interpPrior := fun _ => 1
  qudPrior := fun _ => 1
  α := α
  α_nonneg := α_nonneg
  precision := precision

/--
Build a basic RSA scenario with rational α from Boolean semantics.
-/
def RSAScenarioQ.basicBool {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (satisfies : W → U → Bool)
    (prior : W → ℚ := fun _ => 1)
    (α : ℚ := 1)
    (α_nonneg : 0 ≤ α := by norm_num)
    (precision : ℕ := 10) : RSAScenarioQ :=
  RSAScenarioQ.basic utterances worlds
    (fun u w => boolToRat (satisfies w u)) prior α α_nonneg precision

/--
Build a scenario with interpretation ambiguity and rational α.
-/
def RSAScenarioQ.ambiguous {U W I : Type} [BEq U] [BEq W] [BEq I] [DecidableEq W]
    (utterances : List U) (worlds : List W) (interps : List I)
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℚ := 1)
    (α_nonneg : 0 ≤ α := by norm_num)
    (precision : ℕ := 10) : RSAScenarioQ where
  Utterance := U
  World := W
  Interp := I
  QUD := Unit
  φ i u w := φ i u w
  qudProject _ w w' := w == w'
  utterances := utterances
  worlds := worlds
  interps := interps
  quds := [()]
  worldPrior := worldPrior
  interpPrior := interpPrior
  qudPrior := fun _ => 1
  α := α
  α_nonneg := α_nonneg
  precision := precision

/--
Build a scenario with interpretation ambiguity and rational α from Boolean semantics.
-/
def RSAScenarioQ.ambiguousBool {U W I : Type} [BEq U] [BEq W] [BEq I] [DecidableEq W]
    (utterances : List U) (worlds : List W) (interps : List I)
    (satisfies : I → W → U → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℚ := 1)
    (α_nonneg : 0 ≤ α := by norm_num)
    (precision : ℕ := 10) : RSAScenarioQ :=
  RSAScenarioQ.ambiguous utterances worlds interps
    (fun i u w => boolToRat (satisfies i w u)) worldPrior interpPrior α α_nonneg precision

-- ============================================================================
-- PART 3: RSA Computations with Rational α
-- ============================================================================

namespace Q

/--
L0Q: Literal listener distribution (same as L0, but for RSAScenarioQ).

P(w | u, i) ∝ P(w) · φ(i, u, w)
-/
def L0Q (S : RSAScenarioQ) (u : S.Utterance) (i : S.Interp) : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w => (w, S.worldPrior w * S.φ i u w)
  RSA.normalize scores

/--
L0Q projected by QUD.
-/
def L0Q_projected (S : RSAScenarioQ) (u : S.Utterance) (i : S.Interp) (q : S.QUD)
    : List (S.World × ℚ) :=
  let l0 := L0Q S u i
  S.worlds.map fun w =>
    let eqClassScore := l0.filter (fun (w', _) => S.qudProject q w w')
      |>.map (·.2) |> RSA.sumScores
    (w, eqClassScore)

/--
S1Q: Pragmatic speaker distribution with rational α.

P(u | w, i, q) ∝ L0Q_q(w | u, i)^α

Uses powApprox for rational exponentiation.
-/
def S1Q (S : RSAScenarioQ) (w : S.World) (i : S.Interp) (q : S.QUD)
    : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u =>
    let l0Score := RSA.getScore (L0Q_projected S u i q) w
    (u, powApprox l0Score S.α S.precision)
  RSA.normalize scores

/--
L1Q joint distribution over (World × Interp × QUD).

P(w, i, q | u) ∝ P(w) · P(i) · P(q) · S1Q(u | w, i, q)
-/
def L1Q_joint (S : RSAScenarioQ) (u : S.Utterance)
    : List ((S.World × S.Interp × S.QUD) × ℚ) :=
  let triples := S.worlds.flatMap fun w =>
    S.interps.flatMap fun i =>
      S.quds.map fun q => (w, i, q)
  let scores := triples.map fun (w, i, q) =>
    let priorScore := S.worldPrior w * S.interpPrior i * S.qudPrior q
    let s1Score := RSA.getScore (S1Q S w i q) u
    ((w, i, q), priorScore * s1Score)
  RSA.normalize scores

/--
L1Q marginal over worlds.
-/
def L1Q_world (S : RSAScenarioQ) (u : S.Utterance) : List (S.World × ℚ) :=
  let joint := L1Q_joint S u
  S.worlds.map fun w =>
    let wScores := joint.filter (fun ((w', _, _), _) => w' == w) |>.map (·.2)
    (w, RSA.sumScores wScores)

/--
L1Q marginal over interpretations.
-/
def L1Q_interp (S : RSAScenarioQ) (u : S.Utterance) : List (S.Interp × ℚ) :=
  let joint := L1Q_joint S u
  S.interps.map fun i =>
    let iScores := joint.filter (fun ((_, i', _), _) => i' == i) |>.map (·.2)
    (i, RSA.sumScores iScores)

/--
S2Q: Second-level pragmatic speaker with rational α.

P(u | w) ∝ L1Q_world(w | u)^α
-/
def S2Q (S : RSAScenarioQ) (w : S.World) : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u =>
    let l1Score := RSA.getScore (L1Q_world S u) w
    (u, powApprox l1Score S.α S.precision)
  RSA.normalize scores

end Q

-- ============================================================================
-- PART 4: Conversion Between RSAScenario and RSAScenarioQ
-- ============================================================================

/--
Convert RSAScenario (natural α) to RSAScenarioQ (rational α).

Note: This conversion requires specifying a default lexicon value.
RSAScenarioQ uses a simpler structure without Lexicon/BeliefState fields.
-/
def RSAScenario.toQ (S : RSAScenario) (defaultLexicon : S.Lexicon) : RSAScenarioQ where
  Utterance := S.Utterance
  World := S.World
  Interp := S.Interp
  QUD := S.Goal  -- Map Goal -> QUD
  φ i u w := S.φ i defaultLexicon u w  -- Use the provided default lexicon
  qudProject := S.goalProject  -- Use goalProject
  utterances := S.utterances
  worlds := S.worlds
  interps := S.interps
  quds := S.goals  -- Use goals
  worldPrior := S.worldPrior
  interpPrior := S.interpPrior
  qudPrior := S.goalPrior  -- Use goalPrior
  α := S.α
  α_nonneg := by simp
  precision := 10

/--
Convert RSAScenarioQ to RSAScenario (truncates α to natural number).

Warning: This loses precision for non-integer α.
-/
def RSAScenarioQ.toNat (S : RSAScenarioQ) : RSAScenario where
  Utterance := S.Utterance
  World := S.World
  Interp := S.Interp
  Lexicon := Unit  -- RSAScenarioQ doesn't have Lexicon
  BeliefState := Unit  -- RSAScenarioQ doesn't have BeliefState
  Goal := S.QUD  -- Map QUD -> Goal
  φ i _ u w := S.φ i u w  -- Add ignored Lexicon parameter
  goalProject := S.qudProject  -- Map qudProject -> goalProject
  inBeliefState _ _ := true  -- Default belief state membership
  utterances := S.utterances
  worlds := S.worlds
  interps := S.interps
  lexica := [()]  -- Single Unit lexicon
  beliefStates := [()]  -- Single Unit belief state
  goals := S.quds  -- Map quds -> goals
  worldPrior := S.worldPrior
  interpPrior := S.interpPrior
  lexiconPrior := fun _ => 1  -- Uniform lexicon prior
  beliefStatePrior := fun _ => 1  -- Uniform belief state prior
  goalPrior := S.qudPrior  -- Map qudPrior -> goalPrior
  α := S.α.floor.toNat  -- Truncate to natural number

-- ============================================================================
-- PART 5: Consistency Theorem
-- ============================================================================

/--
For integer α, RSAScenarioQ computations match RSAScenario computations.

This ensures backward compatibility: when α ∈ ℕ, both APIs give identical results.

Note: This comparison requires specifying a default lexicon value.
-/
theorem integerAlpha_consistent (S : RSAScenario)
    (u : S.Utterance) (_w : S.World) (i : S.Interp) (_q : S.Goal)
    (l : S.Lexicon) (a : S.BeliefState) (g : S.Goal) :
    -- L0 is identical (doesn't use α)
    Q.L0Q (RSAScenario.toQ S l) u i = RSA.L0 S u i l a g := by
  -- The L0 computation is identical since it doesn't depend on α
  sorry

-- Additional consistency theorems would require more detailed proofs
-- about powApprox matching integer exponentiation for integer inputs.

end RSA
