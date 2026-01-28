/-
# RSA with Bayesian Theory of Mind Structure

A unified RSA architecture that separates:
1. **Convention**: Shared linguistic infrastructure (Interp, Lexicon)
2. **SpeakerMentalState**: Private beliefs and goals (A, QUD)

Both can be uncertain and marginalized over by L1:
- Convention uncertainty → Lexical Uncertainty (Bergen et al. 2016)
- Mental state uncertainty → BToM-style projection (Scontras & Tonhauser 2025)

## Theoretical Background

Classic BToM (Baker, Saxe, Tenenbaum):
- Beliefs: What agent thinks is true
- Desires: What agent wants
- Intentions: How agent plans to achieve desires

Linguistic BToM:
- Beliefs → Speaker's private assumptions A (epistemic state)
- Desires → QUD (communicative goal)
- Intentions → Utterance choice (S1's output)

Plus: Convention (grammar, lexicon) as the shared infrastructure.

## Timescales

- Convention: Stable across utterances, learned over interactions
  (uncertain in convention formation, typically fixed in single interaction)
- Mental state: Varies per utterance, always inferred by listener

## References

- Baker, Saxe & Tenenbaum (2009). Action understanding as inverse planning.
- Bergen, Levy & Goodman (2016). Pragmatic reasoning through semantic inference.
- Hawkins et al. (2023). From partners to populations.
- Scontras & Tonhauser (2025). Projection without lexically-specified presupposition.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Basic
import Linglib.Theories.RSA.Core

namespace RSA.BToM

-- ============================================================================
-- PART 1: Core Types
-- ============================================================================

/--
Speaker's mental state: beliefs about the world + communicative goal.

This is the BToM component that listeners reason about.
-/
structure SpeakerMentalState (W : Type) (Q : Type) where
  /-- Private beliefs: worlds the speaker considers possible (A ⊆ W) -/
  beliefWorlds : W → Prop
  /-- Communicative goal: what aspect of the world to communicate -/
  goal : Q

/--
Linguistic convention: shared interpretation and lexical mappings.

This is typically shared but can be uncertain (LU, convention formation).
-/
structure Convention (I : Type) (L : Type) where
  /-- Interpretation mode (e.g., scope reading) -/
  interp : I
  /-- Lexicon choice -/
  lexicon : L

-- ============================================================================
-- PART 2: BToM RSA Scenario
-- ============================================================================

/--
RSA scenario with explicit BToM structure.

Separates what's conventionalized from what's mental state.
Both can be marginalized over by L1.
-/
structure BToMScenario where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of world states -/
  World : Type

  -- Convention types (can be Unit if fixed)
  /-- Interpretation type (scope readings, etc.) -/
  Interp : Type := Unit
  /-- Lexicon type (for LU models) -/
  Lexicon : Type := Unit

  -- Mental state types (can be Unit if not modeling)
  /-- Type of belief states (subsets of worlds) -/
  BeliefState : Type := Unit
  /-- Type of QUDs/communicative goals -/
  Goal : Type := Unit

  /-- Core meaning function: given convention, does utterance apply to world? -/
  φ : Interp → Lexicon → Utterance → World → ℚ

  /-- Goal projection: are two worlds equivalent under this goal? -/
  goalProject : Goal → World → World → Bool

  /-- Belief state membership: is world in speaker's belief state? -/
  inBeliefState : BeliefState → World → Bool

  -- Enumerations
  utterances : List Utterance
  worlds : List World
  interps : List Interp
  lexica : List Lexicon
  beliefStates : List BeliefState
  goals : List Goal

  -- Priors
  worldPrior : World → ℚ := fun _ => 1
  interpPrior : Interp → ℚ := fun _ => 1
  lexiconPrior : Lexicon → ℚ := fun _ => 1
  beliefStatePrior : BeliefState → ℚ := fun _ => 1
  goalPrior : Goal → ℚ := fun _ => 1

  /-- Rationality parameter -/
  α : ℕ := 1

  [uttBEq : BEq Utterance]
  [worldBEq : BEq World]
  [interpBEq : BEq Interp]
  [lexiconBEq : BEq Lexicon]
  [beliefStateBEq : BEq BeliefState]
  [goalBEq : BEq Goal]

attribute [instance] BToMScenario.uttBEq BToMScenario.worldBEq
  BToMScenario.interpBEq BToMScenario.lexiconBEq
  BToMScenario.beliefStateBEq BToMScenario.goalBEq

-- ============================================================================
-- PART 3: Smart Constructors
-- ============================================================================

/--
Build a standard RSA scenario (no convention uncertainty, no mental state inference).

Equivalent to RSAScenario.basic.
-/
def BToMScenario.basic {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (prior : W → ℚ := fun _ => 1) : BToMScenario where
  Utterance := U
  World := W
  φ _ _ u w := φ u w
  goalProject _ w w' := w == w'
  inBeliefState _ _ := true  -- All worlds in belief state
  utterances := utterances
  worlds := worlds
  interps := [()]
  lexica := [()]
  beliefStates := [()]
  goals := [()]
  worldPrior := prior

/--
Build a scenario with mental state inference (beliefs + goals).

This is for BToM-style projection models like Scontras & Tonhauser 2025.
-/
def BToMScenario.mentalState {U W A Q : Type}
    [BEq U] [BEq W] [BEq A] [BEq Q] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (beliefStates : List A) (goals : List Q)
    (φ : U → W → ℚ)
    (inBeliefState : A → W → Bool)
    (goalProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (beliefStatePrior : A → ℚ := fun _ => 1)
    (goalPrior : Q → ℚ := fun _ => 1) : BToMScenario where
  Utterance := U
  World := W
  BeliefState := A
  Goal := Q
  φ _ _ := φ
  goalProject := goalProject
  inBeliefState := inBeliefState
  utterances := utterances
  worlds := worlds
  interps := [()]
  lexica := [()]
  beliefStates := beliefStates
  goals := goals
  worldPrior := worldPrior
  beliefStatePrior := beliefStatePrior
  goalPrior := goalPrior

/--
Build a scenario with convention uncertainty (LU-style).

This is for lexical uncertainty models like Bergen et al. 2016.
-/
def BToMScenario.conventionUncertainty {U W L : Type}
    [BEq U] [BEq W] [BEq L] [DecidableEq W]
    (utterances : List U) (worlds : List W) (lexica : List L)
    (φ : L → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (lexiconPrior : L → ℚ := fun _ => 1) : BToMScenario where
  Utterance := U
  World := W
  Lexicon := L
  φ _ l u w := φ l u w
  goalProject _ w w' := w == w'
  inBeliefState _ _ := true
  utterances := utterances
  worlds := worlds
  interps := [()]
  lexica := lexica
  beliefStates := [()]
  goals := [()]
  worldPrior := worldPrior
  lexiconPrior := lexiconPrior

-- ============================================================================
-- PART 4: RSA Computations with BToM Structure
-- ============================================================================

namespace BToMRSA

/--
L0: Literal listener given full context (convention + mental state).

P(w | u, i, l, a) ∝ P(w) · φ(i,l,u,w) · [w ∈ a]

Standard RSA: L0 uses world prior. This matches the paper's equation (5).
(Note: WebPPL implementation uses uniformDraw, but paper has P(w').)
-/
def L0 (S : BToMScenario) (u : S.Utterance)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (_q : S.Goal)
    : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w =>
    let semantic := S.φ i l u w
    let inBelief := if S.inBeliefState a w then 1 else 0
    (w, S.worldPrior w * semantic * inBelief)
  RSA.normalize scores

/--
L0 projected by QUD: probability of landing in same QUD cell as target.

P_L0(Q(w) | u, a, q) = Σ_{w' ~ w under q, w' ∈ a ∩ ⟦u⟧} P(w') / Z
-/
def L0_projected (S : BToMScenario) (u : S.Utterance)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : List (S.World × ℚ) :=
  let l0 := L0 S u i l a q
  S.worlds.map fun w =>
    -- Sum over worlds in same QUD cell
    let cellScore := l0.filter (fun (w', _) => S.goalProject q w w')
      |>.map (·.2) |> RSA.sumScores
    (w, cellScore)

/--
S1: Speaker chooses utterance to maximize L0's inference about QUD cell.

P(u | w, i, l, a, q) ∝ [u true in w] · P_L0(Q(w) | u, a, q)^α

The speaker only produces utterances that are TRUE in the actual world w.
This matches the WebPPL model: condition(meaning(utterance, state))
-/
def S1 (S : BToMScenario) (w : S.World)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u =>
    -- Speaker only produces true utterances
    let truthful := S.φ i l u w
    let l0Score := RSA.getScore (L0_projected S u i l a q) w
    (u, truthful * l0Score ^ S.α)
  RSA.normalize scores

/--
L1: Pragmatic listener marginalizes over ALL latent variables.

P(w, i, l, a, q | u) ∝ P(w) · P(i) · P(l) · P(a) · P(q) · S1(u | w, i, l, a, q)

This is the full BToM inference: reasoning about conventions AND mental state.
-/
def L1_joint (S : BToMScenario) (u : S.Utterance)
    : List ((S.World × S.Interp × S.Lexicon × S.BeliefState × S.Goal) × ℚ) :=
  let tuples := S.worlds.flatMap fun w =>
    S.interps.flatMap fun i =>
      S.lexica.flatMap fun l =>
        S.beliefStates.flatMap fun a =>
          S.goals.map fun q => (w, i, l, a, q)
  let scores := tuples.map fun (w, i, l, a, q) =>
    let prior := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                 S.beliefStatePrior a * S.goalPrior q
    let s1Score := RSA.getScore (S1 S w i l a q) u
    ((w, i, l, a, q), prior * s1Score)
  RSA.normalize scores

/--
L1 marginal over worlds: P(w | u)
-/
def L1_world (S : BToMScenario) (u : S.Utterance) : List (S.World × ℚ) :=
  let joint := L1_joint S u
  S.worlds.map fun w =>
    let wScores := joint.filter (fun ((w', _, _, _, _), _) => w' == w)
      |>.map (·.2)
    (w, RSA.sumScores wScores)

/--
L1 marginal over belief states: P(A | u)

What private assumptions does the listener infer the speaker has?
(Marginalizes over QUD - use L1_beliefState_givenQUD if QUD is observed)
-/
def L1_beliefState (S : BToMScenario) (u : S.Utterance) : List (S.BeliefState × ℚ) :=
  let joint := L1_joint S u
  S.beliefStates.map fun a =>
    let aScores := joint.filter (fun ((_, _, _, a', _), _) => a' == a)
      |>.map (·.2)
    (a, RSA.sumScores aScores)

/--
L1 joint over (world, belief state) given a FIXED QUD.

P(w, A | u, Q) ∝ P(w) · P(A) · [w ∈ A] · S1(u | w, A, Q)

This is equation (7) from Scontras & Tonhauser (2025), where QUD is observed.
Marginalizes over interpretations and lexica (convention uncertainty).

IMPORTANT: We add constraint [w ∈ A] because the speaker can only have
assumptions A that include the true world w. Otherwise A contradicts reality.
-/
def L1_joint_givenQUD (S : BToMScenario) (u : S.Utterance) (q : S.Goal)
    : List ((S.World × S.BeliefState) × ℚ) :=
  -- Build all (w, i, l, a) tuples
  let tuples := S.worlds.flatMap fun w =>
    S.interps.flatMap fun i =>
      S.lexica.flatMap fun l =>
        S.beliefStates.map fun a => (w, i, l, a)
  -- Score each tuple with S1 (QUD is fixed)
  -- Constraint: w must be in A (speaker can't have contradictory assumptions)
  let scores := tuples.map fun (w, i, l, a) =>
    let wInA := if S.inBeliefState a w then 1 else 0
    let prior := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                 S.beliefStatePrior a
    let s1Score := RSA.getScore (S1 S w i l a q) u
    ((w, i, l, a), prior * wInA * s1Score)
  -- Normalize to get joint
  let normalized := RSA.normalize scores
  -- Marginalize over i, l to get P(w, a | u, q)
  let pairs := S.worlds.flatMap fun w =>
    S.beliefStates.map fun a => (w, a)
  pairs.map fun (w, a) =>
    let matching := normalized.filter (fun ((w', _, _, a'), _) => w' == w && a' == a)
      |>.map (·.2)
    ((w, a), RSA.sumScores matching)

/--
L1 marginal over belief states given a FIXED QUD.

P(A | u, Q) = Σ_w P(w, A | u, Q)

This is what we need for computing projection strength.
-/
def L1_beliefState_givenQUD (S : BToMScenario) (u : S.Utterance) (q : S.Goal)
    : List (S.BeliefState × ℚ) :=
  let joint := L1_joint_givenQUD S u q
  S.beliefStates.map fun a =>
    let aScores := joint.filter (fun ((_, a'), _) => a' == a)
      |>.map (·.2)
    (a, RSA.sumScores aScores)

/--
L1 marginal over worlds given a FIXED QUD.

P(w | u, Q) = Σ_A P(w, A | u, Q)
-/
def L1_world_givenQUD (S : BToMScenario) (u : S.Utterance) (q : S.Goal)
    : List (S.World × ℚ) :=
  let joint := L1_joint_givenQUD S u q
  S.worlds.map fun w =>
    let wScores := joint.filter (fun ((w', _), _) => w' == w)
      |>.map (·.2)
    (w, RSA.sumScores wScores)

/--
L1 marginal over goals/QUDs: P(Q | u)

What communicative goal does the listener infer?
-/
def L1_goal (S : BToMScenario) (u : S.Utterance) : List (S.Goal × ℚ) :=
  let joint := L1_joint S u
  S.goals.map fun q =>
    let qScores := joint.filter (fun ((_, _, _, _, q'), _) => q' == q)
      |>.map (·.2)
    (q, RSA.sumScores qScores)

/--
L1 marginal over lexica: P(L | u)

What convention/lexicon does the listener infer?
(Key for LU and convention formation models)
-/
def L1_lexicon (S : BToMScenario) (u : S.Utterance) : List (S.Lexicon × ℚ) :=
  let joint := L1_joint S u
  S.lexica.map fun l =>
    let lScores := joint.filter (fun ((_, _, l', _, _), _) => l' == l)
      |>.map (·.2)
    (l, RSA.sumScores lScores)

end BToMRSA

-- ============================================================================
-- PART 5: Projection as Mental State Inference
-- ============================================================================

/--
**Key insight for projection**:

Projection = listener's inference about what the speaker privately assumes.

If L1 infers high probability for belief states A where C is true,
then C "projects" (listener concludes C is likely true).

P(C | u) = Σ_A P(A | u) · [C holds in A]
-/
def projectionStrength (S : BToMScenario) (u : S.Utterance)
    (contentHoldsIn : S.BeliefState → Bool) : ℚ :=
  let beliefDist := BToMRSA.L1_beliefState S u
  beliefDist.foldl (fun acc (a, p) =>
    if contentHoldsIn a then acc + p else acc) 0

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## Architecture

```
BToMScenario
├── Convention (typically shared, can be uncertain)
│   ├── Interp : Type
│   └── Lexicon : Type
│
└── SpeakerMentalState (inferred by listener)
    ├── BeliefState : Type  (≈ A, private assumptions)
    └── Goal : Type         (≈ QUD, communicative goal)
```

## Computation

L1 marginalizes over ALL latent variables:
- Convention: Interp × Lexicon
- Mental state: BeliefState × Goal

This unifies:
- Standard RSA: All latent types = Unit
- Scope ambiguity: Interp varies
- Lexical uncertainty: Lexicon varies
- BToM projection: BeliefState × Goal vary
- Full model: Everything varies

## Key Functions

- `L0`: Literal listener given full context
- `L0_projected`: QUD-projected literal listener
- `S1`: Speaker optimizes for L0's QUD inference
- `L1_joint`: Full joint distribution
- `L1_world`, `L1_beliefState`, `L1_goal`, `L1_lexicon`: Marginals
- `projectionStrength`: Projection as belief-state inference
-/

end RSA.BToM
