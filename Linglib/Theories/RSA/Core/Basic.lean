/-
# Linglib.Core.RSA

Core RSA (Rational Speech Acts) infrastructure.

## Architecture

RSA uses exact rational arithmetic (ℚ) for all probability computations.
This enables mathematical proofs about pragmatic reasoning.

### Key Type

- `RSAScenario`: Unified type supporting all RSA variants

### RSA Model

RSA models communication as recursive reasoning between speakers and listeners:
- L0: Literal interpretation (semantic denotation)
- S1: Pragmatic speaker (chooses utterances to maximize informativity)
- L1: Pragmatic listener (reasons about what speaker meant)
- S2: Second-level pragmatic speaker

### Smart Constructors

- `RSAScenario.basic`: Simple reference games (no interp, no QUD)
- `RSAScenario.basicBool`: Boolean version of basic
- `RSAScenario.ambiguous`: Scope/interpretation ambiguity (Scontras & Pearl)
- `RSAScenario.ambiguousBool`: Boolean version of ambiguous
- `RSAScenario.qud`: QUD-sensitive models (Kao et al.)
- `RSAScenario.qudBool`: Boolean version of qud

Reference: Frank & Goodman (2012), Goodman & Frank (2016)
-/

import Mathlib.Data.Rat.Defs
import Linglib.Core.Distribution

-- ============================================================================
-- Utility Functions
-- ============================================================================

/-- Convert Bool to ℚ (1 if true, 0 if false) -/
def boolToRat (b : Bool) : ℚ := if b then 1 else 0

-- ============================================================================
-- RSAScenario: Unified Type (supports all RSA variants)
-- ============================================================================

/--
Unified RSA scenario supporting all RSA model variants.

This is the unified type with 5 latent variable categories:
- **World**: What's actually true (epistemic)
- **BeliefState**: Speaker's private assumptions - what the listener reasons the
  speaker takes for granted (epistemic-private, reasoned about by listener)
- **Goal**: Communicative intention/QUD (telic)
- **Interp**: Compositional meaning choice (convention)
- **Lexicon**: Word meaning uncertainty (convention)

This supports:
- Basic models (all latent types = Unit)
- Scope ambiguity models (Interp varies)
- QUD-sensitive models (Goal varies)
- Mental state models (BeliefState + Goal vary) - Scontras & Tonhauser 2025
- Lexical uncertainty models (Lexicon varies) - Bergen et al. 2016
- Full BToM models (all 5 latent types vary)

## Fields

- `Utterance`, `World`: Core domain types
- `Interp`, `Lexicon`: Convention types (shared)
- `BeliefState`, `Goal`: Mental state types (inferred by listener)
- `φ`: Agreement function parameterized by interpretation and lexicon
- `goalProject`: Goal equivalence relation on worlds
- `inBeliefState`: Belief state membership predicate
- Priors: `worldPrior`, `interpPrior`, `lexiconPrior`, `beliefStatePrior`, `goalPrior`
- `α`: Rationality parameter

## Smart Constructors

Use the smart constructors for common patterns:
- `RSAScenario.basic`: Simple reference games
- `RSAScenario.ambiguous`: Scope ambiguity
- `RSAScenario.qud`: QUD-sensitive models (hyperbole, metaphor)
- `RSAScenario.mentalState`: BToM projection models
- `RSAScenario.lexicalUncertainty`: LU models

## References

- Frank & Goodman (2012): Basic RSA
- Scontras & Pearl (2021): Scope ambiguity
- Kao et al. (2014): QUD-sensitive models
- Bergen et al. (2016): Lexical uncertainty
- Scontras & Tonhauser (2025): BToM projection
-/
structure RSAScenario where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of world states -/
  World : Type
  /-- Type of interpretations (e.g., scope readings). Use Unit for basic models. -/
  Interp : Type := Unit
  /-- Type of lexica (for lexical uncertainty). Use Unit for fixed lexicon. -/
  Lexicon : Type := Unit
  /-- Type of speaker's belief states (what the speaker privately assumes).
      The listener reasons about this - it represents the speaker's/partner's
      private epistemic state, not the listener's own beliefs. Use Unit if not modeling. -/
  BeliefState : Type := Unit
  /-- Type of communicative goals/QUDs. Use Unit for non-QUD models. -/
  Goal : Type := Unit

  /-- Agreement function: φ(interp, lexicon, utterance, world) ∈ [0,1] -/
  φ : Interp → Lexicon → Utterance → World → ℚ
  /-- Goal projection: are two worlds equivalent under this goal/QUD? -/
  goalProject : Goal → World → World → Bool
  /-- Belief state membership: is world in speaker's belief state? -/
  inBeliefState : BeliefState → World → Bool := fun _ _ => true

  /-- Enumeration of utterances -/
  utterances : List Utterance
  /-- Enumeration of worlds -/
  worlds : List World
  /-- Enumeration of interpretations -/
  interps : List Interp
  /-- Enumeration of lexica -/
  lexica : List Lexicon
  /-- Enumeration of belief states -/
  beliefStates : List BeliefState
  /-- Enumeration of goals/QUDs -/
  goals : List Goal

  /-- Prior over worlds -/
  worldPrior : World → ℚ := fun _ => 1
  /-- Prior over interpretations -/
  interpPrior : Interp → ℚ := fun _ => 1
  /-- Prior over lexica -/
  lexiconPrior : Lexicon → ℚ := fun _ => 1
  /-- Prior over belief states -/
  beliefStatePrior : BeliefState → ℚ := fun _ => 1
  /-- Prior over goals/QUDs -/
  goalPrior : Goal → ℚ := fun _ => 1

  /-- Rationality parameter. Higher = more informative speaker. -/
  α : ℕ := 1

  /-- BEq instance for utterances -/
  [uttBEq : BEq Utterance]
  /-- BEq instance for worlds -/
  [worldBEq : BEq World]
  /-- BEq instance for interpretations -/
  [interpBEq : BEq Interp]
  /-- BEq instance for lexica -/
  [lexiconBEq : BEq Lexicon]
  /-- BEq instance for belief states -/
  [beliefStateBEq : BEq BeliefState]
  /-- BEq instance for goals/QUDs -/
  [goalBEq : BEq Goal]

attribute [instance] RSAScenario.uttBEq RSAScenario.worldBEq
  RSAScenario.interpBEq RSAScenario.lexiconBEq
  RSAScenario.beliefStateBEq RSAScenario.goalBEq

-- ============================================================================
-- Backward Compatibility Aliases (QUD → Goal)
-- ============================================================================

/-- Backward compatibility: QUD is an alias for Goal -/
abbrev RSAScenario.QUD (S : RSAScenario) := S.Goal

/-- Backward compatibility: quds is an alias for goals -/
def RSAScenario.quds (S : RSAScenario) := S.goals

/-- Backward compatibility: qudPrior is an alias for goalPrior -/
def RSAScenario.qudPrior (S : RSAScenario) := S.goalPrior

/-- Backward compatibility: qudProject is an alias for goalProject -/
def RSAScenario.qudProject (S : RSAScenario) := S.goalProject

/-- Backward compatibility: qudBEq is an alias for goalBEq -/
def RSAScenario.qudBEq (S : RSAScenario) := S.goalBEq

-- ============================================================================
-- Smart Constructors for RSAScenario
-- ============================================================================

/--
Build a basic RSA scenario (no interpretation ambiguity, no QUD).

This is for simple reference games like Frank & Goodman (2012).

## Example

```lean
def myScenario : RSAScenario :=
  RSAScenario.basic [.blue, .square] [.obj1, .obj2] myMeaning
```
-/
def RSAScenario.basic {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (prior : W → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := Unit
  φ _ _ u w := φ u w
  goalProject _ w w' := w == w'
  inBeliefState _ _ := true
  utterances := utterances
  worlds := worlds
  interps := [()]
  lexica := [()]
  beliefStates := [()]
  goals := [()]
  worldPrior := prior
  interpPrior := fun _ => 1
  lexiconPrior := fun _ => 1
  beliefStatePrior := fun _ => 1
  goalPrior := fun _ => 1
  α := α

/--
Build a basic RSA scenario from Boolean semantics.
-/
def RSAScenario.basicBool {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (satisfies : W → U → Bool)
    (prior : W → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario :=
  RSAScenario.basic utterances worlds (fun u w => boolToRat (satisfies w u)) prior α

/--
Build a scenario with interpretation ambiguity (e.g., scope readings).

This is for lifted-variable RSA like Scontras & Pearl (2021).

## Example

```lean
def scopeScenario : RSAScenario :=
  RSAScenario.ambiguous
    [.everyHorseNotJump]
    [0, 1, 2]  -- worlds
    [.surface, .inverse]  -- interpretations
    scopeMeaning
```
-/
def RSAScenario.ambiguous {U W I : Type} [BEq U] [BEq W] [BEq I] [DecidableEq W]
    (utterances : List U) (worlds : List W) (interps : List I)
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario where
  Utterance := U
  World := W
  Interp := I
  Lexicon := Unit
  BeliefState := Unit
  Goal := Unit
  φ i _ u w := φ i u w
  goalProject _ w w' := w == w'
  inBeliefState _ _ := true
  utterances := utterances
  worlds := worlds
  interps := interps
  lexica := [()]
  beliefStates := [()]
  goals := [()]
  worldPrior := worldPrior
  interpPrior := interpPrior
  lexiconPrior := fun _ => 1
  beliefStatePrior := fun _ => 1
  goalPrior := fun _ => 1
  α := α

/--
Build a scenario with interpretation ambiguity from Boolean semantics.
-/
def RSAScenario.ambiguousBool {U W I : Type} [BEq U] [BEq W] [BEq I] [DecidableEq W]
    (utterances : List U) (worlds : List W) (interps : List I)
    (satisfies : I → W → U → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario :=
  RSAScenario.ambiguous utterances worlds interps
    (fun i u w => boolToRat (satisfies i w u)) worldPrior interpPrior α

/--
Build a QUD-sensitive scenario (e.g., hyperbole, metaphor).

This is for QUD-RSA like Kao et al. (2014).

## Example

```lean
def hyperboleScenario : RSAScenario :=
  RSAScenario.qud
    allUtterances allMeanings allGoals
    extendedSemantics
    qudEquiv
    meaningPrior
    goalPrior
```
-/
def RSAScenario.qud {U W Q : Type} [BEq U] [BEq W] [BEq Q]
    (utterances : List U) (worlds : List W) (quds : List Q)
    (φ : U → W → ℚ)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (qudPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := Q
  φ _ _ u w := φ u w
  goalProject := qudProject
  inBeliefState _ _ := true
  utterances := utterances
  worlds := worlds
  interps := [()]
  lexica := [()]
  beliefStates := [()]
  goals := quds
  worldPrior := worldPrior
  interpPrior := fun _ => 1
  lexiconPrior := fun _ => 1
  beliefStatePrior := fun _ => 1
  goalPrior := qudPrior
  α := α

/--
Build a QUD-sensitive scenario from Boolean semantics.
-/
def RSAScenario.qudBool {U W Q : Type} [BEq U] [BEq W] [BEq Q]
    (utterances : List U) (worlds : List W) (quds : List Q)
    (satisfies : W → U → Bool)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (qudPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario :=
  RSAScenario.qud utterances worlds quds
    (fun u w => boolToRat (satisfies w u)) qudProject worldPrior qudPrior α

/--
Build a scenario with mental state inference (beliefs + goals).

This is for BToM-style projection models like Scontras & Tonhauser (2025).

## Example

```lean
def projectionScenario : RSAScenario :=
  RSAScenario.mentalState
    allUtterances allWorlds allBeliefStates allGoals
    literalMeaning inBeliefState goalProject
```
-/
def RSAScenario.mentalState {U W A Q : Type}
    [BEq U] [BEq W] [BEq A] [BEq Q] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (beliefStates : List A) (goals : List Q)
    (φ : U → W → ℚ)
    (inBeliefState : A → W → Bool)
    (goalProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (beliefStatePrior : A → ℚ := fun _ => 1)
    (goalPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := Unit
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
  interpPrior := fun _ => 1
  lexiconPrior := fun _ => 1
  beliefStatePrior := beliefStatePrior
  goalPrior := goalPrior
  α := α

/--
Build a scenario with mental state inference from Boolean semantics.
-/
def RSAScenario.mentalStateBool {U W A Q : Type}
    [BEq U] [BEq W] [BEq A] [BEq Q] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (beliefStates : List A) (goals : List Q)
    (satisfies : W → U → Bool)
    (inBeliefState : A → W → Bool)
    (goalProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (beliefStatePrior : A → ℚ := fun _ => 1)
    (goalPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario :=
  RSAScenario.mentalState utterances worlds beliefStates goals
    (fun u w => boolToRat (satisfies w u)) inBeliefState goalProject
    worldPrior beliefStatePrior goalPrior α

/--
Build a scenario with lexical uncertainty.

This is for LU models like Bergen et al. (2016).

## Example

```lean
def luScenario : RSAScenario :=
  RSAScenario.lexicalUncertainty
    allUtterances allWorlds allLexica
    lexiconMeaning
    worldPrior lexiconPrior
```
-/
def RSAScenario.lexicalUncertainty {U W L : Type}
    [BEq U] [BEq W] [BEq L] [DecidableEq W]
    (utterances : List U) (worlds : List W) (lexica : List L)
    (φ : L → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (lexiconPrior : L → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := L
  BeliefState := Unit
  Goal := Unit
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
  interpPrior := fun _ => 1
  lexiconPrior := lexiconPrior
  beliefStatePrior := fun _ => 1
  goalPrior := fun _ => 1
  α := α

/--
Build a scenario with lexical uncertainty from Boolean semantics.
-/
def RSAScenario.lexicalUncertaintyBool {U W L : Type}
    [BEq U] [BEq W] [BEq L] [DecidableEq W]
    (utterances : List U) (worlds : List W) (lexica : List L)
    (satisfies : L → W → U → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (lexiconPrior : L → ℚ := fun _ => 1)
    (α : ℕ := 1) : RSAScenario :=
  RSAScenario.lexicalUncertainty utterances worlds lexica
    (fun l u w => boolToRat (satisfies l w u)) worldPrior lexiconPrior α

-- ============================================================================
-- RSA Computations
-- ============================================================================

namespace RSA

/-- Sum a list of rationals -/
def sumScores (scores : List ℚ) : ℚ :=
  scores.foldl (· + ·) 0

/-- Look up score in distribution -/
def getScore {α : Type} [BEq α] (dist : List (α × ℚ)) (x : α) : ℚ :=
  match dist.find? (·.1 == x) with
  | some (_, s) => s
  | none => 0

/-- Normalize a distribution (divide each score by total) -/
def normalize {α : Type} (dist : List (α × ℚ)) : List (α × ℚ) :=
  let total := sumScores (dist.map (·.2))
  dist.map fun (x, s) =>
    (x, if total ≠ 0 then s / total else 0)

-- ============================================================================
-- L0: Literal Listener
-- ============================================================================

/--
L0: Literal listener distribution given full context.

P(w | u, i, l, a) ∝ P(w) · φ(i, l, u, w) · [w ∈ a]

For basic scenarios, pass `()` for interpretation, lexicon, and belief state.
Standard RSA: L0 uses world prior (matches papers).
-/
def L0 (S : RSAScenario) (u : S.Utterance)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (_q : S.Goal)
    : List (S.World × ℚ) :=
  let scores := S.worlds.map fun w =>
    let semantic := S.φ i l u w
    let inBelief := if S.inBeliefState a w then 1 else 0
    (w, S.worldPrior w * semantic * inBelief)
  normalize scores

/--
L0 projected by Goal/QUD.

P_q(w | u, i, l, a) ∝ Σ_{w' ~ w under q} P(w') · φ(i, l, u, w') · [w' ∈ a]

Returns the summed probability mass of the equivalence class containing w.
-/
def L0_projected (S : RSAScenario) (u : S.Utterance)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : List (S.World × ℚ) :=
  let l0 := L0 S u i l a q
  S.worlds.map fun w =>
    -- Sum over all worlds equivalent to w under this goal/QUD
    let eqClassScore := l0.filter (fun (w', _) => S.goalProject q w w') |>.map (·.2) |> sumScores
    (w, eqClassScore)

-- ============================================================================
-- S1: Pragmatic Speaker
-- ============================================================================

/--
S1: Pragmatic speaker distribution.

P(u | w, i, l, a, q) ∝ [u true in w] · L0_q(w | u, i, l, a)^α

For basic scenarios, pass `()` for all latent variables except world.
For QUD models, the speaker optimizes informativity w.r.t. the projected meaning.
The speaker only produces utterances that are TRUE in the actual world w.
-/
def S1 (S : RSAScenario) (w : S.World)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u =>
    -- Speaker only produces true utterances
    let truthful := S.φ i l u w
    let l0Score := getScore (L0_projected S u i l a q) w
    (u, truthful * l0Score ^ S.α)
  normalize scores

-- ============================================================================
-- L1: Pragmatic Listener
-- ============================================================================

/--
L1 joint distribution over all 5 latent variables.

P(w, i, l, a, q | u) ∝ P(w) · P(i) · P(l) · P(a) · P(q) · S1(u | w, i, l, a, q)

This is the full BToM inference: reasoning about conventions AND mental state.
-/
def L1_joint (S : RSAScenario) (u : S.Utterance)
    : List ((S.World × S.Interp × S.Lexicon × S.BeliefState × S.Goal) × ℚ) :=
  let tuples := S.worlds.flatMap fun w =>
    S.interps.flatMap fun i =>
      S.lexica.flatMap fun l =>
        S.beliefStates.flatMap fun a =>
          S.goals.map fun q => (w, i, l, a, q)
  let scores := tuples.map fun (w, i, l, a, q) =>
    let priorScore := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                      S.beliefStatePrior a * S.goalPrior q
    let s1Score := getScore (S1 S w i l a q) u
    ((w, i, l, a, q), priorScore * s1Score)
  normalize scores

/--
L1 marginal over worlds.

P(w | u) = Σ_{i,l,a,q} P(w, i, l, a, q | u)
-/
def L1_world (S : RSAScenario) (u : S.Utterance) : List (S.World × ℚ) :=
  let joint := L1_joint S u
  S.worlds.map fun w =>
    let wScores := joint.filter (fun ((w', _, _, _, _), _) => w' == w) |>.map (·.2)
    (w, sumScores wScores)

/--
L1 marginal over interpretations.

P(i | u) = Σ_{w,l,a,q} P(w, i, l, a, q | u)
-/
def L1_interp (S : RSAScenario) (u : S.Utterance) : List (S.Interp × ℚ) :=
  let joint := L1_joint S u
  S.interps.map fun i =>
    let iScores := joint.filter (fun ((_, i', _, _, _), _) => i' == i) |>.map (·.2)
    (i, sumScores iScores)

/--
L1 marginal over lexica.

P(l | u) = Σ_{w,i,a,q} P(w, i, l, a, q | u)
-/
def L1_lexicon (S : RSAScenario) (u : S.Utterance) : List (S.Lexicon × ℚ) :=
  let joint := L1_joint S u
  S.lexica.map fun l =>
    let lScores := joint.filter (fun ((_, _, l', _, _), _) => l' == l) |>.map (·.2)
    (l, sumScores lScores)

/--
L1 marginal over belief states.

P(a | u) = Σ_{w,i,l,q} P(w, i, l, a, q | u)

What private assumptions does the listener infer the speaker has?
-/
def L1_beliefState (S : RSAScenario) (u : S.Utterance) : List (S.BeliefState × ℚ) :=
  let joint := L1_joint S u
  S.beliefStates.map fun a =>
    let aScores := joint.filter (fun ((_, _, _, a', _), _) => a' == a) |>.map (·.2)
    (a, sumScores aScores)

/--
L1 marginal over goals/QUDs.

P(q | u) = Σ_{w,i,l,a} P(w, i, l, a, q | u)
-/
def L1_goal (S : RSAScenario) (u : S.Utterance) : List (S.Goal × ℚ) :=
  let joint := L1_joint S u
  S.goals.map fun q =>
    let qScores := joint.filter (fun ((_, _, _, _, q'), _) => q' == q) |>.map (·.2)
    (q, sumScores qScores)

/-- Backward compatibility alias -/
def L1_qud (S : RSAScenario) (u : S.Utterance) : List (S.Goal × ℚ) :=
  L1_goal S u

-- ============================================================================
-- L1 Given Goal: For models where goal/QUD is observed
-- ============================================================================

/--
L1 joint over (World × BeliefState) given a FIXED Goal.

P(w, A | u, Q) ∝ P(w) · P(A) · [w ∈ A] · S1(u | w, A, Q)

This is equation (7) from Scontras & Tonhauser (2025), where QUD is observed.
Marginalizes over interpretations and lexica (convention uncertainty).

IMPORTANT: We add constraint [w ∈ A] because the speaker can only have
assumptions A that include the true world w. Otherwise A contradicts reality.
-/
def L1_joint_givenGoal (S : RSAScenario) (u : S.Utterance) (q : S.Goal)
    : List ((S.World × S.BeliefState) × ℚ) :=
  -- Build all (w, i, l, a) tuples
  let tuples := S.worlds.flatMap fun w =>
    S.interps.flatMap fun i =>
      S.lexica.flatMap fun l =>
        S.beliefStates.map fun a => (w, i, l, a)
  -- Score each tuple with S1 (Goal is fixed)
  -- Constraint: w must be in A (speaker can't have contradictory assumptions)
  let scores := tuples.map fun (w, i, l, a) =>
    let wInA := if S.inBeliefState a w then 1 else 0
    let prior := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                 S.beliefStatePrior a
    let s1Score := getScore (S1 S w i l a q) u
    ((w, i, l, a), prior * wInA * s1Score)
  -- Normalize to get joint
  let normalized := normalize scores
  -- Marginalize over i, l to get P(w, a | u, q)
  let pairs := S.worlds.flatMap fun w =>
    S.beliefStates.map fun a => (w, a)
  pairs.map fun (w, a) =>
    let matching := normalized.filter (fun ((w', _, _, a'), _) => w' == w && a' == a)
      |>.map (·.2)
    ((w, a), sumScores matching)

/--
L1 marginal over belief states given a FIXED Goal.

P(A | u, Q) = Σ_w P(w, A | u, Q)

This is what we need for computing projection strength.
-/
def L1_beliefState_givenGoal (S : RSAScenario) (u : S.Utterance) (q : S.Goal)
    : List (S.BeliefState × ℚ) :=
  let joint := L1_joint_givenGoal S u q
  S.beliefStates.map fun a =>
    let aScores := joint.filter (fun ((_, a'), _) => a' == a)
      |>.map (·.2)
    (a, sumScores aScores)

/--
L1 marginal over worlds given a FIXED Goal.

P(w | u, Q) = Σ_A P(w, A | u, Q)
-/
def L1_world_givenGoal (S : RSAScenario) (u : S.Utterance) (q : S.Goal)
    : List (S.World × ℚ) :=
  let joint := L1_joint_givenGoal S u q
  S.worlds.map fun w =>
    let wScores := joint.filter (fun ((w', _), _) => w' == w)
      |>.map (·.2)
    (w, sumScores wScores)

-- ============================================================================
-- S2: Second-Level Pragmatic Speaker
-- ============================================================================

/--
S2: Second-level pragmatic speaker.

P(u | w) ∝ L1_world(w | u)^α

This can be used for modeling truth-value judgments (endorsement).
-/
def S2 (S : RSAScenario) (w : S.World) : List (S.Utterance × ℚ) :=
  let scores := S.utterances.map fun u =>
    let l1Score := getScore (L1_world S u) w
    (u, l1Score ^ S.α)
  normalize scores

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Count worlds compatible with an utterance under interpretation and lexicon -/
def compatibleCount (S : RSAScenario) (u : S.Utterance) (i : S.Interp) (l : S.Lexicon) : Nat :=
  (S.worlds.filter fun w => S.φ i l u w > 0).length

/-- Informativity under interpretation and lexicon -/
def informativity (S : RSAScenario) (u : S.Utterance) (i : S.Interp) (l : S.Lexicon) : ℚ :=
  let n := compatibleCount S u i l
  if n > 0 then 1 / n else 0

-- ============================================================================
-- Projection as Mental State Inference
-- ============================================================================

/--
Projection strength: listener's inference about what the speaker privately assumes.

P(C | u) = Σ_A P(A | u) · [C holds in A]

If L1 infers high probability for belief states A where C is true,
then C "projects" (listener concludes C is likely true).
-/
def projectionStrength (S : RSAScenario) (u : S.Utterance)
    (contentHoldsIn : S.BeliefState → Bool) : ℚ :=
  let beliefDist := L1_beliefState S u
  beliefDist.foldl (fun acc (a, p) =>
    if contentHoldsIn a then acc + p else acc) 0

/--
Projection strength given a fixed Goal/QUD.

P(C | u, Q) = Σ_A P(A | u, Q) · [C holds in A]
-/
def projectionStrength_givenGoal (S : RSAScenario) (u : S.Utterance) (q : S.Goal)
    (contentHoldsIn : S.BeliefState → Bool) : ℚ :=
  let beliefDist := L1_beliefState_givenGoal S u q
  beliefDist.foldl (fun acc (a, p) =>
    if contentHoldsIn a then acc + p else acc) 0

end RSA

