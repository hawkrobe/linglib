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
- `speakerCredence`: Belief state membership predicate
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
  /-- Speaker's credence: P_speaker(w | a).

      The speaker's subjective probability for world w given epistemic state a.

      - Value 0: world w is impossible given state a
      - Value > 0: relative weight/probability for world w

      Default: uniform (all worlds equally weighted).
  -/
  speakerCredence : BeliefState → World → ℚ := fun _ _ => 1

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

  /-- Utterance cost function. Higher cost → less likely to be produced.

      Standard RSA uses: S1(u|w) ∝ exp(α * (ln L0 - cost))

      Since we use rationals, we approximate with:
      S1(u|w) ∝ L0^α / (1 + cost)^α

      Default: zero cost for all utterances. -/
  cost : Utterance → ℚ := fun _ => 0

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
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := Unit
  φ _ _ u w := φ u w
  goalProject _ w w' := w == w'
  speakerCredence _ _ := 1
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
  cost := cost

/--
Build a basic RSA scenario from Boolean semantics.
-/
def RSAScenario.basicBool {U W : Type} [BEq U] [BEq W] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (satisfies : W → U → Bool)
    (prior : W → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario :=
  RSAScenario.basic utterances worlds (fun u w => boolToRat (satisfies w u)) prior α cost

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
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario where
  Utterance := U
  World := W
  Interp := I
  Lexicon := Unit
  BeliefState := Unit
  Goal := Unit
  φ i _ u w := φ i u w
  goalProject _ w w' := w == w'
  speakerCredence _ _ := 1
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
  cost := cost

/--
Build a scenario with interpretation ambiguity from Boolean semantics.
-/
def RSAScenario.ambiguousBool {U W I : Type} [BEq U] [BEq W] [BEq I] [DecidableEq W]
    (utterances : List U) (worlds : List W) (interps : List I)
    (satisfies : I → W → U → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario :=
  RSAScenario.ambiguous utterances worlds interps
    (fun i u w => boolToRat (satisfies i w u)) worldPrior interpPrior α cost

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
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := Q
  φ _ _ u w := φ u w
  goalProject := qudProject
  speakerCredence _ _ := 1
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
  cost := cost

/--
Build a QUD-sensitive scenario from Boolean semantics.
-/
def RSAScenario.qudBool {U W Q : Type} [BEq U] [BEq W] [BEq Q]
    (utterances : List U) (worlds : List W) (quds : List Q)
    (satisfies : W → U → Bool)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (qudPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario :=
  RSAScenario.qud utterances worlds quds
    (fun u w => boolToRat (satisfies w u)) qudProject worldPrior qudPrior α cost

/--
Build a scenario with mental state inference (beliefs + goals).

This is for BToM-style projection models like Scontras & Tonhauser (2025).

## Example

```lean
def projectionScenario : RSAScenario :=
  RSAScenario.mentalState
    allUtterances allWorlds allBeliefStates allGoals
    literalMeaning speakerCredence goalProject
```
-/
def RSAScenario.mentalState {U W A Q : Type}
    [BEq U] [BEq W] [BEq A] [BEq Q] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (beliefStates : List A) (goals : List Q)
    (φ : U → W → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (beliefStatePrior : A → ℚ := fun _ => 1)
    (goalPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := Unit
  BeliefState := A
  Goal := Q
  φ _ _ := φ
  goalProject := goalProject
  speakerCredence := speakerCredence
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
  cost := cost

/--
Build a scenario with mental state inference from Boolean semantics.
-/
def RSAScenario.mentalStateBool {U W A Q : Type}
    [BEq U] [BEq W] [BEq A] [BEq Q] [DecidableEq W]
    (utterances : List U) (worlds : List W)
    (beliefStates : List A) (goals : List Q)
    (satisfies : W → U → Bool)
    (speakerCredence : A → W → Bool)
    (goalProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (beliefStatePrior : A → ℚ := fun _ => 1)
    (goalPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario :=
  RSAScenario.mentalState utterances worlds beliefStates goals
    (fun u w => boolToRat (satisfies w u))
    (fun a w => boolToRat (speakerCredence a w))
    goalProject worldPrior beliefStatePrior goalPrior α cost

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
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := L
  BeliefState := Unit
  Goal := Unit
  φ _ l u w := φ l u w
  goalProject _ w w' := w == w'
  speakerCredence _ _ := 1
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
  cost := cost

/--
Build a scenario with lexical uncertainty from Boolean semantics.
-/
def RSAScenario.lexicalUncertaintyBool {U W L : Type}
    [BEq U] [BEq W] [BEq L] [DecidableEq W]
    (utterances : List U) (worlds : List W) (lexica : List L)
    (satisfies : L → W → U → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (lexiconPrior : L → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenario :=
  RSAScenario.lexicalUncertainty utterances worlds lexica
    (fun l u w => boolToRat (satisfies l w u)) worldPrior lexiconPrior α cost

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
    let credence := S.speakerCredence a w
    (w, S.worldPrior w * semantic * credence)
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
    -- Cost discount: higher cost → lower probability
    -- Approximates exp(-α * cost) with 1/(1 + cost)^α
    let costDiscount := 1 / ((1 + S.cost u) ^ S.α)
    (u, truthful * l0Score ^ S.α * costDiscount)
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

P(w, A | u, Q) ∝ P(w) · P(A) · P_speaker(w | A) · S1(u | w, A, Q)

This is equation (7) from Scontras & Tonhauser (2025), where QUD is observed.
Marginalizes over interpretations and lexica (convention uncertainty).

The speakerCredence term P_speaker(w | A) weights how probable world w is
from the speaker's perspective given their epistemic state A.
-/
def L1_joint_givenGoal (S : RSAScenario) (u : S.Utterance) (q : S.Goal)
    : List ((S.World × S.BeliefState) × ℚ) :=
  -- Build all (w, i, l, a) tuples
  let tuples := S.worlds.flatMap fun w =>
    S.interps.flatMap fun i =>
      S.lexica.flatMap fun l =>
        S.beliefStates.map fun a => (w, i, l, a)
  -- Score each tuple with S1 (Goal is fixed)
  -- Weight by speaker's credence P_speaker(w | A)
  let scores := tuples.map fun (w, i, l, a) =>
    let credence := S.speakerCredence a w
    let prior := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                 S.beliefStatePrior a
    let s1Score := getScore (S1 S w i l a q) u
    ((w, i, l, a), prior * credence * s1Score)
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

-- ============================================================================
-- RSAScenarioF: Fintype-Based Unified Type
-- ============================================================================

/--
Fintype-based RSA scenario for compile-time guarantees.

This is the type-safe version of RSAScenario that uses Fintype constraints
instead of explicit List enumerations. It enables:
- Compile-time completeness proofs
- Type-safe distribution operations via ExactDist
- Better integration with Mathlib's measure theory

All fields are the same as RSAScenario except:
- No List enumerations (derived from Fintype instances)
- Returns ExactDist instead of List (α × ℚ)

## Example

```lean
def myScenario : RSAScenarioF where
  Utterance := MyUtterance
  World := MyWorld
  φ := fun _ _ u w => if myMeaning u w then 1 else 0
  goalProject := fun _ w w' => w == w'
```
-/
structure RSAScenarioF where
  /-- Type of utterances -/
  Utterance : Type
  /-- Type of world states -/
  World : Type
  /-- Type of interpretations (e.g., scope readings). Use Unit for basic models. -/
  Interp : Type := Unit
  /-- Type of lexica (for lexical uncertainty). Use Unit for fixed lexicon. -/
  Lexicon : Type := Unit
  /-- Type of speaker's belief states. Use Unit if not modeling. -/
  BeliefState : Type := Unit
  /-- Type of communicative goals/QUDs. Use Unit for non-QUD models. -/
  Goal : Type := Unit

  /-- Agreement function: φ(interp, lexicon, utterance, world) ∈ [0,1] -/
  φ : Interp → Lexicon → Utterance → World → ℚ
  /-- Goal projection: are two worlds equivalent under this goal/QUD? -/
  goalProject : Goal → World → World → Bool
  /-- Speaker's credence: P_speaker(w | a). -/
  speakerCredence : BeliefState → World → ℚ := fun _ _ => 1

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

  /-- Utterance cost function. -/
  cost : Utterance → ℚ := fun _ => 0

  /-- Fintype instances -/
  [uttFintype : Fintype Utterance]
  [worldFintype : Fintype World]
  [interpFintype : Fintype Interp]
  [lexiconFintype : Fintype Lexicon]
  [beliefStateFintype : Fintype BeliefState]
  [goalFintype : Fintype Goal]

  /-- DecidableEq instances -/
  [uttDecEq : DecidableEq Utterance]
  [worldDecEq : DecidableEq World]
  [interpDecEq : DecidableEq Interp]
  [lexiconDecEq : DecidableEq Lexicon]
  [beliefStateDecEq : DecidableEq BeliefState]
  [goalDecEq : DecidableEq Goal]

attribute [instance] RSAScenarioF.uttFintype RSAScenarioF.worldFintype
  RSAScenarioF.interpFintype RSAScenarioF.lexiconFintype
  RSAScenarioF.beliefStateFintype RSAScenarioF.goalFintype
  RSAScenarioF.uttDecEq RSAScenarioF.worldDecEq
  RSAScenarioF.interpDecEq RSAScenarioF.lexiconDecEq
  RSAScenarioF.beliefStateDecEq RSAScenarioF.goalDecEq

-- ============================================================================
-- Smart Constructors for RSAScenarioF
-- ============================================================================

/--
Build a basic Fintype RSA scenario (no interpretation ambiguity, no QUD).
-/
def RSAScenarioF.basic {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (φ : U → W → ℚ)
    (prior : W → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenarioF where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := Unit
  φ _ _ u w := φ u w
  goalProject _ w w' := w == w'
  speakerCredence _ _ := 1
  worldPrior := prior
  interpPrior := fun _ => 1
  lexiconPrior := fun _ => 1
  beliefStatePrior := fun _ => 1
  goalPrior := fun _ => 1
  α := α
  cost := cost

/--
Build a basic Fintype RSA scenario from Boolean semantics.
-/
def RSAScenarioF.basicBool {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (satisfies : W → U → Bool)
    (prior : W → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenarioF :=
  RSAScenarioF.basic (fun u w => boolToRat (satisfies w u)) prior α cost

/--
Build a Fintype scenario with interpretation ambiguity (e.g., scope readings).
-/
def RSAScenarioF.ambiguous {U W I : Type}
    [Fintype U] [Fintype W] [Fintype I]
    [DecidableEq U] [DecidableEq W] [DecidableEq I]
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenarioF where
  Utterance := U
  World := W
  Interp := I
  Lexicon := Unit
  BeliefState := Unit
  Goal := Unit
  φ i _ u w := φ i u w
  goalProject _ w w' := w == w'
  speakerCredence _ _ := 1
  worldPrior := worldPrior
  interpPrior := interpPrior
  lexiconPrior := fun _ => 1
  beliefStatePrior := fun _ => 1
  goalPrior := fun _ => 1
  α := α
  cost := cost

/--
Build a Fintype scenario with interpretation ambiguity from Boolean semantics.
-/
def RSAScenarioF.ambiguousBool {U W I : Type}
    [Fintype U] [Fintype W] [Fintype I]
    [DecidableEq U] [DecidableEq W] [DecidableEq I]
    (satisfies : I → W → U → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenarioF :=
  RSAScenarioF.ambiguous (fun i u w => boolToRat (satisfies i w u)) worldPrior interpPrior α cost

/--
Build a Fintype QUD-sensitive scenario.
-/
def RSAScenarioF.qud {U W Q : Type}
    [Fintype U] [Fintype W] [Fintype Q]
    [DecidableEq U] [DecidableEq W] [DecidableEq Q]
    (φ : U → W → ℚ)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (qudPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenarioF where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := Unit
  BeliefState := Unit
  Goal := Q
  φ _ _ u w := φ u w
  goalProject := qudProject
  speakerCredence _ _ := 1
  worldPrior := worldPrior
  interpPrior := fun _ => 1
  lexiconPrior := fun _ => 1
  beliefStatePrior := fun _ => 1
  goalPrior := qudPrior
  α := α
  cost := cost

/--
Build a Fintype QUD-sensitive scenario from Boolean semantics.
-/
def RSAScenarioF.qudBool {U W Q : Type}
    [Fintype U] [Fintype W] [Fintype Q]
    [DecidableEq U] [DecidableEq W] [DecidableEq Q]
    (satisfies : W → U → Bool)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (qudPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenarioF :=
  RSAScenarioF.qud (fun u w => boolToRat (satisfies w u)) qudProject worldPrior qudPrior α cost

/--
Build a Fintype scenario with mental state inference.
-/
def RSAScenarioF.mentalState {U W A Q : Type}
    [Fintype U] [Fintype W] [Fintype A] [Fintype Q]
    [DecidableEq U] [DecidableEq W] [DecidableEq A] [DecidableEq Q]
    (φ : U → W → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (beliefStatePrior : A → ℚ := fun _ => 1)
    (goalPrior : Q → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenarioF where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := Unit
  BeliefState := A
  Goal := Q
  φ _ _ := φ
  goalProject := goalProject
  speakerCredence := speakerCredence
  worldPrior := worldPrior
  interpPrior := fun _ => 1
  lexiconPrior := fun _ => 1
  beliefStatePrior := beliefStatePrior
  goalPrior := goalPrior
  α := α
  cost := cost

/--
Build a Fintype scenario with lexical uncertainty.
-/
def RSAScenarioF.lexicalUncertainty {U W L : Type}
    [Fintype U] [Fintype W] [Fintype L]
    [DecidableEq U] [DecidableEq W] [DecidableEq L]
    (φ : L → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (lexiconPrior : L → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0) : RSAScenarioF where
  Utterance := U
  World := W
  Interp := Unit
  Lexicon := L
  BeliefState := Unit
  Goal := Unit
  φ _ l u w := φ l u w
  goalProject _ w w' := w == w'
  speakerCredence _ _ := 1
  worldPrior := worldPrior
  interpPrior := fun _ => 1
  lexiconPrior := lexiconPrior
  beliefStatePrior := fun _ => 1
  goalPrior := fun _ => 1
  α := α
  cost := cost

-- ============================================================================
-- RSAF: Fintype-Based RSA Computations
-- ============================================================================

namespace RSAF

variable (S : RSAScenarioF)

/-- Helper: sum scores over Fintype -/
private def sumScores (scores : S.World → ℚ) : ℚ :=
  ∑ w : S.World, scores w

/-- Helper: try to normalize scores to ExactDist -/
private def tryNormalize {α : Type*} [Fintype α]
    (scores : α → ℚ) (hnonneg : ∀ x, 0 ≤ scores x) : Option (ExactDist α) :=
  ExactDist.tryNormalize scores hnonneg

-- ============================================================================
-- L0: Literal Listener
-- ============================================================================

/--
L0: Literal listener distribution given full context.

Returns None if no world is compatible with the utterance.
-/
def L0 (u : S.Utterance)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (_q : S.Goal)
    : Option (ExactDist S.World) :=
  let scores := fun w => S.worldPrior w * S.φ i l u w * S.speakerCredence a w
  let hnonneg : ∀ w, 0 ≤ scores w := fun w => by
    apply mul_nonneg
    apply mul_nonneg
    · sorry -- worldPrior nonneg (TODO: add as field constraint)
    · sorry -- φ nonneg
    · sorry -- speakerCredence nonneg
  tryNormalize scores hnonneg

/--
L0 projected by Goal/QUD.
-/
def L0_projected (u : S.Utterance)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist S.World) :=
  match L0 S u i l a q with
  | none => none
  | some l0 =>
    let scores := fun w =>
      ∑ w' : S.World, if S.goalProject q w w' then l0.mass w' else 0
    let hnonneg : ∀ w, 0 ≤ scores w := fun _ => by
      apply Finset.sum_nonneg
      intro w' _
      split_ifs
      · exact l0.nonneg w'
      · exact le_refl 0
    tryNormalize scores hnonneg

-- ============================================================================
-- S1: Pragmatic Speaker
-- ============================================================================

/--
S1: Pragmatic speaker distribution.

Returns None if no utterance is available.
-/
def S1 (w : S.World)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist S.Utterance) :=
  let scores := fun u =>
    let truthful := S.φ i l u w
    let l0Score : ℚ := match L0_projected S u i l a q with
      | some d => d.mass w
      | none => 0
    let costDiscount : ℚ := 1 / ((1 + S.cost u) ^ S.α)
    truthful * (l0Score ^ S.α : ℚ) * costDiscount
  let hnonneg : ∀ u, 0 ≤ scores u := fun _ => by
    sorry
  tryNormalize scores hnonneg

-- ============================================================================
-- L1: Pragmatic Listener
-- ============================================================================

/--
L1 marginal over worlds.
-/
def L1_world (u : S.Utterance) : Option (ExactDist S.World) :=
  let scores := fun w =>
    ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ a : S.BeliefState, ∑ q : S.Goal,
      let priorScore := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                        S.beliefStatePrior a * S.goalPrior q
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      priorScore * s1Score
  let hnonneg : ∀ w, 0 ≤ scores w := fun _ => by
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    sorry -- prior * s1Score nonneg
  tryNormalize scores hnonneg

/--
L1 marginal over interpretations.
-/
def L1_interp (u : S.Utterance) : Option (ExactDist S.Interp) :=
  let scores := fun i =>
    ∑ w : S.World, ∑ l : S.Lexicon, ∑ a : S.BeliefState, ∑ q : S.Goal,
      let priorScore := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                        S.beliefStatePrior a * S.goalPrior q
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      priorScore * s1Score
  let hnonneg : ∀ i, 0 ≤ scores i := fun _ => by
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    sorry
  tryNormalize scores hnonneg

/--
L1 marginal over belief states.
-/
def L1_beliefState (u : S.Utterance) : Option (ExactDist S.BeliefState) :=
  let scores := fun a =>
    ∑ w : S.World, ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ q : S.Goal,
      let priorScore := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                        S.beliefStatePrior a * S.goalPrior q
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      priorScore * s1Score
  let hnonneg : ∀ a, 0 ≤ scores a := fun _ => by
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    sorry
  tryNormalize scores hnonneg

/--
L1 marginal over goals/QUDs.
-/
def L1_goal (u : S.Utterance) : Option (ExactDist S.Goal) :=
  let scores := fun q =>
    ∑ w : S.World, ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ a : S.BeliefState,
      let priorScore := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                        S.beliefStatePrior a * S.goalPrior q
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      priorScore * s1Score
  let hnonneg : ∀ q, 0 ≤ scores q := fun _ => by
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    sorry
  tryNormalize scores hnonneg

-- ============================================================================
-- L1 Given Goal (for BToM models)
-- ============================================================================

/--
L1 marginal over worlds given a FIXED Goal.
-/
def L1_world_givenGoal (u : S.Utterance) (q : S.Goal)
    : Option (ExactDist S.World) :=
  let scores := fun w =>
    ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ a : S.BeliefState,
      let credence := S.speakerCredence a w
      let prior := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                   S.beliefStatePrior a
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      prior * credence * s1Score
  let hnonneg : ∀ w, 0 ≤ scores w := fun _ => by
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    sorry
  tryNormalize scores hnonneg

/--
L1 marginal over belief states given a FIXED Goal.
-/
def L1_beliefState_givenGoal (u : S.Utterance) (q : S.Goal)
    : Option (ExactDist S.BeliefState) :=
  let scores := fun a =>
    ∑ w : S.World, ∑ i : S.Interp, ∑ l : S.Lexicon,
      let credence := S.speakerCredence a w
      let prior := S.worldPrior w * S.interpPrior i * S.lexiconPrior l *
                   S.beliefStatePrior a
      let s1Score := match S1 S w i l a q with
        | some d => d.mass u
        | none => 0
      prior * credence * s1Score
  let hnonneg : ∀ a, 0 ≤ scores a := fun _ => by
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    apply Finset.sum_nonneg; intro _ _
    sorry
  tryNormalize scores hnonneg

-- ============================================================================
-- S2: Second-Level Pragmatic Speaker
-- ============================================================================

/--
S2: Second-level pragmatic speaker.
-/
def S2 (w : S.World) : Option (ExactDist S.Utterance) :=
  let scores := fun u =>
    let l1Score : ℚ := match L1_world S u with
      | some d => d.mass w
      | none => 0
    (l1Score ^ S.α : ℚ)
  let hnonneg : ∀ u, 0 ≤ scores u := fun _ => by sorry
  tryNormalize scores hnonneg

end RSAF

-- ============================================================================
-- Conversion: RSAScenario ↔ RSAScenarioF
-- ============================================================================

/--
Convert RSAScenarioF to RSAScenario (for compatibility with List-based functions).
-/
noncomputable def RSAScenarioF.toRSAScenario (S : RSAScenarioF) : RSAScenario where
  Utterance := S.Utterance
  World := S.World
  Interp := S.Interp
  Lexicon := S.Lexicon
  BeliefState := S.BeliefState
  Goal := S.Goal
  φ := S.φ
  goalProject := S.goalProject
  speakerCredence := S.speakerCredence
  utterances := Fintype.elems.toList
  worlds := Fintype.elems.toList
  interps := Fintype.elems.toList
  lexica := Fintype.elems.toList
  beliefStates := Fintype.elems.toList
  goals := Fintype.elems.toList
  worldPrior := S.worldPrior
  interpPrior := S.interpPrior
  lexiconPrior := S.lexiconPrior
  beliefStatePrior := S.beliefStatePrior
  goalPrior := S.goalPrior
  α := S.α
  cost := S.cost

/-- Coercion from RSAScenarioF to RSAScenario -/
noncomputable instance : Coe RSAScenarioF RSAScenario where
  coe := RSAScenarioF.toRSAScenario

