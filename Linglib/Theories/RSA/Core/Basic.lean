/-
# Linglib.Core.RSA

Core RSA (Rational Speech Acts) infrastructure.

## Architecture

RSA uses exact rational arithmetic (ℚ) for all probability computations.
This enables mathematical proofs about pragmatic reasoning.

### Key Type

- `RSAScenario`: Fintype-based scenario with compile-time guarantees

### RSA Model

RSA models communication as recursive reasoning between speakers and listeners:
- L0: Literal interpretation (semantic denotation)
- S1: Pragmatic speaker (chooses utterances to maximize informativity)
- L1: Pragmatic listener (reasons about what speaker meant)
- S2: Second-level pragmatic speaker

### Namespace

- `RSA`: Core RSA computations returning `Option (ExactDist α)`

For `#eval` demonstrations, use `RSA.Eval` which provides list-based helpers.

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
-- RSAScenario: Fintype-Based Unified Type (Primary API)
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
- Includes non-negativity proofs for all weight functions

## Example

```lean
def myScenario : RSAScenario where
  Utterance := MyUtterance
  World := MyWorld
  φ := fun _ _ u w => if myMeaning u w then 1 else 0
  goalProject := fun _ w w' => w == w'
```
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

  /-- Non-negativity constraints for probability functions -/
  φ_nonneg : ∀ i l u w, 0 ≤ φ i l u w := by intros; decide
  worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide
  interpPrior_nonneg : ∀ i, 0 ≤ interpPrior i := by intros; decide
  lexiconPrior_nonneg : ∀ l, 0 ≤ lexiconPrior l := by intros; decide
  beliefStatePrior_nonneg : ∀ a, 0 ≤ beliefStatePrior a := by intros; decide
  goalPrior_nonneg : ∀ q, 0 ≤ goalPrior q := by intros; decide
  speakerCredence_nonneg : ∀ a w, 0 ≤ speakerCredence a w := by intros; decide
  cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide

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

attribute [instance] RSAScenario.uttFintype RSAScenario.worldFintype
  RSAScenario.interpFintype RSAScenario.lexiconFintype
  RSAScenario.beliefStateFintype RSAScenario.goalFintype
  RSAScenario.uttDecEq RSAScenario.worldDecEq
  RSAScenario.interpDecEq RSAScenario.lexiconDecEq
  RSAScenario.beliefStateDecEq RSAScenario.goalDecEq

-- ============================================================================
-- Smart Constructors for RSAScenario
-- ============================================================================

/--
Build a basic Fintype RSA scenario (no interpretation ambiguity, no QUD).
-/
def RSAScenario.basic {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (φ : U → W → ℚ)
    (φ_nonneg : ∀ u w, 0 ≤ φ u w := by intros; decide)
    (prior : W → ℚ := fun _ => 1)
    (prior_nonneg : ∀ w, 0 ≤ prior w := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide) : RSAScenario where
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
  φ_nonneg := fun _ _ u w => φ_nonneg u w
  worldPrior_nonneg := prior_nonneg
  interpPrior_nonneg := fun _ => le_refl 0 |> fun _ => by decide
  lexiconPrior_nonneg := fun _ => le_refl 0 |> fun _ => by decide
  beliefStatePrior_nonneg := fun _ => le_refl 0 |> fun _ => by decide
  goalPrior_nonneg := fun _ => le_refl 0 |> fun _ => by decide
  speakerCredence_nonneg := fun _ _ => le_refl 0 |> fun _ => by decide
  cost_nonneg := cost_nonneg

/--
Build a basic Fintype RSA scenario from Boolean semantics.
-/
def RSAScenario.basicBool {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (satisfies : W → U → Bool)
    (prior : W → ℚ := fun _ => 1)
    (prior_nonneg : ∀ w, 0 ≤ prior w := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide) : RSAScenario :=
  RSAScenario.basic (fun u w => boolToRat (satisfies w u))
    (fun _ _ => by simp only [boolToRat]; split_ifs <;> decide)
    prior prior_nonneg α cost cost_nonneg

/--
Build a Fintype scenario with interpretation ambiguity (e.g., scope readings).
-/
def RSAScenario.ambiguous {U W I : Type}
    [Fintype U] [Fintype W] [Fintype I]
    [DecidableEq U] [DecidableEq W] [DecidableEq I]
    (φ : I → U → W → ℚ)
    (φ_nonneg : ∀ i u w, 0 ≤ φ i u w := by intros; decide)
    (worldPrior : W → ℚ := fun _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (interpPrior : I → ℚ := fun _ => 1)
    (interpPrior_nonneg : ∀ i, 0 ≤ interpPrior i := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide) : RSAScenario where
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
  φ_nonneg := fun i _ u w => φ_nonneg i u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := interpPrior_nonneg
  lexiconPrior_nonneg := fun _ => by decide
  beliefStatePrior_nonneg := fun _ => by decide
  goalPrior_nonneg := fun _ => by decide
  speakerCredence_nonneg := fun _ _ => by decide
  cost_nonneg := cost_nonneg

/--
Build a Fintype scenario with interpretation ambiguity from Boolean semantics.
-/
def RSAScenario.ambiguousBool {U W I : Type}
    [Fintype U] [Fintype W] [Fintype I]
    [DecidableEq U] [DecidableEq W] [DecidableEq I]
    (satisfies : I → W → U → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (interpPrior : I → ℚ := fun _ => 1)
    (interpPrior_nonneg : ∀ i, 0 ≤ interpPrior i := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide) : RSAScenario :=
  RSAScenario.ambiguous (fun i u w => boolToRat (satisfies i w u))
    (fun _ _ _ => by simp only [boolToRat]; split_ifs <;> decide)
    worldPrior worldPrior_nonneg interpPrior interpPrior_nonneg α cost cost_nonneg

/--
Build a Fintype QUD-sensitive scenario.
-/
def RSAScenario.qud {U W Q : Type}
    [Fintype U] [Fintype W] [Fintype Q]
    [DecidableEq U] [DecidableEq W] [DecidableEq Q]
    (φ : U → W → ℚ)
    (φ_nonneg : ∀ u w, 0 ≤ φ u w := by intros; decide)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (qudPrior : Q → ℚ := fun _ => 1)
    (qudPrior_nonneg : ∀ q, 0 ≤ qudPrior q := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide) : RSAScenario where
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
  φ_nonneg := fun _ _ u w => φ_nonneg u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := fun _ => by decide
  lexiconPrior_nonneg := fun _ => by decide
  beliefStatePrior_nonneg := fun _ => by decide
  goalPrior_nonneg := qudPrior_nonneg
  speakerCredence_nonneg := fun _ _ => by decide
  cost_nonneg := cost_nonneg

/--
Build a Fintype QUD-sensitive scenario from Boolean semantics.
-/
def RSAScenario.qudBool {U W Q : Type}
    [Fintype U] [Fintype W] [Fintype Q]
    [DecidableEq U] [DecidableEq W] [DecidableEq Q]
    (satisfies : W → U → Bool)
    (qudProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (qudPrior : Q → ℚ := fun _ => 1)
    (qudPrior_nonneg : ∀ q, 0 ≤ qudPrior q := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide) : RSAScenario :=
  RSAScenario.qud (fun u w => boolToRat (satisfies w u))
    (fun _ _ => by simp only [boolToRat]; split_ifs <;> decide)
    qudProject worldPrior worldPrior_nonneg qudPrior qudPrior_nonneg α cost cost_nonneg

/--
Build a Fintype scenario with mental state inference.
-/
def RSAScenario.mentalState {U W A Q : Type}
    [Fintype U] [Fintype W] [Fintype A] [Fintype Q]
    [DecidableEq U] [DecidableEq W] [DecidableEq A] [DecidableEq Q]
    (φ : U → W → ℚ)
    (φ_nonneg : ∀ u w, 0 ≤ φ u w := by intros; decide)
    (speakerCredence : A → W → ℚ)
    (speakerCredence_nonneg : ∀ a w, 0 ≤ speakerCredence a w := by intros; decide)
    (goalProject : Q → W → W → Bool)
    (worldPrior : W → ℚ := fun _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (beliefStatePrior : A → ℚ := fun _ => 1)
    (beliefStatePrior_nonneg : ∀ a, 0 ≤ beliefStatePrior a := by intros; decide)
    (goalPrior : Q → ℚ := fun _ => 1)
    (goalPrior_nonneg : ∀ q, 0 ≤ goalPrior q := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide) : RSAScenario where
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
  φ_nonneg := fun _ _ u w => φ_nonneg u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := fun _ => by decide
  lexiconPrior_nonneg := fun _ => by decide
  beliefStatePrior_nonneg := beliefStatePrior_nonneg
  goalPrior_nonneg := goalPrior_nonneg
  speakerCredence_nonneg := speakerCredence_nonneg
  cost_nonneg := cost_nonneg

/--
Build a Fintype scenario with lexical uncertainty.
-/
def RSAScenario.lexicalUncertainty {U W L : Type}
    [Fintype U] [Fintype W] [Fintype L]
    [DecidableEq U] [DecidableEq W] [DecidableEq L]
    (φ : L → U → W → ℚ)
    (φ_nonneg : ∀ l u w, 0 ≤ φ l u w := by intros; decide)
    (worldPrior : W → ℚ := fun _ => 1)
    (worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide)
    (lexiconPrior : L → ℚ := fun _ => 1)
    (lexiconPrior_nonneg : ∀ l, 0 ≤ lexiconPrior l := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide) : RSAScenario where
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
  φ_nonneg := fun _ l u w => φ_nonneg l u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := fun _ => by decide
  lexiconPrior_nonneg := lexiconPrior_nonneg
  beliefStatePrior_nonneg := fun _ => by decide
  goalPrior_nonneg := fun _ => by decide
  speakerCredence_nonneg := fun _ _ => by decide
  cost_nonneg := cost_nonneg

-- ============================================================================
-- RSAF: Fintype-Based RSA Computations
-- ============================================================================

namespace RSA

variable (S : RSAScenario)

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
  let hnonneg : ∀ w, 0 ≤ scores w := fun w =>
    mul_nonneg (mul_nonneg (S.worldPrior_nonneg w) (S.φ_nonneg i l u w)) (S.speakerCredence_nonneg a w)
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
  let hnonneg : ∀ u, 0 ≤ scores u := fun u => by
    apply mul_nonneg
    apply mul_nonneg
    · exact S.φ_nonneg i l u w
    · apply pow_nonneg
      cases h : L0_projected S u i l a q with
      | none => simp
      | some d => exact d.nonneg w
    · apply div_nonneg (by norm_num : (0 : ℚ) ≤ 1)
      apply pow_nonneg
      have := S.cost_nonneg u
      linarith
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
  let hnonneg : ∀ w, 0 ≤ scores w := fun w => by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro a _
    apply Finset.sum_nonneg; intro q _
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
      · exact S.goalPrior_nonneg q
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
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
  let hnonneg : ∀ i, 0 ≤ scores i := fun i => by
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro a _
    apply Finset.sum_nonneg; intro q _
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
      · exact S.goalPrior_nonneg q
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
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
  let hnonneg : ∀ a, 0 ≤ scores a := fun a => by
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro q _
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
      · exact S.goalPrior_nonneg q
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
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
  let hnonneg : ∀ q, 0 ≤ scores q := fun q => by
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro a _
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
      · exact S.goalPrior_nonneg q
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
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
  let hnonneg : ∀ w, 0 ≤ scores w := fun w => by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply Finset.sum_nonneg; intro a _
    apply mul_nonneg
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
    · exact S.speakerCredence_nonneg a w
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
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
  let hnonneg : ∀ a, 0 ≤ scores a := fun a => by
    apply Finset.sum_nonneg; intro w _
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro l _
    apply mul_nonneg
    apply mul_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      · exact S.worldPrior_nonneg w
      · exact S.interpPrior_nonneg i
      · exact S.lexiconPrior_nonneg l
      · exact S.beliefStatePrior_nonneg a
    · exact S.speakerCredence_nonneg a w
    · cases h : S1 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
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
  let hnonneg : ∀ u, 0 ≤ scores u := fun u => by
    apply pow_nonneg
    cases h : L1_world S u with
    | none => simp
    | some d => exact d.nonneg w
  tryNormalize scores hnonneg

end RSA

