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
import Mathlib.Data.FinEnum
import Linglib.Core.Distribution

-- Chain Variant

/--
RSA chain variant: which literal agent is the base of the recursion.

- `L0Based`: L0 → S1 → L1 → S2 → ... (standard RSA, literal listener base)
- `S0Based`: S0 → L1 → S1 → L2 → ... (literal speaker base)

The standard RSA chain is L0-based.
S0-based chains are used when modeling speaker production data (e.g., van Tiel et al. 2021).
-/
inductive RSA.ChainVariant
  | L0Based  -- L0 → S1 → L1 (literal listener base, standard)
  | S0Based  -- S0 → L1 → S1 (literal speaker base)
  deriving Repr, DecidableEq, BEq, Inhabited

instance : ToString RSA.ChainVariant where
  toString
    | .L0Based => "L0-based (L0→S1→L1)"
    | .S0Based => "S0-based (S0→L1→S1)"

-- Utility Functions

/-- Convert Bool to ℚ (1 if true, 0 if false) -/
def boolToRat (b : Bool) : ℚ := if b then 1 else 0

-- RSAScenario: Fintype-Based Unified Type (Primary API)

/--
Parametric RSA scenario for compile-time type safety and clean inference.

U (Utterance) and W (World) are explicit type parameters, enabling:
- Clean type inference without explicit type witnesses
- Simpler eval methods: `scenario.evalL1 .myUtterance`
- Compile-time completeness proofs via Fintype constraints
- Type-safe distribution operations via ExactDist

Latent types (Interp, Lexicon, BeliefState, Goal) remain as fields with
Unit defaults, since most scenarios don't use them.

## Example

```lean
def scenario : RSAScenario CausalExpression CausalWorld :=
  RSAScenario.basicBool (satisfies := fun w u => expressionMeaning w u)

-- Clean eval without type annotations
#eval scenario.evalL1 .caused
```
-/
structure RSAScenario (U W : Type) [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W] where
  /-- Type of interpretations (e.g., scope readings). Use Unit for basic models. -/
  Interp : Type := Unit
  /-- Type of lexica (for lexical uncertainty). Use Unit for fixed lexicon. -/
  Lexicon : Type := Unit
  /-- Type of speaker's belief states. Use Unit if not modeling. -/
  BeliefState : Type := Unit
  /-- Type of communicative goals/QUDs. Use Unit for non-QUD models. -/
  Goal : Type := Unit

  /-- Agreement function: φ(interp, lexicon, utterance, world) ∈ [0,1] -/
  φ : Interp → Lexicon → U → W → ℚ
  /-- Goal projection: are two worlds equivalent under this goal/QUD? -/
  goalProject : Goal → W → W → Bool
  /-- Speaker's credence: P_speaker(w | a). -/
  speakerCredence : BeliefState → W → ℚ := fun _ _ => 1

  /-- Prior over worlds -/
  worldPrior : W → ℚ := fun _ => 1
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
  cost : U → ℚ := fun _ => 0

  /-- Prior over utterances (salience/accessibility). Used by S0 literal speaker. -/
  utterancePrior : U → ℚ := fun _ => 1

  /-- Non-negativity constraints for probability functions -/
  φ_nonneg : ∀ i l u w, 0 ≤ φ i l u w := by intros; decide
  worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide
  interpPrior_nonneg : ∀ i, 0 ≤ interpPrior i := by intros; decide
  lexiconPrior_nonneg : ∀ l, 0 ≤ lexiconPrior l := by intros; decide
  beliefStatePrior_nonneg : ∀ a, 0 ≤ beliefStatePrior a := by intros; decide
  goalPrior_nonneg : ∀ q, 0 ≤ goalPrior q := by intros; decide
  speakerCredence_nonneg : ∀ a w, 0 ≤ speakerCredence a w := by intros; decide
  cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide
  utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide

  /-- Fintype instances for latent types -/
  [interpFintype : Fintype Interp]
  [lexiconFintype : Fintype Lexicon]
  [beliefStateFintype : Fintype BeliefState]
  [goalFintype : Fintype Goal]

  /-- DecidableEq instances for latent types -/
  [interpDecEq : DecidableEq Interp]
  [lexiconDecEq : DecidableEq Lexicon]
  [beliefStateDecEq : DecidableEq BeliefState]
  [goalDecEq : DecidableEq Goal]

attribute [instance] RSAScenario.interpFintype RSAScenario.lexiconFintype
  RSAScenario.beliefStateFintype RSAScenario.goalFintype
  RSAScenario.interpDecEq RSAScenario.lexiconDecEq
  RSAScenario.beliefStateDecEq RSAScenario.goalDecEq

-- Smart Constructors for RSAScenario

/--
Build a basic RSA scenario (no interpretation ambiguity, no QUD).
-/
def RSAScenario.basic {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (φ : U → W → ℚ)
    (φ_nonneg : ∀ u w, 0 ≤ φ u w := by intros; decide)
    (prior : W → ℚ := fun _ => 1)
    (prior_nonneg : ∀ w, 0 ≤ prior w := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := fun _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
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
  utterancePrior := utterancePrior
  φ_nonneg := fun _ _ u w => φ_nonneg u w
  worldPrior_nonneg := prior_nonneg
  interpPrior_nonneg := fun _ => le_refl 0 |> fun _ => by decide
  lexiconPrior_nonneg := fun _ => le_refl 0 |> fun _ => by decide
  beliefStatePrior_nonneg := fun _ => le_refl 0 |> fun _ => by decide
  goalPrior_nonneg := fun _ => le_refl 0 |> fun _ => by decide
  speakerCredence_nonneg := fun _ _ => le_refl 0 |> fun _ => by decide
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

/--
Build a basic RSA scenario from Boolean semantics.
-/
def RSAScenario.basicBool {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    (satisfies : W → U → Bool)
    (prior : W → ℚ := fun _ => 1)
    (prior_nonneg : ∀ w, 0 ≤ prior w := by intros; decide)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := fun _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W :=
  RSAScenario.basic (fun u w => boolToRat (satisfies w u))
    (fun _ _ => by simp only [boolToRat]; split_ifs <;> decide)
    prior prior_nonneg α cost cost_nonneg utterancePrior utterancePrior_nonneg

/--
Build a scenario with interpretation ambiguity (e.g., scope readings).
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
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := fun _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
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
  utterancePrior := utterancePrior
  φ_nonneg := fun i _ u w => φ_nonneg i u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := interpPrior_nonneg
  lexiconPrior_nonneg := fun _ => by decide
  beliefStatePrior_nonneg := fun _ => by decide
  goalPrior_nonneg := fun _ => by decide
  speakerCredence_nonneg := fun _ _ => by decide
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

/--
Build a scenario with interpretation ambiguity from Boolean semantics.
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
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := fun _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W :=
  RSAScenario.ambiguous (fun i u w => boolToRat (satisfies i w u))
    (fun _ _ _ => by simp only [boolToRat]; split_ifs <;> decide)
    worldPrior worldPrior_nonneg interpPrior interpPrior_nonneg α cost cost_nonneg
    utterancePrior utterancePrior_nonneg

/--
Build a QUD-sensitive scenario.
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
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := fun _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
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
  utterancePrior := utterancePrior
  φ_nonneg := fun _ _ u w => φ_nonneg u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := fun _ => by decide
  lexiconPrior_nonneg := fun _ => by decide
  beliefStatePrior_nonneg := fun _ => by decide
  goalPrior_nonneg := qudPrior_nonneg
  speakerCredence_nonneg := fun _ _ => by decide
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

/--
Build a QUD-sensitive scenario from Boolean semantics.
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
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := fun _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W :=
  RSAScenario.qud (fun u w => boolToRat (satisfies w u))
    (fun _ _ => by simp only [boolToRat]; split_ifs <;> decide)
    qudProject worldPrior worldPrior_nonneg qudPrior qudPrior_nonneg α cost cost_nonneg
    utterancePrior utterancePrior_nonneg

/--
Build a scenario with mental state inference.
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
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := fun _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
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
  utterancePrior := utterancePrior
  φ_nonneg := fun _ _ u w => φ_nonneg u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := fun _ => by decide
  lexiconPrior_nonneg := fun _ => by decide
  beliefStatePrior_nonneg := beliefStatePrior_nonneg
  goalPrior_nonneg := goalPrior_nonneg
  speakerCredence_nonneg := speakerCredence_nonneg
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

/--
Build a scenario with lexical uncertainty.
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
    (cost_nonneg : ∀ u, 0 ≤ cost u := by intros; decide)
    (utterancePrior : U → ℚ := fun _ => 1)
    (utterancePrior_nonneg : ∀ u, 0 ≤ utterancePrior u := by intros; decide)
    : RSAScenario U W where
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
  utterancePrior := utterancePrior
  φ_nonneg := fun _ l u w => φ_nonneg l u w
  worldPrior_nonneg := worldPrior_nonneg
  interpPrior_nonneg := fun _ => by decide
  lexiconPrior_nonneg := lexiconPrior_nonneg
  beliefStatePrior_nonneg := fun _ => by decide
  goalPrior_nonneg := fun _ => by decide
  speakerCredence_nonneg := fun _ _ => by decide
  cost_nonneg := cost_nonneg
  utterancePrior_nonneg := utterancePrior_nonneg

-- RSA: Fintype-Based RSA Computations

namespace RSA

variable {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
variable (S : RSAScenario U W)

/-- Helper: sum scores over Fintype -/
private def sumScores (scores : W → ℚ) : ℚ :=
  ∑ w : W, scores w

/-- Helper: try to normalize scores to ExactDist -/
private def tryNormalize {α : Type*} [Fintype α]
    (scores : α → ℚ) (hnonneg : ∀ x, 0 ≤ scores x) : Option (ExactDist α) :=
  ExactDist.tryNormalize scores hnonneg

-- L0: Literal Listener

/--
L0: Literal listener distribution given full context.

Returns None if no world is compatible with the utterance.
-/
def L0 (u : U)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (_q : S.Goal)
    : Option (ExactDist W) :=
  let scores := fun w => S.worldPrior w * S.φ i l u w * S.speakerCredence a w
  let hnonneg : ∀ w, 0 ≤ scores w := fun w =>
    mul_nonneg (mul_nonneg (S.worldPrior_nonneg w) (S.φ_nonneg i l u w)) (S.speakerCredence_nonneg a w)
  tryNormalize scores hnonneg

/--
L0 projected by Goal/QUD.
-/
def L0_projected (u : U)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist W) :=
  match L0 S u i l a q with
  | none => none
  | some l0 =>
    let scores := fun w =>
      ∑ w' : W, if S.goalProject q w w' then l0.mass w' else 0
    let hnonneg : ∀ w, 0 ≤ scores w := fun _ => by
      apply Finset.sum_nonneg
      intro w' _
      split_ifs
      · exact l0.nonneg w'
      · exact le_refl 0
    tryNormalize scores hnonneg

-- S0: Literal Speaker

/--
S0: Literal speaker distribution given full context.

P(m | w) ∝ utterancePrior(m) · φ(i, l, m, w)

This is the "production-first" alternative to L0 (which is "comprehension-first").
- L0: Given utterance m, infer world w. P(w | m) ∝ Prior(w) · φ(m, w)
- S0: Given world w, choose utterance m. P(m | w) ∝ Salience(m) · φ(m, w)

Returns None if no utterance is true in this world.
-/
def S0 (w : W)
    (i : S.Interp) (l : S.Lexicon) (_a : S.BeliefState) (_q : S.Goal)
    : Option (ExactDist U) :=
  let scores := fun u => S.utterancePrior u * S.φ i l u w
  let hnonneg : ∀ u, 0 ≤ scores u := fun u =>
    mul_nonneg (S.utterancePrior_nonneg u) (S.φ_nonneg i l u w)
  tryNormalize scores hnonneg

/--
L1 from S0: Pragmatic listener reasoning about a literal speaker.

This is an alternative to the standard L1 which reasons about S1.
Use this for production-based models like van Tiel et al. (2021).

P(w | m) ∝ Prior(w) · P_S0(m | w)
-/
def L1_fromS0 (u : U)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist W) :=
  let scores := fun w =>
    let s0Score := match S0 S w i l a q with
      | some d => d.mass u
      | none => 0
    S.worldPrior w * s0Score
  let hnonneg : ∀ w, 0 ≤ scores w := fun w => by
    apply mul_nonneg
    · exact S.worldPrior_nonneg w
    · cases h : S0 S w i l a q with
      | none => simp
      | some d => exact d.nonneg u
  tryNormalize scores hnonneg

-- S1: Pragmatic Speaker

/--
S1: Pragmatic speaker distribution.

Returns None if no utterance is available.
-/
def S1 (w : W)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist U) :=
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

-- L1: Pragmatic Listener

/--
L1 marginal over worlds.
-/
def L1_world (u : U) : Option (ExactDist W) :=
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
def L1_interp (u : U) : Option (ExactDist S.Interp) :=
  let scores := fun i =>
    ∑ w : W, ∑ l : S.Lexicon, ∑ a : S.BeliefState, ∑ q : S.Goal,
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
def L1_beliefState (u : U) : Option (ExactDist S.BeliefState) :=
  let scores := fun a =>
    ∑ w : W, ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ q : S.Goal,
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
def L1_goal (u : U) : Option (ExactDist S.Goal) :=
  let scores := fun q =>
    ∑ w : W, ∑ i : S.Interp, ∑ l : S.Lexicon, ∑ a : S.BeliefState,
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

-- L1 Given Goal (for BToM models)

/--
L1 marginal over worlds given a FIXED Goal.
-/
def L1_world_givenGoal (u : U) (q : S.Goal)
    : Option (ExactDist W) :=
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
def L1_beliefState_givenGoal (u : U) (q : S.Goal)
    : Option (ExactDist S.BeliefState) :=
  let scores := fun a =>
    ∑ w : W, ∑ i : S.Interp, ∑ l : S.Lexicon,
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

-- S2: Second-Level Pragmatic Speaker

/--
S2: Second-level pragmatic speaker.
-/
def S2 (w : W) : Option (ExactDist U) :=
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

-- S1 from L1_fromS0: Pragmatic Speaker via Production-First Chain

/--
S1 based on L1_fromS0: Pragmatic speaker reasoning about a listener who
reasons about a literal speaker.

This completes the production-first chain: S0 → L1_fromS0 → S1_fromL1S0.
Compare with the standard chain: L0 → S1 → L1.

P(m | w) ∝ utterancePrior(m) · P_L1_fromS0(w | m)^α · costDiscount(m)
-/
def S1_fromL1S0 (w : W)
    (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist U) :=
  let scores := fun u =>
    let l1Score : ℚ := match L1_fromS0 S u i l a q with
      | some d => d.mass w
      | none => 0
    let costDiscount : ℚ := 1 / ((1 + S.cost u) ^ S.α)
    S.utterancePrior u * (l1Score ^ S.α : ℚ) * costDiscount
  let hnonneg : ∀ u, 0 ≤ scores u := fun u => by
    apply mul_nonneg
    apply mul_nonneg
    · exact S.utterancePrior_nonneg u
    · apply pow_nonneg
      cases h : L1_fromS0 S u i l a q with
      | none => simp
      | some d => exact d.nonneg w
    · apply div_nonneg (by norm_num : (0 : ℚ) ≤ 1)
      apply pow_nonneg
      have := S.cost_nonneg u
      linarith
  tryNormalize scores hnonneg

-- Unified API with ChainVariant (Primary Interface)

/-!
## Unified Chain API

These functions provide a cleaner interface using `ChainVariant` to select
between production-first and comprehension-first chains.

Default is `.comprehension` (standard RSA: L0 → S1 → L1).
-/

/--
Pragmatic speaker distribution with chain selection.

- `.L0Based` (default): Standard S1 reasoning about L0
- `.S0Based`: S1 reasoning about L1 who reasons about S0
-/
def speaker (chain : ChainVariant := .L0Based)
    (w : W) (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist U) :=
  match chain with
  | .L0Based => S1 S w i l a q
  | .S0Based => S1_fromL1S0 S w i l a q

/--
Pragmatic listener distribution over worlds with chain selection.

- `.L0Based` (default): Standard L1 marginalizing over all latent variables
- `.S0Based`: L1 reasoning about S0 with specified latent variables
-/
def listener (chain : ChainVariant := .L0Based)
    (u : U) (i : S.Interp) (l : S.Lexicon) (a : S.BeliefState) (q : S.Goal)
    : Option (ExactDist W) :=
  match chain with
  | .L0Based => L1_world S u  -- marginalizes over latent variables
  | .S0Based => L1_fromS0 S u i l a q

end RSA

-- FinEnum-Based Eval Bridge (for #eval with RSAScenario)

/-!
## FinEnum-Based Evaluation

These functions provide computable evaluation for RSAScenario when types have
FinEnum instances. This bridges the gap between:
- `RSAScenario` with Fintype (for proofs via ExactDist)
- `RSA.Eval.*` with explicit lists (for `#eval` demonstrations)

### Usage

Add FinEnum instances to your types:
```lean
instance : FinEnum MyUtterance :=
  FinEnum.ofList [.u1, .u2, .u3] (by decide)

instance : FinEnum MyWorld :=
  FinEnum.ofList [.w1, .w2] (by decide)
```

Then use the eval methods directly on your scenario:
```lean
#eval myScenario.evalL1 .u1
```

This eliminates the need to define separate `allUtterances`/`allWorlds` lists
and call `RSA.Eval.basicL1` manually.
-/

namespace RSAScenario

variable {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]

/-- Get list of all utterances via FinEnum -/
def allUtterances (s : RSAScenario U W) [FinEnum U] : List U :=
  FinEnum.toList U

/-- Get list of all worlds via FinEnum -/
def allWorlds (s : RSAScenario U W) [FinEnum W] : List W :=
  FinEnum.toList W

/-- Get list of all interpretations via FinEnum -/
def allInterps (s : RSAScenario U W) [FinEnum s.Interp] : List s.Interp :=
  FinEnum.toList s.Interp

/-- Get list of all lexica via FinEnum -/
def allLexica (s : RSAScenario U W) [FinEnum s.Lexicon] : List s.Lexicon :=
  FinEnum.toList s.Lexicon

/-- Get list of all belief states via FinEnum -/
def allBeliefStates (s : RSAScenario U W) [FinEnum s.BeliefState] : List s.BeliefState :=
  FinEnum.toList s.BeliefState

/-- Get list of all goals via FinEnum -/
def allGoals (s : RSAScenario U W) [FinEnum s.Goal] : List s.Goal :=
  FinEnum.toList s.Goal

-- List-based helpers (inlined to avoid circular import with RSA.Eval)

private def sumScores (scores : List ℚ) : ℚ :=
  scores.foldl (· + ·) 0

private def getScore {α : Type} [BEq α] (dist : List (α × ℚ)) (x : α) : ℚ :=
  match dist.find? (·.1 == x) with
  | some (_, s) => s
  | none => 0

private def normalize {α : Type} (dist : List (α × ℚ)) : List (α × ℚ) :=
  let total := sumScores (dist.map (·.2))
  dist.map fun (x, s) =>
    (x, if total ≠ 0 then s / total else 0)

private def L0_projected' {U W : Type} [BEq W]
    (_utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ)
    (u : U)
    : List (W × ℚ) :=
  let scores := worlds.map fun w => (w, worldPrior w * φ u w)
  normalize scores

private def S1' {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ)
    (cost : U → ℚ)
    (α : ℕ)
    (w : W)
    : List (U × ℚ) :=
  let scores := utterances.map fun u =>
    let truthful := φ u w
    let l0Score := getScore (L0_projected' utterances worlds φ worldPrior u) w
    let costDiscount := 1 / ((1 + cost u) ^ α)
    (u, truthful * l0Score ^ α * costDiscount)
  normalize scores

private def L1_world' {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    : List (W × ℚ) :=
  let scores := worlds.map fun w =>
    let s1 := S1' utterances worlds φ worldPrior cost α w
    let s1Score := getScore s1 u
    (w, worldPrior w * s1Score)
  normalize scores

-- Eval Methods for RSAScenario (Basic: Interp/Lexicon/BeliefState/Goal = Unit)

/--
Run L0 (literal listener) and return as list.

For basic scenarios where Interp, Lexicon, BeliefState, and Goal are all Unit.
Requires FinEnum instances for U and W.

## Example
```lean
#eval scenario.evalL0 .caused
```
-/
def evalL0 (s : RSAScenario U W)
    [FinEnum U] [FinEnum W]
    [BEq W]
    (u : U)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (_ha : s.BeliefState = Unit := by rfl)
    (_hg : s.Goal = Unit := by rfl)
    : List (W × ℚ) :=
  let φ := fun u w => s.φ (hi ▸ ()) (hl ▸ ()) u w
  L0_projected' s.allUtterances s.allWorlds φ s.worldPrior u

/--
Run S1 (pragmatic speaker) and return as list.

For basic scenarios where Interp, Lexicon, BeliefState, and Goal are all Unit.
Requires FinEnum instances for U and W.

## Example
```lean
#eval scenario.evalS1 world_full
```
-/
def evalS1 (s : RSAScenario U W)
    [FinEnum U] [FinEnum W]
    [BEq U] [BEq W]
    (w : W)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (_ha : s.BeliefState = Unit := by rfl)
    (_hg : s.Goal = Unit := by rfl)
    : List (U × ℚ) :=
  let φ := fun u w => s.φ (hi ▸ ()) (hl ▸ ()) u w
  S1' s.allUtterances s.allWorlds φ s.worldPrior s.cost s.α w

/--
Run L1 (pragmatic listener) and return as list.

For basic scenarios where Interp, Lexicon, BeliefState, and Goal are all Unit.
Requires FinEnum instances for U and W.

## Example
```lean
#eval scenario.evalL1 .caused
```
-/
def evalL1 (s : RSAScenario U W)
    [FinEnum U] [FinEnum W]
    [BEq U] [BEq W]
    (u : U)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (_ha : s.BeliefState = Unit := by rfl)
    (_hg : s.Goal = Unit := by rfl)
    : List (W × ℚ) :=
  let φ := fun u w => s.φ (hi ▸ ()) (hl ▸ ()) u w
  L1_world' s.allUtterances s.allWorlds φ s.worldPrior s.cost s.α u

end RSAScenario

-- Top-level FinEnum Eval Functions (simpler API)

/-!
## Top-level Eval Functions

These functions provide an additional API for basic RSA scenarios.
With the new parametric RSAScenario, the cleanest approach is to use
the scenario methods directly: `scenario.evalL1 .myUtterance`.

These top-level functions are kept for backward compatibility but
are rarely needed with the new parametric design.
-/

namespace RSA

/--
Run L0 for a basic scenario.

## Example
```lean
def runL0 (u : MyUtt) := RSA.evalL0 scenario u
```
-/
def evalL0 {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    [FinEnum U] [FinEnum W] [BEq W]
    (s : RSAScenario U W)
    (u : U)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (ha : s.BeliefState = Unit := by rfl)
    (hg : s.Goal = Unit := by rfl)
    : List (W × ℚ) :=
  s.evalL0 u hi hl ha hg

/--
Run S1 for a basic scenario.

## Example
```lean
def runS1 (w : MyWorld) := RSA.evalS1 scenario w
```
-/
def evalS1 {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    [FinEnum U] [FinEnum W] [BEq U] [BEq W]
    (s : RSAScenario U W)
    (w : W)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (ha : s.BeliefState = Unit := by rfl)
    (hg : s.Goal = Unit := by rfl)
    : List (U × ℚ) :=
  s.evalS1 w hi hl ha hg

/--
Run L1 for a basic scenario.

## Example
```lean
def runL1 (u : MyUtt) := RSA.evalL1 scenario u
```
-/
def evalL1 {U W : Type}
    [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    [FinEnum U] [FinEnum W] [BEq U] [BEq W]
    (s : RSAScenario U W)
    (u : U)
    (hi : s.Interp = Unit := by rfl)
    (hl : s.Lexicon = Unit := by rfl)
    (ha : s.BeliefState = Unit := by rfl)
    (hg : s.Goal = Unit := by rfl)
    : List (W × ℚ) :=
  s.evalL1 u hi hl ha hg

end RSA

