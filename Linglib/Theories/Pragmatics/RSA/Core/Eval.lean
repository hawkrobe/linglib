/-
# RSA Eval Helpers

List-based computation helpers for RSA implementations.

## When to Use This Module vs RSAScenario

### Use `RSAScenario` + `scenario.evalL0/S1/L1` when:

- You have a **fixed scenario** with static semantics and priors
- All latent types are `Unit` (basic RSA with just utterances and worlds)
- You want the cleanest API: `scenario.evalL1 u`

Example:
```lean
def scenario : RSAScenario MyUtterance MyWorld := RSAScenario.basicBool
  (satisfies := λ w u => mySemantics u w)
  (prior := λ _ => 1)
  ...

#eval scenario.evalL1 .someUtterance  -- Clean!
```

### Use `RSA.Eval.*` functions when:

- You have **runtime parameters** (varying priors, alphas, configs)
- You need **latent dimensions** (Interp, Lexicon, BeliefState, Goal)
- You need specialized computations (L1_world, L1_interp, L1_goal, etc.)

Example:
```lean
def runL1 (cfg : MyConfig) (u : Utterance) :=
  RSA.Eval.basicL1 allUtterances allWorlds
    mySemantics cfg.prior cfg.alpha cfg.cost u
```

## Future API Vision

The long-term goal is to extend `RSAScenario` methods to handle latent dimensions:

```lean
-- Current (requires Unit latent types):
scenario.evalL1 u

-- Future (marginalize over latent dimensions):
scenario.evalL1_world u        -- marginalize to World
scenario.evalL1_interp u       -- marginalize to Interp
scenario.evalL1_goal u         -- marginalize to Goal
scenario.evalL1_joint u        -- full joint distribution
```

This would allow scenarios with non-Unit latent types to use the clean API:
```lean
def ambiguousScenario : RSAScenario Utterance World := RSAScenario.ambiguous
  (I := ScopeConfig)
  (φ := scopeSemantics)
  ...

#eval ambiguousScenario.evalL1_world .someUtterance   -- Future!
#eval ambiguousScenario.evalL1_interp .someUtterance  -- Future!
```

## Current Functions

### Basic RSA (no latent dimensions)
- `basicL0`, `basicS0`, `basicS1`, `basicL1` - pass lists, priors, semantics directly

### Full RSA (with latent dimensions)
- `L0`, `S1`, `L1_world`, `L1_interp`, `L1_goal` - explicit enumeration of all dimensions

### QUD-Sensitive RSA
- `qudL1_world` - specialized for Goal/QUD inference

### Utilities
- `normalize`, `marginalize`, `getScore`, `sumScores`
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Mathlib.Data.Rat.Defs

namespace RSA.Eval

-- List-based Utility Functions

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
  dist.map λ (x, s) =>
    (x, if total ≠ 0 then s / total else 0)

/-- Normalization preserves list length. -/
@[simp] theorem normalize_length {α : Type} (dist : List (α × ℚ)) :
    (normalize dist).length = dist.length := by
  simp only [normalize, List.length_map]

/-- Marginalize a joint distribution by projecting onto a component -/
def marginalize {α β : Type} [BEq β] (dist : List (α × ℚ)) (proj : α → β) : List (β × ℚ) :=
  let projected := dist.map λ (x, s) => (proj x, s)
  let uniqueKeys := projected.map (·.1) |>.eraseDups
  uniqueKeys.map λ k =>
    let total := projected.filter (λ (k', _) => k' == k) |>.map (·.2) |> sumScores
    (k, total)

-- List-based RSA Computations

/--
L0: Literal listener distribution (list-based).

For a basic scenario with no latent variables, pass `()` for i, l, a, q.
-/
def L0 {U W I L A Q : Type} [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (speakerCredence : A → W → ℚ)
    (u : U) (i : I) (l : L) (a : A) (_q : Q)
    : List (W × ℚ) :=
  let scores := worlds.map λ w =>
    let semantic := φ i l u w
    let credence := speakerCredence a w
    (w, worldPrior w * semantic * credence)
  normalize scores

/--
L0 projected by Goal/QUD (list-based).
-/
def L0_projected {U W I L A Q : Type} [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (u : U) (i : I) (l : L) (a : A) (q : Q)
    : List (W × ℚ) :=
  let l0 := L0 utterances worlds φ worldPrior speakerCredence u i l a q
  worlds.map λ w =>
    let eqClassScore := l0.filter (λ (w', _) => goalProject q w w') |>.map (·.2) |> sumScores
    (w, eqClassScore)

/--
S0: Literal speaker distribution (list-based).

P(m | w) ∝ utterancePrior(m) · φ(i, l, m, w)

This is the "production-first" alternative to L0.
-/
def S0 {U W I L A Q : Type} [BEq U]
    (utterances : List U) (_worlds : List W)
    (φ : I → L → U → W → ℚ)
    (utterancePrior : U → ℚ)
    (w : W) (i : I) (l : L) (_a : A) (_q : Q)
    : List (U × ℚ) :=
  let scores := utterances.map λ u =>
    (u, utterancePrior u * φ i l u w)
  normalize scores

/--
L1 from S0: Pragmatic listener reasoning about a literal speaker (list-based).

P(w | m) ∝ Prior(w) · P_S0(m | w)
-/
def L1_fromS0 {U W I L A Q : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (utterancePrior : U → ℚ)
    (u : U) (i : I) (l : L) (a : A) (q : Q)
    : List (W × ℚ) :=
  let scores := worlds.map λ w =>
    let s0Dist := S0 utterances worlds φ utterancePrior w i l a q
    let s0Score := getScore s0Dist u
    (w, worldPrior w * s0Score)
  normalize scores

/--
S1: Pragmatic speaker distribution (list-based).
-/
def S1 {U W I L A Q : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (cost : U → ℚ)
    (α : ℕ)
    (w : W) (i : I) (l : L) (a : A) (q : Q)
    : List (U × ℚ) :=
  let scores := utterances.map λ u =>
    let truthful := φ i l u w
    let l0Score := getScore (L0_projected utterances worlds φ worldPrior speakerCredence goalProject u i l a q) w
    let costDiscount := 1 / ((1 + cost u) ^ α)
    (u, truthful * l0Score ^ α * costDiscount)
  normalize scores

/--
L1 marginal over worlds (list-based).
-/
def L1_world {U W I L A Q : Type} [BEq U] [BEq W] [BEq I] [BEq L] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (interps : List I) (lexica : List L)
    (beliefStates : List A) (goals : List Q)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (interpPrior : I → ℚ)
    (lexiconPrior : L → ℚ)
    (beliefStatePrior : A → ℚ)
    (goalPrior : Q → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    : List (W × ℚ) :=
  let tuples := worlds.flatMap λ w =>
    interps.flatMap λ i =>
      lexica.flatMap λ l =>
        beliefStates.flatMap λ a =>
          goals.map λ q => (w, i, l, a, q)
  let scores := tuples.map λ (w, i, l, a, q) =>
    let priorScore := worldPrior w * interpPrior i * lexiconPrior l *
                      beliefStatePrior a * goalPrior q
    let s1 := S1 utterances worlds φ worldPrior speakerCredence goalProject cost α w i l a q
    let s1Score := getScore s1 u
    ((w, i, l, a, q), priorScore * s1Score)
  let normalized := normalize scores
  -- Marginalize over i, l, a, q
  worlds.map λ w =>
    let wScores := normalized.filter (λ ((w', _, _, _, _), _) => w' == w) |>.map (·.2)
    (w, sumScores wScores)

-- Simplified API for Basic Scenarios

/--
Basic L0 for simple scenarios (no interp, lexicon, belief state, goal).
-/
def basicL0 {U W : Type} [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (u : U)
    : List (W × ℚ) :=
  L0 utterances worlds (λ _ _ => φ) worldPrior (λ _ _ => 1) u () () () ()

/--
Basic S0 for simple scenarios (literal speaker).

P(m | w) ∝ utterancePrior(m) · φ(m, w)
-/
def basicS0 {U W : Type} [BEq U]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (utterancePrior : U → ℚ := λ _ => 1)
    (w : W)
    : List (U × ℚ) :=
  S0 utterances worlds (λ _ _ => φ) utterancePrior w () () () ()

/--
Basic L1 from S0 for simple scenarios.

P(w | m) ∝ Prior(w) · P_S0(m | w)
-/
def basicL1_fromS0 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (utterancePrior : U → ℚ := λ _ => 1)
    (u : U)
    : List (W × ℚ) :=
  L1_fromS0 utterances worlds (λ _ _ => φ) worldPrior utterancePrior u () () () ()

/--
Basic S1 for simple scenarios.
-/
def basicS1 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (w : W)
    : List (U × ℚ) :=
  S1 utterances worlds (λ _ _ => φ) worldPrior (λ _ _ => 1)
     (λ _ w w' => w == w') cost α w () () () ()

/--
Basic S1 via production-first chain (S0 → L1_fromS0 → S1_fromL1S0).

P(m | w) ∝ utterancePrior(m) · P_L1_fromS0(w | m)^α · costDiscount(m)
-/
def basicS1_fromL1S0 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (utterancePrior : U → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (w : W)
    : List (U × ℚ) :=
  let scores := utterances.map λ u =>
    let l1Dist := basicL1_fromS0 utterances worlds φ worldPrior utterancePrior u
    let l1Score := getScore l1Dist w
    let costDiscount := 1 / ((1 + cost u) ^ α)
    (u, utterancePrior u * l1Score ^ α * costDiscount)
  normalize scores

/--
Basic L1 for simple scenarios.
-/
def basicL1 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (u : U)
    : List (W × ℚ) :=
  L1_world utterances worlds [()] [()] [()] [()]
    (λ _ _ => φ) worldPrior (λ _ => 1) (λ _ => 1) (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ _ w w' => w == w') cost α u

-- Unified API with ChainVariant

/--
Run S1 (pragmatic speaker) with chain selection.

- `.L0Based` (default): Standard S1 reasoning about L0
- `.S0Based`: S1 reasoning about L1 who reasons about S0
-/
def runS1 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (utterancePrior : U → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (chain : RSA.ChainVariant := .L0Based)
    (w : W)
    : List (U × ℚ) :=
  match chain with
  | .L0Based => basicS1 utterances worlds φ worldPrior α cost w
  | .S0Based => basicS1_fromL1S0 utterances worlds φ worldPrior utterancePrior α cost w

/--
Run L1 (pragmatic listener) with chain selection.

- `.L0Based` (default): Standard L1 reasoning about S1
- `.S0Based`: L1 reasoning about S0
-/
def runL1 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (utterancePrior : U → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (chain : RSA.ChainVariant := .L0Based)
    (u : U)
    : List (W × ℚ) :=
  match chain with
  | .L0Based => basicL1 utterances worlds φ worldPrior α cost u
  | .S0Based => basicL1_fromS0 utterances worlds φ worldPrior utterancePrior u

-- Full Joint and Marginal Distributions

/--
L1 joint distribution over all latent variables (W × I × L × A × Q).
Returns unnormalized then normalized joint scores.
-/
def L1_joint {U W I L A Q : Type} [BEq U] [BEq W] [BEq I] [BEq L] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (interps : List I) (lexica : List L)
    (beliefStates : List A) (goals : List Q)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (interpPrior : I → ℚ)
    (lexiconPrior : L → ℚ)
    (beliefStatePrior : A → ℚ)
    (goalPrior : Q → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    : List ((W × I × L × A × Q) × ℚ) :=
  let tuples := worlds.flatMap λ w =>
    interps.flatMap λ i =>
      lexica.flatMap λ l =>
        beliefStates.flatMap λ a =>
          goals.map λ q => (w, i, l, a, q)
  let scores := tuples.map λ (w, i, l, a, q) =>
    let priorScore := worldPrior w * interpPrior i * lexiconPrior l *
                      beliefStatePrior a * goalPrior q
    let s1 := S1 utterances worlds φ worldPrior speakerCredence goalProject cost α w i l a q
    let s1Score := getScore s1 u
    ((w, i, l, a, q), priorScore * s1Score)
  normalize scores

/--
L1 marginal over interpretations.
-/
def L1_interp {U W I L A Q : Type} [BEq U] [BEq W] [BEq I] [BEq L] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (interps : List I) (lexica : List L)
    (beliefStates : List A) (goals : List Q)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (interpPrior : I → ℚ)
    (lexiconPrior : L → ℚ)
    (beliefStatePrior : A → ℚ)
    (goalPrior : Q → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    : List (I × ℚ) :=
  let joint := L1_joint utterances worlds interps lexica beliefStates goals
    φ worldPrior interpPrior lexiconPrior beliefStatePrior goalPrior
    speakerCredence goalProject cost α u
  marginalize joint (λ (_, i, _, _, _) => i)

/--
L1 marginal over goals/QUDs.
-/
def L1_goal {U W I L A Q : Type} [BEq U] [BEq W] [BEq I] [BEq L] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (interps : List I) (lexica : List L)
    (beliefStates : List A) (goals : List Q)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (interpPrior : I → ℚ)
    (lexiconPrior : L → ℚ)
    (beliefStatePrior : A → ℚ)
    (goalPrior : Q → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    : List (Q × ℚ) :=
  let joint := L1_joint utterances worlds interps lexica beliefStates goals
    φ worldPrior interpPrior lexiconPrior beliefStatePrior goalPrior
    speakerCredence goalProject cost α u
  marginalize joint (λ (_, _, _, _, q) => q)

/--
L1 marginal over lexica.
-/
def L1_lexicon {U W I L A Q : Type} [BEq U] [BEq W] [BEq I] [BEq L] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (interps : List I) (lexica : List L)
    (beliefStates : List A) (goals : List Q)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (interpPrior : I → ℚ)
    (lexiconPrior : L → ℚ)
    (beliefStatePrior : A → ℚ)
    (goalPrior : Q → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    : List (L × ℚ) :=
  let joint := L1_joint utterances worlds interps lexica beliefStates goals
    φ worldPrior interpPrior lexiconPrior beliefStatePrior goalPrior
    speakerCredence goalProject cost α u
  marginalize joint (λ (_, _, l, _, _) => l)

/--
L1 marginal over belief states.
-/
def L1_beliefState {U W I L A Q : Type} [BEq U] [BEq W] [BEq I] [BEq L] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (interps : List I) (lexica : List L)
    (beliefStates : List A) (goals : List Q)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (interpPrior : I → ℚ)
    (lexiconPrior : L → ℚ)
    (beliefStatePrior : A → ℚ)
    (goalPrior : Q → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    : List (A × ℚ) :=
  let joint := L1_joint utterances worlds interps lexica beliefStates goals
    φ worldPrior interpPrior lexiconPrior beliefStatePrior goalPrior
    speakerCredence goalProject cost α u
  marginalize joint (λ (_, _, _, a, _) => a)

-- Conditioned Distributions (given specific Goal/QUD)

/--
L1 world distribution conditioned on a specific goal.
Filters joint to only include the specified goal, then marginalizes.
-/
def L1_world_givenGoal {U W I L A Q : Type} [BEq U] [BEq W] [BEq I] [BEq L] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (interps : List I) (lexica : List L)
    (beliefStates : List A) (goals : List Q)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (interpPrior : I → ℚ)
    (lexiconPrior : L → ℚ)
    (beliefStatePrior : A → ℚ)
    (goalPrior : Q → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    (q : Q)
    : List (W × ℚ) :=
  let joint := L1_joint utterances worlds interps lexica beliefStates goals
    φ worldPrior interpPrior lexiconPrior beliefStatePrior goalPrior
    speakerCredence goalProject cost α u
  -- Filter to only this goal
  let filtered := joint.filter (λ ((_, _, _, _, q'), _) => q' == q)
  -- Renormalize
  let renorm := normalize filtered
  -- Marginalize over w
  marginalize renorm (λ (w, _, _, _, _) => w)

/--
L1 belief state distribution conditioned on a specific goal.
-/
def L1_beliefState_givenGoal {U W I L A Q : Type} [BEq U] [BEq W] [BEq I] [BEq L] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (interps : List I) (lexica : List L)
    (beliefStates : List A) (goals : List Q)
    (φ : I → L → U → W → ℚ)
    (worldPrior : W → ℚ)
    (interpPrior : I → ℚ)
    (lexiconPrior : L → ℚ)
    (beliefStatePrior : A → ℚ)
    (goalPrior : Q → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (cost : U → ℚ)
    (α : ℕ)
    (u : U)
    (q : Q)
    : List (A × ℚ) :=
  let joint := L1_joint utterances worlds interps lexica beliefStates goals
    φ worldPrior interpPrior lexiconPrior beliefStatePrior goalPrior
    speakerCredence goalProject cost α u
  -- Filter to only this goal
  let filtered := joint.filter (λ ((_, _, _, _, q'), _) => q' == q)
  -- Renormalize
  let renorm := normalize filtered
  -- Marginalize over belief states
  marginalize renorm (λ (_, _, _, a, _) => a)

-- Simplified APIs for Common Scenario Types

/--
L1 joint for ambiguous scenarios (interp varies, others fixed).
Returns distribution over (W × I).
-/
def ambiguousL1_joint {U W I : Type} [BEq U] [BEq W] [BEq I]     (utterances : List U) (worlds : List W) (interps : List I)
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (interpPrior : I → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (u : U)
    : List ((W × I) × ℚ) :=
  let joint := L1_joint utterances worlds interps [()] [()] [()]
    (λ i _ => φ i) worldPrior interpPrior (λ _ => 1) (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ _ w w' => w == w') cost α u
  -- Project to (W × I)
  joint.map λ ((w, i, _, _, _), p) => ((w, i), p)

/--
L1 world marginal for ambiguous scenarios.
-/
def ambiguousL1_world {U W I : Type} [BEq U] [BEq W] [BEq I]     (utterances : List U) (worlds : List W) (interps : List I)
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (interpPrior : I → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (u : U)
    : List (W × ℚ) :=
  let joint := ambiguousL1_joint utterances worlds interps φ worldPrior interpPrior α cost u
  marginalize joint (·.1)

/--
L1 interp marginal for ambiguous scenarios.
-/
def ambiguousL1_interp {U W I : Type} [BEq U] [BEq W] [BEq I]     (utterances : List U) (worlds : List W) (interps : List I)
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (interpPrior : I → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (u : U)
    : List (I × ℚ) :=
  let joint := ambiguousL1_joint utterances worlds interps φ worldPrior interpPrior α cost u
  marginalize joint (·.2)

/--
L1 for QUD/goal scenarios (goal varies, others fixed).
-/
def qudL1_world {U W Q : Type} [BEq U] [BEq W] [BEq Q]     (utterances : List U) (worlds : List W) (goals : List Q)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (goalPrior : Q → ℚ := λ _ => 1)
    (goalProject : Q → W → W → Bool)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (u : U)
    : List (W × ℚ) :=
  L1_world utterances worlds [()] [()] [()] goals
    (λ _ _ => φ) worldPrior (λ _ => 1) (λ _ => 1) (λ _ => 1) goalPrior
    (λ _ _ => 1) goalProject cost α u

/--
L1 for mental state scenarios (belief states vary).
-/
def mentalStateL1_world {U W A Q : Type} [BEq U] [BEq W] [BEq A] [BEq Q]     (utterances : List U) (worlds : List W)
    (beliefStates : List A) (goals : List Q)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ)
    (beliefStatePrior : A → ℚ)
    (goalPrior : Q → ℚ)
    (speakerCredence : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (u : U)
    : List (W × ℚ) :=
  L1_world utterances worlds [()] [()] beliefStates goals
    (λ _ _ => φ) worldPrior (λ _ => 1) (λ _ => 1) beliefStatePrior goalPrior
    speakerCredence goalProject cost α u

-- Projection-Specific Helpers (Qing 2016, S&T 2025, Warstadt 2022)

/--
L1 context/belief-state marginal for projection scenarios.

Wraps `L1_beliefState_givenGoal` for models where the latent variable is a
context set (subset of worlds) and the semantics is Boolean.
Used by Qing et al. (2016), Scontras & Tonhauser (2025), Warstadt (2022).
-/
def projectionL1_context {U W A Q : Type} [BEq U] [BEq W] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (contexts : List A) (goals : List Q)
    (meaning : U → W → Bool)
    (worldPrior : W → ℚ)
    (contextPrior : A → ℚ)
    (compatible : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (α : ℕ)
    (u : U) (q : Q)
    : List (A × ℚ) :=
  L1_beliefState_givenGoal
    utterances worlds [()] [()] contexts goals
    (λ _ _ u' w => if meaning u' w then 1 else 0)
    worldPrior (λ _ => 1) (λ _ => 1) contextPrior (λ _ => 1)
    compatible goalProject (λ _ => 0) α u q

/--
L1 world marginal for projection scenarios.

Wraps `L1_world_givenGoal` with the same simplifications as `projectionL1_context`.
-/
def projectionL1_world {U W A Q : Type} [BEq U] [BEq W] [BEq A] [BEq Q]
    (utterances : List U) (worlds : List W)
    (contexts : List A) (goals : List Q)
    (meaning : U → W → Bool)
    (worldPrior : W → ℚ)
    (contextPrior : A → ℚ)
    (compatible : A → W → ℚ)
    (goalProject : Q → W → W → Bool)
    (α : ℕ)
    (u : U) (q : Q)
    : List (W × ℚ) :=
  L1_world_givenGoal
    utterances worlds [()] [()] contexts goals
    (λ _ _ u' w => if meaning u' w then 1 else 0)
    worldPrior (λ _ => 1) (λ _ => 1) contextPrior (λ _ => 1)
    compatible goalProject (λ _ => 0) α u q

/--
L1 for lexical uncertainty scenarios (lexicon varies).
-/
def lexUncertaintyL1_world {U W L : Type} [BEq U] [BEq W] [BEq L]     (utterances : List U) (worlds : List W) (lexica : List L)
    (φ : L → U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (lexiconPrior : L → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (u : U)
    : List (W × ℚ) :=
  L1_world utterances worlds [()] lexica [()] [()]
    (λ _ l => φ l) worldPrior (λ _ => 1) lexiconPrior (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ _ w w' => w == w') cost α u

/--
L1 lexicon marginal for lexical uncertainty scenarios.
-/
def lexUncertaintyL1_lexicon {U W L : Type} [BEq U] [BEq W] [BEq L]     (utterances : List U) (worlds : List W) (lexica : List L)
    (φ : L → U → W → ℚ)
    (worldPrior : W → ℚ := λ _ => 1)
    (lexiconPrior : L → ℚ := λ _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := λ _ => 0)
    (u : U)
    : List (L × ℚ) :=
  L1_lexicon utterances worlds [()] lexica [()] [()]
    (λ _ l => φ l) worldPrior (λ _ => 1) lexiconPrior (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ _ w w' => w == w') cost α u

-- Utility Aliases

-- ============================================================================
-- Knowledge-State S1 (G&S 2013 Eq. 2-3)
-- ============================================================================

/-- Quality filter: utterance must be true at every world the speaker considers possible.
    Implements the ln(0) = -∞ penalty from log-utility: any false-at-a-believed-world
    utterance gets utility -∞ and probability 0. -/
def qualityFilter {U W : Type}
    (meaning : U → W → Bool) (belief : W → ℚ) (allWorlds : List W) (u : U) : Bool :=
  allWorlds.all λ w => belief w ≤ 0 || meaning u w

/-- Knowledge-state S1 score (unnormalized).
    0 if quality filter fails; else 1/|compat(u)| (informativity).
    For uniform L0, this equals exp(E_belief[ln L0(·|u)]). -/
def ksS1Score {U W : Type}
    (meaning : U → W → Bool) (belief : W → ℚ) (allWorlds : List W) (u : U) : ℚ :=
  if qualityFilter meaning belief allWorlds u then
    let compat := allWorlds.filter (meaning u)
    if compat.length > 0 then 1 / compat.length else 0
  else 0

/-- Knowledge-state S1: pragmatic speaker with uncertain beliefs.
    P_S1(u|belief) ∝ qualityFilter(u) × informativity(u).
    Implements G&S 2013 Eq. (2): U(w;s) = ln P_lex(s|w). -/
def ksS1 {U W : Type} [BEq U]
    (allUtts : List U) (allWorlds : List W)
    (meaning : U → W → Bool) (belief : W → ℚ) : List (U × ℚ) :=
  normalize (allUtts.map λ u => (u, ksS1Score meaning belief allWorlds u))

/-- Knowledge-state L1 with interpretation marginalization.
    L1(w|u) ∝ P(w) × Σ_i P(i) × Σ_b P(b|w) × S1_ks(u | b, meaning_i).

    The `Interp` dimension handles any source of truth-conditional ambiguity:
    - Type-shifting (Kennedy 2015: exact vs lower-bound numerals)
    - Scope ambiguity (Scontras & Pearl 2021: surface vs inverse)
    - Lexical ambiguity (multiple word senses)

    **Unified principle**: the interpretation space for an utterance is the set of
    grammatically available parses that produce distinct truth conditions.
    RSA always marginalizes over this space. When `I = Unit` (single parse),
    this reduces to the standard knowledge-state L1.

    The quality filter acts as an *interpretation selector*: when the speaker's
    epistemic state makes one interpretation quality-risky but another safe,
    the quality filter shifts weight to the safe interpretation. The listener,
    reasoning about this, recovers the speaker's intended interpretation. -/
def ksL1 {U W B : Type} [BEq U] [BEq W]
    (allUtts : List U) (allWorlds : List W) (allBeliefs : List B)
    (meaning : U → W → Bool) (worldPrior : W → ℚ)
    (beliefProb : B → W → ℚ)  -- P(b|w): probability of belief state given world
    (belief : B → W → ℚ)      -- belief_b(w): speaker's credence about w in state b
    (u : U) : List (W × ℚ) :=
  -- Special case: single interpretation (I = Unit)
  let scores := allWorlds.map λ w =>
    let s1Marginal := sumScores (allBeliefs.map λ b =>
      getScore (ksS1 allUtts allWorlds meaning (belief b)) u * beliefProb b w)
    (w, worldPrior w * s1Marginal)
  normalize scores

/-- Knowledge-state L1 with interpretation marginalization.
    Generalizes `ksL1` to marginalize over grammatically available parses.
    Each interpretation `i` provides a different meaning function;
    the listener marginalizes over interpretations weighted by `interpPrior`.

    This is the general form. `ksL1` is the special case with a single interpretation. -/
def ksL1Interp {U W B I : Type} [BEq U] [BEq W]
    (allUtts : List U) (allWorlds : List W) (allBeliefs : List B) (allInterps : List I)
    (meaning : I → U → W → Bool)  -- interpretation-parametrized meaning
    (worldPrior : W → ℚ)
    (beliefProb : B → W → ℚ)
    (belief : B → W → ℚ)
    (interpPrior : I → ℚ := λ _ => 1)
    (u : U) : List (W × ℚ) :=
  let scores := allWorlds.map λ w =>
    let interpMarginal := sumScores (allInterps.map λ i =>
      let s1Marginal := sumScores (allBeliefs.map λ b =>
        getScore (ksS1 allUtts allWorlds (meaning i) (belief b)) u * beliefProb b w)
      interpPrior i * s1Marginal)
    (w, worldPrior w * interpMarginal)
  normalize scores

/-- Joint distribution over worlds and interpretations.
    L1(w,i|u) ∝ P(w) × P(i) × Σ_b P(b|w) × S1_ks(u | b, meaning_i).
    Useful for recovering which interpretation the listener selects. -/
def ksL1InterpJoint {U W B I : Type} [BEq U] [BEq W] [BEq I]
    (allUtts : List U) (allWorlds : List W) (allBeliefs : List B) (allInterps : List I)
    (meaning : I → U → W → Bool)
    (worldPrior : W → ℚ)
    (beliefProb : B → W → ℚ)
    (belief : B → W → ℚ)
    (interpPrior : I → ℚ := λ _ => 1)
    (u : U) : List ((W × I) × ℚ) :=
  let scores := allWorlds.flatMap λ w =>
    allInterps.map λ i =>
      let s1Marginal := sumScores (allBeliefs.map λ b =>
        getScore (ksS1 allUtts allWorlds (meaning i) (belief b)) u * beliefProb b w)
      ((w, i), worldPrior w * interpPrior i * s1Marginal)
  normalize scores

/-- Interpretation marginal: which parse does the listener select?
    L1(i|u) = Σ_w L1(w,i|u). -/
def ksL1InterpMarginal {U W B I : Type} [BEq U] [BEq W] [BEq I]
    (allUtts : List U) (allWorlds : List W) (allBeliefs : List B) (allInterps : List I)
    (meaning : I → U → W → Bool)
    (worldPrior : W → ℚ)
    (beliefProb : B → W → ℚ)
    (belief : B → W → ℚ)
    (interpPrior : I → ℚ := λ _ => 1)
    (u : U) : List (I × ℚ) :=
  let joint := ksL1InterpJoint allUtts allWorlds allBeliefs allInterps
    meaning worldPrior beliefProb belief interpPrior u
  marginalize joint (·.2)

-- Utility Aliases

/-- Alias for normalize (some files use normalizeScores) -/
def normalizeScores (scores : List ℚ) : List ℚ :=
  let total := sumScores scores
  if total > 0 then scores.map (· / total) else scores.map (λ _ => 0)

/-- Rational power function (kept for backward compatibility) -/
def powRat (base : ℚ) (exp : ℕ) : ℚ :=
  if exp = 0 then 1
  else base * powRat base (exp - 1)

/-- Convert Int to Float -/
def intToFloat (i : Int) : Float :=
  if i >= 0 then i.toNat.toFloat else -(-i).toNat.toFloat

/-- Convert ℚ to Float -/
def ratToFloat (q : ℚ) : Float :=
  intToFloat q.num / q.den.toFloat

/-- Convert Float to ℚ (approximate, with 6 decimal places precision) -/
def floatToRat (f : Float) : ℚ :=
  let scaled := (f * 1000000).round
  let intPart : Int := if scaled >= 0 then scaled.toUInt64.toNat else -(-scaled).toUInt64.toNat
  intPart / 1000000

/-- True softmax using Float exponentials.
    P(i) = exp(α · u_i) / Σ_j exp(α · u_j) -/
def softmax (α : ℚ) (utilities : List ℚ) : List ℚ :=
  let αF := ratToFloat α
  let exps := utilities.map λ u => Float.exp (αF * ratToFloat u)
  let total := exps.foldl (· + ·) 0.0
  if total > 0 then
    exps.map λ e => floatToRat (e / total)
  else
    utilities.map λ _ => 0

-- ============================================================================
-- Soft Knowledge-State S1 (G&S 2013 Eq. 2-3, finite α, ε > 0)
-- ============================================================================

/-- Noisy L0: literal listener with ε confusion floor.
    L0_noisy(w|u) = (1-ε) × meaning(u,w)/|compat| + ε/|W|
    Prevents ln(0) in speaker utility computation. -/
def noisyL0 {U W : Type}
    (meaning : U → W → Bool) (allWorlds : List W) (ε : ℚ)
    (u : U) (w : W) : ℚ :=
  let compat := allWorlds.filter (meaning u)
  let nW := allWorlds.length
  if nW = 0 then 0
  else if compat.length = 0 then ε / nW
  else if meaning u w then (1 - ε) / compat.length + ε / nW
  else ε / nW

/-- Log-score for soft knowledge-state S1.
    logS1(u|b) = α × Σ_w b(w) × ln(L0_noisy(w|u))
    Uses Float for transcendental functions. Returns Float. -/
def softKsS1LogScore {U W : Type}
    (meaning : U → W → Bool) (allWorlds : List W)
    (belief : W → ℚ) (ε α : ℚ) (u : U) : Float :=
  let logScore := allWorlds.foldl (λ acc w =>
    let b := ratToFloat (belief w)
    if b > 0 then
      let l0 := ratToFloat (noisyL0 meaning allWorlds ε u w)
      acc + b * Float.log (if l0 > 0 then l0 else 1e-300)
    else acc) 0.0
  ratToFloat α * logScore

/-- Soft knowledge-state S1: normalized speaker distribution with noisy L0.
    Implements G&S 2013 Eq. (2)-(3) with finite α and ε > 0.
    Uses log-sum-exp normalization: P(u|b) = exp(logS1(u) - max) / Σ exp(logS1(u') - max)
    to avoid Float underflow/overflow at high α.
    Recovers hard ksS1 in the limit α → ∞, ε → 0. -/
def softKsS1 {U W : Type} [BEq U]
    (allUtts : List U) (allWorlds : List W)
    (meaning : U → W → Bool) (belief : W → ℚ)
    (ε α : ℚ) : List (U × ℚ) :=
  let logScores := allUtts.map λ u => (u, softKsS1LogScore meaning allWorlds belief ε α u)
  let maxLog := logScores.foldl (λ acc (_, s) =>
    if (Float.decLt acc s).decide then s else acc) (-1e300)
  let expScores := logScores.map λ (u, s) => (u, Float.exp (s - maxLog))
  let total := expScores.foldl (λ acc (_, e) => acc + e) 0.0
  if (Float.decLt 0.0 total).decide then
    expScores.map λ (u, e) => (u, floatToRat (e / total))
  else
    allUtts.map λ u => (u, 0)

/-- Soft knowledge-state L1: pragmatic listener with noisy L0.
    L1(w|u) ∝ prior(w) × Σ_b P(b|w) × softS1(u|b). -/
def softKsL1 {U W B : Type} [BEq U] [BEq W]
    (allUtts : List U) (allWorlds : List W) (allBeliefs : List B)
    (meaning : U → W → Bool) (worldPrior : W → ℚ)
    (beliefProb : B → W → ℚ)
    (belief : B → W → ℚ)
    (ε α : ℚ) (u : U) : List (W × ℚ) :=
  let scores := allWorlds.map λ w =>
    let s1Marginal := sumScores (allBeliefs.map λ b =>
      getScore (softKsS1 allUtts allWorlds meaning (belief b) ε α) u * beliefProb b w)
    (w, worldPrior w * s1Marginal)
  normalize scores

end RSA.Eval
