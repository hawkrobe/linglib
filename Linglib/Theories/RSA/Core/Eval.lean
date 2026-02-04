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
  (satisfies := fun w u => mySemantics u w)
  (prior := fun _ => 1)
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

import Linglib.Theories.RSA.Core.Basic
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
  dist.map fun (x, s) =>
    (x, if total ≠ 0 then s / total else 0)

/-- Marginalize a joint distribution by projecting onto a component -/
def marginalize {α β : Type} [BEq β] (dist : List (α × ℚ)) (proj : α → β) : List (β × ℚ) :=
  let projected := dist.map fun (x, s) => (proj x, s)
  let uniqueKeys := projected.map (·.1) |>.eraseDups
  uniqueKeys.map fun k =>
    let total := projected.filter (fun (k', _) => k' == k) |>.map (·.2) |> sumScores
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
  let scores := worlds.map fun w =>
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
  worlds.map fun w =>
    let eqClassScore := l0.filter (fun (w', _) => goalProject q w w') |>.map (·.2) |> sumScores
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
  let scores := utterances.map fun u =>
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
  let scores := worlds.map fun w =>
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
  let scores := utterances.map fun u =>
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
  let tuples := worlds.flatMap fun w =>
    interps.flatMap fun i =>
      lexica.flatMap fun l =>
        beliefStates.flatMap fun a =>
          goals.map fun q => (w, i, l, a, q)
  let scores := tuples.map fun (w, i, l, a, q) =>
    let priorScore := worldPrior w * interpPrior i * lexiconPrior l *
                      beliefStatePrior a * goalPrior q
    let s1 := S1 utterances worlds φ worldPrior speakerCredence goalProject cost α w i l a q
    let s1Score := getScore s1 u
    ((w, i, l, a, q), priorScore * s1Score)
  let normalized := normalize scores
  -- Marginalize over i, l, a, q
  worlds.map fun w =>
    let wScores := normalized.filter (fun ((w', _, _, _, _), _) => w' == w) |>.map (·.2)
    (w, sumScores wScores)

-- Simplified API for Basic Scenarios

/--
Basic L0 for simple scenarios (no interp, lexicon, belief state, goal).
-/
def basicL0 {U W : Type} [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (u : U)
    : List (W × ℚ) :=
  L0 utterances worlds (fun _ _ => φ) worldPrior (fun _ _ => 1) u () () () ()

/--
Basic S0 for simple scenarios (literal speaker).

P(m | w) ∝ utterancePrior(m) · φ(m, w)
-/
def basicS0 {U W : Type} [BEq U]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (utterancePrior : U → ℚ := fun _ => 1)
    (w : W)
    : List (U × ℚ) :=
  S0 utterances worlds (fun _ _ => φ) utterancePrior w () () () ()

/--
Basic L1 from S0 for simple scenarios.

P(w | m) ∝ Prior(w) · P_S0(m | w)
-/
def basicL1_fromS0 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (utterancePrior : U → ℚ := fun _ => 1)
    (u : U)
    : List (W × ℚ) :=
  L1_fromS0 utterances worlds (fun _ _ => φ) worldPrior utterancePrior u () () () ()

/--
Basic S1 for simple scenarios.
-/
def basicS1 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (w : W)
    : List (U × ℚ) :=
  S1 utterances worlds (fun _ _ => φ) worldPrior (fun _ _ => 1)
     (fun _ w w' => w == w') cost α w () () () ()

/--
Basic S1 via production-first chain (S0 → L1_fromS0 → S1_fromL1S0).

P(m | w) ∝ utterancePrior(m) · P_L1_fromS0(w | m)^α · costDiscount(m)
-/
def basicS1_fromL1S0 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (utterancePrior : U → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (w : W)
    : List (U × ℚ) :=
  let scores := utterances.map fun u =>
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
    (worldPrior : W → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (u : U)
    : List (W × ℚ) :=
  L1_world utterances worlds [()] [()] [()] [()]
    (fun _ _ => φ) worldPrior (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ _ => 1) (fun _ w w' => w == w') cost α u

-- Unified API with ChainVariant

/--
Run S1 (pragmatic speaker) with chain selection.

- `.L0Based` (default): Standard S1 reasoning about L0
- `.S0Based`: S1 reasoning about L1 who reasons about S0
-/
def runS1 {U W : Type} [BEq U] [BEq W]
    (utterances : List U) (worlds : List W)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (utterancePrior : U → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
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
    (worldPrior : W → ℚ := fun _ => 1)
    (utterancePrior : U → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
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
  let tuples := worlds.flatMap fun w =>
    interps.flatMap fun i =>
      lexica.flatMap fun l =>
        beliefStates.flatMap fun a =>
          goals.map fun q => (w, i, l, a, q)
  let scores := tuples.map fun (w, i, l, a, q) =>
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
  marginalize joint (fun (_, i, _, _, _) => i)

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
  marginalize joint (fun (_, _, _, _, q) => q)

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
  marginalize joint (fun (_, _, l, _, _) => l)

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
  marginalize joint (fun (_, _, _, a, _) => a)

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
  let filtered := joint.filter (fun ((_, _, _, _, q'), _) => q' == q)
  -- Renormalize
  let renorm := normalize filtered
  -- Marginalize over w
  marginalize renorm (fun (w, _, _, _, _) => w)

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
  let filtered := joint.filter (fun ((_, _, _, _, q'), _) => q' == q)
  -- Renormalize
  let renorm := normalize filtered
  -- Marginalize over belief states
  marginalize renorm (fun (_, _, _, a, _) => a)

-- Simplified APIs for Common Scenario Types

/--
L1 joint for ambiguous scenarios (interp varies, others fixed).
Returns distribution over (W × I).
-/
def ambiguousL1_joint {U W I : Type} [BEq U] [BEq W] [BEq I]     (utterances : List U) (worlds : List W) (interps : List I)
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (u : U)
    : List ((W × I) × ℚ) :=
  let joint := L1_joint utterances worlds interps [()] [()] [()]
    (fun i _ => φ i) worldPrior interpPrior (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ _ => 1) (fun _ w w' => w == w') cost α u
  -- Project to (W × I)
  joint.map fun ((w, i, _, _, _), p) => ((w, i), p)

/--
L1 world marginal for ambiguous scenarios.
-/
def ambiguousL1_world {U W I : Type} [BEq U] [BEq W] [BEq I]     (utterances : List U) (worlds : List W) (interps : List I)
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (u : U)
    : List (W × ℚ) :=
  let joint := ambiguousL1_joint utterances worlds interps φ worldPrior interpPrior α cost u
  marginalize joint (·.1)

/--
L1 interp marginal for ambiguous scenarios.
-/
def ambiguousL1_interp {U W I : Type} [BEq U] [BEq W] [BEq I]     (utterances : List U) (worlds : List W) (interps : List I)
    (φ : I → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (interpPrior : I → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (u : U)
    : List (I × ℚ) :=
  let joint := ambiguousL1_joint utterances worlds interps φ worldPrior interpPrior α cost u
  marginalize joint (·.2)

/--
L1 for QUD/goal scenarios (goal varies, others fixed).
-/
def qudL1_world {U W Q : Type} [BEq U] [BEq W] [BEq Q]     (utterances : List U) (worlds : List W) (goals : List Q)
    (φ : U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (goalPrior : Q → ℚ := fun _ => 1)
    (goalProject : Q → W → W → Bool)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (u : U)
    : List (W × ℚ) :=
  L1_world utterances worlds [()] [()] [()] goals
    (fun _ _ => φ) worldPrior (fun _ => 1) (fun _ => 1) (fun _ => 1) goalPrior
    (fun _ _ => 1) goalProject cost α u

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
    (cost : U → ℚ := fun _ => 0)
    (u : U)
    : List (W × ℚ) :=
  L1_world utterances worlds [()] [()] beliefStates goals
    (fun _ _ => φ) worldPrior (fun _ => 1) (fun _ => 1) beliefStatePrior goalPrior
    speakerCredence goalProject cost α u

/--
L1 for lexical uncertainty scenarios (lexicon varies).
-/
def lexUncertaintyL1_world {U W L : Type} [BEq U] [BEq W] [BEq L]     (utterances : List U) (worlds : List W) (lexica : List L)
    (φ : L → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (lexiconPrior : L → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (u : U)
    : List (W × ℚ) :=
  L1_world utterances worlds [()] lexica [()] [()]
    (fun _ l => φ l) worldPrior (fun _ => 1) lexiconPrior (fun _ => 1) (fun _ => 1)
    (fun _ _ => 1) (fun _ w w' => w == w') cost α u

/--
L1 lexicon marginal for lexical uncertainty scenarios.
-/
def lexUncertaintyL1_lexicon {U W L : Type} [BEq U] [BEq W] [BEq L]     (utterances : List U) (worlds : List W) (lexica : List L)
    (φ : L → U → W → ℚ)
    (worldPrior : W → ℚ := fun _ => 1)
    (lexiconPrior : L → ℚ := fun _ => 1)
    (α : ℕ := 1)
    (cost : U → ℚ := fun _ => 0)
    (u : U)
    : List (L × ℚ) :=
  L1_lexicon utterances worlds [()] lexica [()] [()]
    (fun _ l => φ l) worldPrior (fun _ => 1) lexiconPrior (fun _ => 1) (fun _ => 1)
    (fun _ _ => 1) (fun _ w w' => w == w') cost α u

-- Utility Aliases

/-- Alias for normalize (some files use normalizeScores) -/
def normalizeScores (scores : List ℚ) : List ℚ :=
  let total := sumScores scores
  if total > 0 then scores.map (· / total) else scores.map (fun _ => 0)

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
  let exps := utilities.map fun u => Float.exp (αF * ratToFloat u)
  let total := exps.foldl (· + ·) 0.0
  if total > 0 then
    exps.map fun e => floatToRat (e / total)
  else
    utilities.map fun _ => 0

end RSA.Eval
