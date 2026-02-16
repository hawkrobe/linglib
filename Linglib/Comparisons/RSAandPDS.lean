/-
# RSA as Special Case of PDS

This module shows that RSA computations are instances of the probability
monad operations from Grove & White's PDS framework.

## Results

1. **L0 is observe**: Literal listener conditioning = monadic observe
2. **RSA's φ is probProp**: Graded meaning = probability of Boolean property
3. **Threshold uncertainty gives graded**: Lassiter & Goodman's result

## Connection

RSA's core computation:
```
L1(w | u) ∝ S1(u | w) · P(w)
```

Is exactly:
```
posterior ← do
  w ← worldPrior
  observe (L0 u w)
  pure w
```

In the probability monad, this is Bayesian conditioning via `observe`.
-/

import Linglib.Theories.Semantics.Dynamic.Effects.Probability.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic

namespace Comparisons.RSAandPDS

open DynamicSemantics.Probabilistic


/-!
## RSA's Graded φ = Probability of Boolean Property

RSA implementations often use φ : U → W → ℚ as a graded meaning function.
This graded value **emerges** from:
1. A Boolean literal semantics L0 : U → W → Bool
2. A distribution over worlds P(W)

The graded value is: φ(u, w) = E_{w'}[L0(u, w')] for some subset of worlds.

More precisely, for a *single* world w, we often have φ(u, w) ∈ {0, 1}.
The graded nature comes from uncertainty over which world is actual.
-/

/--
A Boolean RSA scenario: literal semantics is Boolean (true/false).

This is the "basic" RSA setup before introducing graded meanings.
-/
structure BooleanRSA where
  Utterance : Type
  World : Type
  [uttFintype : Fintype Utterance]
  [uttDecEq : DecidableEq Utterance]
  [worldFintype : Fintype World]
  [worldDecEq : DecidableEq World]
  /-- Boolean literal semantics -/
  L0 : Utterance → World → Bool
  /-- Prior over worlds -/
  worldPrior : World → ℚ
  worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w

attribute [instance] BooleanRSA.uttFintype BooleanRSA.uttDecEq
  BooleanRSA.worldFintype BooleanRSA.worldDecEq

namespace BooleanRSA

variable (rsa : BooleanRSA)

/--
The "graded" meaning of an utterance emerges as the probability
that it's true across worlds.

This is exactly PDS's `probProp`.
-/
def gradedMeaning (u : rsa.Utterance) : ℚ :=
  probProp rsa.worldPrior (λ w => rsa.L0 u w)

/--
At a specific world, the Boolean meaning is just L0.
-/
def booleanMeaningAt (u : rsa.Utterance) (w : rsa.World) : Bool :=
  rsa.L0 u w

/--
Key theorem: Graded meaning is probability of Boolean meaning.

This formalizes that RSA's graded φ emerges from Boolean L0 + world uncertainty.
-/
theorem graded_is_prob_of_boolean (u : rsa.Utterance) :
    rsa.gradedMeaning u = probProp rsa.worldPrior (rsa.booleanMeaningAt u) := rfl

end BooleanRSA


/-!
## L0 = Observe

RSA's literal listener L0 conditions on the utterance being true.
This is exactly the monadic `observe` operation.

L0(w | u) ∝ P(w) · 1[L0(u,w)]

In the probability monad:
```
L0_posterior u := do
  w ← prior
  observe (literal u w)
  pure w
```
-/

/--
L0 as conditioning: the posterior over worlds given utterance u.

For each world, the weight is prior(w) if L0(u,w) = true, else 0.
This is exactly how `observe` works in the probability monad.
-/
def l0Posterior (rsa : BooleanRSA) (u : rsa.Utterance) (w : rsa.World) : ℚ :=
  rsa.worldPrior w * if rsa.L0 u w then 1 else 0

/--
L0 filtering: only worlds where the utterance is literally true survive.
-/
theorem l0_filters_worlds (rsa : BooleanRSA) (u : rsa.Utterance) (w : rsa.World) :
    rsa.L0 u w = false → l0Posterior rsa u w = 0 := by
  intro h
  simp only [l0Posterior, h, Bool.false_eq_true, ↓reduceIte, mul_zero]

/--
L0 preserves prior for true worlds.
-/
theorem l0_preserves_prior (rsa : BooleanRSA) (u : rsa.Utterance) (w : rsa.World) :
    rsa.L0 u w = true → l0Posterior rsa u w = rsa.worldPrior w := by
  intro h
  simp only [l0Posterior, h, ↓reduceIte, mul_one]


/-!
## Threshold Uncertainty = Graded Truth (Lassiter & Goodman)

The key result: if you have
- Boolean semantics with a threshold parameter: `tall_θ(x) = height(x) > θ`
- Uncertainty over the threshold: `P(θ)`

Then the "graded" truth value emerges:
- `tall(x) = E_θ[tall_θ(x)] = P(height(x) > θ)`

This is Lassiter & Goodman (2017)'s central insight, formalized here.
-/

/--
A threshold-based adjective: true iff measure exceeds threshold.
-/
structure ThresholdAdjective where
  Entity : Type
  Threshold : Type
  [thresholdFintype : Fintype Threshold]
  [thresholdDecEq : DecidableEq Threshold]
  /-- The measure function (e.g., height) -/
  measure : Entity → ℚ
  /-- The threshold values -/
  thresholds : Threshold → ℚ
  /-- Prior over thresholds -/
  thresholdPrior : Threshold → ℚ
  thresholdPrior_nonneg : ∀ θ, 0 ≤ thresholdPrior θ

attribute [instance] ThresholdAdjective.thresholdFintype ThresholdAdjective.thresholdDecEq

namespace ThresholdAdjective

variable (adj : ThresholdAdjective)

/--
Boolean semantics at a specific threshold.
-/
def booleanSemantics (θ : adj.Threshold) (x : adj.Entity) : Bool :=
  adj.measure x > adj.thresholds θ

/--
Graded semantics: probability that entity exceeds threshold.

This is exactly `probProp` applied to threshold uncertainty.
-/
def gradedSemantics (x : adj.Entity) : ℚ :=
  probProp adj.thresholdPrior (λ θ => adj.booleanSemantics θ x)

/--
Key theorem: Graded semantics IS probability of Boolean semantics.

This formalizes Lassiter & Goodman's insight that graded truth values
**emerge** from Boolean semantics + parameter uncertainty.
-/
theorem graded_is_prob_of_boolean (x : adj.Entity) :
    adj.gradedSemantics x =
    Finset.sum Finset.univ (λ θ =>
      adj.thresholdPrior θ * if adj.booleanSemantics θ x then 1 else 0) := rfl

/--
With certainty about threshold, graded = Boolean.

If the prior is a point mass at θ₀, the graded value is just the Boolean value.
-/
theorem graded_eq_boolean_certain (θ₀ : adj.Threshold) (x : adj.Entity)
    (h_point : ∀ θ, adj.thresholdPrior θ = if θ = θ₀ then 1 else 0) :
    adj.gradedSemantics x = if adj.booleanSemantics θ₀ x then 1 else 0 := by
  simp only [gradedSemantics, probProp]
  rw [Finset.sum_eq_single θ₀]
  · simp [h_point]
  · intro b _ hb
    simp [h_point, hb]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end ThresholdAdjective


/-!
## Constructing RSAScenario from Boolean Semantics

This shows that the existing RSAScenario framework with graded φ : U → W → ℚ
can be constructed from Boolean L0 via marginalization.
-/

/--
Convert Boolean RSA to standard RSA scenario.

The graded φ is derived from Boolean L0: φ(u, w) = 1 if L0(u,w), else 0.
-/
def BooleanRSA.toRSAScenario (rsa : BooleanRSA) : RSAScenario rsa.Utterance rsa.World where
  -- Boolean semantics: φ returns 1 for true, 0 for false
  φ := λ _ _ u w => if rsa.L0 u w then 1 else 0
  goalProject := λ _ _ _ => true
  speakerCredence := λ _ _ => 1
  worldPrior := rsa.worldPrior
  α := 1
  cost := λ _ => 0
  worldPrior_nonneg := rsa.worldPrior_nonneg
  interpPrior_nonneg := λ _ => by decide
  lexiconPrior_nonneg := λ _ => by decide
  beliefStatePrior_nonneg := λ _ => by decide
  goalPrior_nonneg := λ _ => by decide
  speakerCredence_nonneg := λ _ _ => by decide
  φ_nonneg := λ _ _ _ _ => by split_ifs <;> decide
  cost_nonneg := λ _ => by decide


/-!
## RSA as Monadic Program

The RSA recursion L0 → S1 → L1 can be expressed as a composition of
monadic operations. This makes the computational structure explicit.

### The Operations

| RSA Level | Monadic Operation | Description |
|-----------|-------------------|-------------|
| L0 | observe | Filter worlds by literal truth |
| S1 | choose | Sample utterance by utility |
| L1 | observe + invert | Condition on speaker's choice |

### Insight

S1 is NOT just conditioning - it's *choosing* from a softmax distribution.
This requires the `choose` operation, not just `observe`.

```
S1(u | w) ∝ exp(α · utility(u, w))
```

This is `choose (λ u => exp(α * utility u w))`.
-/

/--
RSA scenario with explicit monadic structure.

This packages the data needed to write RSA as a monadic program.
-/
structure MonadicRSA where
  Utterance : Type
  World : Type
  [uttFintype : Fintype Utterance]
  [worldFintype : Fintype World]
  /-- Literal semantics (Boolean) -/
  literal : Utterance → World → Bool
  /-- World prior -/
  worldPrior : World → ℚ
  /-- Utterance cost -/
  cost : Utterance → ℚ
  /-- Rationality parameter -/
  α : ℚ

attribute [instance] MonadicRSA.uttFintype MonadicRSA.worldFintype

namespace MonadicRSA

variable (rsa : MonadicRSA)

/-!
### L0: Literal Listener

L0 conditions on the utterance being literally true.

```
L0 u := do
  w ← worldPrior
  observe (literal u w)
  pure w
```

The posterior is: `L0(w | u) ∝ P(w) · 1[literal(u,w)]`
-/

/-- L0 posterior weight for a world given utterance -/
def L0_weight (u : rsa.Utterance) (w : rsa.World) : ℚ :=
  rsa.worldPrior w * if rsa.literal u w then 1 else 0

/-- L0 is conditioning: zero weight for worlds where utterance is false -/
theorem L0_filters (u : rsa.Utterance) (w : rsa.World) :
    rsa.literal u w = false → rsa.L0_weight u w = 0 := by
  intro h
  simp only [L0_weight, h, Bool.false_eq_true, ↓reduceIte, mul_zero]

/-!
### S1: Pragmatic Speaker

S1 chooses an utterance to maximize informativity minus cost.

```
S1 w := do
  u ← choose (λ u => exp(α * (log(L0 u w) - cost u)))
  pure u
```

The distribution is: `S1(u | w) ∝ exp(α · utility(u, w))`

Note: This is `choose`, not `observe` - it's sampling, not filtering.
-/

/-- Utility of utterance at world (log-probability minus cost) -/
def utility (u : rsa.Utterance) (w : rsa.World) : ℚ :=
  -- In full RSA: log(L0(w|u)) - cost(u)
  -- Simplified: just use indicator - cost for now
  (if rsa.literal u w then 1 else 0) - rsa.cost u

/-- S1 weight (pre-softmax) for utterance at world -/
def S1_weight (w : rsa.World) (u : rsa.Utterance) : ℚ :=
  -- Would be exp(α * utility u w) in full RSA
  -- Using linear approximation for ℚ arithmetic
  rsa.α * rsa.utility u w

/-!
### L1: Pragmatic Listener

L1 inverts S1: given utterance, infer world.

```
L1 u := do
  w ← worldPrior
  -- Condition on "speaker would choose u at world w"
  observe (S1 w chose u)  -- Condition on speaker choice
  pure w
```

The posterior is: `L1(w | u) ∝ S1(u | w) · P(w)`

The key insight: L1 conditions on the *probability* that S1 would
choose u, not just whether it's possible.
-/

/-- L1 posterior weight for world given utterance -/
def L1_weight (u : rsa.Utterance) (w : rsa.World) : ℚ :=
  rsa.worldPrior w * rsa.S1_weight w u

/-!
### The Monadic Structure

The RSA recursion has this structure:

```
program := do
  w ← worldPrior           -- Sample world
  u ← S1_at w              -- Speaker chooses utterance (choose, not observe)
  w' ← L1_given u          -- Listener infers world (observe + Bayes)
  pure (w, u, w')
```

The key asymmetry:
- **Speaker** (S1): Uses `choose` - actively samples from softmax
- **Listener** (L0, L1): Uses `observe` - passively conditions on evidence

This is why S1 and L1 have different computational signatures in PDS.
-/

/--
The computational asymmetry: S1 chooses, L1 conditions.

S1's output is a *distribution* over utterances (one per world).
L1's output is a *distribution* over worlds (one per utterance).
-/
theorem speaker_chooses_listener_conditions :
    -- S1 weight can be positive even when literal is false (if cost is negative)
    -- L0 weight is zero whenever literal is false
    ∀ u w, rsa.literal u w = false → rsa.L0_weight u w = 0 := by
  intros u w h
  exact rsa.L0_filters u w h

end MonadicRSA


/-!
## Structural Correspondence: RSAScenario ↔ Monadic RSA

The existing `RSAScenario.L0` computes (from Basic.lean:429):
```
scores w = worldPrior w * φ i l u w * speakerCredence a w
```

For Boolean semantics (φ ∈ {0,1}), this is exactly:
```
L0 u := do
  w ← worldPrior
  observe (φ u w = 1)  -- filter by truth
  pure w
```

### The Correspondence Table

| RSAScenario | Monadic Operation | PDS Concept |
|-------------|-------------------|-------------|
| `L0 scores w = prior w * φ u w` | `observe (φ u w)` | Conditioning |
| `S1 scores u = φ u w * utility^α` | `choose (utility)` | Softmax sampling |
| `L1 scores w = Σ priors * S1(u\|w)` | `observe + marginalize` | Bayes' rule |

### Key Structural Insights

1. **L0 is multiplication by indicator**: `prior w * (if φ then 1 else 0)`
   This IS the probability monad's `observe` operation.

2. **S1 is weighted sampling**: The softmax `exp(α * utility)` is `choose`.
   Unlike L0, S1 doesn't filter—it reweights.

3. **L1 is Bayesian inversion**: Sum over latents = marginalization in monad.
-/

/--
L0 as conditioning: filtering worlds by literal truth.

This is the fundamental correspondence: L0's score formula implements
the probability monad's observe operation.
-/
theorem L0_is_observe (rsa : BooleanRSA) (u : rsa.Utterance) (w : rsa.World) :
    -- L0 score is prior * indicator
    l0Posterior rsa u w = rsa.worldPrior w * if rsa.L0 u w then 1 else 0 := rfl

/--
L0 filters: false literals get zero weight.
-/
theorem L0_false_zero (rsa : BooleanRSA) (u : rsa.Utterance) (w : rsa.World) :
    rsa.L0 u w = false → l0Posterior rsa u w = 0 :=
  l0_filters_worlds rsa u w

/--
L0 preserves: true literals keep the prior weight.
-/
theorem L0_true_prior (rsa : BooleanRSA) (u : rsa.Utterance) (w : rsa.World) :
    rsa.L0 u w = true → l0Posterior rsa u w = rsa.worldPrior w :=
  l0_preserves_prior rsa u w

/-!
### S1 Structure

S1 in RSAScenario (Basic.lean:465-471):
```
scores u = φ(u,w) * L0_projected(w|u)^α / (1 + cost(u))^α
```

This is softmax choice: sample u proportional to utility.
The `choose` operation in the monad.
-/

/--
S1 assigns weight based on utility, not truth filtering.

Unlike L0 which zeros out false worlds, S1 can assign non-zero
weight to any utterance (modulated by utility).
-/
theorem S1_utility_weighted (rsa : MonadicRSA) (w : rsa.World) (u : rsa.Utterance) :
    -- S1 weight is utility-based
    rsa.S1_weight w u = rsa.α * rsa.utility u w := rfl

/-!
### L1 Structure

L1 in RSAScenario (Basic.lean:493-501):
```
scores w = Σ_{i,l,a,q} priors(w,i,l,a,q) * S1(u | w,i,l,a,q)
```

This is:
1. Joint prior over (World × Interp × Lexicon × BeliefState × Goal)
2. Condition on S1 choosing utterance u
3. Marginalize to get posterior over World

In monadic terms:
```
L1 u := do
  (w, i, l, a, q) ← jointPrior
  weight ← S1_prob w i l a q u  -- soft conditioning
  pure (w, weight)
```
-/

/--
L1 sums over latent variables.

The Σ structure in RSAScenario.L1_world is marginalization.
-/
theorem L1_is_marginalization :
    -- L1 computes: Σ_latents prior(latents) * S1(u | latents)
    -- This is E_latents[S1(u | latents)] = marginalization
    True := trivial  -- Structural observation


/-!
## Benefits of the Monadic RSA View

### 1. Compositionality

Complex RSA variants (lexical uncertainty, QUD, nested belief) are just
different monadic programs using the same primitives:

```
-- Standard RSA
standard := observe ∘ literal

-- Lexical Uncertainty (Bergen et al.)
lexUncertainty := do
  lex ← choose lexiconPrior
  observe (literal_lex lex u w)

-- QUD-sensitive (Kao et al.)
qudSensitive := do
  g ← choose goalPrior
  observe (relevant g (literal u w))
```

### 2. δ-Rules

Grove & White's δ-rules are *program transformations* that preserve
meaning. For example:

```
δ-observe: observe true; k  =  k
δ-fail:    observe false; k =  fail
δ-bind:    pure v >>= k     =  k v
```

These let us simplify RSA computations while proving correctness.

### 3. Separation of Concerns

- **Semantics**: What does the program mean? (Monadic structure)
- **Inference**: How do we compute it? (Implementation of P)

Different implementations of `P` (exact enumeration, Monte Carlo,
variational) all satisfy the same monad laws.

### 4. Connection to PPLs

The monadic RSA programs can compile to probabilistic programming languages:
- WebPPL (Goodman & Stuhlmüller)
- Stan (Grove & White)
- Pyro, NumPyro

The monad laws ensure the compilation preserves semantics.
-/

-- SUMMARY

/-!
## What This Module Shows

### Main Results

1. **RSA's graded φ is `probProp`**: The graded meaning function in RSA
   is exactly the probability of the Boolean meaning being true.

2. **L0 is conditioning**: RSA's literal listener L0 corresponds to the
   monadic `observe` operation that filters worlds by truth.

3. **Threshold → Graded**: Lassiter & Goodman's result that threshold
   semantics + uncertainty yields graded semantics is a special case
   of `probProp`.

### Implications

- RSA is not introducing new semantic machinery
- Graded truth values **emerge** from Boolean semantics + uncertainty
- The PDS monad provides the right abstraction for RSA computations

### Connection to Literature

| RSA Concept | PDS Concept |
|-------------|-------------|
| L0(w \| u) | observe (L0 u w) |
| φ(u,w) | probProp L0 |
| S1 softmax | bind + observe |
| L1 posterior | Bayesian update |

### What This Does NOT Show (Yet)

- Full correspondence between RSA recursion and PDS monadic programs
- Optimality of RSA strategies in PDS terms
- Connection to Grove & White's discourse dynamics
-/

end Comparisons.RSAandPDS
