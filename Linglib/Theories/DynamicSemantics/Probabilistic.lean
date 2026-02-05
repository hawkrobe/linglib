/-
# Probabilistic Dynamic Semantics (Grove & White)

Basic monad infrastructure for probabilistic semantics following
Grove & White's PDS framework.

## Key Ideas

1. Probability monad `P α`: distributions over values of type α
2. Parameterized state monad `Pσ σ σ' α = σ → P (α × σ')`: discourse dynamics
3. Monad laws: equational theory for probabilistic programs
4. δ-rules: reductions that preserve semantic equivalence

## Connection to Existing Work

The PDS framework shows that:
- Threshold semantics + uncertainty = graded semantics (Lassiter & Goodman)
- RSA's graded φ can emerge from Boolean φ_θ + marginalization
- Different "latent variable" choices (dcS vs cg) are computational variants

## References

- Grove & White. Probabilistic Dynamic Semantics. Elements in Semantics.
- Lassiter & Goodman (2017). Adjectival vagueness in a Bayesian model.
- Bernardy et al. (2018). A Compositional Bayesian Semantics for Natural Language.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators

namespace Theories.DynamicSemantics.Probabilistic


/-!
## The Probability Monad

We define `P α` abstractly as a structure with `pure` and `bind` operations
satisfying the monad laws. This allows us to reason about probabilistic
programs without committing to a specific representation (PMF, measure, etc.).

In Grove & White notation:
- `⌜v⌝` is `pure v` (trivial distribution at v)
- `x ← m; k` is `bind m (λ x => k)`
-/

/--
Abstract probability monad interface.

A probability monad provides:
- `pure`: Lift a value to a trivial distribution
- `bind`: Sequence probabilistic computations
- Monad laws as equalities

This is the semantic interface; implementations may use PMFs, measures, etc.

Note: We use Type instead of Type* to avoid universe issues. For semantic
work, this is typically sufficient.
-/
class ProbMonad (P : Type → Type) where
  /-- Trivial distribution concentrated at a value -/
  pure : {α : Type} → α → P α
  /-- Sequence: sample from m, then continue with k -/
  bind : {α β : Type} → P α → (α → P β) → P β
  /-- Left identity: `pure v >>= k = k v` -/
  pure_bind : {α β : Type} → ∀ (v : α) (k : α → P β), bind (pure v) k = k v
  /-- Right identity: `m >>= pure = m` -/
  bind_pure : {α : Type} → ∀ (m : P α), bind m pure = m
  /-- Associativity: `(m >>= n) >>= o = m >>= (λx. n x >>= o)` -/
  bind_assoc : {α β γ : Type} → ∀ (m : P α) (n : α → P β) (o : β → P γ),
    bind (bind m n) o = bind m (λ x => bind (n x) o)

namespace ProbMonad

variable {P : Type → Type} [ProbMonad P]
variable {α β γ : Type}

/-- Map a function over a distribution -/
def map (f : α → β) (m : P α) : P β :=
  bind m (λ x => pure (f x))

/-- Sequence two distributions, ignoring the first result -/
def seq (m : P α) (n : P β) : P β :=
  bind m (λ _ => n)

/-- Map preserves identity -/
theorem map_id (m : P α) : map (id : α → α) m = m := by
  simp only [map]
  exact bind_pure m

/-- Map composes -/
theorem map_comp (f : α → β) (g : β → γ) (m : P α) :
    map g (map f m) = map (g ∘ f) m := by
  simp only [map, Function.comp]
  rw [bind_assoc]
  congr 1
  ext x
  exact pure_bind (f x) (λ y => pure (g y))

end ProbMonad


/-!
## Parameterized State Monad

In Grove & White's parameterized state monad, the state type can *change* during computation.
This models how discourse updates can modify the structure of the context
(e.g., pushing questions onto the QUD stack).

```
P^σ_σ' α = σ → P(α × σ')
```

The parameters σ and σ' are the input and output state types.
-/

/--
Parameterized probabilistic state monad.

Maps input state σ to a distribution over (value, output state) pairs.
The output state type σ' can differ from σ, allowing type-changing updates.

This is Grove & White's `P^σ_σ' α`.
-/
def PState (P : Type → Type) (σ σ' α : Type) := σ → P (α × σ')

namespace PState

variable {P : Type → Type} [ProbMonad P]
variable {σ σ' σ'' σ''' α β γ : Type}

/--
Return for the parameterized state monad.

Returns the value paired with the unchanged state.
Grove & White: `⌜v⌝^σ = λs. ⌜(v, s)⌝`
-/
def pure (v : α) : PState P σ σ α :=
  λ s => ProbMonad.pure (v, s)

/--
Bind for the parameterized state monad.

Sequences stateful-probabilistic computations, threading state through.
Grove & White: `do { x ← m; k x } = λs. (x, s') ← m(s); k(x)(s')`
-/
def bind (m : PState P σ σ' α) (k : α → PState P σ' σ'' β) : PState P σ σ'' β :=
  λ s => ProbMonad.bind (m s) (λ ⟨x, s'⟩ => k x s')

/--
View (get) a component of the state.

Returns the value of applying `proj` to the current state, without modification.
-/
def view (proj : σ → α) : PState P σ σ α :=
  λ s => ProbMonad.pure (proj s, s)

/--
Set (put) a component of the state.

Returns the new state created by `upd`, with a trivial value.
-/
def set (upd : σ → σ') : PState P σ σ' Unit :=
  λ s => ProbMonad.pure ((), upd s)

/--
Modify the state in place.
-/
def modify (f : σ → σ) : PState P σ σ Unit :=
  λ s => ProbMonad.pure ((), f s)

/--
Left identity for PState: `pure v >>= k = k v`
-/
theorem pure_bind (v : α) (k : α → PState P σ σ' β) :
    bind (pure v) k = k v := by
  funext s
  simp only [bind, pure]
  exact ProbMonad.pure_bind (v, s) (λ ⟨x, s'⟩ => k x s')

/--
Right identity for PState: `m >>= pure = m`
-/
theorem bind_pure (m : PState P σ σ' α) :
    bind m pure = m := by
  funext s
  simp only [bind, pure]
  conv_rhs => rw [← ProbMonad.bind_pure (m s)]

/--
Associativity for PState.
-/
theorem bind_assoc (m : PState P σ σ' α)
    (n : α → PState P σ' σ'' β) (o : β → PState P σ'' σ''' γ) :
    bind (bind m n) o = bind m (λ x => bind (n x) o) := by
  funext s
  simp only [bind]
  rw [ProbMonad.bind_assoc]

end PState


/-!
## Conditioning

Grove & White's `observe` operation conditions a distribution on a boolean.

```
observe : Bool → P Unit
observe true continues; observe false blocks
```

This is the mechanism for assertion: update the CG by observing the asserted
proposition is true.
-/

/--
Extended probability monad with conditioning.

Adds `observe` for conditioning on boolean observations.
-/
class CondProbMonad (P : Type → Type) extends ProbMonad P where
  /-- The zero distribution (blocks all continuations) -/
  fail : {α : Type} → P α
  /-- Condition on a boolean: continue if true, block if false -/
  observe : Bool → P Unit
  /-- Observing true is a no-op -/
  observe_true : observe true = pure ()
  /-- Observing false blocks all continuations -/
  observe_false_bind : {α : Type} → ∀ (k : Unit → P α), bind (observe false) k = fail
  /-- fail is a left zero for bind -/
  fail_bind : {α β : Type} → ∀ (k : α → P β), bind fail k = fail

namespace CondProbMonad

variable {P : Type → Type} [CondProbMonad P]

/-- Observe filters: observe true then return is identity -/
theorem observe_true_pure :
    ProbMonad.bind (observe true) (λ _ => ProbMonad.pure (P := P) ()) = observe true := by
  rw [observe_true, ProbMonad.pure_bind]

/-- Observe false blocks: any continuation after observe false gives fail -/
theorem observe_false_pure :
    ProbMonad.bind (observe false) (λ _ => ProbMonad.pure (P := P) ()) = fail := by
  exact observe_false_bind _

end CondProbMonad


/-!
## Choice Operations

RSA's S1 isn't just conditioning - it's *choosing* an utterance weighted by utility.
This requires a `choose` operation in addition to `observe`.

```
choose : (α → ℚ) → P α   -- sample from weighted distribution
```

The relationship:
- `observe b` filters: keeps current path if b, blocks otherwise
- `choose w` samples: draws from distribution proportional to weights w
-/

/--
Probability monad with choice (for speaker models).

Adds `choose` for sampling from weighted distributions.
This is what S1's softmax requires.
-/
class ChoiceProbMonad (P : Type → Type) extends CondProbMonad P where
  /-- Sample from a weighted distribution over a finite type -/
  choose : {α : Type} → [Fintype α] → (α → ℚ) → P α
  /-- choose with uniform weights is like a uniform prior -/
  choose_uniform : {α : Type} → [Fintype α] → [Nonempty α] →
    choose (λ _ : α => 1) = choose (λ _ => 1)  -- trivial, but states the interface
  /-- choose then observe is like weighted observe -/
  choose_observe : {α : Type} → [Fintype α] → ∀ (w : α → ℚ) (p : α → Bool),
    bind (choose w) (λ a => bind (observe (p a)) (λ _ => pure a)) =
    choose (λ a => w a * if p a then 1 else 0)

namespace ChoiceProbMonad

variable {P : Type → Type} [ChoiceProbMonad P]
variable {α : Type} [Fintype α]

/--
Softmax choice: choose with exp-scaled weights.

This is S1's decision rule: P(u) ∝ exp(α · utility(u))

Note: We use ℚ so can't compute exp directly. In practice, implementations
use Float or work with log-probabilities. This definition is for the interface.
-/
def softmaxChoice (utility : α → ℚ) (temperature : ℚ) : P α :=
  -- In exact arithmetic, we'd compute exp(utility/temperature)
  -- For now, just use the utility as weight (linear approximation)
  choose utility

end ChoiceProbMonad


/-!
## Threshold Semantics

Threshold semantics + threshold uncertainty produces graded truth values
(Lassiter & Goodman 2017). This is a special case of the PDS framework.

For a gradable adjective like "tall":
- `measure : Entity → ℝ` gives heights
- `threshold : θ` is the standard of comparison
- `⟦tall⟧_θ(x) = measure(x) > θ` is Boolean

With uncertainty over θ:
- `⟦tall⟧(x) = E_θ[⟦tall⟧_θ(x)] = P(measure(x) > θ)`

This probability is the graded truth value.
-/

variable {ε : Type}

/--
Threshold semantics: entity satisfies predicate if measure exceeds threshold.
-/
def thresholdSem (measure : ε → ℚ) (threshold : ℚ) (x : ε) : Bool :=
  measure x > threshold

/--
Graded truth from threshold uncertainty.

Given a prior over thresholds, the graded truth is the probability
that the entity's measure exceeds the threshold.
-/
def gradedFromThreshold {Θ : Type} [Fintype Θ] [DecidableEq Θ]
    (measure : ε → ℚ) (thresholds : Θ → ℚ) (prior : Θ → ℚ) (x : ε) : ℚ :=
  Finset.sum Finset.univ λ θ =>
    prior θ * if measure x > thresholds θ then 1 else 0

/--
For a point-mass prior (no uncertainty), graded truth reduces to Boolean.

This shows that graded semantics *reduces to* Boolean semantics when
there's no parameter uncertainty.
-/
theorem graded_eq_bool_of_point_mass {Θ : Type} [Fintype Θ] [DecidableEq Θ]
    (measure : ε → ℚ) (thresholds : Θ → ℚ) (θ₀ : Θ) (x : ε) :
    let pointMass : Θ → ℚ := λ θ => if θ = θ₀ then 1 else 0
    gradedFromThreshold measure thresholds pointMass x =
      if measure x > thresholds θ₀ then 1 else 0 := by
  simp only [gradedFromThreshold]
  rw [Finset.sum_eq_single θ₀]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact (h (Finset.mem_univ _)).elim


/-!
## Connection to RSA

Grove & White's framework connects to RSA as follows:

1. Literal meaning φ: a function `ι → Bool` (proposition)
2. Common ground: a distribution `P ι` over indices
3. Assertion: `observe(φ(i))` for `i ← cg`
4. Probability computation: `Pr[φ] = E_i[1_{φ(i)}]`

RSA's graded φ emerges from:
- Boolean φ_θ indexed by parameters θ
- A prior distribution over θ
- Marginalization: φ(x) = E_θ[φ_θ(x)]

This is exactly Lassiter & Goodman's "threshold + uncertainty = graded".
-/

/--
A proposition in the PDS sense: a function from indices to truth values.
-/
def Prop' (ι : Type) := ι → Bool

/--
Probability of a proposition in a finite distribution.

This is `Pr[φ] = E_i[1_{φ(i)}]` in Grove & White notation.
For finite distributions, this is the sum of masses where φ holds.
-/
def probProp {ι : Type} [Fintype ι] (mass : ι → ℚ) (φ : Prop' ι) : ℚ :=
  Finset.sum Finset.univ λ i => mass i * if φ i then 1 else 0

/--
Probability of a true proposition is the total mass (1 for normalized distributions).
-/
theorem probProp_true {ι : Type} [Fintype ι] (mass : ι → ℚ) :
    probProp mass (λ _ => true) = Finset.sum Finset.univ mass := by
  simp only [probProp, ↓reduceIte, mul_one]

/--
Probability of a false proposition is 0.
-/
theorem probProp_false {ι : Type} [Fintype ι] (mass : ι → ℚ) :
    probProp mass (λ _ => false) = 0 := by
  simp only [probProp]
  have h : ∀ i, mass i * (if false then 1 else 0) = 0 := λ i => by simp
  simp only [h, Finset.sum_const_zero]

end Theories.DynamicSemantics.Probabilistic
