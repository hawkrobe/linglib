import Linglib.Theories.Semantics.Dynamic.Core.Basic

/-!
# Nondeterminism Effect: Plural/Choice Alternatives

The nondeterminism effect models indefinites as introducing sets of alternatives
rather than single values. This underlies:
- Indefinites as choice functions (Reinhart 1997, Winter 1997)
- Plural/cumulative readings (Charlow 2019, Bumford 2015)
- Set-valued update (pointwise lifting)

The key type is `Set α` (or `List α` for computational purposes) — meanings
are sets of possible values rather than single values.

## Submodules

- `PointwiseUpdate`: Charlow's ↑/↓ bridge between pointwise and collectivized update
- `Charlow2019`: StateCCP, distributivity for nondeterministic dynamic semantics
-/

namespace Semantics.Dynamic.Effects.Nondeterminism

open Semantics.Dynamic.Core

/--
A nondeterministic meaning: produces a set of possible outputs.

This is the semantic type for indefinites — "a man" denotes the set
of all men, and the nondeterminism effect handles choice.
-/
def NDMeaning (α : Type*) (β : Type*) := α → Set β

/--
Bind for the nondeterminism monad (Set).

Sequencing nondeterministic computations: for each possible value from
the first computation, run the second and collect all results.
-/
def NDMeaning.bind {α β γ : Type*} (m : NDMeaning α β) (f : β → Set γ) : NDMeaning α γ :=
  λ a => { c | ∃ b ∈ m a, c ∈ f b }

/--
Pure/return for nondeterminism: a single deterministic value.
-/
def NDMeaning.pure {α β : Type*} (b : β) : NDMeaning α β :=
  λ _ => {b}

/--
Alternative/choice: union of two nondeterministic meanings.
-/
def NDMeaning.alt {α β : Type*} (m₁ m₂ : NDMeaning α β) : NDMeaning α β :=
  λ a => m₁ a ∪ m₂ a

/--
Maximization: select maximal elements from a nondeterministic meaning
with respect to some ordering. Used for cumulative readings.
-/
def NDMeaning.maximize {α β : Type*} (m : NDMeaning α β) (better : β → β → Prop) : NDMeaning α β :=
  λ a => { b ∈ m a | ∀ b' ∈ m a, ¬better b b' }

end Semantics.Dynamic.Effects.Nondeterminism
