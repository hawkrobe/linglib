import Linglib.Semantics.Modality.ProbabilityOrdering

/-!
# Nested epistemic probability operators

World-dependent threshold semantics for epistemic modals, after
[fagin-halpern-1994]'s logic of knowledge and probability: their
probability formulas `w_i(φ) ≥ b` can be nested —
`w_i(w_j(φ) ≥ b₁) ≥ b₂` — so `nestedThreshold` takes a proposition to
a proposition and iterates. `WorldCredence` is the world-indexed
credence `μ_{i,s}` this requires: at each world the agent has a
possibly different belief state, which is what complex expressions
like "certainly likely" quantify over ([herbstritt-franke-2019]'s
higher-order uncertainty). The flat, world-independent threshold
semantics of attitude verbs is `Attitudes/EpistemicThreshold.lean`.

A probability assignment over worlds induces a Kratzer ordering
source (`Modality/ProbabilityOrdering.lean`); cutting that ordering
at threshold values recovers this semantics on finite single-agent
models. Propositions here are `W → Bool` so nesting stays computable
by construction; migration to the `Set`-based question substrate is
pending.
-/

namespace Modality.EpistemicProbability

/-! ### World-Dependent Credence -/

/-- World-dependent agent credence: at each world `w`, agent `a` has
    a (possibly different) probability distribution, yielding credence
    in proposition `φ`.

    This is [fagin-halpern-1994]'s `μ_{i,s}`: the probability space
    associated with agent `i` at state `s`. The world parameter is what
    distinguishes this from flat threshold credence — the agent's
    beliefs can vary across worlds (reflecting different information
    states).

    In [herbstritt-franke-2019]'s urn scenario, each (observation, access)
    pair induces a different belief distribution over urn states, so
    the agent's credence in "RED is probable" depends on which world
    (= which observation) they are in. -/
abbrev WorldCredence (E W : Type*) := E → W → (W → Bool) → ℚ

/-! ### Nested Threshold Operators -/

/-- Nested threshold: agent `a`'s credence in `φ` meets threshold `θ`
    *at world `w`*. Returns a `(W → Bool)` that can be nested further.

    This is the core compositional operator for complex probability
    expressions. Each application adds one layer of threshold evaluation:

    ```
    nestedThreshold wcr θ_prob a RED         -- ⟦probably(RED)⟧ : (W → Bool)
    nestedThreshold wcr θ_cert a             -- ⟦certainly(·)⟧ : (W → Bool) → (W → Bool)
      (nestedThreshold wcr θ_prob a RED)     -- ⟦certainly(probably(RED))⟧ : (W → Bool)
    ```

    The output type `(W → Bool) = W → Bool` is the same as the input
    proposition type, so nesting is well-typed by construction. -/
def nestedThreshold {E W : Type*} (wcr : WorldCredence E W)
    (θ : ℚ) (a : E) (φ : (W → Bool)) : (W → Bool) :=
  fun w => decide (wcr a w φ ≥ θ)

/-- Negated nested threshold: agent `a`'s credence in `φ` falls below
    `1 − θ` at world `w`. For negated expressions like "certainly not"
    and "probably not" ([herbstritt-franke-2019] eq. 14):

    ⟦certainly not(p)⟧ = {s ∈ S | s/10 < 1 − θ_certainly}
    ⟦probably not(p)⟧  = {s ∈ S | s/10 < 1 − θ_probably} -/
def nestedThresholdNeg {E W : Type*} (wcr : WorldCredence E W)
    (θ : ℚ) (a : E) (φ : (W → Bool)) : (W → Bool) :=
  fun w => decide (wcr a w φ < 1 - θ)

/-- Complex expressions compose: the result of one `nestedThreshold`
    can be the input to another.

    Example ([herbstritt-franke-2019]):
    `certainly(probably(RED))` = `nestedThreshold θ_cert (nestedThreshold θ_prob RED)` -/
def complexExpression {E W : Type*} (wcr : WorldCredence E W)
    (θ_outer θ_inner : ℚ) (a : E) (φ : (W → Bool)) : (W → Bool) :=
  nestedThreshold wcr θ_outer a (nestedThreshold wcr θ_inner a φ)

end Modality.EpistemicProbability
