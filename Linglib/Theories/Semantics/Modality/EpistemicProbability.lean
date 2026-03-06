import Linglib.Theories.Semantics.Attitudes.EpistemicThreshold
import Linglib.Theories.Semantics.Modality.ProbabilityOrdering

/-!
# Epistemic Modality: Nested Threshold Semantics
@cite{fagin-halpern-1994} @cite{herbstritt-franke-2019} @cite{lassiter-goodman-2017} @cite{ying-zhi-xuan-wong-mansinghka-tenenbaum-2025}

Extends the flat threshold semantics of `Attitudes/EpistemicThreshold.lean`
with *world-dependent credence* and *nested thresholds* for epistemic modals.

## Attitudes/ vs Modality/

The split between these directories mirrors a real theoretical distinction:

- **`Attitudes/EpistemicThreshold`**: flat (world-independent) threshold
  semantics for attitude verbs. `AgentCredence E W = E → BProp W → ℚ`.
  The agent's credence in φ is a single number, regardless of which world
  we evaluate at. Handles: *believes*, *knows*, *is certain that*.

- **`Modality/EpistemicProbability` (this file)**: world-dependent threshold semantics
  for epistemic modals, especially nested/complex expressions.
  `WorldCredence E W = E → W → BProp W → ℚ`. The agent's credence in φ
  can vary across worlds (reflecting different information states). Handles:
  *probably*, *certainly*, *certainly likely*, *might be possible*.

The key difference is **higher-order uncertainty**: when we say "it's
certainly likely that P", we are asserting something about the agent's
*distribution over possible credence levels* — not just a single credence
value. This requires world-dependent credence: at each possible world, the
agent has a different belief state, and the outer expression quantifies
over those belief states.

## Fagin & Halpern (1994)

The formal foundation is @cite{fagin-halpern-1994}'s logic for reasoning
about knowledge and probability. Their key innovation: probability formulas
`w_i(φ) ≥ b` (agent i assigns probability ≥ b to φ) can be *nested*:

    w_i(w_j(φ) ≥ b₁) ≥ b₂

meaning "agent i believes with probability ≥ b₂ that agent j assigns
probability ≥ b₁ to φ." In our formalization, this becomes:

    nestedThreshold wcr θ₂ i (nestedThreshold wcr θ₁ j φ)

The compositional structure is captured by the type: `nestedThreshold`
takes a `BProp W` and returns a `BProp W`, so it can be iterated.

## Connection to Kratzer

The bridge is `Modality/ProbabilityOrdering.lean`: a probability assignment
P over worlds induces a Kratzer ordering source where more probable worlds
rank higher. The threshold semantics then arises by cutting this ordering at
specific probability values. For finite models with a single epistemic agent,
the two formalizations agree.
-/

set_option autoImplicit false

namespace Semantics.Modality.EpistemicProbability

open Semantics.Attitudes.EpistemicThreshold
open Core.Proposition

-- ============================================================================
-- §1. World-Dependent Credence
-- ============================================================================

/-- World-dependent agent credence: at each world `w`, agent `a` has
    a (possibly different) probability distribution, yielding credence
    in proposition `φ`.

    This is @cite{fagin-halpern-1994}'s `μ_{i,s}`: the probability space
    associated with agent `i` at state `s`. The key difference from
    `AgentCredence` is the world parameter — the agent's beliefs can
    vary across worlds (reflecting different information states).

    In @cite{herbstritt-franke-2019}'s urn scenario, each (observation, access)
    pair induces a different belief distribution over urn states, so
    the agent's credence in "RED is probable" depends on which world
    (= which observation) they are in. -/
abbrev WorldCredence (E W : Type*) := E → W → BProp W → ℚ

/-- Lift world-independent credence to world-dependent credence.

    When the agent's credence does not vary across worlds (i.e., no
    higher-order uncertainty), `AgentCredence` embeds into `WorldCredence`
    by ignoring the world parameter. This is the degenerate case where
    simple and complex expressions collapse to the same interpretation. -/
def liftCredence {E W : Type*}
    (cr : AgentCredence E W) : WorldCredence E W :=
  fun a _w φ => cr a φ

-- ============================================================================
-- §2. Nested Threshold Operators
-- ============================================================================

/-- Nested threshold: agent `a`'s credence in `φ` meets threshold `θ`
    *at world `w`*. Returns a `BProp W` that can be nested further.

    This is the core compositional operator for complex probability
    expressions. Each application adds one layer of threshold evaluation:

    ```
    nestedThreshold wcr θ_prob a RED         -- ⟦probably(RED)⟧ : BProp W
    nestedThreshold wcr θ_cert a             -- ⟦certainly(·)⟧ : BProp W → BProp W
      (nestedThreshold wcr θ_prob a RED)     -- ⟦certainly(probably(RED))⟧ : BProp W
    ```

    The output type `BProp W = W → Bool` is the same as the input
    proposition type, so nesting is well-typed by construction. -/
def nestedThreshold {E W : Type*} (wcr : WorldCredence E W)
    (θ : ℚ) (a : E) (φ : BProp W) : BProp W :=
  fun w => decide (wcr a w φ ≥ θ)

/-- Negated nested threshold: agent `a`'s credence in `φ` falls below
    `1 − θ` at world `w`. For negated expressions like "certainly not"
    and "probably not" (@cite{herbstritt-franke-2019} eq. 14):

    ⟦certainly not(p)⟧ = {s ∈ S | s/10 < 1 − θ_certainly}
    ⟦probably not(p)⟧  = {s ∈ S | s/10 < 1 − θ_probably} -/
def nestedThresholdNeg {E W : Type*} (wcr : WorldCredence E W)
    (θ : ℚ) (a : E) (φ : BProp W) : BProp W :=
  fun w => decide (wcr a w φ < 1 - θ)

/-- Complex expressions compose: the result of one `nestedThreshold`
    can be the input to another.

    Example (@cite{herbstritt-franke-2019}):
    `certainly(probably(RED))` = `nestedThreshold θ_cert (nestedThreshold θ_prob RED)` -/
def complexExpression {E W : Type*} (wcr : WorldCredence E W)
    (θ_outer θ_inner : ℚ) (a : E) (φ : BProp W) : BProp W :=
  nestedThreshold wcr θ_outer a (nestedThreshold wcr θ_inner a φ)

-- ============================================================================
-- §3. Bridge to Flat Threshold Semantics
-- ============================================================================

/-- When credence is world-independent, `nestedThreshold` agrees with
    `meetsThreshold` (modulo the Prop/Bool distinction).

    This is the consistency check: the nested framework correctly
    generalizes the flat framework. First-order expressions give the
    same interpretation either way. -/
theorem nestedThreshold_const_iff {E W : Type*}
    (cr : AgentCredence E W) (θ : ℚ) (a : E) (φ : BProp W) (w : W) :
    (nestedThreshold (liftCredence cr) θ a φ) w = true ↔
    meetsThreshold cr θ a φ := by
  simp only [nestedThreshold, liftCredence, meetsThreshold, decide_eq_true_eq]

-- ============================================================================
-- §4. Standard Thresholds for Probability Expressions
-- ============================================================================

/-- Standard thresholds for probability expressions.

    These are the LaBToM-fitted values
    (@cite{ying-zhi-xuan-wong-mansinghka-tenenbaum-2025}, Table 1(b)).
    @cite{herbstritt-franke-2019} independently infers similar values from
    production/interpretation data:

    | Expression | LaBToM θ | H&F2019 θ (mean) |
    |------------|----------|------------------|
    | possibly   | might=0.20 / may=0.30 | 0.247 |
    | probably   | likely=0.70 | 0.549 |
    | certainly  | certain=0.95 | 0.949 |

    The "probably" discrepancy (0.70 vs 0.55) may reflect the difference
    between "likely" (LaBToM's ToM task) and "probably" (H&F's production
    task), or differences in the experimental paradigm. -/
def θ_certainly := EpistemicEntry.certain_.θ
def θ_probably  := EpistemicEntry.likely_.θ
def θ_possibly  := EpistemicEntry.might_.θ

/-- The threshold ordering for probability expressions:
    certainly > probably > possibly. -/
theorem threshold_ordering :
    θ_possibly < θ_probably ∧ θ_probably < θ_certainly := by
  constructor <;> simp [θ_possibly, θ_probably, θ_certainly,
    EpistemicEntry.might_, EpistemicEntry.likely_, EpistemicEntry.certain_] <;> norm_num

end Semantics.Modality.EpistemicProbability
