import Mathlib.Data.Set.Basic
import Linglib.Core.Order.Boundedness
import Linglib.Semantics.Degree.Predicate
import Linglib.Core.Order.ComparativeScale
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Attitudes.Confidence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Epistemic Threshold Semantics

[ying-zhi-xuan-wong-mansinghka-tenenbaum-2025] [baker-jara-ettinger-saxe-tenenbaum-2017] [klein-1980] [lassiter-goodman-2017] [hintikka-1962]

Epistemic vocabulary — attitude verbs (`believes`, `knows`), modal verbs
(`might`, `must`), and modal adjectives (`likely`, `certain`) — denotes
**threshold functions over agent credence** Pr(A, φ).

This file formalizes the **probabilistic-credence-with-threshold** tradition
(LaBToM: [ying-zhi-xuan-wong-mansinghka-tenenbaum-2025]; epistemic
modals: [lassiter-goodman-2017]). It is **not** a formalization of
[cariani-santorio-wellwood-2024]'s confidence semantics — CSW's account
is in `Confidence.lean` and is explicitly non-probabilistic. §6 below
documents the empirical disagreement between the two traditions; the
refutation theorem `confidence_not_probabilistic` packages it formally.

## The Core Idea

Every epistemic expression reduces to a comparison of the agent's credence
against a threshold (Table 1(a)):

    believes(A, φ) ⟺ Pr(A, φ) ≥ θ_believes
    knows_that(A, φ) ⟺ believes(A, φ) ∧ φ
    certain(A, φ) ⟺ Pr(A, φ) ≥ θ_certain
    must(φ) ⟺ λA. Pr(A, φ) ≥ θ_must
    likely(φ) ⟺ λA. Pr(A, φ) ≥ θ_likely
    might(φ) ⟺ λA. Pr(A, φ) ≥ θ_might

## Degree-Threshold Isomorphism

The threshold semantics is structurally identical to the positive form of
gradable adjectives:

    ⟦tall⟧(x) = height(x) ≥ θ_tall (the ≥-threshold condition)
    ⟦believes⟧(A, φ) = Pr(A, φ) ≥ θ_bel (meetsThreshold)

Both are instances of the same degree-threshold architecture: a measure
function maps an entity to a degree on a scale, and the predicate holds
iff the degree meets a contextual/lexical threshold. Epistemic expressions
are gradable predicates on a probability scale bounded by [0, 1].

This connection is formalized in §8 via `epistemicAsDirectedMeasure`.

## Unification of Three Formalizations

This collapses three previously separate treatments in the library:

1. **Doxastic.lean** (Hintikka): Boolean accessibility. Believes iff φ holds
   at ALL accessible worlds — the θ → 1 limit of threshold semantics.

2. **Confidence.lean**: Ordinal confidence ordering. Credence
   induces the same upward-monotone preorder (`credence_upward_monotone`
   below), but CSW's ordering is explicitly non-probabilistic (conjunction
   fallacy compatible), while LaBToM's Pr is a genuine probability.

3. **Modality/ProbabilityOrdering.lean**: Probability → Kratzer ordering.
   Threshold semantics generalizes this to agent-relative epistemic modality,
   unifying epistemic modals with attitude verbs under one mechanism.

## Attitude–Modal Unification

Attitude verbs and epistemic modals differ only in threshold and whether
the agent is syntactically projected or λ-abstracted:

| Expression | Agent     | θ    | Category      |
|------------|-----------|------|---------------|
| believes   | explicit  | 0.75 | attitude verb |
| knows      | explicit  | 0.75 + factive | attitude verb |
| certain    | explicit  | 0.95 | attitude adj  |
| should     | abstracted| 0.80 | modal verb    |
| must       | abstracted| 0.95 | modal verb    |
| likely     | abstracted| 0.70 | modal adj     |
| may        | abstracted| 0.30 | modal verb    |
| might      | abstracted| 0.20 | modal verb    |

## BToM Grounding

Pr(A, φ) is computed via BToM inference (`Core`). Given an observed
action `a`, the observer estimates agent credence by marginalizing:

    Pr_obs(Agent, φ | a) = Σ_b P(b | a) · ⟦φ⟧_b

where P(b | a) is the BToM belief marginal (`BToMModel.beliefMarginal`).
Through the RSA-BToM bridge (`L1_eq_btom_worldMarginal`), this connects
to the pragmatic listener's interpretation of epistemic language.

-/

namespace Semantics.Attitudes.EpistemicThreshold

-- ============================================================================
-- §1. Agent Credence
-- ============================================================================

/-- Agent credence: the degree of confidence agent `a` assigns to
    proposition `φ` being true.

    This is the fundamental primitive of epistemic threshold semantics.
    In LaBToM, it is grounded in BToM inference: the observer computes
    the agent's credence by marginalizing over inferred belief states.
    In the abstract theory, it is any function from agents and propositions
    to rationals satisfying basic ordering axioms. -/
abbrev AgentCredence (E W : Type*) := E → (W → Bool) → ℚ

-- ============================================================================
-- §2. Epistemic Lexicon
-- ============================================================================

/-- An epistemic lexical entry: a threshold comparison over agent credence.

    Each epistemic expression (attitude verb, modal verb, modal adjective)
    is characterized by:
    - `θ`: the credence threshold — the expression holds iff Pr(A, φ) ≥ θ
    - `factive`: whether the expression additionally requires φ to be true
      at the evaluation world (e.g., `knows` but not `believes`)

    The lexical *form* (English string) is not stored on the entry —
    Fragment files (`Fragments/English/...`) carry the form-to-entry
    mapping; the entry itself is purely semantic. -/
structure EpistemicEntry where
  /-- Credence threshold -/
  θ : ℚ
  /-- Factivity flag -/
  factive : Bool := false
  deriving DecidableEq, Repr

/-! Standard epistemic thresholds ([ying-zhi-xuan-wong-mansinghka-tenenbaum-2025], Table 1(b)).

These are the best-fit values from LaBToM's grid-search parameter
fitting against human plausibility ratings in a Doors, Keys, & Gems
gridworld experiment (§4.5, Table B1). The ordering is the
theoretical commitment; the specific values are empirical fits:

  must/certain (0.95) > should (0.80) > believes (0.75) >
  likely/uncertain (0.70) > unlikely (0.40) > may (0.30) >
  might/could (0.20) -/
namespace EpistemicEntry

def believes_ : EpistemicEntry := ⟨3/4, false⟩
def knows_    : EpistemicEntry := ⟨3/4, true⟩
def certain_  : EpistemicEntry := ⟨19/20, false⟩
def must_     : EpistemicEntry := ⟨19/20, false⟩
def should_   : EpistemicEntry := ⟨4/5, false⟩
def likely_   : EpistemicEntry := ⟨7/10, false⟩
def may_      : EpistemicEntry := ⟨3/10, false⟩
def might_    : EpistemicEntry := ⟨1/5, false⟩
def could_    : EpistemicEntry := ⟨1/5, false⟩

/-! Reversed-polarity entries: these hold when credence is BELOW a threshold.
`uncertain` and `unlikely` use strict `<` rather than `≥`. They are not
modeled via `holdsAt` but via `failsThreshold` (§3). -/
def uncertain_ : EpistemicEntry := ⟨7/10, false⟩
def unlikely_  : EpistemicEntry := ⟨2/5, false⟩

/-- The full threshold scale (Table 1(b)) is strictly decreasing:
    must = certain > should > believes > likely = uncertain > unlikely > may > might = could.

    Proven by reducing `IsChain` on the explicit list to a conjunction of
    pairwise inequalities, then closing each by `norm_num`. -/
theorem epistemic_scale_sorted :
    [19/20, 4/5, 3/4, 7/10, 2/5, 3/10, (1 : ℚ)/5].IsChain (· > ·) := by
  refine .cons_cons (by norm_num) (.cons_cons (by norm_num)
    (.cons_cons (by norm_num) (.cons_cons (by norm_num)
      (.cons_cons (by norm_num) (.cons_cons (by norm_num)
        (.singleton _))))))

/-- The superlative multiplier α_most = 1.5 (Table 1(b)). -/
def α_most : ℚ := 3/2

end EpistemicEntry

-- ============================================================================
-- §3. Core Operators
-- ============================================================================

variable {E W : Type*}

/-- Threshold semantics: agent `a`'s credence in `φ` meets threshold `θ`.

    This is the single mechanism underlying all epistemic vocabulary.
    `believes`, `knows`, `certain`, `must`, `might` are all instances.

    Structurally identical to the degree-semantic ≥-threshold condition
    `measure(entity) ≥ threshold`. -/
def meetsThreshold (cr : AgentCredence E W) (θ : ℚ)
    (a : E) (φ : (W → Bool)) : Prop :=
  cr a φ ≥ θ

/-- Reversed threshold: agent `a`'s credence in `φ` is strictly BELOW `θ`.

    Used for `uncertain` and `unlikely`: uncertain_if(A, φ, ψ) holds iff
    Pr(A, φ) < θ_uncertain ∧ Pr(A, ψ) < θ_uncertain (Table 1(a)). -/
def failsThreshold (cr : AgentCredence E W) (θ : ℚ)
    (a : E) (φ : (W → Bool)) : Prop :=
  cr a φ < θ

/-- Full epistemic evaluation: credence meets threshold, plus factivity.

    - `believes(A, φ, w)` = Pr(A, φ) ≥ 0.75
    - `knows(A, φ, w)` = Pr(A, φ) ≥ 0.75 ∧ φ(w) = true -/
def holdsAt (cr : AgentCredence E W) (entry : EpistemicEntry)
    (a : E) (φ : (W → Bool)) (w : W) : Prop :=
  meetsThreshold cr entry.θ a φ ∧ (entry.factive = true → φ w = true)

-- ── Structural operators from Table 1(a) ──

/-- `knows_if(A, φ)` = knows_that(A, φ) ∨ knows_that(A, ¬φ).
    The agent knows the answer to the yes/no question ?φ. -/
def knowsIf (cr : AgentCredence E W) (a : E) (φ : (W → Bool)) (w : W) : Prop :=
  holdsAt cr .knows_ a φ w ∨
  holdsAt cr .knows_ a (fun w' => !φ w') w

/-- `not_knows_that(A, φ)` = ¬believes(A, φ) ∧ φ.
    False belief: φ is true but the agent doesn't believe it. -/
def notKnowsThat (cr : AgentCredence E W) (a : E) (φ : (W → Bool)) (w : W) : Prop :=
  ¬meetsThreshold cr EpistemicEntry.believes_.θ a φ ∧ φ w = true

/-- `uncertain_if(A, φ, ψ)` = Pr(A, φ) < θ_uncertain ∧ Pr(A, ψ) < θ_uncertain.
    The agent is uncertain between two alternatives. -/
def uncertainIf (cr : AgentCredence E W) (a : E) (φ ψ : (W → Bool)) : Prop :=
  failsThreshold cr EpistemicEntry.uncertain_.θ a φ ∧
  failsThreshold cr EpistemicEntry.uncertain_.θ a ψ

-- ── Degree function and comparatives (Table 1(a)) ──

/-- Comparative credence: `more(P, φ, ψ)` = cr(A, φ) > cr(A, ψ).

    The agent's credence in φ strictly exceeds credence in ψ. Mirrors the
    comparative from `Confidence.lean` and from `Degree/Basic.lean`. -/
def moreCredent (cr : AgentCredence E W)
    (a : E) (φ ψ : (W → Bool)) : Prop :=
  cr a ψ < cr a φ

/-- Superlative: `most_str(P, φ)` = degree(P, A, φ) ≥ α_most · θ_P.
    Strengthened superlative with multiplier α_most = 1.5 (Table 1(b)). -/
def mostStr (cr : AgentCredence E W) (entry : EpistemicEntry)
    (a : E) (φ : (W → Bool)) : Prop :=
  cr a φ ≥ EpistemicEntry.α_most * entry.θ

-- ============================================================================
-- §4. Entailment Properties
-- ============================================================================

/-- Higher thresholds entail lower thresholds.

    If an expression with threshold θ₂ holds, then any expression with
    a lower threshold θ₁ ≤ θ₂ also holds. This derives the entailment
    patterns of epistemic vocabulary from the threshold ordering alone. -/
theorem threshold_monotone (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) {θ₁ θ₂ : ℚ} (h : θ₁ ≤ θ₂) :
    meetsThreshold cr θ₂ a φ → meetsThreshold cr θ₁ a φ :=
  fun h₂ => le_trans h h₂

/-- Generic `holdsAt` entailment: a stronger entry (higher threshold,
    weaker factivity) entails a weaker one.

    Factors `threshold_monotone` plus the factivity-loss requirement.
    Every named pairwise entailment below is one application of this
    lemma. -/
theorem holdsAt_mono_of_le {e₁ e₂ : EpistemicEntry}
    (hθ : e₁.θ ≤ e₂.θ) (hf : e₁.factive = true → e₂.factive = true)
    (cr : AgentCredence E W) (a : E) (φ : (W → Bool)) (w : W) :
    holdsAt cr e₂ a φ w → holdsAt cr e₁ a φ w := by
  intro ⟨hcr, hfact⟩
  refine ⟨threshold_monotone cr a φ hθ hcr, ?_⟩
  intro h₁
  exact hfact (hf h₁)

/-- `knows` entails `believes`: same threshold, `knows` adds factivity. -/
theorem knows_entails_believes (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) (w : W) :
    holdsAt cr .knows_ a φ w → holdsAt cr .believes_ a φ w :=
  holdsAt_mono_of_le (le_refl (3/4 : ℚ)) (by decide) cr a φ w

/-- `knows` is veridical: knowledge entails truth.

    This mirrors `Veridicality.veridical` in `Doxastic.lean`: veridical
    predicates entail their complement. In ELoT, veridicality is the
    `factive = true` flag. -/
theorem knows_is_veridical (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) (w : W) :
    holdsAt cr .knows_ a φ w → φ w = true :=
  fun ⟨_, h⟩ => h rfl

/-- `certain` entails `believes`: θ_certain = 19/20 ≥ θ_believes = 3/4. -/
theorem certain_entails_believes (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) (w : W) :
    holdsAt cr .certain_ a φ w → holdsAt cr .believes_ a φ w :=
  holdsAt_mono_of_le (by norm_num : (3 : ℚ)/4 ≤ 19/20) (by decide) cr a φ w

/-- `must` entails `should`: θ_must = 19/20 ≥ θ_should = 4/5. -/
theorem must_entails_should (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) (w : W) :
    holdsAt cr .must_ a φ w → holdsAt cr .should_ a φ w :=
  holdsAt_mono_of_le (by norm_num : (4 : ℚ)/5 ≤ 19/20) (by decide) cr a φ w

/-- `should` entails `likely`: θ_should = 4/5 ≥ θ_likely = 7/10. -/
theorem should_entails_likely (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) (w : W) :
    holdsAt cr .should_ a φ w → holdsAt cr .likely_ a φ w :=
  holdsAt_mono_of_le (by norm_num : (7 : ℚ)/10 ≤ 4/5) (by decide) cr a φ w

/-- `must` entails `might`: necessity entails possibility (□φ → ◇φ).
    θ_must = 19/20 ≥ θ_might = 1/5. -/
theorem must_entails_might (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) (w : W) :
    holdsAt cr .must_ a φ w → holdsAt cr .might_ a φ w :=
  holdsAt_mono_of_le (by norm_num : (1 : ℚ)/5 ≤ 19/20) (by decide) cr a φ w

/-- `believes` entails `may`: θ_believes = 3/4 ≥ θ_may = 3/10. -/
theorem believes_entails_may (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) (w : W) :
    holdsAt cr .believes_ a φ w → holdsAt cr .may_ a φ w :=
  holdsAt_mono_of_le (by norm_num : (3 : ℚ)/10 ≤ 3/4) (by decide) cr a φ w

-- ============================================================================
-- §5. Comparative Properties
-- ============================================================================

/-- Comparative credence is transitive.

    Mirrors `comparative_transitive` in `Confidence.lean` (CSW (54)). -/
theorem moreCredent_transitive (cr : AgentCredence E W)
    (a : E) (φ ψ χ : (W → Bool))
    (h₁ : moreCredent cr a φ ψ) (h₂ : moreCredent cr a ψ χ) :
    moreCredent cr a φ χ :=
  lt_trans h₂ h₁

/-- Upward monotonicity of belief under the credence ordering.

    If the agent believes φ and is at least as confident of ψ as of φ,
    then the agent believes ψ. This is the credence-based analogue of
    `confidence_upward_monotone` in `Confidence.lean` (CSW (53)). -/
theorem credence_upward_monotone (cr : AgentCredence E W)
    (θ : ℚ) (a : E) (φ ψ : (W → Bool))
    (h_bel : meetsThreshold cr θ a φ) (h_more : cr a φ ≤ cr a ψ) :
    meetsThreshold cr θ a ψ :=
  le_trans h_bel h_more

-- ============================================================================
-- §6. Probabilistic Credence and Conjunction
-- ============================================================================

/-!
### Key Divergence from Confidence.lean

CSW's confidence ordering is NOT constrained to respect logical conjunction
(it imposes no conjunction-monotonicity axiom on the background preorder), so it
is consistent to be confident of (p ∧ q) without being confident of p.

When `AgentCredence` is a genuine probability measure (as in LaBToM), this
cannot happen: Pr(A, p ∧ q) ≤ Pr(A, p) always (`isProbabilistic_conj_elim`).
The witness that the two diverge is `confidence_not_probabilistic` below.
-/

/-- A probabilistic credence function is `Monotone` (from Mathlib) in
    the pointwise Bool ordering on `(W → Bool)`: if φ ⊆ ψ then
    Pr(A, φ) ≤ Pr(A, ψ).

    This is the axiom that separates LaBToM's probabilistic credence
    from CSW's ordinal confidence ordering, which imposes no
    conjunction-monotonicity constraint and so permits conjunction
    fallacies; `isProbabilistic` rules them out (witness:
    `confidence_not_probabilistic`).

    Conjunction elimination (`isProbabilistic_conj_elim`) is a
    consequence: since `φ ∧ ψ ≤ φ` pointwise, monotonicity gives
    `Pr(A, φ ∧ ψ) ≤ Pr(A, φ)`. In fact the two are equivalent on
    `(W → Bool)` (a `SemilatticeInf`), since `a ≤ b ↔ a ⊓ b = a`.

    By using Mathlib's `Monotone`, this connects to the same abstract
    notion used throughout linglib: `IsUpwardEntailing = Monotone`
    (`Entailment/Polarity.lean`), `MeasureMonotone = ∀ i w, Monotone`
    (`KnowledgeProbability.lean`), etc. -/
def isProbabilistic (cr : AgentCredence E W) : Prop :=
  ∀ (a : E), Monotone (cr a)

/-- Conjunction elimination follows from `isProbabilistic`: since
    `φ ∧ ψ ≤ φ` in the pointwise Bool ordering, monotonicity gives
    `Pr(A, φ ∧ ψ) ≤ Pr(A, φ)`. -/
theorem isProbabilistic_conj_elim (cr : AgentCredence E W)
    (h_prob : isProbabilistic cr) (a : E) (φ ψ : (W → Bool)) :
    cr a (fun w => φ w && ψ w) ≤ cr a φ :=
  h_prob a (fun {v} => Bool.and_le_left (φ v) (ψ v))

/-- Probabilistic credence validates conjunction elimination for belief.

    If the agent believes (φ ∧ ψ) and credence is probabilistic, then
    the agent believes φ. This fails for CSW's non-probabilistic ordering
    (conjunction fallacy). -/
theorem prob_conjunction_elim (cr : AgentCredence E W)
    (h_prob : isProbabilistic cr) (θ : ℚ) (a : E) (φ ψ : (W → Bool))
    (h_bel : meetsThreshold cr θ a (fun w => φ w && ψ w)) :
    meetsThreshold cr θ a φ :=
  le_trans h_bel (isProbabilistic_conj_elim cr h_prob a φ ψ)

/-- **CSW vs threshold-credence divergence theorem.**

    There exists an `AgentCredence` admitting a conjunction-fallacy witness —
    `cr (φ ∧ ψ) > cr φ` with `φ`, `ψ`, and `φ ∧ ψ` all *consistent* — that
    consequently fails `isProbabilistic`.

    This formalizes the empirical disagreement CSW §4.6 (around (52)) use against
    probabilistic-credence accounts of confidence: a confidence ordering can rank
    a conjunction strictly above one of its conjuncts (the Tversky–Kahneman
    pattern, [tversky-kahneman-1983]), whereas any probabilistic credence forbids
    it (`prob_conjunction_elim`). The two theories make incompatible predictions
    on the same datum.

    Witness (Unit-agent / Bool-world): `cr a p = if p false then 0 else 1`,
    `φ = ⊤` (always true), `ψ = {true}` (`fun w => w`). Then `φ ∧ ψ = {true} ⊊ φ`,
    all three *consistent*, and `cr φ = 0 < 1 = cr (φ ∧ ψ)`. The `cr` is
    non-monotone because `{true} ≤ ⊤` pointwise yet `cr {true} = 1 > 0 = cr ⊤`.
    (Earlier this used a `φ ∧ ψ = ⊥` witness — confidence in a contradiction —
    which proved the existential but modelled the fallacy degenerately.) -/
theorem confidence_not_probabilistic :
    ∃ (cr : AgentCredence Unit Bool),
      ¬ isProbabilistic cr ∧
      ∃ (φ ψ : Bool → Bool),
        cr () φ < cr () (fun w => φ w && ψ w) := by
  refine ⟨fun _ p => if p false then (0 : ℚ) else 1,
          ?_, (fun _ => true), (fun w => w), ?_⟩
  · intro h
    have hle : (fun w => w) ≤ (fun _ : Bool => true) := by intro w; cases w <;> decide
    have : (1 : ℚ) ≤ 0 := h () hle
    linarith
  · show (0 : ℚ) < 1
    norm_num


-- ============================================================================
-- §8. Degree-Threshold Bridge
-- ============================================================================

/-!
### Epistemic Expressions as Gradable Predicates

The structural analogy between adjective degree semantics ([kennedy-2007],
[lassiter-goodman-2017]) and epistemic threshold semantics: both are
instances of `μ(entity) ≥ θ`. The threshold semantics makes this precise:

    ⟦tall⟧(x) = height(x) ≥ θ_tall (the ≥-threshold condition)
    ⟦believes⟧(A, φ) = Pr(A, φ) ≥ θ_bel (meetsThreshold)

Both are instances of `μ(entity) ≥ θ`. The epistemic scale is the
probability interval [0, 1], which is **closed** in the sense of [kennedy-2007]: it has both an upper bound (certainty, 1) and a lower bound
(impossibility, 0).

This has consequences for scale structure:
- Closed-scale adjectives (like `full`, `certain`) license absolute
  standards (the endpoint). For `certain`, the endpoint IS θ = 0.95 ≈ 1.
- Open-scale adjectives (like `tall`) require contextual standards.
  For `likely`, the threshold θ = 0.70 is contextually fit.

The structural parallel also extends to comparatives and superlatives:
- "more likely than" = moreCredent (comparative on probability scale)
- "most likely" = mostStr with multiplier α_most = 1.5

See `Semantics/Probabilistic/SDS/ThresholdSemantics.lean` for
the unified threshold pattern across adjectives, generics, and epistemic
expressions.
-/

/-- The epistemic probability scale is closed: bounded by [0, 1].

    This classifies the credence scale as `Boundedness.closed`, meaning
    epistemic adjectives like `certain` license absolute standards. -/
def epistemicBoundedness : Core.Order.Boundedness := .closed

/-- An epistemic gradable predicate: an `EpistemicEntry` viewed as a
    `DirectedMeasure` on the probability scale.

    The entity type is `E × (W → Bool)` (agent–proposition pairs), and the
    measure function is agent credence `cr`. This makes the structural
    identity with degree semantics explicit and type-checked.

    Polarity: threshold entries (`believes`, `must`, `likely`) are positive
    (upward monotone: higher credence → more likely to satisfy). Reversed
    entries (`uncertain`, `unlikely`) are negative (downward monotone). -/
def epistemicAsDirectedMeasure (cr : AgentCredence E W) (_entry : EpistemicEntry)
    : Degree.DirectedMeasure ℚ (E × (W → Bool)) where
  μ := fun ⟨a, φ⟩ => cr a φ
  boundedness := epistemicBoundedness

/-- The degree-threshold identity: `meetsThreshold` is the ≥-threshold
    condition `θ ≤ μ(entity)` with credence as the measure function.

    This is the formal statement that epistemic threshold semantics IS
    degree semantics (the positive-form `Comparison.ge.over μ θ`
    condition) with credence as the measure function. -/
theorem meetsThreshold_eq_threshold (cr : AgentCredence E W) (θ : ℚ)
    (a : E) (φ : (W → Bool)) :
    meetsThreshold cr θ a φ ↔ θ ≤ cr a φ := by
  rfl

/-- The epistemic scale is licensed: closed → admits absolute standards.

    Since credence is bounded by [0, 1], [kennedy-2007]'s licensing
    prediction says epistemic adjectives like `certain` license endpoint
    standards and maximizers ("completely certain") via the same
    `Boundedness.closed` route as closed-scale adjectives ("completely
    full"); cross-source agreement is `LicensingPipeline.universal`
    (`Core/Order/Boundedness.lean`). -/
theorem epistemicScale_licensed :
    epistemicBoundedness.IsLicensed := trivial

-- ============================================================================
-- §9. Connection to Holliday–Icard Epistemic Likelihood
-- ============================================================================

/-!
### From Credence to Comparative Likelihood

When `AgentCredence` is a genuine probability measure (probabilistic
credence), it induces the full [holliday-icard-2013] hierarchy:

    AgentCredence → FinAddMeasure → EpistemicSystemFA
                                    ↓
                              comparative likelihood ≿
                                    ↓
                              threshold cuts → ELoT

The key insight: `moreCredent cr a φ ψ` (comparative epistemic) is
exactly `FinAddMeasure.inducedGe` applied to singleton propositions.
Threshold semantics then arises by cutting this comparative ordering
at specific points on the scale.

This places the Ying et al. threshold semantics within the algebraic
framework of `Core/Scales/EpistemicScale.lean`: the fitted thresholds from
Table 1(b) are points on a finitely additive probability scale that
satisfies System FA (and hence all of W ⊂ F ⊂ FA).
-/

/-- Threshold semantics is upward monotone in the credence ordering:
    if `cr a φ ≥ θ` and `cr a φ ≤ cr a ψ`, then `cr a ψ ≥ θ`.

    This is an instance of `Degree.IsUpwardMonotone` applied to the
    epistemic scale. The family of propositions `P(θ) = meetsThreshold θ`
    is upward monotone in credence — higher credence always satisfies
    lower thresholds.

    Connects to CSW's `confidence_upward_monotone` and to Lassiter's
    observation that epistemic modals form a Horn scale ordered by
    threshold strength. -/
theorem threshold_upwardMonotone (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) :
    ∀ (θ₁ θ₂ : ℚ), θ₁ ≤ θ₂ →
    meetsThreshold cr θ₂ a φ → meetsThreshold cr θ₁ a φ :=
  fun _ _ h h₂ => le_trans h h₂

/-- `failsThreshold` is downward monotone: if credence is below θ₁
    and θ₁ ≤ θ₂, then credence is below θ₂. This is the polarity
    reversal for `uncertain`/`unlikely`: higher thresholds are easier
    to fail.

    Connects to Kennedy's negative adjective pattern (short, cold):
    negative polarity on the same scale. -/
theorem failsThreshold_downwardMonotone (cr : AgentCredence E W)
    (a : E) (φ : (W → Bool)) :
    ∀ (θ₁ θ₂ : ℚ), θ₁ ≤ θ₂ →
    failsThreshold cr θ₁ a φ → failsThreshold cr θ₂ a φ :=
  fun _ _ h h₁ => lt_of_lt_of_le h₁ h

/-- The epistemic threshold scale forms a `ComparativeScale` with
    closed boundedness. This places it in the same categorical
    structure as Kennedy's adjective scales, Krifka's mereological
    scales, and Holliday–Icard's epistemic likelihood scales. -/
def epistemicComparativeScale : Core.Order.ComparativeScale ℚ where
  boundedness := epistemicBoundedness

-- ============================================================================
-- §10. Degree-Semantic Bridges ([klein-1980])
-- ============================================================================

/-!
### Klein's Reduction: Comparative from Positive

The central formal insight of [klein-1980] — extended here to
epistemic modality — is that the comparative is not an independent
primitive but *reduces to* the positive form via existential quantification
over thresholds (or contexts, in Klein's original delineation semantics):

    "φ more likely than ψ" ↔ ∃θ. likely_θ(φ) ∧ ¬likely_θ(ψ)

In words: φ is more likely than ψ iff there is some threshold that φ's
credence meets but ψ's doesn't. This means the comparative ordering on
propositions is *determined by* the family of positive-form predicates
{meetsThreshold θ | θ ∈ ℚ}. The same reduction works for adjectives:

    "A taller than B" ↔ ∃θ. tall_θ(A) ∧ ¬tall_θ(B)

The non-trivial part is that this is a *biconditional*: not only does
a separating threshold imply the comparative (easy direction), but the
comparative implies a separating threshold exists (uses the witness
θ = cr(a, φ), which meets for φ by reflexivity and fails for ψ by
the comparative hypothesis). This is a genuine mathematical fact about
the structure of threshold semantics on a linear order.
-/

/-- **Klein's reduction**: the comparative reduces to the positive form.

    "φ more likely than ψ" iff there exists a threshold that φ meets
    and ψ fails. This is THE structural theorem connecting comparative
    and positive-form degree semantics, originally due to
    [klein-1980]'s delineation semantics for adjectives and
    extended to epistemic vocabulary by treating credence as a measure
    function.

    - Forward: if cr(a,ψ) < cr(a,φ), witness θ = cr(a,φ).
    - Backward: if θ separates, then cr(a,ψ) < θ ≤ cr(a,φ).

    Note: linglib's `Semantics/Gradability/Theory.lean` follows
    [kennedy-2007]'s degree typology (open/closed scales,
    min/max-standard adjectives), which is downstream of Klein's
    comparative reduction. -/
theorem comparative_from_positive (cr : AgentCredence E W)
    (a : E) (φ ψ : (W → Bool)) :
    moreCredent cr a φ ψ ↔
    ∃ θ : ℚ, meetsThreshold cr θ a φ ∧ ¬meetsThreshold cr θ a ψ := by
  constructor
  · intro h
    exact ⟨cr a φ, le_refl _, not_le.mpr h⟩
  · intro ⟨θ, hφ, hψ⟩
    exact lt_of_lt_of_le (not_le.mp hψ) hφ

/-- Polarity duality: `meetsThreshold` (positive) ↔ ¬`failsThreshold`.

    On a linear order, cr(a,φ) ≥ θ iff ¬(cr(a,φ) < θ). This is not
    `rfl` — it requires `not_lt` on `ℚ`'s linear order.

    On a probability scale, positive and negative epistemic modals are
    contradictories, not contraries — the same threshold θ separates
    "likely" from "unlikely" (cf. [lassiter-goodman-2017] fn. 8
    for the analogous tall/short case). -/
theorem meetsThreshold_iff_not_failsThreshold (cr : AgentCredence E W)
    (θ : ℚ) (a : E) (φ : (W → Bool)) :
    meetsThreshold cr θ a φ ↔ ¬failsThreshold cr θ a φ := by
  simp [meetsThreshold, failsThreshold, not_lt]

/-- **Antonymy from polarity**: the comparative holds iff there exists a
    threshold where the *positive* predicate holds for φ and the
    *negative* predicate holds for ψ.

    This is the formal content of "antonymy = scale reversal": the
    comparative "more likely" decomposes into a threshold that is
    simultaneously *met* by φ (positive: likely_θ) and *failed* by ψ
    (negative: unlikely_θ). Unlike the `rfl`-level type coincidence,
    this *derives* the antonymy connection from `comparative_from_positive`
    + `meetsThreshold_iff_not_failsThreshold`.

    The likely/unlikely pattern parallels [lassiter-goodman-2017]'s
    tall/short (Eqs. 22–23): same scale, reversed polarity. -/
theorem antonymy_from_polarity (cr : AgentCredence E W)
    (a : E) (φ ψ : (W → Bool)) :
    moreCredent cr a φ ψ ↔
    ∃ θ : ℚ, meetsThreshold cr θ a φ ∧ failsThreshold cr θ a ψ := by
  rw [comparative_from_positive]
  constructor
  · intro ⟨θ, hφ, hψ⟩
    exact ⟨θ, hφ, not_le.mp hψ⟩
  · intro ⟨θ, hφ, hψ⟩
    exact ⟨θ, hφ, not_le.mpr hψ⟩

-- ============================================================================
-- §11. Quantified Operators (Table 1(a))
-- ============================================================================

/-!
### Operators with Quantification over Entities

Table 1(a) includes operators that quantify over a context-restricted
domain of entities: `knows_about`, `certain_about`, `uncertain_about`,
and `most_sup`. These handle sentences like *"The player knows which
box has the key"* (knows_about) or *"The player is uncertain about
what's in box 3"* (uncertain_about).

These are parameterized by an entity type `X` (the quantification domain)
and a context set `C : X → Prop` restricting the domain.
-/

variable {X : Type*}

/-- `knows_about(A, C, φ)` = `∃x. C(x) ∧ knows_that(A, φ(x))`.

    The agent knows, for some contextually relevant entity x, that φ(x).
    Table 1(a): Type ε, Arg Types `A, Φ/O, Φ/O`. -/
def knowsAbout (cr : AgentCredence E W) (a : E)
    (C : X → Prop) (φ : X → (W → Bool)) (w : W) : Prop :=
  ∃ x, C x ∧ holdsAt cr .knows_ a (φ x) w

/-- `certain_about(A, C, φ)` = `∃x. C(x) ∧ Pr(A, φ(x)) ≥ θ_certain`.

    The agent is certain, for some contextually relevant entity, that φ holds.
    Table 1(a). -/
def certainAbout (cr : AgentCredence E W) (a : E)
    (C : X → Prop) (φ : X → (W → Bool)) : Prop :=
  ∃ x, C x ∧ meetsThreshold cr EpistemicEntry.certain_.θ a (φ x)

/-- `uncertain_about(A, C, φ)` = `∀x. C(x) → Pr(A, φ(x)) < θ_uncertain`.

    The agent is uncertain about φ for ALL contextually relevant entities.
    Note the universal quantification — this is the dual of `certain_about`'s
    existential.
    Table 1(a). -/
def uncertainAbout (cr : AgentCredence E W) (a : E)
    (C : X → Prop) (φ : X → (W → Bool)) : Prop :=
  ∀ x, C x → failsThreshold cr EpistemicEntry.uncertain_.θ a (φ x)

/-- `most_sup(P, O, C, φ)`: the degree of φ(O) is at least as great as
    the degree of φ(x) for every x in the context set C.

    "The player believes the key is *most likely* to be in box 1" means
    credence in "key in box 1" ≥ credence in "key in box x" for all
    relevant boxes x.
    Table 1(a). -/
def mostSup (cr : AgentCredence E W) (a : E)
    (o : X) (C : X → Prop) (φ : X → (W → Bool)) : Prop :=
  ∀ x, C x → cr a (φ x) ≤ cr a (φ o)

-- ── Entailments for quantified operators ──

/-- `knows_about` entails `knows_that` for any witness. -/
theorem knowsAbout_entails_knowsThat (cr : AgentCredence E W)
    (a : E) (C : X → Prop) (φ : X → (W → Bool)) (w : W) (x : X) (hC : C x) :
    holdsAt cr .knows_ a (φ x) w → knowsAbout cr a C φ w :=
  fun h => ⟨x, hC, h⟩

/-- `certain_about` entails that the agent believes the witness proposition. -/
theorem certainAbout_entails_believes (cr : AgentCredence E W)
    (a : E) (C : X → Prop) (φ : X → (W → Bool))
    (h : certainAbout cr a C φ) :
    ∃ x, C x ∧ meetsThreshold cr EpistemicEntry.believes_.θ a (φ x) := by
  obtain ⟨x, hC, hcr⟩ := h
  exact ⟨x, hC, le_trans (by norm_num : (3 : ℚ)/4 ≤ 19/20) hcr⟩

/-- `uncertain_about` and `certain_about` are incompatible: if the agent is
    uncertain about all C-entities, there is no C-entity about which the
    agent is certain. -/
theorem uncertainAbout_contradicts_certainAbout (cr : AgentCredence E W)
    (a : E) (C : X → Prop) (φ : X → (W → Bool))
    (h_unc : uncertainAbout cr a C φ)
    (h_cert : certainAbout cr a C φ) : False := by
  obtain ⟨x, hC, hcr⟩ := h_cert
  have h_fail := h_unc x hC
  simp only [failsThreshold, EpistemicEntry.uncertain_] at h_fail
  simp only [meetsThreshold, EpistemicEntry.certain_] at hcr
  linarith

-- ============================================================================
-- §12. Modal Embedding (Table 1(a))
-- ============================================================================

/-!
### Compositional Modal Embedding

The key compositional device from Table 1(a): `believes_modal(A, M) = M(A)`.
"*A believes it might rain*" = `might(rain)(A)` = `Pr(A, rain) ≥ θ_might`.
The belief verb contributes only agent projection; the modal's threshold
wins.

This is direct function application — no `believesModal` wrapper is
needed in the substrate. Study files that want to mark "this is the
modal-embedding position" should annotate at the call site rather than
introduce an identity-function alias. -/

-- ============================================================================
-- §13. Conjunction Elimination + Threshold Exhaustiveness
-- ============================================================================

/-!
### Conjunction-Closure Side of the CSW Divergence

The headline empirical disagreement between this file and `Confidence.lean`
is conjunction elimination. CSW's confidence ordering admits the conjunction
fallacy (its background preorder imposes no conjunction-monotonicity
constraint). Probabilistic credence rules it out, as the lemmas in this
section make precise. The packaged refutation lives in §6
(`confidence_not_probabilistic`) above.
-/

/-- Probabilistic credence validates conjunction elimination for `meetsThreshold`,
    but CSW's non-probabilistic ordering does not. This is the key empirical
    divergence between the two theories.

    Formally: under `isProbabilistic`, if `meetsThreshold cr θ a (φ ∧ ψ)` then
    `meetsThreshold cr θ a φ`. Under CSW's ordering, this can fail
    (conjunction fallacy). -/
theorem probabilistic_conjunction_elim_for_all_thresholds
    (cr : AgentCredence E W) (h_prob : isProbabilistic cr)
    (a : E) (φ ψ : (W → Bool)) (θ : ℚ) :
    meetsThreshold cr θ a (fun w => φ w && ψ w) →
    meetsThreshold cr θ a φ :=
  fun h => le_trans h (isProbabilistic_conj_elim cr h_prob a φ ψ)

/-- `meetsThreshold` and `failsThreshold` are exhaustive: for any
    credence and threshold, exactly one holds. This is excluded middle
    on the linear order ℚ. -/
theorem threshold_exhaustive (cr : AgentCredence E W) (θ : ℚ)
    (a : E) (φ : (W → Bool)) :
    meetsThreshold cr θ a φ ∨ failsThreshold cr θ a φ := by
  simp only [meetsThreshold, failsThreshold, ge_iff_le]
  exact le_or_gt θ (cr a φ)

end Semantics.Attitudes.EpistemicThreshold
