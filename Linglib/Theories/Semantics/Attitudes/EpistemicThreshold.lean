import Linglib.Core.Proposition
import Linglib.Core.EpistemicScale
import Linglib.Core.BToM
import Linglib.Theories.Semantics.Degree.Core
import Mathlib.Tactic.NormNum

/-!
# Epistemic Threshold Semantics (Ying, Zhi-Xuan, Wong, Mansinghka & Tenenbaum 2025)

@cite{ying-zhi-xuan-wong-mansinghka-tenenbaum-2025}

Epistemic vocabulary — attitude verbs (`believes`, `knows`), modal verbs
(`might`, `must`), and modal adjectives (`likely`, `certain`) — denotes
**threshold functions over agent credence** Pr(A, φ).

## The Core Idea

Every epistemic expression reduces to a comparison of the agent's credence
against a threshold (Table 1):

    believes(A, φ) ⟺ Pr(A, φ) ≥ θ_believes
    knows_that(A, φ) ⟺ believes(A, φ) ∧ φ
    certain(A, φ)  ⟺ Pr(A, φ) ≥ θ_certain
    must(φ)        ⟺ λA. Pr(A, φ) ≥ θ_must
    likely(φ)      ⟺ λA. Pr(A, φ) ≥ θ_likely
    might(φ)       ⟺ λA. Pr(A, φ) ≥ θ_might

## Degree-Threshold Isomorphism

The threshold semantics is structurally identical to the positive form of
gradable adjectives (Kennedy 2007, Lassiter 2017):

    ⟦tall⟧(x) = height(x) ≥ θ_tall       (Degree/Core.positiveSem)
    ⟦believes⟧(A, φ) = Pr(A, φ) ≥ θ_bel  (meetsThreshold)

Both are instances of the same degree-threshold architecture: a measure
function maps an entity to a degree on a scale, and the predicate holds
iff the degree meets a contextual/lexical threshold. Epistemic expressions
are gradable predicates on a probability scale bounded by [0, 1].

This connection is formalized in §8 via `epistemicAsGradable`.

## Unification of Three Formalizations

This collapses three previously separate treatments in the library:

1. **Doxastic.lean** (Hintikka): Boolean accessibility. Believes iff φ holds
   at ALL accessible worlds — the θ → 1 limit of threshold semantics.

2. **Confidence.lean** (CSW 2024): Ordinal confidence ordering. Credence
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

Pr(A, φ) is computed via BToM inference (`Core.BToM`). Given an observed
action `a`, the observer estimates agent credence by marginalizing:

    Pr_obs(Agent, φ | a) = Σ_b P(b | a) · ⟦φ⟧_b

where P(b | a) is the BToM belief marginal (`BToMModel.beliefMarginal`).
Through the RSA-BToM bridge (`L1_eq_btom_worldMarginal`), this connects
to the pragmatic listener's interpretation of epistemic language.

## References

- Ying, L., Zhi-Xuan, T., Wong, L., Mansinghka, V. & Tenenbaum, J. B.
  (2025). Understanding Epistemic Language with a Language-Augmented
  Bayesian Theory of Mind. TACL 13, 613–637.
- Hintikka, J. (1969). Knowledge and Belief.
- Cariani, F., Santorio, P. & Wellwood, A. (2024). Confidence reports.
- Baker, Jara-Ettinger, Saxe & Tenenbaum (2017). BToM.
- Kennedy, C. (2007). Vagueness and grammar.
- Lassiter, D. (2017). Graded modality.
-/

namespace Semantics.Attitudes.EpistemicThreshold

open Core.Proposition

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
abbrev AgentCredence (E W : Type*) := E → BProp W → ℚ

-- ============================================================================
-- §2. Epistemic Lexicon
-- ============================================================================

/-- An epistemic lexical entry: a threshold comparison over agent credence.

    Each epistemic expression (attitude verb, modal verb, modal adjective)
    is characterized by:
    - `θ`: the credence threshold — the expression holds iff Pr(A, φ) ≥ θ
    - `factive`: whether the expression additionally requires φ to be true
      at the evaluation world (e.g., `knows` but not `believes`) -/
structure EpistemicEntry where
  /-- Lexical item name -/
  name : String
  /-- Credence threshold -/
  θ : ℚ
  /-- Factivity flag -/
  factive : Bool := false
  deriving DecidableEq, Repr, BEq

/-! Standard epistemic thresholds (Ying et al. 2025, Table 1(b)).

These are the best-fit values from LaBToM's comparison against human
judgments on the Badges and BigToM datasets. The ordering is the
theoretical commitment; the specific values are empirical fits:

  must/certain (0.95) > should (0.80) > believes (0.75) >
  likely/uncertain (0.70) > unlikely (0.40) > may (0.30) >
  might/could (0.20) -/
namespace EpistemicEntry

def believes_ : EpistemicEntry := ⟨"believes", 3/4, false⟩
def knows_    : EpistemicEntry := ⟨"knows", 3/4, true⟩
def certain_  : EpistemicEntry := ⟨"certain", 19/20, false⟩
def must_     : EpistemicEntry := ⟨"must", 19/20, false⟩
def should_   : EpistemicEntry := ⟨"should", 4/5, false⟩
def likely_   : EpistemicEntry := ⟨"likely", 7/10, false⟩
def may_      : EpistemicEntry := ⟨"may", 3/10, false⟩
def might_    : EpistemicEntry := ⟨"might", 1/5, false⟩
def could_    : EpistemicEntry := ⟨"could", 1/5, false⟩

/-! Reversed-polarity entries: these hold when credence is BELOW a threshold.
`uncertain` and `unlikely` use strict `<` rather than `≥`. They are not
modeled via `holdsAt` but via `failsThreshold` (§3). -/
def uncertain_ : EpistemicEntry := ⟨"uncertain", 7/10, false⟩
def unlikely_  : EpistemicEntry := ⟨"unlikely", 2/5, false⟩

/-- The full threshold scale (Table 1(b)):
    must = certain > should > believes > likely = uncertain > unlikely > may > might = could -/
theorem scale_must_gt_should : (19 : ℚ)/20 > 4/5 := by norm_num
theorem scale_should_gt_believes : (4 : ℚ)/5 > 3/4 := by norm_num
theorem scale_believes_gt_likely : (3 : ℚ)/4 > 7/10 := by norm_num
theorem scale_likely_gt_unlikely : (7 : ℚ)/10 > 2/5 := by norm_num
theorem scale_unlikely_gt_may : (2 : ℚ)/5 > 3/10 := by norm_num
theorem scale_may_gt_might : (3 : ℚ)/10 > 1/5 := by norm_num

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

    Structurally identical to `Degree.positiveSem μ θ x`: both are
    `measure(entity) ≥ threshold`. -/
def meetsThreshold (cr : AgentCredence E W) (θ : ℚ)
    (a : E) (φ : BProp W) : Prop :=
  cr a φ ≥ θ

/-- Reversed threshold: agent `a`'s credence in `φ` is strictly BELOW `θ`.

    Used for `uncertain` and `unlikely`: uncertain_if(A, φ, ψ) holds iff
    Pr(A, φ) < θ_uncertain ∧ Pr(A, ψ) < θ_uncertain (Table 1(a)). -/
def failsThreshold (cr : AgentCredence E W) (θ : ℚ)
    (a : E) (φ : BProp W) : Prop :=
  cr a φ < θ

/-- Full epistemic evaluation: credence meets threshold, plus factivity.

    - `believes(A, φ, w)` = Pr(A, φ) ≥ 0.75
    - `knows(A, φ, w)` = Pr(A, φ) ≥ 0.75 ∧ φ(w) = true -/
def holdsAt (cr : AgentCredence E W) (entry : EpistemicEntry)
    (a : E) (φ : BProp W) (w : W) : Prop :=
  meetsThreshold cr entry.θ a φ ∧ (entry.factive = true → φ w = true)

-- ── Structural operators from Table 1(a) ──

/-- `knows_if(A, φ)` = knows_that(A, φ) ∨ knows_that(A, ¬φ).
    The agent knows the answer to the yes/no question ?φ. -/
def knowsIf (cr : AgentCredence E W) (a : E) (φ : BProp W) (w : W) : Prop :=
  holdsAt cr .knows_ a φ w ∨
  holdsAt cr .knows_ a (fun w' => !φ w') w

/-- `not_knows_that(A, φ)` = ¬believes(A, φ) ∧ φ.
    False belief: φ is true but the agent doesn't believe it. -/
def notKnowsThat (cr : AgentCredence E W) (a : E) (φ : BProp W) (w : W) : Prop :=
  ¬meetsThreshold cr EpistemicEntry.believes_.θ a φ ∧ φ w = true

/-- `uncertain_if(A, φ, ψ)` = Pr(A, φ) < θ_uncertain ∧ Pr(A, ψ) < θ_uncertain.
    The agent is uncertain between two alternatives. -/
def uncertainIf (cr : AgentCredence E W) (a : E) (φ ψ : BProp W) : Prop :=
  failsThreshold cr EpistemicEntry.uncertain_.θ a φ ∧
  failsThreshold cr EpistemicEntry.uncertain_.θ a ψ

-- ── Degree function and comparatives (Table 1(a)) ──

/-- `degree(likely, A, φ)` = Pr(A, φ).
    The raw credence, used as input to comparative and superlative
    constructions. This IS the measure function on the epistemic scale. -/
def degree (cr : AgentCredence E W) (a : E) (φ : BProp W) : ℚ :=
  cr a φ

/-- Comparative credence: `more(P, φ, ψ)` = degree(P, A, φ) > degree(P, A, ψ).

    The agent's credence in φ strictly exceeds credence in ψ. Mirrors the
    comparative from `Confidence.lean` (CSW 2024) and from `Degree/Core.lean`. -/
def moreCredent (cr : AgentCredence E W)
    (a : E) (φ ψ : BProp W) : Prop :=
  cr a ψ < cr a φ

/-- Superlative: `most_str(P, φ)` = degree(P, A, φ) ≥ α_most · θ_P.
    Strengthened superlative with multiplier α_most = 1.5 (Table 1(b)). -/
def mostStr (cr : AgentCredence E W) (entry : EpistemicEntry)
    (a : E) (φ : BProp W) : Prop :=
  cr a φ ≥ EpistemicEntry.α_most * entry.θ

-- ============================================================================
-- §4. Entailment Properties
-- ============================================================================

/-- Higher thresholds entail lower thresholds.

    If an expression with threshold θ₂ holds, then any expression with
    a lower threshold θ₁ ≤ θ₂ also holds. This derives the entailment
    patterns of epistemic vocabulary from the threshold ordering alone. -/
theorem threshold_monotone (cr : AgentCredence E W)
    (a : E) (φ : BProp W) {θ₁ θ₂ : ℚ} (h : θ₁ ≤ θ₂) :
    meetsThreshold cr θ₂ a φ → meetsThreshold cr θ₁ a φ :=
  fun h₂ => le_trans h h₂

/-- `knows` entails `believes`: knowledge implies belief.

    Since `knows` and `believes` share the same threshold (0.75) and
    `knows` only adds factivity, the credence condition carries over. -/
theorem knows_entails_believes (cr : AgentCredence E W)
    (a : E) (φ : BProp W) (w : W) :
    holdsAt cr .knows_ a φ w → holdsAt cr .believes_ a φ w := by
  intro ⟨hcr, _⟩
  exact ⟨hcr, by simp [EpistemicEntry.believes_]⟩

/-- `knows` is veridical: knowledge entails truth.

    This mirrors `Veridicality.veridical` in `Doxastic.lean`: veridical
    predicates entail their complement. In ELoT, veridicality is the
    `factive = true` flag. -/
theorem knows_is_veridical (cr : AgentCredence E W)
    (a : E) (φ : BProp W) (w : W) :
    holdsAt cr .knows_ a φ w → φ w = true :=
  fun ⟨_, h⟩ => h rfl

/-- `certain` entails `believes`: θ_certain = 19/20 ≥ θ_believes = 3/4. -/
theorem certain_entails_believes (cr : AgentCredence E W)
    (a : E) (φ : BProp W) (w : W) :
    holdsAt cr .certain_ a φ w → holdsAt cr .believes_ a φ w := by
  intro ⟨hcr, _⟩
  exact ⟨le_trans (by norm_num : (3 : ℚ)/4 ≤ 19/20) hcr,
         by simp [EpistemicEntry.believes_]⟩

/-- `must` entails `should`: θ_must = 19/20 ≥ θ_should = 4/5. -/
theorem must_entails_should (cr : AgentCredence E W)
    (a : E) (φ : BProp W) (w : W) :
    holdsAt cr .must_ a φ w → holdsAt cr .should_ a φ w := by
  intro ⟨hcr, _⟩
  exact ⟨le_trans (by norm_num : (4 : ℚ)/5 ≤ 19/20) hcr,
         by simp [EpistemicEntry.should_]⟩

/-- `should` entails `likely`: θ_should = 4/5 ≥ θ_likely = 7/10. -/
theorem should_entails_likely (cr : AgentCredence E W)
    (a : E) (φ : BProp W) (w : W) :
    holdsAt cr .should_ a φ w → holdsAt cr .likely_ a φ w := by
  intro ⟨hcr, _⟩
  exact ⟨le_trans (by norm_num : (7 : ℚ)/10 ≤ 4/5) hcr,
         by simp [EpistemicEntry.likely_]⟩

/-- `must` entails `might`: necessity entails possibility.

    θ_must = 19/20 ≥ θ_might = 1/5. This is the epistemic modal
    analogue of □φ → ◇φ. -/
theorem must_entails_might (cr : AgentCredence E W)
    (a : E) (φ : BProp W) (w : W) :
    holdsAt cr .must_ a φ w → holdsAt cr .might_ a φ w := by
  intro ⟨hcr, _⟩
  exact ⟨le_trans (by norm_num : (1 : ℚ)/5 ≤ 19/20) hcr,
         by simp [EpistemicEntry.might_]⟩

/-- `believes` entails `may`: θ_believes = 3/4 ≥ θ_may = 3/10. -/
theorem believes_entails_may (cr : AgentCredence E W)
    (a : E) (φ : BProp W) (w : W) :
    holdsAt cr .believes_ a φ w → holdsAt cr .may_ a φ w := by
  intro ⟨hcr, _⟩
  exact ⟨le_trans (by norm_num : (3 : ℚ)/10 ≤ 3/4) hcr,
         by simp [EpistemicEntry.may_]⟩

-- ============================================================================
-- §5. Comparative Properties
-- ============================================================================

/-- Comparative credence is transitive.

    Mirrors `comparative_transitive` in `Confidence.lean` (CSW (54)). -/
theorem moreCredent_transitive (cr : AgentCredence E W)
    (a : E) (φ ψ χ : BProp W)
    (h₁ : moreCredent cr a φ ψ) (h₂ : moreCredent cr a ψ χ) :
    moreCredent cr a φ χ :=
  lt_trans h₂ h₁

/-- Upward monotonicity of belief under the credence ordering.

    If the agent believes φ and is at least as confident of ψ as of φ,
    then the agent believes ψ. This is the credence-based analogue of
    `confidence_upward_monotone` in `Confidence.lean` (CSW (53)). -/
theorem credence_upward_monotone (cr : AgentCredence E W)
    (θ : ℚ) (a : E) (φ ψ : BProp W)
    (h_bel : meetsThreshold cr θ a φ) (h_more : cr a φ ≤ cr a ψ) :
    meetsThreshold cr θ a ψ :=
  le_trans h_bel h_more

-- ============================================================================
-- §6. Probabilistic Credence and Conjunction
-- ============================================================================

/-!
### Key Divergence from Confidence.lean

CSW's confidence ordering is NOT constrained to respect logical conjunction:
`conjunction_fallacy_compatible` (Confidence.lean) shows it is consistent
to be confident of (p ∧ q) without being confident of p.

When `AgentCredence` is a genuine probability measure (as in LaBToM), this
cannot happen: Pr(A, p ∧ q) ≤ Pr(A, p) always. The two theories make
different empirical predictions about conjunction fallacy data.
-/

/-- A probabilistic credence function respects conjunction elimination:
    Pr(A, φ ∧ ψ) ≤ Pr(A, φ). This is the axiom that separates LaBToM's
    probabilistic credence from CSW's ordinal confidence ordering. -/
def isProbabilistic (cr : AgentCredence E W) : Prop :=
  ∀ (a : E) (φ ψ : BProp W),
    (∀ w, (φ w && ψ w) = true → φ w = true) →
    cr a (fun w => φ w && ψ w) ≤ cr a φ

/-- Probabilistic credence validates conjunction elimination for belief.

    If the agent believes (φ ∧ ψ) and credence is probabilistic, then
    the agent believes φ. This fails for CSW's non-probabilistic ordering
    (conjunction fallacy). -/
theorem prob_conjunction_elim (cr : AgentCredence E W)
    (h_prob : isProbabilistic cr) (θ : ℚ) (a : E) (φ ψ : BProp W)
    (h_bel : meetsThreshold cr θ a (fun w => φ w && ψ w)) :
    meetsThreshold cr θ a φ :=
  le_trans h_bel (h_prob a φ ψ fun w h => by
    simp only [Bool.and_eq_true] at h; exact h.1)

-- ============================================================================
-- §7. BToM-Derived Credence
-- ============================================================================

/-!
### Connection to BToM Inference

The observer estimates an agent's credence by marginalizing over the
BToM belief marginal (`BToMModel.beliefMarginal`):

    Pr_obs(Agent, φ | a) = Σ_b P(b | a) · ⟦φ⟧_b

When B = W (the RSA-BToM bridge's perfect-knowledge assumption,
`RSAConfig.toBToM`), this becomes:

    Pr_obs(Agent, φ | a) = Σ_w P(w | a) · φ(w)

which is just the observer's expected truth-value of φ under their
posterior about the world — exactly what RSA's L1 listener computes.
The full chain is:

    L1 posterior → BToM belief marginal → agent credence → threshold → ELoT

This makes the interpretation of epistemic language a BToM inference
problem: understanding "the player thinks the key might be in box 3"
requires jointly inferring the player's belief state via inverse planning,
then evaluating the ELoT formula against the inferred credences.

See `BToMModel.beliefExpectation` in `Core.BToM` for the generic
belief-weighted sum, and `L1_eq_btom_worldMarginal` in
`RSA.Core.BToMGrounding` for the RSA-BToM identity.
-/

open Core.BToM in
/-- Agent credence derived from BToM belief-marginal inference.

    Given a BToM model with belief type `B` and an evaluation function
    `eval : B → BProp W → ℚ` that computes how belief state `b` rates
    proposition `φ`, the observer estimates the agent's credence after
    observing action `a`:

        Pr_obs(Agent, φ | a) = Σ_b P(b | a) · eval(b, φ)

    This is `BToMModel.beliefExpectation` applied to `fun b => eval b φ`,
    grounding the abstract `AgentCredence` in concrete BToM inference.

    When `B = W` and `eval b φ = if φ b then 1 else 0` (the RSA-BToM
    bridge's perfect-knowledge assumption), this reduces to the L1
    listener's expected truth-value under their world posterior. -/
noncomputable def btomCredence
    {A P B D S M W : Type*}
    [Fintype P] [Fintype B] [Fintype D] [Fintype S] [Fintype M] [Fintype W]
    (model : BToMModel ℚ A P B D S M W)
    (eval : B → BProp W → ℚ)
    (a : A) (φ : BProp W) : ℚ :=
  model.beliefExpectation (λ b => eval b φ) a

-- ============================================================================
-- §8. Degree-Threshold Bridge
-- ============================================================================

/-!
### Epistemic Expressions as Gradable Predicates

Lassiter (2017) argues that epistemic modals are gradable expressions on
a probability scale. The threshold semantics makes this precise:

    ⟦tall⟧(x) = height(x) ≥ θ_tall       (Degree.positiveSem)
    ⟦believes⟧(A, φ) = Pr(A, φ) ≥ θ_bel  (meetsThreshold)

Both are instances of `μ(entity) ≥ θ`. The epistemic scale is the
probability interval [0, 1], which is **closed** in the sense of Kennedy
(2007): it has both an upper bound (certainty, 1) and a lower bound
(impossibility, 0).

This has consequences for scale structure:
- Closed-scale adjectives (like `full`, `certain`) license absolute
  standards (the endpoint). For `certain`, the endpoint IS θ = 0.95 ≈ 1.
- Open-scale adjectives (like `tall`) require contextual standards.
  For `likely`, the threshold θ = 0.70 is contextually fit.

The structural parallel also extends to comparatives and superlatives:
- "more likely than" = moreCredent (comparative on probability scale)
- "most likely" = mostStr with multiplier α_most = 1.5

See `Theories/Semantics/Probabilistic/SDS/ThresholdSemantics.lean` for
the unified threshold pattern across adjectives, generics, and epistemic
expressions.
-/

/-- The epistemic probability scale is closed: bounded by [0, 1].

    This classifies the credence scale as `Boundedness.closed`, meaning
    epistemic adjectives like `certain` license absolute standards
    (Kennedy 2007). -/
def epistemicBoundedness : Core.Scale.Boundedness := .closed

/-- An epistemic gradable predicate: an `EpistemicEntry` viewed as a
    `GradablePredicate` on the probability scale.

    The entity type is `E × BProp W` (agent–proposition pairs), and the
    measure function is agent credence `cr`. This makes the structural
    identity with degree semantics explicit and type-checked.

    Polarity: threshold entries (`believes`, `must`, `likely`) are positive
    (upward monotone: higher credence → more likely to satisfy). Reversed
    entries (`uncertain`, `unlikely`) are negative (downward monotone). -/
def epistemicAsGradable (cr : AgentCredence E W) (entry : EpistemicEntry)
    : Semantics.Degree.GradablePredicate (E × BProp W) ℚ where
  form := entry.name
  μ := fun ⟨a, φ⟩ => cr a φ
  boundedness := epistemicBoundedness

/-- The degree-threshold identity: `meetsThreshold` is `positiveSem`
    instantiated on the epistemic scale.

    This is the formal statement that epistemic threshold semantics IS
    degree semantics with credence as the measure function. -/
theorem meetsThreshold_eq_positiveSem (cr : AgentCredence E W) (θ : ℚ)
    (a : E) (φ : BProp W) :
    meetsThreshold cr θ a φ ↔
    Semantics.Degree.positiveSem (fun (p : E × BProp W) => cr p.1 p.2) θ (a, φ) := by
  rfl

/-- The epistemic scale is licensed: closed → admits absolute standards.

    Since credence is bounded by [0, 1], Kennedy's (2007) licensing
    prediction says epistemic adjectives like `certain` can use endpoint
    standards (θ ≈ 1.0). This unifies with the five-framework licensing
    agreement from `Core/EpistemicScale.lean`. -/
theorem epistemicScale_licensed :
    epistemicBoundedness.isLicensed = true := rfl

-- ============================================================================
-- §9. Connection to Holliday–Icard Epistemic Likelihood
-- ============================================================================

/-!
### From Credence to Comparative Likelihood

When `AgentCredence` is a genuine probability measure (probabilistic
credence), it induces the full Holliday & Icard (2013) hierarchy:

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
framework of Core/EpistemicScale.lean: the fitted thresholds from
Table 1(b) are points on a finitely additive probability scale that
satisfies System FA (and hence all of W ⊂ F ⊂ FA).
-/

/-- Threshold semantics is upward monotone in the credence ordering:
    if `cr a φ ≥ θ` and `cr a φ ≤ cr a ψ`, then `cr a ψ ≥ θ`.

    This is an instance of `Core.Scale.IsUpwardMonotone` applied to the
    epistemic scale. The family of propositions `P(θ) = meetsThreshold θ`
    is upward monotone in credence — higher credence always satisfies
    lower thresholds.

    Connects to CSW's `confidence_upward_monotone` and to Lassiter's
    observation that epistemic modals form a Horn scale ordered by
    threshold strength. -/
theorem threshold_upwardMonotone (cr : AgentCredence E W)
    (a : E) (φ : BProp W) :
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
    (a : E) (φ : BProp W) :
    ∀ (θ₁ θ₂ : ℚ), θ₁ ≤ θ₂ →
    failsThreshold cr θ₁ a φ → failsThreshold cr θ₂ a φ :=
  fun _ _ h h₁ => lt_of_lt_of_le h₁ h

/-- The epistemic threshold scale forms a `ComparativeScale` with
    closed boundedness. This places it in the same categorical
    structure as Kennedy's adjective scales, Krifka's mereological
    scales, and Holliday–Icard's epistemic likelihood scales. -/
def epistemicComparativeScale : Core.Scale.ComparativeScale ℚ where
  boundedness := epistemicBoundedness

/-- Comparative credence is the measure-induced ordering on propositions:
    `moreCredent cr a φ ψ ↔ cr a ψ < cr a φ`.

    This is the analogue of `FinAddMeasure.inducedGe` (Holliday & Icard
    2013) applied to agent credence: the comparative likelihood ordering
    on propositions is induced by the credence measure. The threshold
    entries from Table 1(b) are then points where we cut this ordering. -/
theorem moreCredent_iff_degree (cr : AgentCredence E W)
    (a : E) (φ ψ : BProp W) :
    moreCredent cr a φ ψ ↔ degree cr a ψ < degree cr a φ := by
  rfl

-- ============================================================================
-- §10. Lassiter (2017) Degree-Semantic Bridges
-- ============================================================================

/-!
### Kennedy's Reduction: Comparative from Positive

The central formal insight of Kennedy (2007) — applied to epistemic modality
by Lassiter (2017) Ch. 4 — is that the comparative is not an independent
primitive but *reduces to* the positive form via existential quantification
over thresholds:

    "φ more likely than ψ"  ↔  ∃θ. likely_θ(φ) ∧ ¬likely_θ(ψ)

In words: φ is more likely than ψ iff there is some threshold that φ's
credence meets but ψ's doesn't. This means the comparative ordering on
propositions is *determined by* the family of positive-form predicates
{meetsThreshold θ | θ ∈ ℚ}. The same reduction works for adjectives:

    "A taller than B"  ↔  ∃θ. tall_θ(A) ∧ ¬tall_θ(B)

The non-trivial part is that this is a *biconditional*: not only does
a separating threshold imply the comparative (easy direction), but the
comparative implies a separating threshold exists (uses the witness
θ = cr(a, φ), which meets for φ by reflexivity and fails for ψ by
the comparative hypothesis). This is a genuine mathematical fact about
the structure of threshold semantics on a linear order.
-/

/-- **Kennedy's reduction**: the comparative reduces to the positive form.

    "φ more likely than ψ" iff there exists a threshold that φ meets
    and ψ fails. This is THE structural theorem connecting comparative
    and positive-form degree semantics.

    - Forward: if cr(a,ψ) < cr(a,φ), witness θ = cr(a,φ).
    - Backward: if θ separates, then cr(a,ψ) < θ ≤ cr(a,φ).

    Kennedy (2007) §3; Lassiter (2017) §4.2: the same reduction applies
    to epistemic modals because credence IS a measure function. -/
theorem comparative_from_positive (cr : AgentCredence E W)
    (a : E) (φ ψ : BProp W) :
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

    Lassiter (2017): positive and negative epistemic modals are
    contradictories on the probability scale, not contraries. The
    same threshold θ separates "likely" from "unlikely." -/
theorem meetsThreshold_iff_not_failsThreshold (cr : AgentCredence E W)
    (θ : ℚ) (a : E) (φ : BProp W) :
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

    Lassiter (2017) §4.3: likely/unlikely parallel tall/short. -/
theorem antonymy_from_polarity (cr : AgentCredence E W)
    (a : E) (φ ψ : BProp W) :
    moreCredent cr a φ ψ ↔
    ∃ θ : ℚ, meetsThreshold cr θ a φ ∧ failsThreshold cr θ a ψ := by
  rw [comparative_from_positive]
  constructor
  · intro ⟨θ, hφ, hψ⟩
    exact ⟨θ, hφ, not_le.mp hψ⟩
  · intro ⟨θ, hφ, hψ⟩
    exact ⟨θ, hφ, not_le.mpr hψ⟩

end Semantics.Attitudes.EpistemicThreshold
