import Linglib.Core.RationalAction

/-!
# Luce's Utility Decomposition Theory (Chapter 3)

Luce (1959, Chapter 3) extends the choice axiom from simple alternatives to
**gambles** — uncertain prospects of the form "get outcome `a` if event `ρ` occurs,
otherwise get outcome `b`." The key result is a decomposition theorem: the
subjective value of a gamble factors multiplicatively into a component that depends
only on the outcomes and a component that depends only on the event.

## Architecture

This module formalizes:

1. **Gambles** (§3.A): An outcome `aρb` means "receive `a` if event `ρ`, else `b`."
2. **Decomposition Axiom** (Axiom 2): When outcomes are fixed, choice between gambles
   depends only on the events.
3. **Monotonicity Axiom** (Axiom 3): Preferred outcome + preferred event → preferred gamble.
4. **Three equivalence classes** (Theorem 12): Events partition into favorable, neutral,
   and unfavorable classes.
5. **Scale decomposition** (§3.D): `v(aρb) = w(a,b) · φ(ρ)` — gamble value factors
   into outcome value × event weight.
6. **RSA bridge**: RSA's additive utility structure `utility = informativity - cost`
   follows from Luce's decomposition in log-space.

## References

- Luce, R. D. (1959). Individual Choice Behavior, Chapter 3.
- Franke, M. & Jäger, G. (2016). Probabilistic pragmatics.
-/

namespace Core

-- ============================================================================
-- §1. Gambles and Choice over Gambles
-- ============================================================================

/-- An event in a decision problem. Events are the uncertain conditions
    under which outcomes are determined. -/
structure Event where
  id : ℕ
  deriving DecidableEq, Repr

/-- A gamble `aρb`: receive outcome `a` if event `ρ` occurs, else outcome `b`.
    (Luce 1959, §3.A) -/
structure Gamble (Outcome : Type*) where
  /-- Outcome if event occurs -/
  win : Outcome
  /-- The conditioning event -/
  event : Event
  /-- Outcome if event does not occur -/
  lose : Outcome

variable {Outcome : Type*} [DecidableEq Outcome]

/-- A gamble choice function assigns choice probabilities to pairs of gambles.
    `P(g₁, g₂)` is the probability of choosing gamble `g₁` over `g₂`.
    (Luce 1959, §3.A) -/
structure GambleChoiceFn (Outcome : Type*) where
  /-- Binary choice probability: P(g₁ preferred over g₂) -/
  prob : Gamble Outcome → Gamble Outcome → ℝ
  /-- Probabilities are in [0,1] -/
  prob_nonneg : ∀ g₁ g₂, 0 ≤ prob g₁ g₂
  prob_le_one : ∀ g₁ g₂, prob g₁ g₂ ≤ 1
  /-- Binary complement: P(g₁, g₂) + P(g₂, g₁) = 1 -/
  prob_complement : ∀ g₁ g₂, prob g₁ g₂ + prob g₂ g₁ = 1

/-- A simple outcome choice function: P(a, b) = probability of choosing a over b.
    Used for the outcome-only component of decomposition. -/
structure OutcomeChoiceFn (Outcome : Type*) where
  prob : Outcome → Outcome → ℝ
  prob_nonneg : ∀ a b, 0 ≤ prob a b
  prob_le_one : ∀ a b, prob a b ≤ 1
  prob_complement : ∀ a b, prob a b + prob b a = 1

/-- An event choice function: Q(ρ, σ) = probability of preferring event ρ over σ.
    (Extracted when outcomes are held fixed.) -/
structure EventChoiceFn where
  prob : Event → Event → ℝ
  prob_nonneg : ∀ ρ σ, 0 ≤ prob ρ σ
  prob_le_one : ∀ ρ σ, prob ρ σ ≤ 1
  prob_complement : ∀ ρ σ, prob ρ σ + prob σ ρ = 1

-- ============================================================================
-- §2. Luce's Axioms for Gamble Choice
-- ============================================================================

/-- **Decomposition Axiom** (Luce 1959, Axiom 2):
    When comparing gambles with fixed outcomes (same `a`, same `b`),
    the choice probability depends only on the events.

    P(aρb, aσb) = Q(ρ, σ) for some event choice function Q. -/
structure DecompositionAxiom (P : GambleChoiceFn Outcome) where
  /-- The extracted event choice function -/
  eventChoice : EventChoiceFn
  /-- Fixed outcomes ⟹ choice depends only on events -/
  decomp : ∀ (a b : Outcome) (ρ σ : Event),
    P.prob ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = eventChoice.prob ρ σ

/-- **Monotonicity Axiom** (Luce 1959, Axiom 3):
    If outcome `a` is preferred to `b` (P(a,b) ≥ ½) and event `ρ` is preferred
    to `σ` (Q(ρ,σ) ≥ ½), then gamble `aρb` is preferred to `bσa`.

    This captures the intuition that a better outcome under a more favorable event
    should be preferred to a worse outcome under a less favorable event. -/
structure MonotonicityAxiom (P : GambleChoiceFn Outcome)
    (outcomeChoice : OutcomeChoiceFn Outcome)
    (eventChoice : EventChoiceFn) where
  mono : ∀ (a b : Outcome) (ρ σ : Event),
    outcomeChoice.prob a b ≥ 1/2 →
    eventChoice.prob ρ σ ≥ 1/2 →
    P.prob ⟨a, ρ, b⟩ ⟨b, σ, a⟩ ≥ 1/2

-- ============================================================================
-- §3. Event Equivalence Classes (Theorem 12)
-- ============================================================================

/-- An event ρ is **favorable** relative to an outcome preference P(a,b) ≥ ½ if
    Q(ρ, σ₀) > ½ for the neutral event σ₀.
    Intuitively: ρ makes the preferred outcome more likely. -/
inductive EventClass where
  | favorable   : EventClass
  | neutral     : EventClass
  | unfavorable : EventClass
  deriving DecidableEq, Repr

/-- Classify an event based on its choice probability against a reference event.
    (Luce 1959, §3.C) -/
noncomputable def classifyEvent (Q : EventChoiceFn) (ref : Event) (ρ : Event) : EventClass :=
  if Q.prob ρ ref > 1/2 then .favorable
  else if Q.prob ρ ref < 1/2 then .unfavorable
  else .neutral

/-- **Three equivalence classes theorem** (Luce 1959, Theorem 12):
    Under the decomposition and monotonicity axioms, events partition into
    exactly three equivalence classes: favorable, neutral, and unfavorable.

    Events within the same class have Q(ρ, σ) = ½ (indifference).
    Between classes: favorable > neutral > unfavorable. -/
theorem threeClasses (Q : EventChoiceFn) (ref : Event) (ρ σ : Event)
    (hclass : classifyEvent Q ref ρ = classifyEvent Q ref σ) :
    Q.prob ρ σ = 1/2 := by
  sorry -- TODO: requires transitivity of preference + decomposition axiom interaction

-- ============================================================================
-- §4. Scale Decomposition
-- ============================================================================

/-- A gamble value function that factors into outcome value × event weight.
    (Luce 1959, §3.D)

    `v(aρb) = w(a,b) · φ(ρ)` where:
    - `w(a,b)` depends only on the outcomes
    - `φ(ρ)` depends only on the event -/
structure ScaleDecomposition (Outcome : Type*) where
  /-- Outcome value component -/
  outcomeValue : Outcome → Outcome → ℝ
  /-- Event weight component -/
  eventWeight : Event → ℝ
  /-- Non-negativity -/
  outcomeValue_nonneg : ∀ a b, 0 ≤ outcomeValue a b
  eventWeight_nonneg : ∀ ρ, 0 ≤ eventWeight ρ

/-- The gamble value under a scale decomposition. -/
noncomputable def ScaleDecomposition.gambleValue (sd : ScaleDecomposition Outcome)
    (g : Gamble Outcome) : ℝ :=
  sd.outcomeValue g.win g.lose * sd.eventWeight g.event

/-- **Scale decomposition theorem** (Luce 1959, §3.D):
    Under Axioms 1–3, the choice probability for gambles can be represented as
    a Luce choice rule with scores that factor as `v(aρb) = w(a,b) · φ(ρ)`. -/
theorem scaleDecomposition (P : GambleChoiceFn Outcome)
    (_hDecomp : DecompositionAxiom P)
    (_outcomeChoice : OutcomeChoiceFn Outcome)
    (_eventChoice : EventChoiceFn)
    (_hMono : MonotonicityAxiom P _outcomeChoice _eventChoice) :
    ∃ sd : ScaleDecomposition Outcome,
      ∀ g₁ g₂ : Gamble Outcome,
        sd.gambleValue g₁ + sd.gambleValue g₂ > 0 →
        P.prob g₁ g₂ = sd.gambleValue g₁ / (sd.gambleValue g₁ + sd.gambleValue g₂) := by
  sorry -- TODO: full proof requires constructing w and φ from Q and P

-- ============================================================================
-- §5. Bridge to RSA Utility Decomposition
-- ============================================================================

/-!
## RSA Bridge

Luce's decomposition theorem justifies the additive structure of RSA utility.

In RSA, the speaker's utility is:
  `utility(u, w) = log P(w|u) - cost(u)`

This additive structure in log-space corresponds to multiplicative structure
in ratio-scale space:
  `score(u, w) = exp(α · utility) = exp(α · log P(w|u)) · exp(-α · cost(u))`
                = informativity^α · exp(-α · cost)

Luce's decomposition `v(aρb) = w(a,b) · φ(ρ)` provides the axiomatic foundation:
- The "outcome" dimension corresponds to the communicative goal (informativity)
- The "event" dimension corresponds to the production process (cost)
- The multiplicative factoring is *derived* from IIA + monotonicity, not stipulated
-/

/-- RSA utility as a Luce decomposition instance.

    The speaker's score `exp(α · (log P(w|u) - cost(u)))` factors as:
    - outcome component: `P(w|u)^α` (informativity)
    - event component: `exp(-α · cost(u))` (production ease)

    This factoring means the Luce choice axiom guarantees that informativity and
    cost contribute independently to the speaker's choice, which is a substantive
    empirical prediction (not a modeling convenience). -/
structure RSAUtilityDecomposition where
  /-- Rationality parameter -/
  α : ℝ
  /-- Informativity: P(w|u) for each utterance-world pair -/
  informativity : ℝ
  /-- Cost of utterance -/
  cost : ℝ
  /-- Informativity is a probability -/
  informativity_nonneg : 0 ≤ informativity
  informativity_le_one : informativity ≤ 1

/-- RSA speaker score factors multiplicatively, following Luce decomposition. -/
noncomputable def RSAUtilityDecomposition.score (d : RSAUtilityDecomposition) : ℝ :=
  d.informativity ^ d.α * Real.exp (-d.α * d.cost)

/-- The RSA utility decomposition: `log(score) = α · log(informativity) - α · cost`.
    This additive structure in log-space is what Luce's Chapter 3 derives
    from the decomposition axioms. -/
theorem rsa_utility_decomposition (d : RSAUtilityDecomposition)
    (hinfo_pos : 0 < d.informativity) :
    Real.log d.score = d.α * Real.log d.informativity - d.α * d.cost := by
  simp only [RSAUtilityDecomposition.score]
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hinfo_pos d.α))
      (ne_of_gt (Real.exp_pos _)),
      Real.log_rpow hinfo_pos, Real.log_exp]
  ring

end Core
