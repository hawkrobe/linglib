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
4. **Luce ratio scales** (§2a): The Luce choice axiom applied to event and gamble
   choice functions, providing ratio-scale representations `Q(ρ,σ) = v(ρ)/(v(ρ)+v(σ))`.
5. **Three equivalence classes** (Theorem 12): Under the Luce choice axiom, events
   classified as neutral relative to a reference are indifferent: Q(ρ,σ) = ½.
6. **Scale decomposition** (§3.D): `v(aρb) = w(a,b) · φ(ρ)` — gamble value factors
   into outcome value × event weight.
7. **RSA bridge**: RSA's additive utility structure `utility = informativity - cost`
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
-- §2a. Luce Ratio Scales for Choice Functions
-- ============================================================================

/-- A Luce ratio scale for an event choice function: Q(ρ,σ) = v(ρ)/(v(ρ)+v(σ))
    for some positive scoring function v. This is the event-level analog of the
    Luce choice rule from `RationalAction`. -/
structure EventLuceScale (Q : EventChoiceFn) where
  v : Event → ℝ
  v_pos : ∀ ρ, 0 < v ρ
  luce_rule : ∀ ρ σ, Q.prob ρ σ = v ρ / (v ρ + v σ)

/-- A Luce ratio scale for a gamble choice function: P(g₁,g₂) = v(g₁)/(v(g₁)+v(g₂))
    for some positive scoring function v. This is the gamble-level Luce choice axiom
    (Luce 1959, Chapter 1 applied to gamble alternatives). -/
structure GambleLuceScale (P : GambleChoiceFn Outcome) where
  v : Gamble Outcome → ℝ
  v_pos : ∀ g, 0 < v g
  luce_rule : ∀ g₁ g₂, P.prob g₁ g₂ = v g₁ / (v g₁ + v g₂)

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

/-- Extract Q.prob ρ ref = 1/2 from neutral classification. -/
private lemma neutral_imp_prob_eq_half (Q : EventChoiceFn) (ref ρ : Event)
    (h : classifyEvent Q ref ρ = .neutral) : Q.prob ρ ref = 1/2 := by
  have h1 : ¬(Q.prob ρ ref > 1/2) := by
    intro hgt; unfold classifyEvent at h; rw [if_pos hgt] at h; exact absurd h (by decide)
  have h2 : ¬(Q.prob ρ ref < 1/2) := by
    intro hlt; unfold classifyEvent at h; rw [if_neg h1, if_pos hlt] at h
    exact absurd h (by decide)
  linarith [not_lt.mp h1, not_lt.mp h2]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Extract Q.prob ρ ref > 1/2 from favorable classification. -/
private lemma favorable_imp_gt_half (Q : EventChoiceFn) (ref ρ : Event)
    (h : classifyEvent Q ref ρ = .favorable) : Q.prob ρ ref > 1/2 := by
  unfold classifyEvent at h
  split_ifs at h with h1
  · exact h1
  all_goals exact absurd h (by decide)

/-- Extract Q.prob ρ ref < 1/2 from unfavorable classification. -/
private lemma unfavorable_imp_lt_half (Q : EventChoiceFn) (ref ρ : Event)
    (h : classifyEvent Q ref ρ = .unfavorable) : Q.prob ρ ref < 1/2 := by
  by_contra h2; push_neg at h2
  by_cases h1 : Q.prob ρ ref > 1/2
  · unfold classifyEvent at h; rw [if_pos h1] at h; exact absurd h (by decide)
  · unfold classifyEvent at h; rw [if_neg h1, if_neg (not_lt_of_ge h2)] at h
    exact absurd h (by decide)

/-- Under a Luce scale, Q(ρ,σ) = 1/2 iff v(ρ) = v(σ). -/
private lemma luce_eq_half_iff {Q : EventChoiceFn} (hScale : EventLuceScale Q)
    (ρ σ : Event) : Q.prob ρ σ = 1/2 ↔ hScale.v ρ = hScale.v σ := by
  rw [hScale.luce_rule]
  constructor
  · intro h
    have hne : hScale.v ρ + hScale.v σ ≠ 0 := by
      linarith [hScale.v_pos ρ, hScale.v_pos σ]
    rw [div_eq_iff hne] at h; linarith
  · intro h
    have hne : hScale.v ρ + hScale.v σ ≠ 0 := by
      linarith [hScale.v_pos ρ, hScale.v_pos σ]
    rw [div_eq_iff hne, h]; ring

/-- **Neutral class indifference** (Luce 1959, Theorem 12):
    Under the Luce choice axiom, events classified as neutral relative to a
    reference event are indifferent to each other: Q(ρ, σ) = ½.

    If v(ρ) = v(ref) (neutral) and v(σ) = v(ref) (neutral), then v(ρ) = v(σ),
    hence Q(ρ,σ) = v(ρ)/(v(ρ)+v(σ)) = ½.

    Note: For favorable and unfavorable events, same-class membership does NOT
    imply indifference — events within these classes can have different v-values
    and thus Q(ρ,σ) ≠ ½. See `favorable_over_unfavorable` for the between-class
    ordering. -/
theorem threeClasses (Q : EventChoiceFn) (hScale : EventLuceScale Q)
    (ref : Event) (ρ σ : Event)
    (hρ : classifyEvent Q ref ρ = .neutral)
    (hσ : classifyEvent Q ref σ = .neutral) :
    Q.prob ρ σ = 1/2 := by
  have hv_ρ := (luce_eq_half_iff hScale ρ ref).mp (neutral_imp_prob_eq_half Q ref ρ hρ)
  have hv_σ := (luce_eq_half_iff hScale σ ref).mp (neutral_imp_prob_eq_half Q ref σ hσ)
  exact (luce_eq_half_iff hScale ρ σ).mpr (by linarith)

/-- Between-class ordering: favorable events are preferred over unfavorable events.
    If v(ρ) > v(ref) (favorable) and v(σ) < v(ref) (unfavorable),
    then v(ρ) > v(σ), hence Q(ρ,σ) > ½. -/
theorem favorable_over_unfavorable (Q : EventChoiceFn) (hScale : EventLuceScale Q)
    (ref : Event) (ρ σ : Event)
    (hρ : classifyEvent Q ref ρ = .favorable)
    (hσ : classifyEvent Q ref σ = .unfavorable) :
    Q.prob ρ σ > 1/2 := by
  suffices h : hScale.v σ < hScale.v ρ by
    rw [hScale.luce_rule, gt_iff_lt,
        lt_div_iff₀ (show (0 : ℝ) < hScale.v ρ + hScale.v σ from
          by linarith [hScale.v_pos ρ, hScale.v_pos σ])]
    linarith
  have h1 : hScale.v ref < hScale.v ρ := by
    have := favorable_imp_gt_half Q ref ρ hρ
    rw [hScale.luce_rule, gt_iff_lt,
        lt_div_iff₀ (show (0 : ℝ) < hScale.v ρ + hScale.v ref from
          by linarith [hScale.v_pos ρ, hScale.v_pos ref])] at this
    linarith
  have h2 : hScale.v σ < hScale.v ref := by
    have := unfavorable_imp_lt_half Q ref σ hσ
    rw [hScale.luce_rule,
        div_lt_iff₀ (show (0 : ℝ) < hScale.v σ + hScale.v ref from
          by linarith [hScale.v_pos σ, hScale.v_pos ref])] at this
    linarith
  linarith

/-- Between-class ordering: favorable events are preferred over neutral events. -/
theorem favorable_over_neutral (Q : EventChoiceFn) (hScale : EventLuceScale Q)
    (ref : Event) (ρ σ : Event)
    (hρ : classifyEvent Q ref ρ = .favorable)
    (hσ : classifyEvent Q ref σ = .neutral) :
    Q.prob ρ σ > 1/2 := by
  suffices h : hScale.v σ < hScale.v ρ by
    rw [hScale.luce_rule, gt_iff_lt,
        lt_div_iff₀ (show (0 : ℝ) < hScale.v ρ + hScale.v σ from
          by linarith [hScale.v_pos ρ, hScale.v_pos σ])]
    linarith
  have h1 : hScale.v ref < hScale.v ρ := by
    have := favorable_imp_gt_half Q ref ρ hρ
    rw [hScale.luce_rule, gt_iff_lt,
        lt_div_iff₀ (show (0 : ℝ) < hScale.v ρ + hScale.v ref from
          by linarith [hScale.v_pos ρ, hScale.v_pos ref])] at this
    linarith
  have h2 : hScale.v σ = hScale.v ref :=
    (luce_eq_half_iff hScale σ ref).mp (neutral_imp_prob_eq_half Q ref σ hσ)
  linarith

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

/-- Algebraic fact: equal fractions x/(x+y) imply equal ratios x/y.
    From x₁/(x₁+y₁) = x₂/(x₂+y₂), cross-multiplying gives
    x₁·y₂ = x₂·y₁, hence x₁/y₁ = x₂/y₂. -/
private lemma ratio_eq_of_frac_eq {x₁ y₁ x₂ y₂ : ℝ}
    (_hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (_hx₂ : 0 < x₂) (hy₂ : 0 < y₂)
    (h : x₁ / (x₁ + y₁) = x₂ / (x₂ + y₂)) :
    x₁ / y₁ = x₂ / y₂ := by
  have h1 : x₁ + y₁ ≠ 0 := by linarith
  have h2 : x₂ + y₂ ≠ 0 := by linarith
  rw [div_eq_div_iff h1 h2] at h
  rw [div_eq_div_iff (ne_of_gt hy₁) (ne_of_gt hy₂)]
  nlinarith

omit [DecidableEq Outcome] in
/-- The ratio v(a₁,ρ,b₁)/v(a₁,σ,b₁) is independent of outcomes (a₁,b₁).
    Both ratios equal Q(ρ,σ)/Q(σ,ρ) via the decomposition axiom + Luce scale. -/
private lemma ratio_independent (P : GambleChoiceFn Outcome) (hLuce : GambleLuceScale P)
    (hDecomp : DecompositionAxiom P)
    (a₁ b₁ a₂ b₂ : Outcome) (ρ σ : Event) :
    hLuce.v ⟨a₁, ρ, b₁⟩ / hLuce.v ⟨a₁, σ, b₁⟩ =
    hLuce.v ⟨a₂, ρ, b₂⟩ / hLuce.v ⟨a₂, σ, b₂⟩ := by
  apply ratio_eq_of_frac_eq (hLuce.v_pos _) (hLuce.v_pos _) (hLuce.v_pos _) (hLuce.v_pos _)
  rw [← hLuce.luce_rule, ← hLuce.luce_rule, hDecomp.decomp, hDecomp.decomp]

omit [DecidableEq Outcome] in
/-- The Luce scale value factors multiplicatively:
    v(g) = v(g.win, ρ₀, g.lose) · v(a₀, g.event, b₀) / v(a₀, ρ₀, b₀).
    This is the core step of the decomposition: the ratio v(g)/v(g.win,ρ₀,g.lose)
    depends only on the event (not on outcomes), so it can be factored out. -/
private lemma v_eq_product (P : GambleChoiceFn Outcome) (hLuce : GambleLuceScale P)
    (hDecomp : DecompositionAxiom P) (ρ₀ : Event) (a₀ b₀ : Outcome)
    (g : Gamble Outcome) :
    hLuce.v g = hLuce.v ⟨g.win, ρ₀, g.lose⟩ *
      (hLuce.v ⟨a₀, g.event, b₀⟩ / hLuce.v ⟨a₀, ρ₀, b₀⟩) := by
  have hratio := ratio_independent P hLuce hDecomp g.win g.lose a₀ b₀ g.event ρ₀
  -- hratio : v(g) / v(g.win,ρ₀,g.lose) = v(a₀,g.event,b₀) / v(a₀,ρ₀,b₀)
  have hne : hLuce.v ⟨g.win, ρ₀, g.lose⟩ ≠ 0 := ne_of_gt (hLuce.v_pos _)
  have hne' : hLuce.v ⟨a₀, ρ₀, b₀⟩ ≠ 0 := ne_of_gt (hLuce.v_pos _)
  field_simp at hratio ⊢
  nlinarith

omit [DecidableEq Outcome] in
/-- **Scale decomposition theorem** (Luce 1959, §3.D):
    Under the Luce choice axiom and the decomposition axiom, the choice
    probability for gambles can be represented as a Luce choice rule with
    scores that factor as `v(aρb) = w(a,b) · φ(ρ)`.

    The construction: fix a reference event ρ₀ and reference outcomes a₀, b₀.
    - `w(a,b) := v(a,ρ₀,b)` (gamble value with reference event)
    - `φ(ρ) := v(a₀,ρ,b₀) / v(a₀,ρ₀,b₀)` (event weight normalized by reference)

    The decomposition axiom ensures that v(g)/v(g.win,ρ₀,g.lose) depends only
    on the event, so v(g) = w(g.win,g.lose) · φ(g.event). -/
theorem scaleDecomposition (P : GambleChoiceFn Outcome)
    (hDecomp : DecompositionAxiom P)
    (hLuce : GambleLuceScale P)
    (ρ₀ : Event) (a₀ b₀ : Outcome) :
    ∃ sd : ScaleDecomposition Outcome,
      ∀ g₁ g₂ : Gamble Outcome,
        sd.gambleValue g₁ + sd.gambleValue g₂ > 0 →
        P.prob g₁ g₂ = sd.gambleValue g₁ / (sd.gambleValue g₁ + sd.gambleValue g₂) := by
  refine ⟨{
    outcomeValue := λ a b => hLuce.v ⟨a, ρ₀, b⟩,
    eventWeight := λ ρ => hLuce.v ⟨a₀, ρ, b₀⟩ / hLuce.v ⟨a₀, ρ₀, b₀⟩,
    outcomeValue_nonneg := λ a b => le_of_lt (hLuce.v_pos _),
    eventWeight_nonneg := λ ρ => div_nonneg (le_of_lt (hLuce.v_pos _))
      (le_of_lt (hLuce.v_pos _)),
  }, ?_⟩
  intro g₁ g₂ _
  simp only [ScaleDecomposition.gambleValue]
  -- Each gamble value equals v(g) by the factoring lemma
  have hv1 := v_eq_product P hLuce hDecomp ρ₀ a₀ b₀ g₁
  have hv2 := v_eq_product P hLuce hDecomp ρ₀ a₀ b₀ g₂
  -- Rewrite the products back to v(g), then apply Luce rule
  rw [← hv1, ← hv2, ← hLuce.luce_rule]

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
