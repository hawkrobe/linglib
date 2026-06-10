import Linglib.Pragmatics.RSA.Canonical
import Linglib.Features.Subjectivity
import Mathlib.Probability.Distributions.Uniform

/-!
# [yoon-etal-2020] — Polite speech emerges from competing social goals

RSA model of [yoon-etal-2020] (Open Mind 4): polite speech arises from a
speaker trading off three communicative goals — to be informative, to be
kind, and to *appear* informative and kind. The experimental domain: Ann
rates Bob's poem (states `s₀–s₃`, hearts) and chooses among eight
utterances ({terrible, bad, good, amazing} × {plain, negated}).

The model stack (the paper's Figure 4): a literal listener
`P_L0(s|w) ∝ L(w,s)·P(s)` over empirically elicited *soft* semantics; a
first-order speaker with utility
`U_S1 = φ·ln P_L0(s|w) + (1−φ)·E_{P_L0}[V(s)] − c·l(w)`; a pragmatic
listener jointly inferring state and goal weight,
`P_L1(s,φ|w) ∝ P_S1(w|s,φ)·P(s)·P(φ)`; and a second-order polite speaker
with `U_S2 = ω_inf·ln P_L1(s|w) + ω_soc·E_{P_L1}[V(s)] +
ω_pres·ln P_L1(φ̂|w) − c·l(w)`.

Instantiated on the canonical pipeline: the S1 speaker is
`RSA.Canonical.S1` over `(state × φ)` speaker situations, and the pragmatic
listener is `RSA.Canonical.L1`, the joint posterior over
`HeartState × Phi` — the paper's eq. (4) by construction, with the
`U_pres` marginal available as `.snd`. The paper's L0-gate (utterances
with zero literal fit are unavailable to informativity-sensitive speakers)
is the `⊥`-utility branch.

## Main statements

* `social_prefers_indirect` / `social_prefers_positive` — the pure-social
  speaker (φ = 0) prefers indirect and positive utterances (Figure 2, S1
  social facet), for every α > 0: pure expected-value comparisons.
* `informative_prefers_direct` / `informative_prefers_direct_positive` —
  the pure-informative speaker (φ = 1) prefers direct utterances
  (Figure 2, S1 informational facet), for every α > 0: the first is the
  L0-gate, the second a log-monotonicity comparison.
* `s2Utility` — the full three-goal S2 utility over the joint listener,
  with the Table-2 MAP weight profiles.
* `socialGoalSubjectivityLevel` — bridge to [traugott-dasher-2002]'s
  intersubjectivity cline.

## Implementation notes

**Lexicon provenance.** `softSemantics` stipulates acceptance proportions
`k/49` attributed to `literal_semantics.csv` in the paper's repository
(the paper itself prints no θ table; N = 51 recruited per the supplement).
-- UNVERIFIED: the k/49 values and the N = 49-after-exclusions claim await
verification against the CSV. Negated utterances use graded negation
`⟦not φ⟧ = 1 − ⟦φ⟧` — **a compositional construction of this file, not the
paper's lexicon**: the paper elicits θ per utterance, including negated
forms. The φ grid discretizes the paper's continuous `φ ~ Uniform(0,1)` to
five points.

**Findings policy.** S1-level preferences are stated as theorems: they are
parameter-free (any α > 0) and robust to lexicon perturbation. The S2-level
negation preferences and the L1 state-inference orderings are *numeric*
facts — α-dependent and, for S2, sensitive to the third decimal of single
norming proportions — and are recorded as verified prose (§S2 below), per
the library's policy on findings whose truth depends on exact parameter
values. Notably, independent recomputation shows the paper's headline
`U_S2(not terrible) > U_S2(terrible)` under both-goal weights at state s₀
is TRUE at the fitted parameters (margin ≈ 0.14) — correcting the previous
version of this file, which left it `sorry`ed with a docstring wrongly
claiming it fails under point-estimate semantics (the old reflection
tactic's interval arithmetic merely could not separate the sides).
-/

set_option autoImplicit false

namespace YoonEtAl2020

open scoped ENNReal
open RSA.Canonical

/-! ### States, utterances, goals -/

/-- World states: the true rating (number of hearts) deserved. -/
inductive HeartState where
  | h0 | h1 | h2 | h3
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Subjective value `V(s)`: the paper's linear state-value mapping. -/
def subjectiveValue : HeartState → ℚ
  | .h0 => 0
  | .h1 => 1
  | .h2 => 2
  | .h3 => 3

/-- The eight utterances: four adjectives × {plain, negated}. -/
inductive Utterance where
  | terrible | bad | good | amazing
  | notTerrible | notBad | notGood | notAmazing
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Is this a negated utterance? -/
def Utterance.isNegated : Utterance → Bool
  | .notTerrible | .notBad | .notGood | .notAmazing => true
  | _ => false

/-- Speaker goal conditions from the experiment. -/
inductive GoalCondition where
  | informative | kind | both
  deriving DecidableEq, Repr, Inhabited

/-- Discretized goal weight φ (informativity vs. kindness); the paper's
`φ ~ Uniform(0,1)` discretized to five points. -/
inductive Phi where
  | p0 | p25 | p50 | p75 | p100
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The rational value of each φ level. -/
def Phi.val : Phi → ℚ
  | .p0 => 0
  | .p25 => 1/4
  | .p50 => 1/2
  | .p75 => 3/4
  | .p100 => 1

/-! ### The soft lexicon -/

/-- Soft semantic acceptance proportions for the four positive adjectives.
-- UNVERIFIED: stipulated as `k/49` from `literal_semantics.csv` in the
paper's repository; not printed in the paper. -/
def softSemantics : Utterance → HeartState → ℚ
  | .terrible, .h0 => 1
  | .terrible, .h1 => 26/49
  | .terrible, .h2 => 0
  | .terrible, .h3 => 1/49
  | .bad, .h0 => 1
  | .bad, .h1 => 45/49
  | .bad, .h2 => 0
  | .bad, .h3 => 0
  | .good, .h0 => 1/49
  | .good, .h1 => 2/49
  | .good, .h2 => 47/49
  | .good, .h3 => 1
  | .amazing, .h0 => 1/49
  | .amazing, .h1 => 1/49
  | .amazing, .h2 => 7/49
  | .amazing, .h3 => 47/49
  | _, _ => 0  -- negated forms are derived below

/-- Utterance semantics: positive forms from the norming data; negated
forms by graded negation `⟦not φ⟧ = 1 − ⟦φ⟧`. **This construction is the
formaliser's, not the paper's**: the paper elicits per-utterance θ for all
eight utterances; the derived profiles are qualitatively compatible with
the paper's description of "not terrible" but are not its lexicon. -/
def meaning : Utterance → HeartState → ℚ
  | .notTerrible, s => 1 - softSemantics .terrible s
  | .notBad, s => 1 - softSemantics .bad s
  | .notGood, s => 1 - softSemantics .good s
  | .notAmazing, s => 1 - softSemantics .amazing s
  | u, s => softSemantics u s

/-- The lexicon is soft: values in `[0, 1]`. -/
theorem meaning_bounded : ∀ u s, 0 ≤ meaning u s ∧ meaning u s ≤ 1 := by
  intro u s
  cases u <;> cases s <;> constructor <;> norm_num [meaning, softSemantics]

/-- Utterance cost: length in words ("It was X" = 3, "It wasn't X" = 4);
only the difference matters in comparisons. -/
def utteranceCost : Utterance → ℕ
  | .terrible | .bad | .good | .amazing => 3
  | _ => 4

theorem negation_costlier (u : Utterance) (h : u.isNegated) : utteranceCost u = 4 := by
  cases u <;> first | rfl | simp [Utterance.isNegated] at h

/-! ### The literal listener in closed form

With a uniform state prior, `P_L0(s|w) = meaning w s / Σ_s' meaning w s'`.
The closed rational forms below feed the speaker utility exactly. -/

private theorem sum_hearts (f : HeartState → ℚ) :
    (∑ s : HeartState, f s) = f .h0 + f .h1 + f .h2 + f .h3 := by
  rw [show (Finset.univ : Finset HeartState) = {.h0, .h1, .h2, .h3} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The lexicon mass of an utterance (the L0 partition function). -/
def semMass (u : Utterance) : ℚ := ∑ s : HeartState, meaning u s

/-- `P_L0(s|u)` in closed rational form (uniform state prior cancels). -/
def l0Val (u : Utterance) (s : HeartState) : ℚ := meaning u s / semMass u

/-- `E_{P_L0(·|u)}[V(s)]`: the social value of `u` to the literal listener. -/
def ev (u : Utterance) : ℚ := ∑ s : HeartState, l0Val u s * subjectiveValue s

private theorem ev_terrible : ev .terrible = 29/76 := by
  rw [ev, sum_hearts]
  norm_num [l0Val, semMass, sum_hearts, meaning, softSemantics, subjectiveValue, show Fintype.card HeartState = 4 from rfl]

private theorem ev_notTerrible : ev .notTerrible = 53/24 := by
  rw [ev, sum_hearts]
  norm_num [l0Val, semMass, sum_hearts, meaning, softSemantics, subjectiveValue, show Fintype.card HeartState = 4 from rfl]

private theorem ev_amazing : ev .amazing = 39/14 := by
  rw [ev, sum_hearts]
  norm_num [l0Val, semMass, sum_hearts, meaning, softSemantics, subjectiveValue, show Fintype.card HeartState = 4 from rfl]

private theorem ev_notAmazing : ev .notAmazing = 69/70 := by
  rw [ev, sum_hearts]
  norm_num [l0Val, semMass, sum_hearts, meaning, softSemantics, subjectiveValue, show Fintype.card HeartState = 4 from rfl]

/-! ### The S1 speaker on the canonical pipeline -/

/-- S1 utility (the paper's
`U_S1 = φ·ln P_L0(s|w) + (1−φ)·E_{P_L0}[V] − c·l(w)`, `c = 1`), as an
`EReal` score over speaker situations `(s, φ)`. The `⊥` branch is the
paper's L0-gate: an utterance with zero literal fit is unavailable to any
informativity-sensitive speaker (φ ≠ 0); for the pure-social speaker the
φ-weighted log term vanishes, so the gate does not apply. -/
noncomputable def util (α : ℝ) (p : HeartState × Phi) (u : Utterance) : EReal :=
  if meaning u p.1 = 0 ∧ p.2 ≠ .p0 then ⊥
  else ((α * ((Phi.val p.2 : ℝ) * Real.log (l0Val u p.1 : ℝ)
    + (1 - (Phi.val p.2 : ℝ)) * (ev u : ℝ)
    - (utteranceCost u : ℝ)) : ℝ) : EReal)

instance (α : ℝ) : ViableSpeaker (util α) where
  no_top _ _ := by
    unfold util
    split
    · exact bot_ne_top
    · exact EReal.coe_ne_top _
  some_finite p := by
    obtain ⟨s, φ⟩ := p
    cases s
    · exact ⟨.terrible, by
        unfold util
        rw [if_neg (by norm_num [meaning, softSemantics])]
        exact EReal.coe_ne_bot _⟩
    · exact ⟨.bad, by
        unfold util
        rw [if_neg (by norm_num [meaning, softSemantics])]
        exact EReal.coe_ne_bot _⟩
    · exact ⟨.good, by
        unfold util
        rw [if_neg (by norm_num [meaning, softSemantics])]
        exact EReal.coe_ne_bot _⟩
    · exact ⟨.amazing, by
        unfold util
        rw [if_neg (by norm_num [meaning, softSemantics])]
        exact EReal.coe_ne_bot _⟩

/-- The S1 speaker: the canonical softmax speaker over `util`. -/
noncomputable def speaker (α : ℝ) : HeartState × Phi → PMF Utterance :=
  S1 (util α)

private theorem util_ungated {α : ℝ} {s : HeartState} {φ : Phi} {u : Utterance}
    (h : ¬(meaning u s = 0 ∧ φ ≠ .p0)) :
    util α (s, φ) u
      = ((α * ((Phi.val φ : ℝ) * Real.log (l0Val u s : ℝ)
          + (1 - (Phi.val φ : ℝ)) * (ev u : ℝ) - (utteranceCost u : ℝ)) : ℝ) : EReal) := by
  unfold util
  rw [if_neg h]

private theorem util_gated {α : ℝ} {s : HeartState} {φ : Phi} {u : Utterance}
    (h0 : meaning u s = 0) (hφ : φ ≠ .p0) : util α (s, φ) u = ⊥ := by
  unfold util
  rw [if_pos ⟨h0, hφ⟩]

/-! ### S1 findings (Figure 2, S1 facets) — structural, every α > 0 -/

/-- **The pure-social speaker prefers indirect speech** at the worst state:
"it wasn't terrible" beats "it was terrible" (Figure 2, S1 social facet).
A pure expected-value comparison: the social gain `E[V]` of the indirect
form (53/24 vs 29/76) exceeds its one-word extra cost. -/
theorem social_prefers_indirect {α : ℝ} (hα : 0 < α) :
    speaker α (.h0, .p0) .terrible < speaker α (.h0, .p0) .notTerrible := by
  rw [speaker, S1_prefers_iff,
      util_ungated (by simp), util_ungated (by simp)]
  refine EReal.coe_lt_coe (mul_lt_mul_of_pos_left ?_ hα)
  rw [ev_terrible, ev_notTerrible]
  norm_num [Phi.val, utteranceCost]

/-- **The pure-social speaker prefers positive utterances**: "it was
amazing" beats "it wasn't amazing" (same cost direction reversed: here the
positive form is both kinder and cheaper). -/
theorem social_prefers_positive {α : ℝ} (hα : 0 < α) :
    speaker α (.h0, .p0) .notAmazing < speaker α (.h0, .p0) .amazing := by
  rw [speaker, S1_prefers_iff,
      util_ungated (by simp), util_ungated (by simp)]
  refine EReal.coe_lt_coe (mul_lt_mul_of_pos_left ?_ hα)
  rw [ev_amazing, ev_notAmazing]
  norm_num [Phi.val, utteranceCost]

/-- **The pure-informative speaker prefers direct speech** at the worst
state: "it wasn't terrible" is literally false at zero hearts (graded
meaning 0), so the L0-gate excludes it for any informativity-sensitive
speaker. -/
theorem informative_prefers_direct (α : ℝ) :
    speaker α (.h0, .p100) .notTerrible < speaker α (.h0, .p100) .terrible := by
  rw [speaker, S1_prefers_iff,
      util_gated (by norm_num [meaning, softSemantics]) (by decide),
      util_ungated (by norm_num [meaning, softSemantics])]
  exact EReal.bot_lt_coe _

/-- Even slight informativity (φ = 1/4) suffices to exclude the literally
false indirect form — a gate fact about the discretized model, not a claim
of the paper's. -/
theorem slight_informativity_prefers_direct (α : ℝ) :
    speaker α (.h0, .p25) .notTerrible < speaker α (.h0, .p25) .terrible := by
  rw [speaker, S1_prefers_iff,
      util_gated (by norm_num [meaning, softSemantics]) (by decide),
      util_ungated (by norm_num [meaning, softSemantics])]
  exact EReal.bot_lt_coe _

/-- **The pure-informative speaker prefers the direct positive** at the
best state: "amazing" beats "not amazing" at three hearts — a genuine
log-monotonicity comparison (`P_L0(s₃|amazing) = 47/56 > 1/70 =
P_L0(s₃|not amazing)`), with cost also favouring the direct form. -/
theorem informative_prefers_direct_positive {α : ℝ} (hα : 0 < α) :
    speaker α (.h3, .p100) .notAmazing < speaker α (.h3, .p100) .amazing := by
  rw [speaker, S1_prefers_iff,
      util_ungated (by norm_num [meaning, softSemantics]),
      util_ungated (by norm_num [meaning, softSemantics])]
  refine EReal.coe_lt_coe (mul_lt_mul_of_pos_left ?_ hα)
  have hlog : Real.log ((l0Val .notAmazing .h3 : ℚ) : ℝ)
      < Real.log ((l0Val .amazing .h3 : ℚ) : ℝ) := by
    apply Real.log_lt_log
    · norm_num [l0Val, semMass, sum_hearts, meaning, softSemantics, show Fintype.card HeartState = 4 from rfl]
    · norm_num [l0Val, semMass, sum_hearts, meaning, softSemantics, show Fintype.card HeartState = 4 from rfl]
  simp only [Phi.val]
  norm_num [utteranceCost]
  linarith [hlog]

/-! ### The pragmatic listener: the joint (state, goal) posterior -/

/-- Uniform joint prior over `state × φ` (the paper's uniform `P(s)` and
uniform `P(φ)`, discretized). -/
noncomputable def prior : PMF (HeartState × Phi) := PMF.uniformOfFintype _

theorem prior_pos (p : HeartState × Phi) : prior p ≠ 0 :=
  (prior.mem_support_iff p).mp (PMF.mem_support_uniformOfFintype p)

/-- Every utterance is literally compatible with some state, so every
utterance has positive marginal probability. -/
theorem marginal_ne_zero (α : ℝ) (u : Utterance) :
    PMF.marginal (speaker α) prior u ≠ 0 := by
  have key : ∀ (s : HeartState), meaning u s ≠ 0 →
      PMF.marginal (speaker α) prior u ≠ 0 := fun s hs =>
    PMF.marginal_ne_zero _ _ _ (prior_pos (s, .p100))
      (S1_ne_zero (util α) (by rw [util_ungated (by simp [hs])]; exact EReal.coe_ne_bot _))
  cases u
  · exact key .h0 (by norm_num [meaning, softSemantics])
  · exact key .h0 (by norm_num [meaning, softSemantics])
  · exact key .h3 (by norm_num [meaning, softSemantics])
  · exact key .h3 (by norm_num [meaning, softSemantics])
  · exact key .h2 (by norm_num [meaning, softSemantics])
  · exact key .h2 (by norm_num [meaning, softSemantics])
  · exact key .h0 (by norm_num [meaning, softSemantics])
  · exact key .h0 (by norm_num [meaning, softSemantics])

/-- The pragmatic listener (the paper's eq. (4)): the joint Bayesian
posterior over `(state, φ)` given the utterance. The state marginal
(`.fst`) is `P_L1(s|w)`; the φ marginal (`.snd`) is `P_L1(φ|w)`, the
quantity inside the paper's presentational utility (eq. (3)). -/
noncomputable def listener (α : ℝ) (u : Utterance) : PMF (HeartState × Phi) :=
  L1 (speaker α) prior u (marginal_ne_zero α u)

/-! ### L1 state inferences (prose)

The previous version of this file proved eight L1 state-inference
orderings (e.g. `P_L1(s₀|terrible) > P_L1(s₃|terrible)`: 0.686 vs 0.0003)
by interval-arithmetic reflection. They are numeric facts about
φ-marginalised sums of exponentials; independent recomputation confirms
all eight at α = 3, seven robust over α ∈ [0.01, 100] and one
(`P_L1(s₁|bad) > P_L1(s₀|bad)`, 0.610 vs 0.390) reversing below α ≈ 1.19.
Per the parameter-dependence policy they are recorded here as prose. -/

/-! ### The S2 polite speaker -/

/-- S2 goal weights `ω` and projected goal `φ̂`. MAP estimates from the
paper's Table 2 (main text); `phiHat` discretizes the fitted φ to the grid
(0.36, 0.37 → ¼; 0.49 → ½). -/
structure S2Weights where
  wInf : ℚ
  wSoc : ℚ
  wPres : ℚ
  phiHat : Phi

/-- Both-goal condition (Table 2: ω = (0.36, 0.11, 0.54), φ = 0.36). -/
def bothWeights : S2Weights := ⟨36/100, 11/100, 54/100, .p25⟩

/-- Informative condition (Table 2: ω = (0.36, 0.02, 0.62), φ = 0.49). -/
def informativeWeights : S2Weights := ⟨36/100, 2/100, 62/100, .p50⟩

/-- Kind condition (Table 2's "social" row: ω = (0.25, 0.31, 0.44),
φ = 0.37). -/
def kindWeights : S2Weights := ⟨25/100, 31/100, 44/100, .p25⟩

/-- The S2 utility (the paper's eq. (2) with eq. (3)):
`ω_inf·ln P_L1(s|w) + ω_soc·E_{P_L1(s|w)}[V] + ω_pres·ln P_L1(φ̂|w) − c·l(w)`,
over the joint listener's marginals. The cost sits inside the utility (and
hence inside S2's α-scaling), as in the paper's Figure 4 — correcting the
previous version, which moved it outside as an utterance prior. -/
noncomputable def s2Utility (α c : ℝ) (W : S2Weights) (s : HeartState)
    (u : Utterance) : ℝ :=
  (W.wInf : ℝ) * Real.log (((listener α u).fst s).toReal)
    + (W.wSoc : ℝ)
        * ∑ s' : HeartState, ((listener α u).fst s').toReal * (subjectiveValue s' : ℝ)
    + (W.wPres : ℝ) * Real.log (((listener α u).snd W.phiHat).toReal)
    - c * (utteranceCost u : ℝ)

/-! ### S2 findings (prose, independently recomputed)

At the fitted parameters (α ≈ 4.47, c ≈ 2.64 — both attributed to the
paper's supplement/repository and -- UNVERIFIED from the PDF, which states
only the priors `α ~ Uniform(0,20)`, `c ~ Uniform(1,10)`), with cost
α-scaled as above:

* **informative**: `U_S2(terrible) > U_S2(not terrible)` at s₀
  (−1.13 > −2.62) — projecting honesty favours direct negative utterances
  (the paper's §Model Predictions); robust across the α-scan.
* **kind**: `U_S2(not terrible) > U_S2(terrible)` at s₀ (−1.84 > −2.32);
  holds for α ≳ 2.18.
* **both** (the paper's headline, Figure 6): `U_S2(not terrible) >
  U_S2(terrible)` at s₀ (−2.72 > −2.86, margin ≈ 0.14, confirmed at
  50-digit precision); holds for α ≳ 3.84. The previous version of this
  file `sorry`ed this statement with a docstring claiming it *fails* under
  point-estimate semantics — that claim was false: the reflection tactic's
  interval arithmetic merely could not separate the sides.

Sensitivity (the reason these are prose, not theorems): both negation
preferences flip if the single norming proportion `softSemantics .amazing
.h0 = 1/49 ≈ 0.020` drops to ≈ 0.01 — they hinge on one participant's
judgment in the norming task — and are α-dependent, unlike the S1
theorems above. The model-comparison content (Table 1: the full
informational + social + presentational model beats all ablations, log BF
≥ 11) is Bayesian-fit material outside the formalisation's scope. -/

/-! ### Bridge to the subjectivity cline -/

/-- The politeness model instantiates [traugott-dasher-2002]'s
intersubjectivity: for φ < 1 the speaker trades informativity for
attention to the addressee's face, and S2 additionally manages how kind
they *appear* — doubly intersubjective. [narrog-2010] connects this to
modality: strong obligation is face-threatening because it is performative
and volitive. -/
def socialGoalSubjectivityLevel : Features.Subjectivity.SubjectivityLevel :=
  .intersubjective

end YoonEtAl2020
