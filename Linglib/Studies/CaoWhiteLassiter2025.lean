import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Card
import Mathlib.Probability.Distributions.Uniform
import Linglib.Core.Probability.Constructions
import Linglib.Data.Examples.CaoWhiteLassiter2025
import Linglib.Semantics.Causation.Interpretation
import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Cao, White & Lassiter 2025: graded causative verb semantics

This file formalizes the graded-causative analysis of English *cause*,
*make*, and *force* from [cao-white-lassiter-2025]. On that account,
acceptability tracks three measures defined in one structural causal
model: Pearl's probability of sufficiency ([pearl-2019],
`Causation.SEM.probSufficiency`), a simplified
[halpern-kleiman-weiner-2018] degree of intention (`intentionDegree`),
and the number of alternative actions available to the causee
(`altCount`). The models are time-indexed (`CausalGraph.TimeIndex`),
and their agents play a soft-optimality policy (`softOptimalPolicy`).
The model apparatus is shared with
[cao-geiger-kreiss-icard-gerstenberg-2023].

The paper's in-text judgments (its examples (3)–(11)) are stored as rows
in `Data/Examples/CaoWhiteLassiter2025.json`. Regression estimates
remain in prose; no single measure reliably determines verb choice, and
each verb's per-verb model has a distinct set of reliable interaction
terms.

## References

* [A. Cao, A. S. White, D. Lassiter,
  *Cause, make, and force as graded causatives*][cao-white-lassiter-2025]
-/

namespace CaoWhiteLassiter2025

open Causation Causation.Mechanism Causation.SEM Features
open scoped ENNReal NNReal

/-! ### Soft-optimality policy

The paper's mechanisms for agent moves (§2.1.1): the highest-utility
move — computed by minimax over the game tree, with terminal utility
`Winner × (EmptySpace + 1)` — is taken with probability `ρ + (1−ρ)/n`
and every other available move with `(1−ρ)/n`. The skill parameter ρ
interpolates between a random player (`ρ = 0`, "a less skilled player")
and a professional (`ρ = 1`). -/

section
variable {A : Type*} [Fintype A] [Nonempty A]

/-- The soft-optimality policy of a player of skill `ρ` mixes optimal
    play with uniform noise: the highest-utility move `best` with
    probability `ρ`, otherwise a uniform random move (§2.1.1 of
    [cao-white-lassiter-2025]). -/
noncomputable def softOptimalPolicy (best : A) (ρ : ℝ≥0) (hρ : ρ ≤ 1) : PMF A :=
  PMF.mix ρ hρ (PMF.uniformOfFintype A) (PMF.pure best)

/-- The paper's arithmetic form of the policy: the best move carries
    `ρ + (1 − ρ)/n`, every other available move `(1 − ρ)/n`. -/
theorem softOptimalPolicy_apply [DecidableEq A] (best : A) (ρ : ℝ≥0) (hρ : ρ ≤ 1) (a : A) :
    softOptimalPolicy best ρ hρ a =
      (if a = best then (ρ : ℝ≥0∞) else 0) + (1 - ρ : ℝ≥0) / Fintype.card A := by
  simp [softOptimalPolicy, PMF.pure_apply, PMF.uniformOfFintype_apply, mul_ite, mul_one,
    mul_zero, div_eq_mul_inv, add_comm]

/-- At `ρ = 0` the soft-optimality policy is the uniform random player —
    the paper's limiting case ("assume that the players are infants"),
    under which its worked SUF contrast between contexts collapses. -/
theorem softOptimalPolicy_zero (best : A) :
    softOptimalPolicy best 0 zero_le_one = PMF.uniformOfFintype A :=
  PMF.mix_zero _ _

/-- At `ρ = 1` the soft-optimality policy is the deterministic
    professional — a Dirac on the highest-utility move. -/
theorem softOptimalPolicy_one (best : A) :
    softOptimalPolicy best 1 le_rfl = PMF.pure best :=
  PMF.mix_one _ _

end

/-! ### The ALT measure -/

section
variable {A : Type*} [Fintype A]

/-- `altCount p taken` is the number of alternative actions available to
    the causee — the support of the action distribution `p`, excluding
    the action actually taken. This is the ALT measure of
    [cao-white-lassiter-2025] (§2.2; `ALT(Y₁) = 5` at its fig. 2a board
    state). -/
noncomputable def altCount (p : PMF A) (taken : A) : ℕ :=
  (p.support \ {taken}).ncard

/-- `ALT = 0` says exactly that the causee could not have done
    otherwise — every action other than the one taken has probability
    zero. -/
theorem altCount_eq_zero_iff (p : PMF A) (taken : A) :
    altCount p taken = 0 ↔ ∀ a ≠ taken, p a = 0 := by
  rw [altCount, Set.ncard_eq_zero (Set.toFinite _), Set.sdiff_eq_empty]
  constructor
  · intro hsub a hne
    by_contra hpa
    exact hne (hsub ((p.mem_support_iff a).mpr hpa))
  · intro h a ha
    by_contra hne
    exact (p.mem_support_iff a).mp ha (h a (by simpa using hne))

/-! ### The INT measure

The paper's §2.3 displayed equation, a simplified
[halpern-kleiman-weiner-2018] degree of intention:

`INT(a) = Pr(A = a ∧ G) · u′(a) / Σ_{a′} Pr(A = a′ ∧ G) · u′(a′)`

"the probability that an action performed in a state will result in the
desired outcome, normalized by the probability of all alternative
actions that would have resulted in the same outcome", with each term
weighted by exponentiated utility `u′ = e^u` — the exponential serving
only to make the weights strictly positive. We abstract the weight to
any `w : A → ℝ≥0`; the paper's instantiation is `w = e^u`. -/

/-- `intentionDegree pr w a` is the goal-weighted share of action `a`
    among all goal-conducive alternatives — the INT measure of
    [cao-white-lassiter-2025] (§2.3). Here `pr a′` is the model
    probability that the agent takes `a′` and the goal results, and `w`
    is the action weight (exponentiated utility, in the paper). -/
noncomputable def intentionDegree (pr : A → ℝ≥0∞) (w : A → ℝ≥0) (a : A) : ℝ≥0∞ :=
  (pr a * w a) / ∑ a', pr a' * w a'

/-- INT never exceeds 1. -/
theorem intentionDegree_le_one (pr : A → ℝ≥0∞) (w : A → ℝ≥0) (a : A) :
    intentionDegree pr w a ≤ 1 :=
  ENNReal.div_le_of_le_mul <| by
    rw [one_mul]
    exact Finset.single_le_sum (f := fun a' => pr a' * w a') (fun _ _ => zero_le)
      (Finset.mem_univ a)

/-- The paper's INT over a `SEM` instantiates `intentionDegree` with
    `pr a′` the probability, under the development of the context, that
    the action vertex takes value `a′` and the goal event holds — the
    paper's `Pr((M,u⃗) ⊨ A = a⃗′ ∧ G = g⃗)`. -/
noncomputable def modelIntention {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] (ctx : Valuation α)
    (act : V) [Fintype (α act)] (goal : Set (Valuation α)) (w : α act → ℝ≥0)
    (a : α act) : ℝ≥0∞ :=
  intentionDegree
    (fun a' => (develop M ctx).probOfSet {s | s.hasValue act a' ∧ s ∈ goal}) w a

/-- If every non-taken action has zero probability and the taken
    action's goal-weighted mass is nonzero and finite, its INT is 1. -/
theorem intentionDegree_eq_one_of_no_alternatives
    (pr : A → ℝ≥0∞) (w : A → ℝ≥0) (taken : A)
    (halt : ∀ a ≠ taken, pr a = 0)
    (h0 : pr taken * w taken ≠ 0) (hfin : pr taken ≠ ⊤) :
    intentionDegree pr w taken = 1 := by
  rw [intentionDegree,
    Finset.sum_eq_single taken (fun a _ ha => by rw [halt a ha, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
  exact ENNReal.div_self h0 (ENNReal.mul_ne_top hfin ENNReal.coe_ne_top)

/-- An action without alternatives is trivially intentional. If the
    causee's action distribution `p` leaves no alternatives
    (`altCount = 0`), the taken action's INT degenerates to 1 for any
    joint action-and-goal weights `pr` dominated by `p` — the
    alternative-possibilities principle ([frankfurt-1969], via
    [halpern-kleiman-weiner-2018]) behind the paper's *made*/*forced*
    contrast in its example (8). -/
theorem intentionDegree_eq_one_of_altCount_eq_zero
    (p : PMF A) (pr : A → ℝ≥0∞) (w : A → ℝ≥0) (taken : A)
    (hle : ∀ a, pr a ≤ p a) (halt : altCount p taken = 0)
    (h0 : pr taken * w taken ≠ 0) :
    intentionDegree pr w taken = 1 :=
  intentionDegree_eq_one_of_no_alternatives pr w taken
    (fun a ha => le_antisymm ((altCount_eq_zero_iff p taken).mp halt a ha ▸ hle a) zero_le)
    h0
    (((hle taken).trans (p.coe_le_one taken)).trans_lt ENNReal.one_lt_top).ne

end

/-! ### Deterministic limit

In the deterministic limit, SUF collapses to a {0,1} indicator
(`Causation.SEM.probSufficiency_eq_indicator_of_deterministic`). At the
vacuous (empty) context this is exactly [nadathur-lauer-2020]'s causal
sufficiency (their definition (23)): with nothing observed, Pearl's
counterfactual degenerates to the bare interventional development of
`cause := true`. -/

section
variable {V : Type*} [Fintype V] [DecidableEq V] (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
  [IsDeterministic M]

/-- SUF in the deterministic limit — the {0,1} indicator, over a
    `BoolSEM`, of [nadathur-lauer-2020]'s causal sufficiency (their
    definition (23), `causallySufficient`). -/
noncomputable def deterministicSuf (background : Valuation (fun _ : V => Bool))
    (cause effect : V) : ENNReal :=
  if BoolSEM.causallySufficient M background cause effect then 1 else 0

/-- At the empty context (vacuous abduction), the counterfactual
    `probSufficiency` reduces to the deterministic {0,1} indicator
    `deterministicSuf` — i.e. to [nadathur-lauer-2020]'s causal
    sufficiency. This makes "interventional = counterfactual at a
    vacuous context" a theorem rather than a conflation. -/
theorem probSufficiency_empty_eq_deterministicSuf (c e : V) :
    probSufficiency M Valuation.empty c true e true
      = deterministicSuf M Valuation.empty c e := by
  rw [probSufficiency_eq_indicator_of_deterministic, cfSeed_empty]
  unfold deterministicSuf BoolSEM.causallySufficient SEM.causallySufficient
    SEM.developsToValue
  by_cases h :
      (M.developDet ((Valuation.empty (α := fun _ : V => Bool)).extend c true)).hasValue e true <;>
    simp [h]

/-- The hub denotation for *make* entails maximal SUF at the vacuous
    context — whenever `Causative.toSemantics M .make` holds (both
    clauses of [nadathur-lauer-2020]'s definition (23), over the strict
    development), Pearl's probability of sufficiency is 1. The converse
    fails, since the eager development fills undetermined exogenous
    vertices from their mechanisms; the categorical *make* semantics is
    strictly stronger than maximal graded SUF. -/
theorem probSufficiency_empty_eq_one_of_make (c e : V)
    (h : Causative.toSemantics M .make Valuation.empty c true e true) :
    probSufficiency M Valuation.empty c true e true = 1 := by
  rw [probSufficiency_empty_eq_deterministicSuf]
  unfold deterministicSuf
  exact if_pos (causallySufficient_of_causallyEntails h.2)

end

/-! ### The paper's judgment data

The paper's in-text acceptability contrasts are typed rows in
`Data.Examples.CaoWhiteLassiter2025` (examples (3)–(11)): the
non-interchangeability triplets, the gym gradability triplets, the
could-have-done-otherwise pair, the intent-denial continuations, and the
*make*/*let* sufficiency pair. Regression results stay in the module
docstring: analysis outputs are not Lean content. -/

/-- The force-dynamic dispatch of [nadathur-lauer-2020] gives *make* and
    *force* identical truth conditions, but the paper's minimal pair (8)
    — same frame, a could-have-done-otherwise continuation — pulls them
    apart; *made* tolerates the continuation, *forced* resists it. The
    ALT/INT measures register the difference
    (`intentionDegree_eq_one_of_altCount_eq_zero`). -/
theorem make_force_same_semantics_different_judgments
    {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V] [DecidableValuation α]
    [∀ v, Fintype (α v)] (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [IsDeterministic M] :
    Causative.toSemantics M .make = Causative.toSemantics M .force ∧
    Examples.cwl2025_ex8a.judgment = .acceptable ∧
    Examples.cwl2025_ex8b.judgment = .questionable :=
  ⟨rfl, rfl, rfl⟩

/-! ### A probabilistic example

A 2-vertex SEM whose `effect` mechanism is a `p`-weighted coin —
genuinely probabilistic, not Dirac. Demonstrates that `probSufficiency`
accepts non-deterministic SEMs (no `IsDeterministic` constraint). -/

namespace ProbabilisticExample

open scoped NNReal

/-- A 2-vertex SEM with root `cause` and child `effect`. -/
inductive V | cause | effect
  deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨fun | .cause => ∅ | .effect => {.cause}⟩

variable (p : ℝ≥0) (h : p ≤ 1)

/-- The probabilistic mechanism for `effect`, ignoring its parent and
    returning `true` with probability `p` — genuinely non-Dirac when
    `p ∉ {0, 1}`. -/
noncomputable def effectMech :
    Mechanism graph (fun _ => Bool) .effect :=
  ⟨fun _ => PMF.mix p h (PMF.pure false) (PMF.pure true)⟩

/-- A genuinely probabilistic SEM (not `IsDeterministic` for `p ∉ {0,1}`). -/
noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .cause => const (G := graph) false
      | .effect => effectMech p h }

/-- The 2-vertex graph is time-indexed in the sense of the paper's
    definition 1, with `cause` at step 0 and `effect` at step 1. -/
def timeIndex : CausalGraph.TimeIndex graph where
  time := fun | .cause => 0 | .effect => 1
  parent_succ := by
    intro u v h
    cases v <;> simp [graph] at h
    subst h
    rfl

instance : CausalGraph.IsDAG graph := timeIndex.isDAG

instance : CausalGraph.IsDAG (model p h).graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

/-- `probSufficiency` accepts this SEM despite it NOT being
    `IsDeterministic` — exactly the [cao-white-lassiter-2025]
    requirement that SUF be a real probability. -/
noncomputable example : ENNReal :=
  probSufficiency (model p h) Valuation.empty .cause true .effect true

end ProbabilisticExample

end CaoWhiteLassiter2025
