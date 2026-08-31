import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Card
import Mathlib.Probability.Distributions.Uniform
import Linglib.Core.Probability.Constructions
import Linglib.Data.Examples.CaoWhiteLassiter2025
import Linglib.Semantics.Causation.Interpretation
import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Cao, White and Lassiter 2025: graded causative verb semantics

This file formalizes the graded-causative analysis of English *cause*, *make*, and *force* in
[cao-white-lassiter-2025]. Where [nadathur-lauer-2020] give *make* and *force* a single
categorical truth condition, this account measures three quantities in one structural causal
model of tic-tac-toe — Pearl's probability of sufficiency ([pearl-2019],
`Causation.SEM.probSufficiency`), a simplified [halpern-kleiman-weiner-2018] degree of intention,
and the number of alternative actions open to the causee — and finds that no one of them
determines which verb speakers accept, each verb instead having its own set of reliable
interactions. The model apparatus is shared with [cao-geiger-kreiss-icard-gerstenberg-2023]:
models are time-indexed (`CausalGraph.TimeIndex`) and their agents play a soft-optimality policy.

The paper's in-text judgments, its examples (3)–(11), are rows in
`Data/Examples/CaoWhiteLassiter2025.json`; the regression estimates stay in prose.

## Main definitions

* `softOptimalPolicy` — the move distribution of a player of skill `ρ`
* `altCount`, `intentionDegree`, `modelIntention` — the ALT and INT measures
* `deterministicSuf` — the {0,1} collapse of SUF in the deterministic limit

## Main results

* `softOptimalPolicy_zero`, `softOptimalPolicy_one` — the infant and the professional
* `intentionDegree_eq_one_of_altCount_eq_zero` — an action with no alternative comes out
  maximally intentional, so the simplified INT drops the alternative-possibilities condition
  ([frankfurt-1969], [halpern-kleiman-weiner-2018]) and ALT carries it instead
* `probSufficiency_empty_eq_deterministicSuf` — at the vacuous context Pearl's SUF is
  [nadathur-lauer-2020]'s categorical causal sufficiency
* `probSufficiency_empty_eq_one_of_make` — the categorical *make* semantics is strictly stronger
  than maximal graded SUF
* `make_semantics_eq_force`, `judgment_differs_make_force` — the force-dynamic semantics does not
  distinguish the two verbs the paper's (8) separates

## References

* [cao-white-lassiter-2025]
* [pearl-2019]
* [halpern-kleiman-weiner-2018]
* [frankfurt-1969]
* [nadathur-lauer-2020]
* [cao-geiger-kreiss-icard-gerstenberg-2023]
-/

namespace CaoWhiteLassiter2025

open Causation Causation.Mechanism Causation.SEM Features
open scoped ENNReal NNReal

/-! ### Soft-optimality policy

The paper's mechanism for agent moves (§2.1.1). The highest-utility move — minimax over the game
tree, with terminal utility `Winner × (EmptySpace + 1)` — is taken with probability `ρ + (1−ρ)/n`
and every other available move with `(1−ρ)/n`, for `n` the number of empty spaces. The skill
parameter interpolates between a uniformly random player ("assume that the players are infants"),
under which the paper's worked SUF contrast between two board states collapses, and a
deterministic professional. -/

section
variable {A : Type*} [Fintype A] [Nonempty A] (best : A) (ρ : ℝ≥0) (hρ : ρ ≤ 1)

/-- The move distribution of a player of skill `ρ`: the highest-utility
    move `best` with probability `ρ`, otherwise a uniform random move. -/
noncomputable def softOptimalPolicy : PMF A :=
  PMF.mix ρ hρ (PMF.uniformOfFintype A) (PMF.pure best)

@[simp] theorem softOptimalPolicy_apply_best :
    softOptimalPolicy best ρ hρ best = ρ + (1 - ρ : ℝ≥0) / Fintype.card A := by
  simp [softOptimalPolicy, div_eq_mul_inv, add_comm]

@[simp] theorem softOptimalPolicy_apply_of_ne {a : A} (h : a ≠ best) :
    softOptimalPolicy best ρ hρ a = (1 - ρ : ℝ≥0) / Fintype.card A := by
  simp [softOptimalPolicy, PMF.pure_apply_of_ne _ _ h, div_eq_mul_inv]

theorem softOptimalPolicy_zero :
    softOptimalPolicy best 0 zero_le_one = PMF.uniformOfFintype A := PMF.mix_zero _ _

theorem softOptimalPolicy_one :
    softOptimalPolicy best 1 le_rfl = PMF.pure best := PMF.mix_one _ _

end

/-! ### The ALT measure

ALT (§2.2) counts the alternative actions available to the causee, excluding the one actually
taken — `ALT(Y₁) = 5` at the paper's fig. 2a board state. `ALT = 0` is the Frankfurt-style
could-not-have-done-otherwise configuration. -/

section
variable {A : Type*} [Fintype A] (p : PMF A) (taken : A)

/-- The number of alternative actions available to the causee: the
    support of the action distribution, less the action taken. -/
noncomputable def altCount : ℕ :=
  (p.support \ {taken}).ncard

/-- The causee had no alternative exactly when every other action had probability zero. -/
theorem altCount_eq_zero_iff : altCount p taken = 0 ↔ ∀ a ≠ taken, p a = 0 := by
  rw [altCount, Set.ncard_eq_zero (Set.toFinite _), Set.sdiff_eq_empty,
    Set.subset_singleton_iff]
  exact forall_congr' fun b => not_imp_comm

/-! ### The INT measure

The paper's §2.3 displayed equation, a simplified [halpern-kleiman-weiner-2018] degree of
intention:

`INT(a) = Pr(A = a ∧ G) · u′(a) / Σ_{a′} Pr(A = a′ ∧ G) · u′(a′)`

"the probability that an action performed in a state will result in the desired outcome,
normalized by the probability of all alternative actions that would have resulted in the same
outcome", each term weighted by exponentiated utility `u′ = eᵘ`, the exponential serving only to
make the weights strictly positive. Here `pr a′` is the joint probability that the agent takes
`a′` and the goal results, and the weight is abstracted to any `w : A → ℝ≥0`; `modelIntention`
instantiates `pr` over a `SEM`.

The simplification costs the principle it is motivated by: [halpern-kleiman-weiner-2018] hold,
after [frankfurt-1969], that an action an agent could not have avoided is never intentional,
while under this measure such an action is maximally intentional, its sole goal-conducive
alternative being itself. It is ALT rather than INT that registers the paper's *made*/*forced*
contrast in (8). -/

variable (pr : A → ℝ≥0∞) (w : A → ℝ≥0) (a : A)

/-- The goal-weighted share of action `a` among all goal-conducive
    alternatives. -/
noncomputable def intentionDegree : ℝ≥0∞ :=
  (pr a * w a) / ∑ a', pr a' * w a'

/-- INT is a share, so it never exceeds 1. -/
theorem intentionDegree_le_one : intentionDegree pr w a ≤ 1 :=
  ENNReal.div_le_of_le_mul <| by
    simpa using Finset.single_le_sum (f := fun a' => pr a' * w a') (fun _ _ => zero_le)
      (Finset.mem_univ a)

/-- With nonzero finite total mass, INT is mathlib's `PMF.normalize` of
    the goal-weighted masses, evaluated at the taken action — the
    `PMF.reweight`/`PMF.posterior` family of `Core/Probability/Posterior`. -/
theorem intentionDegree_eq_normalize (h0 : (∑' a', pr a' * w a') ≠ 0)
    (htop : (∑' a', pr a' * w a') ≠ ∞) :
    intentionDegree pr w a = PMF.normalize (fun a' => pr a' * w a') h0 htop a := by
  rw [intentionDegree, PMF.normalize_apply, div_eq_mul_inv, tsum_fintype]

/-- An action that is the only goal-conducive one carries the whole normalized weight. -/
theorem intentionDegree_eq_one_of_no_alternatives
    (h : ∀ a ≠ taken, pr a = 0) (h0 : pr taken ≠ 0) (hw : w taken ≠ 0)
    (htop : pr taken ≠ ∞) :
    intentionDegree pr w taken = 1 := by
  rw [intentionDegree, Finset.sum_eq_single_of_mem taken (Finset.mem_univ taken)
    fun a _ ha => by rw [h a ha, zero_mul]]
  exact ENNReal.div_self (mul_ne_zero h0 (ENNReal.coe_ne_zero.mpr hw))
    (ENNReal.mul_ne_top htop ENNReal.coe_ne_top)

/-- An agent who could not have done otherwise comes out maximally intentional: the simplified
INT does not carry the alternative-possibilities condition, and ALT is what separates *made* from
*forced*. -/
theorem intentionDegree_eq_one_of_altCount_eq_zero
    (hle : pr ≤ ⇑p) (h : altCount p taken = 0) (h0 : pr taken ≠ 0) (hw : w taken ≠ 0) :
    intentionDegree pr w taken = 1 :=
  intentionDegree_eq_one_of_no_alternatives taken pr w
    (fun a ha => le_zero_iff.mp ((altCount_eq_zero_iff p taken).mp h a ha ▸ hle a))
    h0 hw (ne_top_of_le_ne_top (p.apply_ne_top taken) (hle taken))

end

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

/-! ### Deterministic limit

In the deterministic limit SUF collapses to a {0,1} indicator
(`Causation.SEM.probSufficiency_eq_indicator_of_deterministic`). At the vacuous context this is
[nadathur-lauer-2020]'s categorical causal sufficiency: with nothing observed, Pearl's
counterfactual degenerates to the bare interventional development of `cause := true`. -/

section
variable {V : Type*} [Fintype V] [DecidableEq V] (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
  [IsDeterministic M]

/-- The {0,1} indicator of categorical causal sufficiency
    (`causallySufficient`). -/
noncomputable def deterministicSuf (background : Valuation (fun _ : V => Bool))
    (cause effect : V) : ENNReal :=
  if BoolSEM.causallySufficient M background cause effect then 1 else 0

variable (c e : V)

theorem probSufficiency_empty_eq_deterministicSuf :
    BoolSEM.probSufficiency M Valuation.empty c e = deterministicSuf M Valuation.empty c e := by
  unfold BoolSEM.probSufficiency
  rw [probSufficiency_eq_indicator_of_deterministic, cfSeed_empty]
  unfold deterministicSuf
  congr 1

/-- The hub denotation for *make* entails maximal SUF at the vacuous
    context — whenever `Causative.toSemantics M .make` holds (both
    clauses of [nadathur-lauer-2020]'s definition (23), over the strict
    development), Pearl's probability of sufficiency is 1. The converse
    fails, since the eager development fills undetermined exogenous
    vertices from their mechanisms; the categorical *make* semantics is
    strictly stronger than maximal graded SUF. -/
theorem probSufficiency_empty_eq_one_of_make
    (h : Causative.toSemantics M .make Valuation.empty c true e true) :
    BoolSEM.probSufficiency M Valuation.empty c e = 1 := by
  rw [probSufficiency_empty_eq_deterministicSuf]
  unfold deterministicSuf
  exact if_pos (causallySufficient_of_causallyEntails h.2)

end

/-! ### The paper's judgment data

The in-text contrasts are rows in `Data.Examples.CaoWhiteLassiter2025`: the
non-interchangeability triplets (3)–(4), the gym gradability triplets (5)–(7), the
could-have-done-otherwise pair (8), the intent-denial continuations (9)–(10), and the
*make*/*let* sufficiency pair (11). -/

/-- The force-dynamic dispatch gives *make* and *force* the same truth conditions, since both
assert causal sufficiency ([nadathur-lauer-2020]). -/
theorem make_semantics_eq_force
    {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V] [DecidableValuation α]
    [∀ v, Fintype (α v)] (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M] :
    Causative.toSemantics M .make = Causative.toSemantics M .force := rfl

/-- The paper's (8) separates them anyway: in one frame with a could-have-done-otherwise
continuation, *made* tolerates the continuation and *forced* resists it. What the shared
semantics misses is the causee's alternatives, which ALT measures. -/
theorem judgment_differs_make_force :
    Examples.cwl2025_ex8a.judgment ≠ Examples.cwl2025_ex8b.judgment := by decide

/-- The gym triplets (5)–(7) grade the stronger verbs against a constant *cause*: the same three
causing events leave *caused* acceptable throughout while *forced* switches, which is why the
account measures the causal relation rather than classifying it. -/
theorem gym_grades_stronger_verbs :
    Examples.cwl2025_ex5a.judgment = Examples.cwl2025_ex6a.judgment ∧
      Examples.cwl2025_ex6a.judgment = Examples.cwl2025_ex7a.judgment ∧
      Examples.cwl2025_ex5c.judgment ≠ Examples.cwl2025_ex7c.judgment := by decide

/-! ### A probabilistic model

A 2-vertex SEM whose `effect` mechanism is a `p`-weighted coin. `probSufficiency` is defined for
it with no determinism hypothesis, which is what makes SUF the graded measure the paper needs
rather than the indicator of the previous section. -/

namespace ProbabilisticExample

open scoped NNReal

/-- A 2-vertex SEM with root `cause` and child `effect`. -/
inductive V | cause | effect
  deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨fun | .cause => ∅ | .effect => {.cause}⟩

variable (p : ℝ≥0) (h : p ≤ 1)

/-- The mechanism for `effect`: ignore the parent and return `true` with probability `p`. -/
noncomputable def effectMech :
    Mechanism graph (fun _ => Bool) .effect :=
  ⟨fun _ => PMF.mix p h (PMF.pure false) (PMF.pure true)⟩

/-- The model: a `cause` vertex fixed to `false` and an `effect` vertex given by the coin. -/
noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .cause => const (G := graph) false
      | .effect => effectMech p h }

/-- The graph is time-indexed in the sense of the paper's definition 1, with `cause` at step 0
and `effect` at step 1. -/
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

/-- The model is not deterministic for `p` strictly between 0 and 1, so `probSufficiency` takes
it outside the deterministic limit — as the paper's SUF, a genuine probability, requires. -/
theorem isEmpty_isDeterministic (h0 : p ≠ 0) (h1 : p ≠ 1) :
    IsEmpty (SEM.IsDeterministic (model p h)) := by
  refine ⟨fun hd => ?_⟩
  obtain ⟨hdet⟩ := hd
  obtain ⟨f, hf⟩ := hdet .effect
  have hb := hf fun _ => false
  cases hfv : f (fun _ => false) <;> rw [hfv] at hb
  · exact h0 (by simpa [model, effectMech] using DFunLike.congr_fun hb true)
  · exact h1 (by simpa [model, effectMech] using DFunLike.congr_fun hb true)

end ProbabilisticExample

end CaoWhiteLassiter2025
