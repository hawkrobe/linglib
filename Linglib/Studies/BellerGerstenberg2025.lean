import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype
import Linglib.Pragmatics.RSA.Uniform
import Linglib.Semantics.Causation.SEM.Bool
import Linglib.Semantics.Causation.SEM.Counterfactual
import Linglib.Semantics.Alternatives.Lexical

/-!
# Beller and Gerstenberg 2025: causal expressions from counterfactual simulation

This file formalizes Beller and Gerstenberg's counterfactual simulation model of causal
language. A causal knowledge module computes three aspects of causation — whether-causation
(counterfactual necessity), how-causation (a difference to the fine-grained outcome), and
sufficient-causation (whether-causation with the alternative causes removed); a semantics
module defines "affected", "enabled", "caused", and "made no difference" as logical
combinations of the aspects; and a pragmatics module chooses among the true expressions by
informativity, as a rational speech act speaker and listener. We state the Boolean core of
the semantics with its specificity hierarchy, reproduce the paper's four sample scenarios
with their literal-listener and speaker distributions, derive the speaker's preference for
the most informative true expression and the listener's scalar implicature at every positive
rationality, and ground the aspects in the substrate's counterfactual predicates on a
structural causal model.

## Main definitions

* `CausalWorld`: an aspect profile — whether-, how-, and sufficient-causation.
* `expressionMeaning`: the Boolean core of the four expressions' semantics; `gradedMeaning`
  adds the softened negation of how-causation in "made no difference".
* `Scenario`, `Scenario.aspects`, `sem`: the four sample scenarios and each expression's
  extension over them.
* `CausalWorld.ofModel`: the aspect profile of a cause–effect pair in a deterministic
  structural model, read off `Causation.SEM.whetherCause`, `hasDirectLaw`, and
  `sufficientCause`.

## Main results

* `caused_implies_enabled`, `enabled_implies_affected`, `madeNoDifference_iff_not_affected`:
  the specificity hierarchy behind the Horn scale `causalScale`.
* `speaker_s1`, `speaker_s2`: the paper's first-level speaker distributions, exactly.
* `speaker_prefers_caused`, `speaker_prefers_enabled`: the speaker prefers the most
  informative true expression at every positive rationality.
* `listener_enabled_implicature`: hearing "enabled", the pragmatic listener favours the
  scenario where "caused" is false.
* `listener_affected_prefers_howOnly`: the model's prediction for "affected", which the
  listener experiment did not bear out.
* `launch_ofModel`: Michottean launching, as a two-variable structural model, computes the
  profile of the first scenario.

The speaker here is the paper's first-level pragmatic speaker over Boolean aspects; the
fitted model uses a second-level speaker over graded aspects from noisy simulations, with
fitted noise, softening, and optimality parameters (θ, σ, ν, λ).

## References

* [beller-gerstenberg-2025]
* [gerstenberg-goodman-lagnado-tenenbaum-2021]: the counterfactual simulation model.
* [frank-goodman-2012]: rational speech act pragmatics.
* [halpern-pearl-2005]: the event-matching constraint on sufficient-causation.
-/

namespace BellerGerstenberg2025

open Causation Causation.SEM Alternatives RSA
open scoped ENNReal

/-! ### Expressions and aspects -/

/-- The four causal expressions offered to participants. -/
inductive CausalExpression
  | caused
  | enabled
  | affected
  | madeNoDifference
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty CausalExpression := ⟨.caused⟩
instance : MeasurableSpace CausalExpression := ⊤
instance : DiscreteMeasurableSpace CausalExpression := ⟨fun _ => trivial⟩

/-- An aspect profile: whether-causation `W` (1), how-causation `H` (2), and
sufficient-causation `S` (3), at Boolean values. -/
structure CausalWorld where
  whether : Bool
  how : Bool
  sufficient : Bool
  deriving DecidableEq, Repr

/-! ### Semantics -/

/-- The Boolean core of the semantics: `affected = W ∨ H ∨ S` (4), `enabled = W ∨ S` (5),
`caused = H ∧ (W ∨ S)` (6) without the softened movement and uniqueness conjuncts, and
`made no difference = ¬W ∧ ¬H ∧ ¬S` (7) with a hard negation. -/
def expressionMeaning (cw : CausalWorld) : CausalExpression → Prop
  | .affected => cw.whether ∨ cw.how ∨ cw.sufficient
  | .enabled => cw.whether ∨ cw.sufficient
  | .caused => cw.how ∧ (cw.whether ∨ cw.sufficient)
  | .madeNoDifference => ¬ cw.whether ∧ ¬ cw.how ∧ ¬ cw.sufficient

instance (cw : CausalWorld) : ∀ u, Decidable (expressionMeaning cw u)
  | .affected => inferInstanceAs (Decidable (_ ∨ _))
  | .enabled => inferInstanceAs (Decidable (_ ∨ _))
  | .caused => inferInstanceAs (Decidable (_ ∧ _))
  | .madeNoDifference => inferInstanceAs (Decidable (_ ∧ _))

theorem caused_implies_enabled (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .enabled :=
  And.right

theorem enabled_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .enabled → expressionMeaning cw .affected :=
  Or.imp_right Or.inr

theorem caused_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .affected :=
  enabled_implies_affected cw ∘ caused_implies_enabled cw

/-- "Made no difference" is the negation of "affected". -/
theorem madeNoDifference_iff_not_affected (cw : CausalWorld) :
    expressionMeaning cw .madeNoDifference ↔ ¬ expressionMeaning cw .affected := by
  simp only [expressionMeaning, not_or]

/-- The semantics with the softened negation of how-causation in "made no difference": a
how-cause that is neither a whether- nor a sufficient-cause satisfies it to degree `ν` (7). -/
def gradedMeaning (cw : CausalWorld) (ν : ℚ) : CausalExpression → ℚ
  | .affected => if cw.whether || cw.how || cw.sufficient then 1 else 0
  | .enabled => if cw.whether || cw.sufficient then 1 else 0
  | .caused => if cw.how && (cw.whether || cw.sufficient) then 1 else 0
  | .madeNoDifference =>
    (if cw.whether then 0 else 1) * (if cw.how then ν else 1) * (if cw.sufficient then 0 else 1)

/-- Without softening, the graded semantics is the indicator of the Boolean core. -/
theorem gradedMeaning_zero (cw : CausalWorld) (u : CausalExpression) :
    gradedMeaning cw 0 u = if expressionMeaning cw u then 1 else 0 := by
  obtain ⟨w, h, s⟩ := cw
  cases u <;> cases w <;> cases h <;> cases s <;> simp [gradedMeaning, expressionMeaning]

/-! ### The sample scenarios -/

/-- The paper's four sample scenarios: Michottean launching, double prevention, a how-cause
pushing a ball already headed for the gate, and no interaction. -/
inductive Scenario
  | s1
  | s2
  | s3
  | s4
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Scenario := ⟨.s1⟩
instance : MeasurableSpace Scenario := ⊤
instance : DiscreteMeasurableSpace Scenario := ⟨fun _ => trivial⟩

/-- The aspect values of the sample scenarios (Table 1a). -/
def Scenario.aspects : Scenario → CausalWorld
  | .s1 => ⟨true, true, true⟩
  | .s2 => ⟨true, false, true⟩
  | .s3 => ⟨false, true, false⟩
  | .s4 => ⟨false, false, false⟩

/-- Each expression's extension over the sample scenarios under the Boolean core. -/
def sem (u : CausalExpression) : Finset Scenario :=
  Finset.univ.filter fun s => expressionMeaning s.aspects u

theorem expressible : ∀ s, ∃ u, s ∈ sem u := by decide

-- Table 1b, Boolean columns: the extensions.
example :
    sem .caused = {.s1} ∧ sem .enabled = {.s1, .s2} ∧ sem .affected = {.s1, .s2, .s3} ∧
      sem .madeNoDifference = {.s4} := by
  decide

-- Table 1b, the softened cell: at ν = 0.2 the how-cause-only scenario weakly satisfies
-- "made no difference".
example : gradedMeaning Scenario.s3.aspects (1 / 5) .madeNoDifference = 1 / 5 := by
  norm_num [gradedMeaning, Scenario.aspects]

/-- The literal listener is uniform on each expression's extension (Table 1c): hearing
"enabled", the two enabling scenarios are equally likely. -/
theorem literal_enabled :
    uniformListener sem .enabled {.s1} = 2⁻¹ ∧ uniformListener sem .enabled {.s3} = 0 := by
  rw [uniformListener_apply_singleton, uniformListener_apply_singleton, if_pos (by decide),
    if_neg (by decide), show (sem .enabled).card = 2 from by decide]
  norm_num

/-- The first-level speaker at Michottean launching (Table 1d): "caused" 6/11, "enabled"
3/11, "affected" 2/11. -/
theorem speaker_s1 :
    (uniformSpeaker sem 1 .s1).real {.caused} = 6 / 11 ∧
      (uniformSpeaker sem 1 .s1).real {.enabled} = 3 / 11 ∧
      (uniformSpeaker sem 1 .s1).real {.affected} = 2 / 11 := by
  have h := fun c => uniformSpeaker_real_singleton_divPowSum sem (k := 1) (D := 6)
    (t := .s1) (by decide +kernel) c
  simp only [Nat.cast_one] at h
  rw [h, h, h, show (profile sem .s1).divPowSum 6 1 = 11 from by decide +kernel,
    if_pos (by decide), if_pos (by decide), if_pos (by decide),
    show (sem .caused).card = 1 from by decide, show (sem .enabled).card = 2 from by decide,
    show (sem .affected).card = 3 from by decide]
  norm_num

/-- The first-level speaker at double prevention (Table 1d): "enabled" 3/5, "affected" 2/5,
"caused" 0. -/
theorem speaker_s2 :
    (uniformSpeaker sem 1 .s2).real {.enabled} = 3 / 5 ∧
      (uniformSpeaker sem 1 .s2).real {.affected} = 2 / 5 ∧
      (uniformSpeaker sem 1 .s2).real {.caused} = 0 := by
  have h := fun c => uniformSpeaker_real_singleton_divPowSum sem (k := 1) (D := 6)
    (t := .s2) (by decide +kernel) c
  simp only [Nat.cast_one] at h
  rw [h, h, h, show (profile sem .s2).divPowSum 6 1 = 5 from by decide +kernel,
    if_pos (by decide), if_pos (by decide), if_neg (by decide),
    show (sem .enabled).card = 2 from by decide, show (sem .affected).card = 3 from by decide]
  norm_num

/-! ### Informativity and implicature -/

/-- At Michottean launching the speaker prefers "caused" to "enabled" and "enabled" to
"affected", at every positive rationality. -/
theorem speaker_prefers_caused {α : ℝ} (hα : 0 < α) :
    (uniformSpeaker sem α .s1).real {.enabled} < (uniformSpeaker sem α .s1).real {.caused} ∧
      (uniformSpeaker sem α .s1).real {.affected} <
        (uniformSpeaker sem α .s1).real {.enabled} :=
  ⟨uniformSpeaker_real_singleton_lt_of_card_lt sem hα (by decide) (by decide) (by decide),
    uniformSpeaker_real_singleton_lt_of_card_lt sem hα (by decide) (by decide) (by decide)⟩

/-- At double prevention, where "caused" is false, the speaker prefers "enabled" to
"affected" at every positive rationality. -/
theorem speaker_prefers_enabled {α : ℝ} (hα : 0 < α) :
    (uniformSpeaker sem α .s2).real {.affected} < (uniformSpeaker sem α .s2).real {.enabled} :=
  uniformSpeaker_real_singleton_lt_of_card_lt sem hα (by decide) (by decide) (by decide)

/-- Hearing "caused", the pragmatic listener favours Michottean launching over double
prevention, where the expression is false. -/
theorem listener_caused_identifies {α : ℝ} (hα : 0 < α) :
    (uniformJointListener sem id α .caused).fst.real {.s2}
      < (uniformJointListener sem id α .caused).fst.real {.s1} :=
  uniformJointListener_fst_real_lt_of_prodMul_strictDominates sem id expressible hα
    (by decide +kernel)

/-- Hearing "enabled", the pragmatic listener favours double prevention over Michottean
launching, where the speaker would have said "caused": the scalar implicature. -/
theorem listener_enabled_implicature {α : ℝ} (hα : 0 < α) :
    (uniformJointListener sem id α .enabled).fst.real {.s1}
      < (uniformJointListener sem id α .enabled).fst.real {.s2} :=
  uniformJointListener_fst_real_lt_of_prodMul_strictDominates sem id expressible hα
    (by decide +kernel)

/-- Hearing "affected", the pragmatic listener favours the how-cause-only scenario, where
no stronger expression is true, over Michottean launching. The listener experiment found
the opposite preference for the analogous pair, the case the paper singles out as the
model's failure. -/
theorem listener_affected_prefers_howOnly {α : ℝ} (hα : 0 < α) :
    (uniformJointListener sem id α .affected).fst.real {.s1}
      < (uniformJointListener sem id α .affected).fst.real {.s3} :=
  uniformJointListener_fst_real_lt_of_prodMul_strictDominates sem id expressible hα
    (by decide +kernel)

/-- Hearing "made no difference", the pragmatic listener favours the no-interaction scenario
over the how-cause-only one. -/
theorem listener_noDifference_identifies {α : ℝ} (hα : 0 < α) :
    (uniformJointListener sem id α .madeNoDifference).fst.real {.s3}
      < (uniformJointListener sem id α .madeNoDifference).fst.real {.s4} :=
  uniformJointListener_fst_real_lt_of_prodMul_strictDominates sem id expressible hα
    (by decide +kernel)

/-! ### The Horn scale -/

/-- The scale ⟨affected, enabled, caused⟩, weakest to strongest; its order is the
specificity hierarchy `caused_implies_enabled`, `enabled_implies_affected`. -/
def causalScale : HornScale CausalExpression :=
  ⟨[.affected, .enabled, .caused]⟩

theorem affected_alternatives :
    strongerAlternatives causalScale .affected = [.enabled, .caused] := by
  decide

theorem enabled_alternatives : strongerAlternatives causalScale .enabled = [.caused] := by
  decide

/-! ### Aspects from a structural model -/

section Structural

open Causation.Mechanism

/-- The variables of a two-event structural model: the candidate cause and the outcome. -/
inductive Var
  | cause
  | effect
  deriving DecidableEq, Fintype, Repr

/-- Michottean launching: the outcome depends on the candidate cause alone. -/
def launchGraph : CausalGraph Var :=
  ⟨fun | .cause => ∅ | .effect => {.cause}⟩

/-- The launching model: the outcome takes the candidate cause's value. -/
noncomputable def launch : BoolSEM Var :=
  { graph := launchGraph
    mech := fun v => match v with
      | .cause => const (G := launchGraph) false
      | .effect => deterministic (fun ρ => ρ ⟨.cause, by simp [launchGraph]⟩) }

noncomputable instance : SEM.IsDeterministic launch where
  mech_det v := match v with
    | .cause => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .effect => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- The ranking certificate of `launchGraph`. -/
def launchRanking : CausalGraph.Ranking launchGraph :=
  ⟨fun | .cause => 0 | .effect => 1, fun {u v} h => by revert h; cases u <;> cases v <;> decide⟩

instance : CausalGraph.IsDAG launchGraph := launchRanking.isDAG

noncomputable instance : CausalGraph.IsDAG launch.graph :=
  inferInstanceAs (CausalGraph.IsDAG launchGraph)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The aspect profile of `cause → effect` in a deterministic model: `W` is `whetherCause`
(1) at the observed valuation, `H` is a direct law, and `S` is `sufficientCause` (3) at the
valuation with the alternative causes removed. -/
noncomputable def CausalWorld.ofModel (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (observed alternativesRemoved : Valuation fun _ : V => Bool)
    (cause effect : V) : CausalWorld :=
  { whether := decide (whetherCause M observed cause false effect true = 1)
    how := decide (BoolSEM.hasDirectLaw M cause effect)
    sufficient := decide (sufficientCause M alternativesRemoved cause false effect true = 1) }

set_option maxRecDepth 100000 in
/-- Michottean launching computes the profile of the first scenario: with no alternative
causes, sufficient-causation reduces to whether-causation. -/
theorem launch_ofModel :
    CausalWorld.ofModel launch Valuation.empty Valuation.empty .cause .effect =
      Scenario.s1.aspects := by
  have hW : whetherCause launch Valuation.empty .cause false .effect true = 1 := by
    rw [whetherCause_eq_indicator_of_deterministic, if_neg]
    rw [developDet_hasValue_iff]
    intro h
    have hfalse := developDetVtx_eq_of_developDetVtx?_eq_some (M := launch)
      (s := cfSeed launch Valuation.empty .cause false) (v := .effect) (x := false) (by
        rw [cfSeed_empty, ← developDetVtxFuel_eq_developDetVtx? launch launchRanking _
          (show launchRanking .effect < 2 by decide)]
        decide)
    exact Bool.noConfusion (hfalse.symm.trans h)
  have hDir : BoolSEM.hasDirectLaw launch .cause .effect := by decide
  unfold CausalWorld.ofModel sufficientCause
  rw [decide_eq_true hW, decide_eq_true hDir]
  rfl

end Structural

end BellerGerstenberg2025
