module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.InformationTheory.KullbackLeibler.Finite
public import Linglib.Core.InformationTheory.Entropy

/-!
# Tessler, Tenenbaum and Goodman (2022): Logic, Probability, and Pragmatics in Syllogistic Reasoning

This file formalizes [tessler-tenenbaum-goodman-2022]'s Rational Speech Act models of
syllogistic reasoning. A reasoner first acts as a literal listener, conditioning a prior over
Venn states on the truth-conditional meanings of the two premises, (1)–(2), then as a speaker
choosing among nine conclusions: the eight quantified relations between the end terms and
*nothing follows*, formalized as the vacuous utterance true in every state. Three speakers are
compared. The literal speaker (3) scores a conclusion by its posterior probability of truth;
the state-communication speaker (4) by the expected log-probability that a naive literal
listener, who hears the conclusion alone, assigns to the reasoner's state; the belief-alignment
speaker (6) by the negative Kullback–Leibler divergence from the reasoner's posterior to that
naive listener's. A figural preference (section 3.1.1) weights conclusions whose subject term
is the unique end term in subject position in the premises.

The speakers are score speakers of `Linglib.Pragmatics.RSA.Basic`, so the paper's
qualitative claims are theorems over the parameters. The state-communication and
belief-alignment utilities differ by the entropy of the reasoner's posterior, which does not
depend on the conclusion, so under the printed equations the two speakers are one kernel,
`stateCommunication_eq_beliefAlignment`. Without semantic noise the belief-alignment speaker
must say *nothing follows* to a logically invalid syllogism, since every quantified conclusion
is false at some state the reasoner entertains and the naive listener's posterior then fails to
dominate the reasoner's, `beliefAlignment_nvc_of_invalid`; for a valid conclusion its score is
the log ratio of the conclusion's extension to the premises', so the speaker prefers the
conclusion true in fewer states, `beliefAlignment_real_lt_iff_of_valid`, which for Barbara is
*all* over *some* and over *nothing follows*, `barbara_prefers_allAC` (Figure 8). The literal
speaker can never prefer a quantified conclusion to *nothing follows*, `literalSpeaker_le_nvc`.

## Implementation notes

The paper takes existential import on *all* alone (section 2.1): `tesslerAll` conjoins the
modern `syllAll` with the existence of a populated restrictor region, and the other three
forms are the modern ones, the generalized quantifiers over the populated regions of a
three-circle Venn diagram. Semantic noise follows the paper's
prose and released model code: with probability `φ` the listener disregards an utterance, so
a false utterance carries weight `φ` and a true one weight `1`, and the two premises are
disregarded independently. The released code implements the literal and state-communication
speakers with the rationality applied to the posterior probability rather than inside the
exponential as printed, so the fitted state-communication model is not the printed (4) and
does not coincide with belief alignment; the file formalizes the printed equations. The
Bayesian data analysis over the Ragni et al. data set, the fitted parameter values, and the
comparison with mReasoner and the Probability Heuristics Model are not formalized.

## References

* [tessler-tenenbaum-goodman-2022]
* [frank-goodman-2012]
* [goodman-stuhlmuller-2013]
* [chater-oaksford-1999]
* [degen-etal-2020]
-/

@[expose] public section

namespace TesslerTenenbaumGoodman2022

open MeasureTheory ProbabilityTheory InformationTheory RSA
open Quantifier.GQ (every some no subalternation_a_i)
open scoped ENNReal

/-! ### Syllogisms and Venn states -/

/-- The four Aristotelian quantifiers A, I, O and E. -/
inductive AristQuant where
  | all
  | some
  | someNot
  | no
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The seven nonempty regions of a three-circle Venn diagram over the terms A, B and C. -/
inductive Region where
  | A
  | B
  | C
  | AB
  | AC
  | BC
  | ABC
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A Venn state records which regions are populated. -/
abbrev VennState := Region → Bool

/-- The regions inside the circle A. -/
def hasA : Region → Bool
  | .A | .AB | .AC | .ABC => true
  | _ => false

/-- The regions inside the circle B. -/
def hasB : Region → Bool
  | .B | .AB | .BC | .ABC => true
  | _ => false

/-- The regions inside the circle C. -/
def hasC : Region → Bool
  | .C | .AC | .BC | .ABC => true
  | _ => false

/-- A syllogism is two quantified premises sharing the middle term B, and the term orders of
the premises fix the figure. -/
structure Syllogism where
  q1 : AristQuant
  /-- The first premise is `q1 A B` rather than `q1 B A`. -/
  order1AB : Bool
  q2 : AristQuant
  /-- The second premise is `q2 B C` rather than `q2 C B`. -/
  order2BC : Bool
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The nine conclusions are the eight quantified relations between the end terms and
*nothing follows*. -/
inductive Conclusion where
  | allAC
  | allCA
  | someAC
  | someCA
  | someNotAC
  | someNotCA
  | noAC
  | noCA
  | nvc
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Whether a conclusion has A as its subject. -/
def Conclusion.isAC : Conclusion → Bool
  | .allAC | .someAC | .someNotAC | .noAC => true
  | _ => false

instance {R S : Region → Prop} [DecidablePred R] [DecidablePred S] :
    Decidable (every R S) :=
  inferInstanceAs (Decidable (∀ r, R r → S r))

instance {R S : Region → Prop} [DecidablePred R] [DecidablePred S] :
    Decidable (Quantifier.GQ.some R S) :=
  inferInstanceAs (Decidable (∃ r, R r ∧ S r))

instance {R S : Region → Prop} [DecidablePred R] [DecidablePred S] :
    Decidable (no R S) :=
  inferInstanceAs (Decidable (∀ r, R r → ¬ S r))

/-- *All Xs are Ys* on the modern reading, *every* over the populated X-regions. -/
def syllAll (s : VennState) (X Y : Region → Bool) : Bool :=
  decide (every (fun r ↦ s r ∧ X r) fun r ↦ Y r)

/-- *Some Xs are Ys*, *some* over the populated X-regions. -/
def syllSome (s : VennState) (X Y : Region → Bool) : Bool :=
  decide (Quantifier.GQ.some (fun r ↦ s r ∧ X r) fun r ↦ Y r)

/-- *Some Xs are not Ys*, *some* over the populated X-regions with the complement scope. -/
def syllSomeNot (s : VennState) (X Y : Region → Bool) : Bool :=
  decide (Quantifier.GQ.some (fun r ↦ s r ∧ X r) fun r ↦ ¬ Y r)

/-- *No Xs are Ys* on the modern reading, *no* over the populated X-regions. -/
def syllNone (s : VennState) (X Y : Region → Bool) : Bool :=
  decide (no (fun r ↦ s r ∧ X r) fun r ↦ Y r)

/-- *All Xs are Ys* entails *some Xs are Ys* when some populated region is an X-region. -/
theorem syllAll_imp_syllSome (s : VennState) (X Y : Region → Bool)
    (hExists : ∃ r, s r = true ∧ X r = true) (h : syllAll s X Y = true) :
    syllSome s X Y = true := by
  simp only [syllAll, syllSome, decide_eq_true_eq] at h ⊢
  exact subalternation_a_i _ _ hExists h

/-- Barbara, *all A are B* and *all B are C*, the paradigm valid syllogism. -/
def barbara : Syllogism := ⟨.all, true, .all, true⟩

/-- *All A are B* and *all C are B*, the paradigm invalid syllogism. -/
def allAB_allCB : Syllogism := ⟨.all, true, .all, false⟩

/-- Barbara is valid, since its premises entail *all A are C*. -/
theorem barbara_valid (s : VennState) (h1 : syllAll s hasA hasB = true)
    (h2 : syllAll s hasB hasC = true) : syllAll s hasA hasC = true := by
  simp only [syllAll, decide_eq_true_eq] at h1 h2 ⊢
  exact fun r ⟨hs, hA⟩ ↦ h2 r ⟨hs, h1 r ⟨hs, hA⟩⟩

/-- The state populating only the regions AB and BC. -/
def state_AB_BC : VennState
  | .AB | .BC => true
  | _ => false

/-- The state populating only the region ABC. -/
def state_ABC : VennState
  | .ABC => true
  | _ => false

/-- The state populating only the regions A and AC. -/
def state_A_AC : VennState
  | .A | .AC => true
  | _ => false

instance : MeasurableSpace Syllogism := ⊤
instance : DiscreteMeasurableSpace Syllogism := ⟨λ _ => trivial⟩
instance : MeasurableSpace Conclusion := ⊤
instance : DiscreteMeasurableSpace Conclusion := ⟨λ _ => trivial⟩

/-! ### Semantics (section 2.1) -/

/-- *All Xs are Ys* with existential import, so that some populated region is an X-region and
every populated X-region is a Y-region. -/
def tesslerAll (s : VennState) (X Y : Region → Bool) : Bool :=
  syllAll s X Y && decide (∃ r, s r = true ∧ X r = true)

/-- The four quantifiers, *all* with existential import and the others modern (Table 1). -/
def quantEval : AristQuant → VennState → (Region → Bool) → (Region → Bool) → Bool
  | .all => tesslerAll
  | .some => syllSome
  | .someNot => syllSomeNot
  | .no => syllNone

/-- The first premise holds in a state. -/
def premise1 (syl : Syllogism) (s : VennState) : Bool :=
  if syl.order1AB then quantEval syl.q1 s hasA hasB else quantEval syl.q1 s hasB hasA

/-- The second premise holds in a state. -/
def premise2 (syl : Syllogism) (s : VennState) : Bool :=
  if syl.order2BC then quantEval syl.q2 s hasB hasC else quantEval syl.q2 s hasC hasB

/-- Both premises hold in a state. -/
def premises (syl : Syllogism) (s : VennState) : Bool := premise1 syl s && premise2 syl s

/-- The meaning of a conclusion (section 2.3.1); *nothing follows* is the vacuous utterance. -/
def concMeaning : Conclusion → VennState → Bool
  | .allAC, s => tesslerAll s hasA hasC
  | .allCA, s => tesslerAll s hasC hasA
  | .someAC, s => syllSome s hasA hasC
  | .someCA, s => syllSome s hasC hasA
  | .someNotAC, s => syllSomeNot s hasA hasC
  | .someNotCA, s => syllSomeNot s hasC hasA
  | .noAC, s => syllNone s hasA hasC
  | .noCA, s => syllNone s hasC hasA
  | .nvc, _ => true

/-- The states at which a sentence holds. -/
def states (p : VennState → Bool) : Finset VennState := Finset.univ.filter (p · = true)

theorem coe_states (p : VennState → Bool) : (states p : Set VennState) = {s | p s = true} := by
  ext s
  simp [states]

theorem states_nvc : states (concMeaning .nvc) = Finset.univ := by
  simp [states, concMeaning]

/-- The noisy meaning, under which the listener disregards the utterance with probability `φ`. -/
def noisy (φ : ℝ≥0∞) (b : Bool) : ℝ≥0∞ := if b then 1 else φ

theorem noisy_zero (b : Bool) : noisy 0 b = ({s : Bool | s = true}).indicator 1 b := by
  cases b <;> simp [noisy]

theorem noisy_ne_zero {φ : ℝ≥0∞} (hφ : φ ≠ 0) (b : Bool) : noisy φ b ≠ 0 := by
  cases b <;> simp [noisy, hφ]

theorem noisy_ne_top {φ : ℝ≥0∞} (hφ : φ ≠ ∞) (b : Bool) : noisy φ b ≠ ∞ := by
  cases b <;> simp [noisy, hφ]

/-! ### The listeners (section 2.2) -/

section Model

variable (φ : ℝ≥0∞) (μ : Measure VennState)

/-- The reasoner as listener (2), the prior conditioned on the noisy meanings of both premises,
each disregarded independently. -/
noncomputable def reasoner : Kernel Syllogism VennState :=
  literalListener μ λ syl s => noisy φ (premise1 syl s) * noisy φ (premise2 syl s)

/-- The naive listener (1), who hears the conclusion alone. -/
noncomputable def naive : Kernel Conclusion VennState :=
  literalListener μ λ c s => noisy φ (concMeaning c s)

/-- Without noise the reasoner's posterior under the flat prior is uniform on the states
satisfying the premises. -/
theorem reasoner_zero (syl : Syllogism) :
    reasoner 0 (uniformOn Set.univ) syl = uniformOn (states (premises syl) : Set VennState) := by
  have h : (λ syl s => noisy 0 (premise1 syl s) * noisy 0 (premise2 syl s)) =
      λ syl => (states (premises syl) : Set VennState).indicator 1 := by
    funext syl s
    cases h1 : premise1 syl s <;> cases h2 : premise2 syl s <;>
      simp [coe_states, premises, noisy, h1, h2]
  rw [reasoner, h, literalListener_indicator, Kernel.ofFunOfCountable_apply, uniformOn_univ_cond]

/-- Without noise the naive listener's posterior under the flat prior is uniform on the states
satisfying the conclusion. -/
theorem naive_zero (c : Conclusion) :
    naive 0 (uniformOn Set.univ) c = uniformOn (states (concMeaning c) : Set VennState) := by
  have h : (λ c s => noisy 0 (concMeaning c s)) =
      λ c => (states (concMeaning c) : Set VennState).indicator 1 := by
    funext c s
    cases h : concMeaning c s <;> simp [coe_states, noisy, h]
  rw [naive, h, literalListener_indicator, Kernel.ofFunOfCountable_apply, uniformOn_univ_cond]

/-- With noise and a full-support prior the reasoner's posterior is a probability measure. -/
theorem isProbabilityMeasure_reasoner [IsFiniteMeasure μ] (hφ : φ ≠ 0) (hφ' : φ ≠ ∞)
    (hμ : ∀ s, μ {s} ≠ 0) (syl : Syllogism) : IsProbabilityMeasure (reasoner φ μ syl) := by
  refine isProbabilityMeasure_literalListener μ _ syl ?_ ?_ <;> rw [lintegral_fintype]
  · intro h
    have := Finset.sum_eq_zero_iff.mp h default (Finset.mem_univ _)
    exact mul_ne_zero (mul_ne_zero (noisy_ne_zero hφ _) (noisy_ne_zero hφ _)) (hμ default) this
  · exact ENNReal.sum_ne_top.2 λ s _ => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (noisy_ne_top hφ' _) (noisy_ne_top hφ' _)) (measure_ne_top _ _)

/-- With noise and a full-support prior the naive listener's posterior is a probability
measure. -/
theorem isProbabilityMeasure_naive [IsFiniteMeasure μ] (hφ : φ ≠ 0) (hφ' : φ ≠ ∞)
    (hμ : ∀ s, μ {s} ≠ 0) (c : Conclusion) : IsProbabilityMeasure (naive φ μ c) := by
  refine isProbabilityMeasure_literalListener μ _ c ?_ ?_ <;> rw [lintegral_fintype]
  · intro h
    have := Finset.sum_eq_zero_iff.mp h default (Finset.mem_univ _)
    exact mul_ne_zero (noisy_ne_zero hφ _) (hμ default) this
  · exact ENNReal.sum_ne_top.2 λ s _ => ENNReal.mul_ne_top (noisy_ne_top hφ' _) (measure_ne_top _ _)

/-- With noise and a full-support prior the naive listener gives every state positive mass. -/
theorem naive_apply_ne_zero [IsFiniteMeasure μ] (hφ : φ ≠ 0) (hφ' : φ ≠ ∞)
    (hμ : ∀ s, μ {s} ≠ 0) (c : Conclusion) (s : VennState) : naive φ μ c {s} ≠ 0 := by
  rw [naive, literalListener_apply_singleton, ENNReal.div_ne_zero]
  exact ⟨mul_ne_zero (noisy_ne_zero hφ _) (hμ s), ENNReal.sum_ne_top.2 λ s _ =>
    ENNReal.mul_ne_top (noisy_ne_top hφ' _) (measure_ne_top _ _)⟩

/-! ### The speakers (section 2.3) -/

/-- The figural preference (section 3.1.1), under which, when exactly one end term is the
subject of a premise, conclusions with that term as subject carry weight `β`, while *nothing
follows* and every conclusion of the mixed figures carry weight `1`. -/
def figuralWeight (β : ℝ) (syl : Syllogism) (c : Conclusion) : ℝ :=
  if c = .nvc then 1
  else if syl.order1AB && syl.order2BC then if c.isAC then β else 1
  else if !syl.order1AB && !syl.order2BC then if c.isAC then 1 else β
  else 1

variable (α β : ℝ)

/-- The literal speaker's utility (3), the reasoner's posterior probability that the conclusion
is true. -/
noncomputable def literalScore (syl : Syllogism) (c : Conclusion) : EReal :=
  ((Real.log (figuralWeight β syl c) +
    α * (reasoner φ μ syl).real {s | concMeaning c s = true} : ℝ) : EReal)

/-- The literal speaker (3). -/
noncomputable def literalSpeaker : Kernel Syllogism Conclusion :=
  speakerOfScore (literalScore φ μ α β)

/-- The state-communication utility (4): the expected log-probability the naive listener
assigns to the reasoner's state. -/
noncomputable def stateScore (syl : Syllogism) (c : Conclusion) : EReal :=
  ((Real.log (figuralWeight β syl c) +
    α * ∑ s, (reasoner φ μ syl).real {s} * Real.log ((naive φ μ c).real {s}) : ℝ) : EReal)

/-- The state-communication speaker (4). -/
noncomputable def stateCommunication : Kernel Syllogism Conclusion :=
  speakerOfScore (stateScore φ μ α β)

/-- The belief-alignment utility (5)–(6): the negative divergence from the reasoner's
posterior to the naive listener's. -/
noncomputable def alignmentScore (syl : Syllogism) (c : Conclusion) : EReal :=
  (Real.log (figuralWeight β syl c) : EReal) -
    (α : EReal) * (klDiv (reasoner φ μ syl) (naive φ μ c) : EReal)

/-- The belief-alignment speaker (6). -/
noncomputable def beliefAlignment : Kernel Syllogism Conclusion :=
  speakerOfScore (alignmentScore φ μ α β)

variable {φ μ α β}

theorem alignmentScore_of_ne_top {syl : Syllogism} {c : Conclusion}
    (h : klDiv (reasoner φ μ syl) (naive φ μ c) ≠ ∞) :
    alignmentScore φ μ α β syl c = ((Real.log (figuralWeight β syl c) -
      α * (klDiv (reasoner φ μ syl) (naive φ μ c)).toReal : ℝ) : EReal) := by
  rw [alignmentScore, ← EReal.coe_ennreal_toReal h, ← EReal.coe_mul, ← EReal.coe_sub]

/-- A conclusion whose naive posterior fails to dominate the reasoner's is never produced. -/
theorem alignmentScore_of_eq_top (hα : 0 < α) {syl : Syllogism} {c : Conclusion}
    (h : klDiv (reasoner φ μ syl) (naive φ μ c) = ∞) : alignmentScore φ μ α β syl c = ⊥ := by
  rw [alignmentScore, h, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos hα, EReal.sub_top]

theorem alignmentScore_ne_top (hα : 0 < α) (syl : Syllogism) (c : Conclusion) :
    alignmentScore φ μ α β syl c ≠ ⊤ := by
  rcases eq_or_ne (klDiv (reasoner φ μ syl) (naive φ μ c)) ∞ with h | h
  · rw [alignmentScore_of_eq_top hα h]
    exact bot_ne_top
  · rw [alignmentScore_of_ne_top h]
    exact EReal.coe_ne_top _

/-- Under the printed equations the state-communication and belief-alignment utilities differ
by the rationality times the entropy of the reasoner's posterior, a term independent of the
conclusion. -/
theorem alignmentScore_eq_stateScore_add [IsFiniteMeasure μ] (hφ : φ ≠ 0) (hφ' : φ ≠ ∞)
    (hμ : ∀ s, μ {s} ≠ 0) (syl : Syllogism) (c : Conclusion) :
    alignmentScore φ μ α β syl c =
      stateScore φ μ α β syl c + ((α * Hm[reasoner φ μ syl] : ℝ) : EReal) := by
  have := isProbabilityMeasure_reasoner φ μ hφ hφ' hμ syl
  have := isProbabilityMeasure_naive φ μ hφ hφ' hμ c
  have hac : reasoner φ μ syl ≪ naive φ μ c :=
    Measure.absolutelyContinuous_of_forall_singleton λ s h =>
      absurd h (naive_apply_ne_zero φ μ hφ hφ' hμ c s)
  set r := (reasoner φ μ syl).real
  set n := (naive φ μ c).real
  have hkl : ∑ s, r {s} * Real.log (r {s} / n {s}) =
      ∑ s, r {s} * Real.log (r {s}) - ∑ s, r {s} * Real.log (n {s}) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl λ s _ => ?_
    rcases eq_or_ne (r {s}) 0 with h0 | h0
    · simp [h0]
    · rw [Real.log_div h0 λ h => naive_apply_ne_zero φ μ hφ hφ' hμ c s
        ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h)]
      ring
  rw [alignmentScore_of_ne_top (klDiv_ne_top hac .of_finite), stateScore, ← EReal.coe_add,
    toReal_klDiv_eq_sum_log_div hac, measureEntropy_eq_sum, hkl]
  congr 1
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Under the printed equations the state-communication and belief-alignment speakers are one
kernel: the entropy term cancels in the softmax over conclusions. -/
theorem stateCommunication_eq_beliefAlignment [IsFiniteMeasure μ] (hφ : φ ≠ 0) (hφ' : φ ≠ ∞)
    (hμ : ∀ s, μ {s} ≠ 0) : stateCommunication φ μ α β = beliefAlignment φ μ α β :=
  (speakerOfScore_eq_of_add λ syl c => alignmentScore_eq_stateScore_add hφ hφ' hμ syl c).symm

/-! ### The literal speaker and *nothing follows* -/

theorem figuralWeight_one (syl : Syllogism) (c : Conclusion) : figuralWeight 1 syl c = 1 := by
  unfold figuralWeight
  split_ifs <;> rfl

/-- Without the figural preference the literal speaker never prefers a quantified conclusion
to *nothing follows*: the posterior probability of a tautology is maximal. -/
theorem literalSpeaker_le_nvc (hα : 0 ≤ α) (syl : Syllogism) (c : Conclusion) :
    (literalSpeaker φ μ α 1 syl).real {c} ≤ (literalSpeaker φ μ α 1 syl).real {.nvc} := by
  refine not_lt.1 λ h => ?_
  rw [literalSpeaker, speakerOfScore_real_singleton_lt_iff (score := literalScore φ μ α 1)
    (λ _ => EReal.coe_ne_top _) ⟨.nvc, EReal.coe_ne_bot _⟩, literalScore, literalScore,
    EReal.coe_lt_coe_iff,
    figuralWeight_one, figuralWeight_one] at h
  have huniv : {s : VennState | concMeaning .nvc s = true} = Set.univ :=
    Set.eq_univ_of_forall λ _ => rfl
  rw [huniv] at h
  exact absurd h (not_lt.2 (add_le_add_right (mul_le_mul_of_nonneg_left
    (measureReal_mono (Set.subset_univ _)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (literalListener_apply_le_one μ _ syl _))) hα) _))

end Model

/-! ### Without noise (section 2.3.4) -/

section Noiseless

variable {α β : ℝ}

/-- For a conclusion false at a state satisfying the premises, the naive listener's posterior
does not dominate the reasoner's. -/
theorem klDiv_zero_eq_top {syl : Syllogism} {c : Conclusion} {s₀ : VennState}
    (hs : premises syl s₀ = true) (hc : concMeaning c s₀ = false) :
    klDiv (reasoner 0 (uniformOn Set.univ) syl) (naive 0 (uniformOn Set.univ) c) = ∞ := by
  rw [reasoner_zero, naive_zero]
  refine klDiv_of_not_ac λ h => ?_
  have h1 : uniformOn (states (concMeaning c) : Set VennState) {s₀} = 0 := by
    rw [uniformOn_eq_zero_iff (Finset.finite_toSet _), Set.inter_singleton_eq_empty,
      Finset.mem_coe, states, Finset.mem_filter]
    simp [hc]
  have h2 := h h1
  rw [uniformOn_eq_zero_iff (Finset.finite_toSet _), Set.inter_singleton_eq_empty,
    Finset.mem_coe, states, Finset.mem_filter] at h2
  exact h2 ⟨Finset.mem_univ _, hs⟩

/-- Without noise a conclusion false at some state satisfying the premises is never
produced. -/
theorem beliefAlignment_zero_apply_of_false (hα : 0 < α) {syl : Syllogism} {c : Conclusion}
    {s₀ : VennState} (hs : premises syl s₀ = true) (hc : concMeaning c s₀ = false) :
    beliefAlignment 0 (uniformOn Set.univ) α β syl {c} = 0 :=
  speakerOfScore_apply_singleton_eq_zero (alignmentScore_of_eq_top hα (klDiv_zero_eq_top hs hc))

theorem alignmentScore_zero_nvc_ne_bot (syl : Syllogism) :
    alignmentScore 0 (uniformOn Set.univ) α β syl .nvc ≠ ⊥ := by
  have hac : reasoner 0 (uniformOn Set.univ) syl ≪ naive 0 (uniformOn Set.univ) .nvc := by
    rw [naive_zero, states_nvc, Finset.coe_univ]
    exact Measure.absolutelyContinuous_of_forall_singleton λ s h =>
      absurd h (uniformOn_univ_singleton_ne_zero s)
  have : IsFiniteMeasure (reasoner 0 (uniformOn Set.univ) syl) := by
    rw [reasoner_zero]
    exact inferInstanceAs
      (IsFiniteMeasure (Measure.count[|(states (premises syl) : Set VennState)]))
  rw [alignmentScore_of_ne_top (klDiv_ne_top hac .of_finite)]
  exact EReal.coe_ne_bot _

/-- Without noise the belief-alignment speaker says *nothing follows* to a logically invalid
syllogism, one to which no quantified conclusion is true at every state satisfying the
premises. -/
theorem beliefAlignment_nvc_of_invalid (hα : 0 < α) {syl : Syllogism}
    (hinv : ∀ c, c ≠ .nvc → ∃ s, premises syl s = true ∧ concMeaning c s = false) :
    beliefAlignment 0 (uniformOn Set.univ) α β syl {.nvc} = 1 := by
  have : IsMarkovKernel (beliefAlignment 0 (uniformOn Set.univ) α β) :=
    isMarkovKernel_speakerOfScore (λ syl => ⟨.nvc, alignmentScore_zero_nvc_ne_bot syl⟩)
      (λ syl c => alignmentScore_ne_top hα syl c)
  calc beliefAlignment 0 (uniformOn Set.univ) α β syl {.nvc}
      = ∑ c, beliefAlignment 0 (uniformOn Set.univ) α β syl {c} :=
        (Finset.sum_eq_single _ (λ c _ hc => let ⟨s, hs, hc⟩ := hinv c hc
          beliefAlignment_zero_apply_of_false hα hs hc) (λ h => absurd (Finset.mem_univ _) h)).symm
    _ = 1 := by rw [sum_measure_singleton, Finset.coe_univ, measure_univ]

/-- The score of a conclusion entailed by the premises is the log ratio of the premises'
extension to the conclusion's, with the figural weight. -/
theorem alignmentScore_zero_of_valid {syl : Syllogism} {c : Conclusion}
    (hE : (states (premises syl)).Nonempty)
    (hc : states (premises syl) ⊆ states (concMeaning c)) :
    alignmentScore 0 (uniformOn Set.univ) α β syl c =
      ((Real.log (figuralWeight β syl c) -
        α * Real.log ((states (concMeaning c)).card / (states (premises syl)).card) : ℝ) :
          EReal) := by
  rw [alignmentScore, reasoner_zero, naive_zero, klDiv_uniformOn_of_subset hE hc,
    EReal.coe_ennreal_ofReal, max_eq_left (Real.log_nonneg ((one_le_div
      (Nat.cast_pos.2 hE.card_pos)).2 (Nat.cast_le.2 (Finset.card_le_card hc)))),
    ← EReal.coe_mul, ← EReal.coe_sub]

/-- Among conclusions entailed by the premises and equally weighted, the belief-alignment
speaker prefers the one true in fewer states. -/
theorem beliefAlignment_real_lt_iff_of_valid (hα : 0 < α) {syl : Syllogism} {c₁ c₂ : Conclusion}
    (hE : (states (premises syl)).Nonempty)
    (h₁ : states (premises syl) ⊆ states (concMeaning c₁))
    (h₂ : states (premises syl) ⊆ states (concMeaning c₂))
    (hw : figuralWeight β syl c₁ = figuralWeight β syl c₂) :
    (beliefAlignment 0 (uniformOn Set.univ) α β syl).real {c₂} <
        (beliefAlignment 0 (uniformOn Set.univ) α β syl).real {c₁} ↔
      (states (concMeaning c₁)).card < (states (concMeaning c₂)).card := by
  have hE' := Nat.cast_pos (α := ℝ) |>.2 hE.card_pos
  rw [beliefAlignment, speakerOfScore_real_singleton_lt_iff (alignmentScore_ne_top hα syl)
    ⟨.nvc, alignmentScore_zero_nvc_ne_bot syl⟩, alignmentScore_zero_of_valid hE h₁,
    alignmentScore_zero_of_valid hE h₂, EReal.coe_lt_coe_iff, hw, sub_lt_sub_iff_left,
    mul_lt_mul_iff_right₀ hα,
    Real.log_lt_log_iff (div_pos (Nat.cast_pos.2 (hE.mono h₁).card_pos) hE')
      (div_pos (Nat.cast_pos.2 (hE.mono h₂).card_pos) hE'),
    div_lt_div_iff_of_pos_right hE', Nat.cast_lt]

/-! ### Barbara and *All A are B, All C are B* (Figures 3, 4 and 8) -/

/-- Barbara's premises entail *all A are C*, existential import included. -/
theorem premises_barbara_subset : states (premises barbara) ⊆ states (concMeaning .allAC) := by
  intro s hs
  simp only [states, Finset.mem_filter, Finset.mem_univ, true_and, premises, premise1, premise2,
    barbara, quantEval, tesslerAll, Bool.and_eq_true, decide_eq_true_eq, concMeaning,
    ↓reduceIte] at hs ⊢
  exact ⟨barbara_valid s hs.1.1 hs.2.1, hs.1.2⟩

/-- *All A are C* entails *some A are C* under existential import. -/
theorem allAC_subset_someAC : states (concMeaning .allAC) ⊆ states (concMeaning .someAC) := by
  intro s hs
  simp only [states, Finset.mem_filter, Finset.mem_univ, true_and, concMeaning, tesslerAll,
    Bool.and_eq_true, decide_eq_true_eq] at hs ⊢
  exact syllAll_imp_syllSome s hasA hasC hs.2 hs.1

/-- Hearing Barbara, the belief-alignment speaker prefers *all A are C* to *some A are C* and
to *nothing follows*: the entailed conclusion true in the fewest states. -/
theorem barbara_prefers_allAC (hα : 0 < α) (hβ : 1 ≤ β) :
    (beliefAlignment 0 (uniformOn Set.univ) α β barbara).real {.someAC} <
        (beliefAlignment 0 (uniformOn Set.univ) α β barbara).real {.allAC} ∧
      (beliefAlignment 0 (uniformOn Set.univ) α β barbara).real {.nvc} <
        (beliefAlignment 0 (uniformOn Set.univ) α β barbara).real {.allAC} := by
  have hE : (states (premises barbara)).Nonempty :=
    ⟨state_ABC, by simp only [states, Finset.mem_filter, Finset.mem_univ, true_and]; decide⟩
  have hE' := Nat.cast_pos (α := ℝ) |>.2 hE.card_pos
  have hall : state_A_AC ∉ states (concMeaning .allAC) := by
    simp only [states, Finset.mem_filter, Finset.mem_univ, true_and]; decide
  refine ⟨(beliefAlignment_real_lt_iff_of_valid hα hE premises_barbara_subset
    (premises_barbara_subset.trans allAC_subset_someAC) rfl).2 (Finset.card_lt_card
      ((Finset.ssubset_iff_of_subset allAC_subset_someAC).2 ⟨state_A_AC,
        by simp only [states, Finset.mem_filter, Finset.mem_univ, true_and]; decide, hall⟩)), ?_⟩
  rw [beliefAlignment, speakerOfScore_real_singleton_lt_iff (alignmentScore_ne_top hα _)
    ⟨.nvc, alignmentScore_zero_nvc_ne_bot _⟩, alignmentScore_zero_of_valid hE
      premises_barbara_subset, alignmentScore_zero_of_valid hE (states_nvc ▸ Finset.subset_univ _),
    EReal.coe_lt_coe_iff, states_nvc]
  have hlt : Real.log ((states (concMeaning .allAC)).card / (states (premises barbara)).card) <
      Real.log ((Finset.univ : Finset VennState).card / (states (premises barbara)).card) :=
    Real.log_lt_log (div_pos (Nat.cast_pos.2 (hE.mono premises_barbara_subset).card_pos) hE')
      ((div_lt_div_iff_of_pos_right hE').2 (Nat.cast_lt.2 (Finset.card_lt_card
        ((Finset.ssubset_iff_of_subset (Finset.subset_univ _)).2
          ⟨state_A_AC, Finset.mem_univ _, hall⟩))))
  have hw : figuralWeight β barbara .allAC = β := rfl
  have hw' : figuralWeight β barbara .nvc = 1 := rfl
  rw [hw, hw', Real.log_one]
  nlinarith [Real.log_nonneg hβ, mul_lt_mul_of_pos_left hlt hα]

/-- *All A are B, All C are B* is invalid, since every quantified conclusion fails at a state
satisfying the premises, so the noiseless belief-alignment speaker says *nothing follows*. -/
theorem allAB_allCB_nvc (hα : 0 < α) :
    beliefAlignment 0 (uniformOn Set.univ) α β allAB_allCB {.nvc} = 1 := by
  refine beliefAlignment_nvc_of_invalid hα λ c hc => ?_
  cases c with
  | allAC | someAC | allCA | someCA => exact ⟨state_AB_BC, by decide⟩
  | noAC | someNotAC | noCA | someNotCA => exact ⟨state_ABC, by decide⟩
  | nvc => exact absurd rfl hc

end Noiseless

end TesslerTenenbaumGoodman2022
