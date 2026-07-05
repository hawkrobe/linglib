import Linglib.Pragmatics.BToM

/-!
# BToM-derived credence

The bridge from Bayesian Theory of Mind inference to an agent credence: the
observer's estimate of an agent's credence in `φ` is the belief-marginal
expectation of `φ`'s truth value (`BToMModel.beliefExpectation`). This is the
*pragmatic* grounding — reasoning about an interlocutor's mental state — that
produces the credence the (semantic) epistemic-threshold predicates consume
([ying-zhi-xuan-wong-mansinghka-tenenbaum-2025],
[baker-jara-ettinger-saxe-tenenbaum-2017]).

## Main results

* `btomCredence` — credence as the BToM belief-marginal expectation.
* `btomCredence_eq_world_expectation` — under identity perception/belief, this
  collapses to the world-marginal expectation (the RSA-BToM bridge).
-/

namespace Core

open Core in
/-- Agent credence derived from BToM belief-marginal inference.

    Given a BToM model with belief type `B` and an evaluation function
    `eval : B → (W → Bool) → F` that computes how belief state `b` rates
    proposition `φ`, the observer estimates the agent's credence after
    observing action `a`:

        Pr_obs(Agent, φ | a) = Σ_b P(b | a) · eval(b, φ)

    This is `BToMModel.beliefExpectation` applied to `fun b => eval b φ`,
    grounding the abstract `AgentCredence` in concrete BToM inference.

    When `B = W` and `eval b φ = if φ b then 1 else 0` (the RSA-BToM
    bridge's perfect-knowledge assumption), this reduces to the L1
    listener's expected truth-value under their world posterior.

    Polymorphic in `F` so it composes with both ℚ-valued (exact
    computation) and ℝ-valued models. -/
noncomputable def btomCredence
    {F : Type*} [CommSemiring F]
    {A P B D S M W : Type*}
    [Fintype P] [Fintype B] [Fintype D] [Fintype S] [Fintype M] [Fintype W]
    (model : BToMModel F A P B D S M W)
    (eval : B → (W → Bool) → F)
    (a : A) (φ : (W → Bool)) : F :=
  model.beliefExpectation (λ b => eval b φ) a

section IdentityPerception
open Core

variable {F : Type*} [CommSemiring F]
variable {A D S M W : Type*}
variable [DecidableEq W] [Fintype W] [Fintype D] [Fintype S] [Fintype M]

/-- For BToM models with identity perception and identity belief
    (Percept = Belief = World with delta-function maps), the belief
    marginal equals the world marginal.

    This is the structural identity underlying the RSA-BToM bridge:
    when the agent has perfect perception (`P(p|w) = δ(p=w)`) and
    perfect belief formation (`P(b|p) = δ(b=p)`), inferring the
    agent's belief state is the same as inferring the world state.

    Proof: unfold both marginals, substitute the delta functions, then
    collapse via `Finset.sum_ite_eq`. Both sides reduce to
    `Σ_{d,s,m} planModel(b,d,s,m,a) · worldPrior(b) · ...`. -/
private lemma ite_sum {ι G : Type*} [Fintype ι] [AddCommMonoid G]
    {c : Prop} [Decidable c] {f : ι → G} :
    (∑ i, if c then f i else 0) = if c then ∑ i, f i else 0 := by
  split_ifs <;> simp

theorem identity_belief_eq_world_marginal
    (model : BToMModel F A W W D S M W)
    (h_percept : ∀ w p, model.perceptModel w p = if p = w then 1 else 0)
    (h_belief : ∀ p b, model.beliefModel p b = if b = p then 1 else 0)
    (a : A) (b : W) :
    model.beliefMarginal a b = model.worldMarginal a b := by
  simp only [BToMModel.beliefMarginal, BToMModel.worldMarginal, BToMModel.jointScore,
    h_percept, h_belief]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, mul_one]
  -- Collapse inner delta sums (if x = y where y is bound)
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  -- Factor constant ites (if b = x) out of inner sums where x is free
  simp_rw [ite_sum]
  -- Collapse outer delta sums
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- For identity-perception BToM models, `btomCredence` is the
    world-marginal-weighted evaluation of φ.

    This connects the abstract `btomCredence` to concrete RSA
    inference: when the BToM model has identity perception/belief
    (as in the RSA-as-BToM bridge), computing agent credence via BToM
    belief marginals is the same as computing the L1 listener's
    expected truth-value.

        btomCredence(model, eval, a, φ)
          = Σ_b beliefMarginal(a, b) · eval(b, φ)
          = Σ_w worldMarginal(a, w) · eval(w, φ)    [by identity_belief_eq_world_marginal]

    The second line is exactly the L1 listener's posterior expectation
    (via the PMF-face bridge `rsa_btom_bridge` in
    `Studies/RitchieSchiller2024.lean`). -/
theorem btomCredence_eq_world_expectation
    (model : BToMModel F A W W D S M W)
    (h_percept : ∀ w p, model.perceptModel w p = if p = w then 1 else 0)
    (h_belief : ∀ p b, model.beliefModel p b = if b = p then 1 else 0)
    (eval : W → (W → Bool) → F) (a : A) (φ : (W → Bool)) :
    btomCredence model eval a φ =
    ∑ w : W, model.worldMarginal a w * eval w φ := by
  simp only [btomCredence, BToMModel.beliefExpectation]
  congr 1; ext b
  rw [identity_belief_eq_world_marginal model h_percept h_belief]

end IdentityPerception

end Core
