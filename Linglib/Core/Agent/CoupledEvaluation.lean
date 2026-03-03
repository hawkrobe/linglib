import Linglib.Core.Agent.RationalAction

/-!
# Coupled Evaluation: Softmax over Product Spaces

When items are evaluated jointly — via systemic constraints in MaxEnt grammar
or via shared latent variables in RSA — the distribution over individual items
doesn't factorize. This module formalizes the shared pattern:

1. **Per-item scores** `s(i, v)` that depend only on one item's value
2. **Coupling scores** `C(f)` that evaluate the full assignment jointly
3. **Joint probability** via softmax: `P(f) ∝ exp(Σᵢ s(i, f(i)) + C(f))`
4. **Marginal probability**: `P_i(v) = Σ_{f : f(i) = v} P(f)`

The key theorem is **factorization**: when the coupling score is constant
(no coupling), the joint factorizes and each marginal equals the independent
softmax of its per-item score.

## Instances

- **MaxEnt systemic constraints** (@cite{storme-2026}): items = input→output
  mappings, coupling = \*HOMOPHONY or other systemic constraints.
  `componentScore i v = harmonyScore(classicalConstraints, (inputs i, v))`,
  `couplingScore f = -Σₖ wₖ · Sₖ(f)`.

- **RSA lexical uncertainty** (@cite{bergen-levy-goodman-2016}): the analog
  is a mixture model rather than a coupled exponential — the listener
  marginalizes over lexicons: `L1(u,w) ∝ prior(w) · Σ_l prior(l) · S1(l,w,u)`.
  The algebraic form differs (mixture vs coupled exponential), but the
  phenomenon is identical: joint evaluation creates dependencies between items
  that would otherwise be independent, and marginalization recovers individual
  probabilities that reflect the coupling.

  See `RSAConfig.L1agent` in `Theories/Pragmatics/RSA/Core/Config.lean` for the
  RSA marginalization pattern.

- **BToM inference** (`Core/Agent/BToM.lean`): the observer marginalizes over
  latent mental state variables (percept, belief, desire) to recover world
  posteriors. `worldMarginal(a, w) = Σ_{p,b,d,s,m} joint(a,p,b,d,s,m,w)`.

## Factorization

The core theorem (`marginal_eq_independent_when_uncoupled`): when the coupling
score is constant, the joint distribution factorizes as a product of
independent per-item distributions. This is the mathematical basis for:
- Storme: systemic constraint weight = 0 ⟹ marginal = classical MaxEnt
- RSA: single lexicon (|Lexicon| = 1) ⟹ L1 = standard Bayesian update
- MaxEnt↔OT: `softmax_argmax_limit` sends MaxEnt → OT; this theorem sends
  coupled MaxEnt → uncoupled MaxEnt when coupling vanishes
-/

namespace Core

open Real BigOperators Finset

-- ============================================================================
-- § 1: Coupled Softmax Structure
-- ============================================================================

/-- A coupled evaluation over indexed items, where the joint score may not
    decompose into independent per-item scores.

    The joint probability of assignment `f : Index → Value` is:
    `P(f) = softmax(totalScore, 1)(f)` over the space of all assignments.

    When `couplingScore` is constant, `totalScore` decomposes additively
    and the joint factorizes into independent per-item softmax distributions. -/
structure CoupledSoftmax (Index Value : Type*) [Fintype Index] [Fintype Value] where
  /-- Per-item score: depends only on one item's value.
      In MaxEnt: `harmonyScore(classicalConstraints, (input_i, v))`.
      In RSA: `log S1(lexicon, world, utterance)`. -/
  componentScore : Index → Value → ℝ
  /-- Coupling score: evaluates the full assignment jointly.
      In MaxEnt: systemic constraint penalty (e.g., \*HOMOPHONY).
      In RSA: log prior over shared lexicon. -/
  couplingScore : (Index → Value) → ℝ

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

/-- Total score of an assignment: sum of per-item scores plus coupling. -/
noncomputable def CoupledSoftmax.totalScore (cs : CoupledSoftmax I V)
    (f : I → V) : ℝ :=
  (∑ i : I, cs.componentScore i (f i)) + cs.couplingScore f

/-- Joint probability: softmax over the space of all assignments `I → V`. -/
noncomputable def CoupledSoftmax.jointProb [Nonempty V]
    (cs : CoupledSoftmax I V) (f : I → V) : ℝ :=
  softmax cs.totalScore 1 f

-- ============================================================================
-- § 2: Marginalization
-- ============================================================================

/-- Marginal probability: P_i(v) = Σ_{f : f(i) = v} P_joint(f).
    Marginalizes the joint distribution to recover the probability of
    a specific value at a specific index. -/
noncomputable def CoupledSoftmax.marginal [Nonempty V]
    (cs : CoupledSoftmax I V) (i : I) (v : V) : ℝ :=
  ∑ f : I → V, if f i = v then cs.jointProb f else 0

/-- Marginals sum to 1 (marginalization preserves total probability).

    Proof: each assignment `f` contributes to exactly one value `v = f(i)`,
    so `Σ_v marginal(i, v) = Σ_v Σ_{f:f(i)=v} P(f) = Σ_f P(f) = 1`. -/
theorem CoupledSoftmax.marginal_sum_eq_one [Nonempty V]
    (cs : CoupledSoftmax I V) (i : I) :
    ∑ v : V, cs.marginal i v = 1 := by
  simp only [marginal]
  rw [Finset.sum_comm]
  suffices h : ∑ f : I → V, ∑ v : V, (if f i = v then cs.jointProb f else 0) =
      ∑ f : I → V, cs.jointProb f by
    rw [h]; exact softmax_sum_eq_one cs.totalScore 1
  apply Finset.sum_congr rfl; intro f _
  calc ∑ v : V, (if f i = v then cs.jointProb f else 0)
      = ∑ v : V, (if v = f i then cs.jointProb f else 0) := by
        apply Finset.sum_congr rfl; intro v _; simp [eq_comm]
    _ = cs.jointProb f := by
        simp [Finset.sum_ite_eq']

/-- Marginal probabilities are non-negative. -/
theorem CoupledSoftmax.marginal_nonneg [Nonempty V]
    (cs : CoupledSoftmax I V) (i : I) (v : V) :
    0 ≤ cs.marginal i v :=
  Finset.sum_nonneg fun f _ => by
    split
    · exact le_of_lt (softmax_pos cs.totalScore 1 f)
    · exact le_refl 0

-- ============================================================================
-- § 3: Independent (Uncoupled) Evaluation
-- ============================================================================

/-- Independent per-item probability: what the marginal would be if there
    were no coupling. `P_indep(i, v) = softmax(componentScore(i, ·), 1)(v)`. -/
noncomputable def CoupledSoftmax.independentProb [Nonempty V]
    (cs : CoupledSoftmax I V) (i : I) (v : V) : ℝ :=
  softmax (cs.componentScore i) 1 v

-- ============================================================================
-- § 4: Factorization Theorem
-- ============================================================================

/-- **Factorization theorem**: when coupling is constant (no genuine coupling),
    the marginal probability equals the independent per-item softmax.

    This is the shared mathematical core of:
    - @cite{storme-2026}: systemic weight = 0 ⟹ marginal = classical MaxEnt
    - @cite{bergen-levy-goodman-2016}: single lexicon ⟹ L1 = standard posterior
    - BToM: delta-function latent prior ⟹ marginal = direct inference

    ### Proof sketch

    When `couplingScore f = c` for all `f`:

    1. `totalScore f = Σᵢ componentScore(i, f(i)) + c`
    2. By `softmax_add_const`, adding `c` doesn't change softmax:
       `jointProb f = softmax(f ↦ Σᵢ componentScore(i, f(i)), 1)(f)`
    3. Since the score decomposes additively over indices, `exp(Σᵢ sᵢ) = Πᵢ exp(sᵢ)`,
       so the joint factorizes: `jointProb f = Πᵢ softmax(componentScore(i, ·))(f(i))`
    4. Marginalizing: `marginal(i, v) = softmax(componentScore(i, ·))(v) ·
       Π_{j≠i} Σ_{v'} softmax(componentScore(j, ·))(v') = softmax(·)(v) · 1`

    Step 3 uses the finite Fubini theorem:
    `Σ_{f : I → V} Πᵢ g(i, f(i)) = Πᵢ (Σ_v g(i, v))`.

    TODO: formalize via `softmax_add_const` (step 2), `Real.exp_add` (step 3),
    and the finite product-sum interchange (step 3→4). -/
theorem CoupledSoftmax.marginal_eq_independent_when_uncoupled [Nonempty V]
    (cs : CoupledSoftmax I V)
    (h_const : ∃ c, ∀ f, cs.couplingScore f = c)
    (i : I) (v : V) :
    cs.marginal i v = cs.independentProb i v := by
  sorry

-- ============================================================================
-- § 5: Coupling Detector
-- ============================================================================

/-- A coupled evaluation is genuinely coupled at index `i` iff there exist
    two assignments agreeing at `i` but with different total scores.
    This is the observable signature of non-factorization: the score of the
    assignment at position `i` depends on the values at other positions. -/
def CoupledSoftmax.genuinelyCoupled
    (cs : CoupledSoftmax I V) (i : I) : Prop :=
  ∃ f g : I → V, f i = g i ∧
    cs.totalScore f ≠ cs.totalScore g

-- ============================================================================
-- § 6: MaxEnt Instantiation
-- ============================================================================

/-- Construct a `CoupledSoftmax` from MaxEnt grammar components.

    - `componentScore i v = classicalScore(inputs(i), v)`
    - `couplingScore f = systemicScore(f)`

    This shows that the MaxEnt systemic constraint framework from
    `Theories.Phonology.HarmonicGrammar.MaxEnt` is an instance of
    the general coupled evaluation pattern. The `marginal_eq_classical_when_no_systemic`
    theorem in `MaxEnt.lean` is a corollary of `marginal_eq_independent_when_uncoupled`. -/
noncomputable def coupledSoftmaxOfMaxEnt
    {n : Nat} {I O : Type} [Fintype O] [DecidableEq O]
    (inputs : Fin n → I)
    (classicalScore : I × O → ℝ)
    (systemicScore : (Fin n → O) → ℝ) :
    CoupledSoftmax (Fin n) O where
  componentScore i v := classicalScore (inputs i, v)
  couplingScore f := systemicScore f

end Core
