import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier
import Linglib.Theories.Pragmatics.RSA.Core.Noise
import Linglib.Core.Divergence
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# @cite{tessler-tenenbaum-goodman-2022} — Logic, Probability, and Pragmatics in Syllogistic Reasoning

Topics in Cognitive Science 14: 574–601.

## Core Idea

Syllogistic reasoning decomposes into two pragmatic subproblems:
1. **Listener**: interprets premises via Bayesian update over Venn diagram states
2. **Speaker**: selects the conclusion that best communicates beliefs to a naive listener

Three speaker models are formalized:
- **S₀ (Literal Speaker, eq. 3)**: scores conclusions by expected literal truth
- **State Communication (eq. 4)**: scores by expected log-likelihood (standard RSA)
- **Belief Alignment (eq. 6)**: scores by −KL divergence (the paper's winning model,
  r = .82 with 3 parameters: α, φ, β)

State Communication and Belief Alignment produce identical conclusion distributions
after softmax normalization (they differ by an additive constant H(post) that cancels);
their distinct fitted parameters reflect the fitting procedure, not the functional form.
This equivalence is proved as `stateCom_eq_beliefAlignment`.

## Grounding in Linglib

- Syllogistic quantifiers are `every_sem`/`some_sem`/`no_sem`
  from `Quantifier.lean` applied to Venn diagram regions as entities
- Subalternation (All→Some) proved via `subalternation_a_i` from `Quantifier.lean`
- Noisy semantics via `RSA.Noise.noiseChannel`
- Belief Alignment utility via `Core.Divergence.klDivergence`
- SC ≡ BA equivalence via `Core.Divergence.kl_eq_neg_crossEntropy_plus_negEntropy`
- "Nothing follows" as vacuous utterance (true in every state)
-/

set_option autoImplicit false

namespace Phenomena.Quantification.Studies.TesslerTenenbaumGoodman2022

open Semantics.Lexical.Determiner.Quantifier (every_sem some_sem no_sem FiniteModel
  subalternation_a_i)
open Semantics.Montague (Model)

-- ============================================================================
-- §1. Ontology: Venn Diagram Regions and States
-- ============================================================================

/-- The 7 non-empty regions of a three-circle (A, B, C) Venn diagram.
    The empty region {¬A, ¬B, ¬C} does not affect quantifier truth
    conditions for all, some, some...not, none, and is excluded. -/
inductive Region where
  | A | B | C | AB | AC | BC | ABC
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Region where
  elems := {.A, .B, .C, .AB, .AC, .BC, .ABC}
  complete := fun x => by cases x <;> simp

/-- A Venn state: which regions are populated. 2⁷ = 128 possible states. -/
abbrev VennState := Region → Bool

/-- Region predicates: does region r have property X? -/
def hasA : Region → Bool | .A | .AB | .AC | .ABC => true | _ => false
def hasB : Region → Bool | .B | .AB | .BC | .ABC => true | _ => false
def hasC : Region → Bool | .C | .AC | .BC | .ABC => true | _ => false

-- ============================================================================
-- §2. Quantifier Semantics Grounded in GQ Denotations
-- ============================================================================

/-- Regions as a Montague model, enabling reuse of `every_sem`/`some_sem`/`no_sem`. -/
def regionModel : Model := { Entity := Region, decEq := inferInstance }

instance regionFM : FiniteModel regionModel where
  elements := [.A, .B, .C, .AB, .AC, .BC, .ABC]
  complete := fun x => by cases x <;> simp
  nodup := by simp [List.nodup_cons, List.mem_cons]

/-- "All Xs are Ys" in state s: every populated X-region also has Y.
    Grounded in `every_sem` from `Quantifier.lean`. -/
def syllAll (s : VennState) (X Y : Region → Bool) : Bool :=
  every_sem regionModel (fun r => s r && X r) Y

/-- "Some Xs are Ys": some populated X-region also has Y. -/
def syllSome (s : VennState) (X Y : Region → Bool) : Bool :=
  some_sem regionModel (fun r => s r && X r) Y

/-- "Some Xs are not Ys": some populated X-region lacks Y. -/
def syllSomeNot (s : VennState) (X Y : Region → Bool) : Bool :=
  some_sem regionModel (fun r => s r && X r) (fun r => !Y r)

/-- "No Xs are Ys": no populated X-region has Y. -/
def syllNone (s : VennState) (X Y : Region → Bool) : Bool :=
  no_sem regionModel (fun r => s r && X r) Y

-- ============================================================================
-- §3. Conclusion Space and Figural Bias
-- ============================================================================

/-- The 9 possible conclusions: 4 quantifiers × 2 term orders + NVC. -/
inductive Conclusion where
  | allAC | allCA
  | someAC | someCA
  | someNotAC | someNotCA
  | noAC | noCA
  | nvc  -- "nothing follows" / no valid conclusion
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Conclusion where
  elems := {.allAC, .allCA, .someAC, .someCA,
            .someNotAC, .someNotCA, .noAC, .noCA, .nvc}
  complete := fun x => by cases x <;> simp

/-- Does the conclusion use A→C term order (vs C→A)?
    Used for the figural bias parameter β. -/
def Conclusion.isAC : Conclusion → Bool
  | .allAC | .someAC | .someNotAC | .noAC => true
  | _ => false

/-- Figural bias prior weight: conclusions whose term order matches the
    premise figure get weight β; others get weight 1. NVC always gets 1.

    The paper fits β ≈ 2.01 (MAP), meaning conclusions matching the
    premise term order are preferred by roughly 2:1. -/
def figuralWeight (β : ℚ) (premiseIsAB : Bool) (c : Conclusion) : ℚ :=
  if c = .nvc then 1
  else if c.isAC == premiseIsAB then β
  else 1

/-- Literal meaning of each conclusion in a Venn state.
    "Nothing follows" is true in every state — the vacuous utterance. -/
def concMeaning : Conclusion → VennState → Bool
  | .allAC, s      => syllAll s hasA hasC
  | .allCA, s      => syllAll s hasC hasA
  | .someAC, s     => syllSome s hasA hasC
  | .someCA, s     => syllSome s hasC hasA
  | .someNotAC, s  => syllSomeNot s hasA hasC
  | .someNotCA, s  => syllSomeNot s hasC hasA
  | .noAC, s       => syllNone s hasA hasC
  | .noCA, s       => syllNone s hasC hasA
  | .nvc, _        => true

/-- "Nothing follows" is always true: the key insight enabling the Belief
    Alignment model to rationally produce NVC when premises are uninformative. -/
theorem nvc_always_true (s : VennState) : concMeaning .nvc s = true := rfl

-- ============================================================================
-- §4. Logical Validity: Barbara Syllogism
-- ============================================================================

/-- **Barbara** (All A-B, All B-C ⊢ All A-C) is logically valid.

    The proof chains through populated regions: if r is a populated
    A-region, premise 1 gives it B, making it a populated B-region,
    and premise 2 gives it C. This is a *state-restricted* form of
    transitivity — stricter than `every_transitive` from `Quantifier.lean`,
    which applies to unrestricted universal quantification. Here the
    restrictors shift between premises (`s ∧ hasA` vs `s ∧ hasB`),
    and the middle term B bridges them via the population predicate s. -/
theorem barbara_valid (s : VennState)
    (h1 : syllAll s hasA hasB = true)
    (h2 : syllAll s hasB hasC = true) :
    syllAll s hasA hasC = true := by
  unfold syllAll every_sem at *
  simp only [FiniteModel.elements] at *
  rw [List.all_eq_true] at *
  intro r hr
  have h1r := h1 r hr
  have h2r := h2 r hr
  cases r <;> simp_all [hasA, hasB, hasC]

/-- Barbara also validates "Some A are C" (by subalternation: All → Some).
    Uses `barbara_valid` for the All A-C premise, then
    `subalternation_a_i` from `Quantifier.lean` to step from A-form
    to I-form — genuine structural coupling with the GQ infrastructure. -/
theorem barbara_some_valid (s : VennState)
    (h1 : syllAll s hasA hasB = true)
    (h2 : syllAll s hasB hasC = true)
    (hA : syllSome s hasA hasA = true) :
    syllSome s hasA hasC = true := by
  -- Step 1: derive All A-C from Barbara
  have hAllAC := barbara_valid s h1 h2
  -- Step 2: apply subalternation (All → Some when restrictor non-empty)
  unfold syllAll at hAllAC; unfold syllSome
  apply subalternation_a_i _ _ _ hAllAC
  -- Step 3: derive restrictor non-emptiness from hA
  unfold syllSome some_sem at hA
  simp only [FiniteModel.elements] at hA ⊢
  rw [List.any_eq_true] at hA ⊢
  obtain ⟨r, hr, hpred⟩ := hA
  exact ⟨r, hr, by cases r <;> simp_all [hasA]⟩

-- ============================================================================
-- §5. Logical Invalidity
-- ============================================================================

/-- Witness state for invalid syllogisms: only AB and BC populated.
    Compatible with "All A-B, All C-B" but falsifies All/Some A-C. -/
private def state_AB_BC : VennState
  | .AB => true | .BC => true | _ => false

/-- Witness state: only ABC populated. Compatible with "All A-B, All C-B"
    but falsifies No/SomeNot A-C. -/
private def state_ABC : VennState
  | .ABC => true | _ => false

/-- "All A-B, All C-B" is logically invalid: no Aristotelian conclusion
    holds in all compatible states. Proof by two counterexamples. -/
theorem allAB_allCB_invalid :
    -- State 1 falsifies All/Some A-C and C-A
    concMeaning .allAC state_AB_BC = false ∧
    concMeaning .someAC state_AB_BC = false ∧
    concMeaning .allCA state_AB_BC = false ∧
    concMeaning .someCA state_AB_BC = false ∧
    -- State 2 falsifies No/SomeNot A-C and C-A
    concMeaning .noAC state_ABC = false ∧
    concMeaning .someNotAC state_ABC = false ∧
    concMeaning .noCA state_ABC = false ∧
    concMeaning .someNotCA state_ABC = false := by
  simp only [concMeaning, syllAll, syllSome, syllSomeNot, syllNone,
    every_sem, some_sem, no_sem, state_AB_BC, state_ABC,
    FiniteModel.elements, hasA, hasC,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  decide

-- ============================================================================
-- §6. Noisy Semantics via RSA.Noise.noiseChannel
-- ============================================================================

/-- Noisy semantics ℒ(u, s): a small probability φ of misjudging truth value.
    Directly instantiates `RSA.Noise.noiseChannel(1−φ, φ, ⟦u⟧)`:
    ℒ(u,s) = 1−φ when ⟦u⟧(s) = true, φ when false. -/
def noisyConcMeaning (φ : ℚ) (c : Conclusion) (s : VennState) : ℚ :=
  RSA.Noise.noiseChannel (1 - φ) φ (if concMeaning c s then 1 else 0)

/-- When noise is zero, noisy meaning reduces to literal meaning. -/
theorem noisyConcMeaning_zero (c : Conclusion) (s : VennState) :
    noisyConcMeaning 0 c s = if concMeaning c s then 1 else 0 := by
  simp only [noisyConcMeaning, RSA.Noise.noiseChannel]
  split <;> ring

/-- Noisy semantics assigns the NVC utterance a constant value in every state,
    since `concMeaning .nvc s = true` for all s. This means L₀(s|NVC) = P(s):
    hearing "nothing follows" does not update the listener's beliefs. -/
theorem noisyConcMeaning_nvc (φ : ℚ) (s : VennState) :
    noisyConcMeaning φ .nvc s = 1 - φ := by
  simp only [noisyConcMeaning, concMeaning, RSA.Noise.noiseChannel, ↓reduceIte]
  ring

-- ============================================================================
-- §7. L₀ Premise Interpretation
-- ============================================================================

/-- L₀ joint likelihood of two premises in state s (unnormalized).

    Computes ℒ(u₁,s) · ℒ(u₂,s) — the likelihood term only. The full L₀
    posterior (eq. 2) also includes the state prior P(s). The paper fixes
    θ = 0.5 per region, making P(s) = 0.5⁷ = 1/128 for all states — a
    uniform prior that cancels in normalization. For this reason, the
    likelihood alone determines the relative posterior weights. -/
def l0PremiseLikelihood (φ : ℚ) (p1 p2 : VennState → Bool)
    (s : VennState) : ℚ :=
  RSA.Noise.noiseChannel (1 - φ) φ (if p1 s then 1 else 0) *
  RSA.Noise.noiseChannel (1 - φ) φ (if p2 s then 1 else 0)

-- ============================================================================
-- §8. Speaker Models (eqs. 3, 4, 6)
-- ============================================================================

/-- **S₀ (Literal Speaker, eq. 3)**: scores conclusions by expected literal
    truth under the reasoner's posterior.

    S₀(u₃ | u₁,u₂) ∝ exp[α · Σ_s ℒ(u₃,s) · L₀(s|u₁,u₂)]

    Here ℒ(u₃,s) is the *deterministic* semantic function (not the noisy
    version inside L₀). This speaker samples states from the posterior and
    randomly selects conclusions that are literally true. -/
noncomputable def literalSpeakerScore
    (premPost : VennState → ℝ) (α : ℝ) (c : Conclusion) : ℝ :=
  Real.exp (α * ∑ s : VennState,
    (if concMeaning c s then (1 : ℝ) else 0) * premPost s)

/-- **State Communication (S₁, eq. 4)**: scores conclusions by expected
    log-likelihood — standard RSA informativity applied to syllogisms.

    S₁(u₃ | u₁,u₂) ∝ exp[α · Σ_s L₀(s|u₁,u₂) · ln L₀(s|u₃)]

    The two L₀ agents are distinct: L₀(s|u₁,u₂) is the reasoner who
    interpreted the premises; L₀(s|u₃) is a hypothetical naive listener
    who interprets just the conclusion. Both use noisy semantics (same φ). -/
noncomputable def stateComScore
    (premPost : VennState → ℝ) (naivePost : Conclusion → VennState → ℝ)
    (α : ℝ) (c : Conclusion) : ℝ :=
  Real.exp (α * ∑ s : VennState,
    premPost s * Real.log (naivePost c s))

/-- **Belief Alignment (S₁, eq. 6)**: the paper's winning model.
    Scores conclusions by negative KL divergence between the reasoner's
    full posterior and the naive listener's posterior given the conclusion.

    S₁(u₃ | u₁,u₂) ∝ exp[α · −KL(L₀(·|u₁,u₂) ‖ L₀(·|u₃))]

    Uses `Core.Divergence.klDivergence` directly. -/
noncomputable def beliefAlignmentScore
    (premPost : VennState → ℝ) (naivePost : Conclusion → VennState → ℝ)
    (α : ℝ) (c : Conclusion) : ℝ :=
  Real.exp (α * (-Core.Divergence.klDivergence premPost (naivePost c)))

-- ============================================================================
-- §9. State Communication ≡ Belief Alignment
-- ============================================================================

/-- State Communication and Belief Alignment differ by an additive constant
    (the entropy H(post)) that does not depend on the conclusion.

    By `kl_eq_neg_crossEntropy_plus_negEntropy` from `Divergence.lean`:
      KL(P ∥ Q) = Σ P·log P − Σ P·log Q

    So: −KL(P ∥ Q) = Σ P·log Q − Σ P·log P = [State Com utility] + H(P).

    Since H(P) is constant in the conclusion c, it cancels in softmax
    normalization: both models produce identical conclusion distributions.
    The paper's different fit statistics (r = .67 vs .82) reflect different
    optimal α values found by MCMC, not different functional forms. -/
theorem stateCom_eq_beliefAlignment
    (premPost : VennState → ℝ) (naivePost : Conclusion → VennState → ℝ)
    (α : ℝ) (c : Conclusion)
    (hQ : ∀ s, 0 < naivePost c s) :
    beliefAlignmentScore premPost naivePost α c =
    Real.exp (α * (-(∑ s : VennState, premPost s * Real.log (premPost s)))) *
    stateComScore premPost naivePost α c := by
  simp only [beliefAlignmentScore, stateComScore]
  rw [Core.Divergence.kl_eq_neg_crossEntropy_plus_negEntropy premPost
    (naivePost c) hQ]
  rw [show α * -((_ : ℝ) - _) = α * -(∑ s, premPost s * Real.log (premPost s))
    + α * ∑ s, premPost s * Real.log (naivePost c s) from by ring]
  rw [Real.exp_add]

-- ============================================================================
-- §10. Speaker Model Properties
-- ============================================================================

/-- The Belief Alignment score for NVC depends on how much the premises
    shifted beliefs from the prior. When premises are uninformative
    (posterior ≈ prior), KL(post ‖ prior) ≈ 0, so −KL ≈ 0, and
    exp(α · 0) = 1 — the maximum score. This is why the model
    naturally produces NVC for uninformative premise combinations. -/
theorem beliefAlignment_nvc_uninformative
    (post prior : VennState → ℝ) (α : ℝ) :
    beliefAlignmentScore post (fun c => if c = .nvc then prior else fun _ => 0) α .nvc =
    Real.exp (α * (-Core.Divergence.klDivergence post prior)) := by
  simp [beliefAlignmentScore]

-- ============================================================================
-- §11. Informativity: "All" More Informative Than "Some"
-- ============================================================================

/-- Subalternation in the region model: "All A are C" entails "Some A are C"
    (when there are As). Proved by applying `subalternation_a_i` from
    `Quantifier.lean` — the generic A→I entailment for any `FiniteModel`.

    For the Belief Alignment model, this means "All A-C" produces a
    more peaked L₀ posterior than "Some A-C", yielding lower KL
    divergence and hence higher speaker utility — explaining why
    Barbara participants prefer "All" over the also-valid "Some". -/
theorem all_entails_some_AC (s : VennState)
    (hA : syllSome s hasA hasA = true)
    (h : concMeaning .allAC s = true) :
    concMeaning .someAC s = true := by
  simp only [concMeaning] at *
  unfold syllAll at h; unfold syllSome
  apply subalternation_a_i _ _ _ h
  -- Derive restrictor non-emptiness from hA
  unfold syllSome some_sem at hA
  simp only [FiniteModel.elements] at hA ⊢
  rw [List.any_eq_true] at hA ⊢
  obtain ⟨r, hr, hpred⟩ := hA
  exact ⟨r, hr, by cases r <;> simp_all [hasA]⟩

/-- Strict informativity: "All A-C" is compatible with strictly fewer states.
    Witness: `state_A_AC` has regions .A and .AC populated. Region .A has
    property A but not C, so "All A-C" fails while "Some A-C" holds
    (region .AC has both A and C). -/
private def state_A_AC : VennState
  | .A => true | .AC => true | _ => false

theorem all_strictly_stronger_than_some :
    concMeaning .someAC state_A_AC = true ∧
    concMeaning .allAC state_A_AC = false := by
  simp only [concMeaning, syllAll, syllSome, every_sem, some_sem,
    state_A_AC, FiniteModel.elements, hasA, hasC,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  decide

end Phenomena.Quantification.Studies.TesslerTenenbaumGoodman2022
