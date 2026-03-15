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

/-- "All Xs are Ys" in state s: every populated X-region also has Y,
    AND there is at least one populated X-region (existential import).

    Per @cite{tessler-tenenbaum-goodman-2022} footnote 4: "All As are Bs
    is false if there are no As." This ensures All entails Some.
    Grounded in `every_sem` and `some_sem` from `Quantifier.lean`. -/
def syllAll (s : VennState) (X Y : Region → Bool) : Bool :=
  every_sem regionModel (fun r => s r && X r) Y &&
  some_sem regionModel (fun r => s r && X r) (fun _ => true)

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
-- §3. Premise and Conclusion Space
-- ============================================================================

/-- Syllogistic quantifier: the four Aristotelian quantifiers. -/
inductive SyllQuant where
  | all | some | someNot | no
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype SyllQuant where
  elems := {.all, .some, .someNot, .no}
  complete := fun x => by cases x <;> simp

/-- A syllogism is a pair of quantified premises sharing middle term B.
    `order1AB = true` means premise 1 is "Q₁ A-B"; false means "Q₁ B-A".
    `order2BC = true` means premise 2 is "Q₂ B-C"; false means "Q₂ C-B".
    This gives 4 × 2 × 4 × 2 = 64 syllogisms. -/
structure Syllogism where
  q1 : SyllQuant
  order1AB : Bool
  q2 : SyllQuant
  order2BC : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

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

/-- Figural bias prior weight, determined by the Aristotelian figure.

    The "figural effect" biases toward conclusions whose end-term order
    matches the chain direction through the middle term B:
    - **Figure 1** (A-B, B-C): B is predicate of P1, subject of P2 →
      chain reads A→B→C → **A-C** conclusions get weight β
    - **Figure 4** (B-A, C-B): B is subject of P1, predicate of P2 →
      chain reads C→B→A → **C-A** conclusions get weight β
    - **Figures 2 & 3**: B occupies the same position in both premises →
      no directional chain → all conclusions get weight 1

    NVC always gets weight 1 (no directional bias for "nothing follows").
    The paper fits β ≈ 2.01 (MAP). -/
def figuralWeight (β : ℚ) (syl : Syllogism) (c : Conclusion) : ℚ :=
  if c = .nvc then 1
  else if syl.order1AB && syl.order2BC then      -- Figure 1: A-B, B-C → prefer A-C
    if c.isAC then β else 1
  else if !syl.order1AB && !syl.order2BC then    -- Figure 4: B-A, C-B → prefer C-A
    if !c.isAC then β else 1
  else 1                                          -- Figures 2 & 3: no bias

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
  unfold syllAll at *
  simp only [Bool.and_eq_true] at *
  obtain ⟨h1e, h1s⟩ := h1
  obtain ⟨h2e, _⟩ := h2
  constructor
  · -- every_sem: every populated A-region has C
    unfold every_sem at *
    simp only [FiniteModel.elements] at *
    rw [List.all_eq_true] at *
    intro r hr
    have h1r := h1e r hr
    have h2r := h2e r hr
    cases r <;> simp_all [hasA, hasB, hasC]
  · -- some_sem: there exists a populated A-region (inherited from h1)
    exact h1s

/-- Barbara also validates "Some A are C" (by subalternation: All → Some).
    Uses `barbara_valid` for the All A-C premise, then extracts the
    existential import — with existential import in `syllAll`, the
    non-emptiness hypothesis is built in, so no separate witness needed. -/
theorem barbara_some_valid (s : VennState)
    (h1 : syllAll s hasA hasB = true)
    (h2 : syllAll s hasB hasC = true) :
    syllSome s hasA hasC = true := by
  have hAllAC := barbara_valid s h1 h2
  unfold syllAll at hAllAC
  simp only [Bool.and_eq_true] at hAllAC
  obtain ⟨hEvery, hSome⟩ := hAllAC
  -- hEvery : every populated A-region has C
  -- hSome : there exists a populated A-region
  unfold syllSome
  unfold every_sem at hEvery; unfold some_sem at hSome ⊢
  simp only [FiniteModel.elements] at *
  rw [List.any_eq_true] at hSome ⊢
  rw [List.all_eq_true] at hEvery
  obtain ⟨r, hr, hpop⟩ := hSome
  exact ⟨r, hr, by have := hEvery r hr; cases r <;> simp_all [hasA, hasC]⟩

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

/-- Subalternation in the region model: "All A are C" entails "Some A are C".
    With existential import built into `syllAll`, no separate non-emptiness
    hypothesis is needed — `syllAll` guarantees at least one A exists.

    For the Belief Alignment model, this means "All A-C" produces a
    more peaked L₀ posterior than "Some A-C", yielding lower KL
    divergence and hence higher speaker utility — explaining why
    Barbara participants prefer "All" over the also-valid "Some". -/
theorem all_entails_some_AC (s : VennState)
    (h : concMeaning .allAC s = true) :
    concMeaning .someAC s = true := by
  simp only [concMeaning] at *
  unfold syllAll at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hEvery, hSome⟩ := h
  -- hEvery : every populated A-region has C
  -- hSome : there exists a populated A-region (existential import)
  unfold syllSome; unfold every_sem at hEvery; unfold some_sem at hSome ⊢
  simp only [FiniteModel.elements] at *
  rw [List.any_eq_true] at hSome ⊢
  rw [List.all_eq_true] at hEvery
  obtain ⟨r, hr, hpop⟩ := hSome
  exact ⟨r, hr, by have := hEvery r hr; cases r <;> simp_all [hasA, hasC]⟩

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

-- ============================================================================
-- §12. Premise Evaluation and Named Syllogisms
-- ============================================================================

/-- Evaluate a syllogistic quantifier on given terms in a Venn state. -/
def syllQuantEval (q : SyllQuant) (s : VennState) (X Y : Region → Bool) : Bool :=
  match q with
  | .all => syllAll s X Y
  | .some => syllSome s X Y
  | .someNot => syllSomeNot s X Y
  | .no => syllNone s X Y

/-- Truth value of premise 1 in state s. -/
def premise1Truth (syl : Syllogism) (s : VennState) : Bool :=
  if syl.order1AB then syllQuantEval syl.q1 s hasA hasB
  else syllQuantEval syl.q1 s hasB hasA

/-- Truth value of premise 2 in state s. -/
def premise2Truth (syl : Syllogism) (s : VennState) : Bool :=
  if syl.order2BC then syllQuantEval syl.q2 s hasB hasC
  else syllQuantEval syl.q2 s hasC hasB

-- Named syllogisms

/-- Barbara: All A-B, All B-C. Figure 1 (paradigmatic valid syllogism). -/
def barbara : Syllogism := ⟨.all, true, .all, true⟩

/-- All A-B, All C-B. Figure 3 (paradigmatic invalid syllogism). -/
def allAB_allCB : Syllogism := ⟨.all, true, .all, false⟩

/-- Some A-B, Some B-C. Figure 1. -/
def someSome : Syllogism := ⟨.some, true, .some, true⟩

-- ============================================================================
-- §13. L₀ Posterior (Computable in ℚ)
-- ============================================================================

/-- All 128 Venn diagram states, enumerated for computable summation.
    Each state is a function `Region → Bool` indicating which regions
    are populated. Generated by the List monad over all 7 regions. -/
def allStates : List VennState := do
  let a ← [true, false]; let b ← [true, false]; let c ← [true, false]
  let ab ← [true, false]; let ac ← [true, false]; let bc ← [true, false]
  let abc ← [true, false]
  pure fun | .A => a | .B => b | .C => c | .AB => ab
           | .AC => ac | .BC => bc | .ABC => abc

/-- Unnormalized L₀ likelihood for a syllogism in state s.
    Computes ℒ(p₁,s) · ℒ(p₂,s) where ℒ is noisy semantics.
    The uniform prior (θ = 0.5) cancels in normalization. -/
def l0Unnorm (φ : ℚ) (syl : Syllogism) (s : VennState) : ℚ :=
  l0PremiseLikelihood φ (premise1Truth syl) (premise2Truth syl) s

/-- Normalization constant: Σ_s L₀_unnorm(s). Computable via `allStates`. -/
def l0Z (φ : ℚ) (syl : Syllogism) : ℚ :=
  (allStates.map (l0Unnorm φ syl)).sum

/-- Normalized L₀ posterior: L₀(s|premises) = L₀_unnorm(s) / Z. -/
def l0Post (φ : ℚ) (syl : Syllogism) (s : VennState) : ℚ :=
  l0Unnorm φ syl s / l0Z φ syl

/-- Normalization constant for naive L₀ on a single conclusion. -/
def naiveL0Z (φ : ℚ) (c : Conclusion) : ℚ :=
  (allStates.map (noisyConcMeaning φ c)).sum

/-- Naive L₀ posterior for a conclusion: L₀(s|c) ∝ ℒ(c,s).
    The naive listener has heard only the conclusion, not the premises. -/
def naiveL0Post (φ : ℚ) (c : Conclusion) (s : VennState) : ℚ :=
  noisyConcMeaning φ c s / naiveL0Z φ c

-- ============================================================================
-- §14. Full Belief Alignment Pipeline (noncomputable, over ℝ)
-- ============================================================================

/-- Belief Alignment score for conclusion c given syllogism syl.
    Uses the full pipeline: premises → L₀ posterior → KL → exp.
    Parameters: α (rationality), φ (noise), β (figural bias). -/
noncomputable def baScore (α : ℝ) (φ β : ℚ) (syl : Syllogism)
    (c : Conclusion) : ℝ :=
  (figuralWeight β syl c : ℝ) *
  Real.exp (α * (-Core.Divergence.klDivergence
    (fun s => (l0Post φ syl s : ℝ))
    (fun s => (naiveL0Post φ c s : ℝ))))

/-- Conclusion probability: P(c|syl) = baScore(c) / Σ_c' baScore(c'). -/
noncomputable def conclusionProb (α : ℝ) (φ β : ℚ) (syl : Syllogism)
    (c : Conclusion) : ℝ :=
  baScore α φ β syl c / ∑ c' : Conclusion, baScore α φ β syl c'

-- ============================================================================
-- §15. Fitted Parameters
-- ============================================================================

/-- MAP estimates from the Bayesian data analysis on Ragni et al. 2019 data.
    α ≈ 6.88, φ ≈ 0.06, β ≈ 2.01. -/
noncomputable def α_fit : ℝ := 688 / 100
def φ_fit : ℚ := 6 / 100
def β_fit : ℚ := 201 / 100

-- ============================================================================
-- §16. Float-Based Numerical Evaluation
-- ============================================================================

/-- Convert ℚ to Float for numerical evaluation. -/
private def ratToFloat (q : ℚ) : Float :=
  let num : Float := match q.num with
    | .ofNat n => n.toFloat
    | .negSucc n => -(n + 1).toFloat
  num / q.den.toFloat

/-- KL divergence over `allStates` in Float arithmetic.
    Skips states with P(s) = 0 (contributes 0 to KL by convention). -/
def klFloat (P Q : VennState → Float) : Float :=
  allStates.foldl (fun acc s =>
    let p := P s
    let q := Q s
    if p > 0 then acc + p * (Float.log p - Float.log q)
    else acc) 0.0

/-- All 9 conclusions as a list. -/
def allConclusions : List Conclusion :=
  [.allAC, .allCA, .someAC, .someCA, .someNotAC, .someNotCA, .noAC, .noCA, .nvc]

/-- Compute conclusion distribution for a syllogism using Float arithmetic.
    L₀ posteriors are computed exactly in ℚ (via `l0Post`, `naiveL0Post`),
    then converted to Float for the KL divergence and softmax steps.
    Parameters: α (rationality, Float), φ and β (exact in ℚ). -/
def predictFloat (α : Float) (φ β : ℚ) (syl : Syllogism) :
    List (Conclusion × Float) :=
  -- L₀ posterior (exact in ℚ, converted to Float)
  let postFloat : VennState → Float := fun s => ratToFloat (l0Post φ syl s)
  -- For each conclusion, compute BA score
  let scores := allConclusions.map fun c =>
    let naiveFloat : VennState → Float := fun s => ratToFloat (naiveL0Post φ c s)
    let kl := klFloat postFloat naiveFloat
    let figural := ratToFloat (figuralWeight β syl c)
    (c, figural * Float.exp (α * (-kl)))
  -- Normalize
  let total := (scores.map Prod.snd).foldl (· + ·) 0.0
  scores.map fun (c, v) => (c, v / total)

/-- Short name for display. -/
def Conclusion.short : Conclusion → String
  | .allAC => "Aac" | .allCA => "Aca"
  | .someAC => "Iac" | .someCA => "Ica"
  | .someNotAC => "Oac" | .someNotCA => "Oca"
  | .noAC => "Eac" | .noCA => "Eca"
  | .nvc => "NVC"

/-- Compact string output for a syllogism's predicted distribution,
    showing conclusions sorted by predicted probability. -/
def showPrediction (α : Float) (φ β : ℚ) (syl : Syllogism) : String :=
  let preds := predictFloat α φ β syl
  let sorted := preds.toArray.qsort (fun a b => a.2 > b.2) |>.toList
  String.intercalate ", " <| sorted.filterMap fun (c, p) =>
    let pct := Float.toString (p * 100) |>.take 5
    if p > 0.005 then some s!"{c.short}:{pct}%" else none

-- Verified numerical predictions (α=6.88, φ=0.06, β=2.01):
-- (with existential import: "All Xs are Ys" requires Xs to exist)
--
-- Fig 1: Barbara (All A-B, All B-C)   → Aac:96.69%  (A-C bias)
-- Fig 3: All A-B, All C-B (invalid)   → NVC:73.83%, Aac=Aca:6.94%  (no bias)
-- Fig 1: Some A-B, Some B-C           → Iac:41.42%, NVC:26.54%, Ica:20.60%
-- Fig 4: All B-A, All C-B             → Aca:96.69%  (C-A bias, mirror of Fig 1)
-- Fig 2: All B-A, All B-C             → Ica=Iac:35.26%, NVC:17.04%  (no bias)
--
-- #eval showPrediction 6.88 φ_fit β_fit barbara
-- #eval showPrediction 6.88 φ_fit β_fit allAB_allCB
-- #eval showPrediction 6.88 φ_fit β_fit someSome

-- ============================================================================
-- §17. L₀ Posterior Concentration (Computable Verification)
-- ============================================================================

/-- For Barbara (All A-B, All B-C), every L₀-probable state satisfies
    All A-C. Proof: states where both premises are literally true form
    a subset of states where All A-C holds (by `barbara_valid`).

    With noise φ, the L₀ posterior concentrates on these states: the
    likelihood ℒ(p₁,s)·ℒ(p₂,s) is (1−φ)² for consistent states but
    only (1−φ)·φ, φ·(1−φ), or φ² for inconsistent ones.

    This theorem verifies computably that every state where BOTH premises
    are literally true also satisfies All A-C — the semantic backbone
    of the Belief Alignment model's "All A-C" preference for Barbara. -/
theorem barbara_l0_concentrates_on_allAC (s : VennState) :
    premise1Truth barbara s = true →
    premise2Truth barbara s = true →
    concMeaning .allAC s = true := by
  intro h1 h2
  simp only [premise1Truth, premise2Truth, barbara, ↓reduceIte, syllQuantEval] at h1 h2
  exact barbara_valid s h1 h2

/-- For the invalid syllogism (All A-B, All C-B), the L₀ posterior does NOT
    concentrate on any single conclusion — some consistent states satisfy
    All A-C while others falsify it. -/
theorem allAB_allCB_l0_does_not_concentrate :
    -- state_ABC satisfies both premises AND All A-C
    (premise1Truth allAB_allCB state_ABC = true ∧
     premise2Truth allAB_allCB state_ABC = true ∧
     concMeaning .allAC state_ABC = true) ∧
    -- state_AB_BC satisfies both premises but NOT All A-C
    (premise1Truth allAB_allCB state_AB_BC = true ∧
     premise2Truth allAB_allCB state_AB_BC = true ∧
     concMeaning .allAC state_AB_BC = false) := by
  simp only [premise1Truth, premise2Truth, allAB_allCB, ↓reduceIte, syllQuantEval,
    concMeaning, syllAll, every_sem, state_ABC, state_AB_BC,
    FiniteModel.elements, hasA, hasB, hasC,
    List.all_cons, List.all_nil]
  decide

end Phenomena.Quantification.Studies.TesslerTenenbaumGoodman2022
