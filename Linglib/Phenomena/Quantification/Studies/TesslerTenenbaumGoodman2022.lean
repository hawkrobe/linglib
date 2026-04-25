import Linglib.Theories.Semantics.Quantification.Syllogistic.Forms
import Linglib.Theories.Pragmatics.RSA.Channel
import Linglib.Theories.Pragmatics.RSA.Divergence
import Linglib.Core.Logic.Opposition.Probabilistic
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
after softmax normalization within each syllogism (the additive entropy term
H(L₀(·|premises)) is conclusion-independent and cancels in the per-syllogism softmax;
between syllogisms, this entropy varies, which is why the paper's MCMC fits report
different optimal α values for SC vs BA — same functional form, different scale).
This per-syllogism cancellation is proved as `stateCom_eq_beliefAlignment`.

## Substrate (`Semantics.Quantification.Syllogistic`)

This file consumes the syllogistic substrate at `Theories/Semantics/Quantification/`:

- `Region`, `VennState`, `AristQuant`, `Syllogism`, `Conclusion` types
- `hasA`/`hasB`/`hasC` region predicates
- `syllAll`/`syllSome`/`syllSomeNot`/`syllNone` (modern FOL reading)
- `barbara`/`allAB_allCB`/`someSome` named syllogisms
- `state_A_AC`/`state_AB_BC`/`state_ABC` witness states
- Validity (`barbara_valid`) + invalidity (`allAB_allCB_invalid`) theorems

Per footnote 2 of @cite{tessler-tenenbaum-goodman-2022}, this paper takes the
**Aristotelian** stance on the All form: "All As are Bs is false if there are no As."
The substrate is modern (FOL); existential import is added here as a paper-local
wrapper `tesslerAll`. Other Aristotelian forms (E, I, O) take the modern reading
in this paper, so the asymmetric stance is encoded honestly.

## RSA pipeline

- Noisy semantics via `RSA.Noise.noiseChannel`
- Belief Alignment utility via `RSA.Divergence.klDivergence`
- SC ≡ BA equivalence via `RSA.Divergence.kl_eq_neg_crossEntropy_plus_negEntropy`
- "Nothing follows" as vacuous utterance (true in every state)

## See also

- `Core.Opposition.Probabilistic` — the Bayesian listener's posterior
  probabilities `P_μ[c]` jointly satisfy the probabilistic Aristotelian
  inequalities (subalternation `P[A] ≤ P[I]`, contradiction `P[A]+P[O]=1`,
  etc.). Tessler's speaker models are functionals of these probabilities;
  this is the natural framework for unifying RSA-syllogistic models with
  the broader Demey–Smessaert opposition-diagram tradition.

The paper engages the mental-models tradition (Khemlani & Johnson-Laird) and
the Probability Heuristics Model @cite{chater-oaksford-1999}, fits parameters
on the Ragni et al. 2019 dataset; bib entries for the latter two are deferred
pending verified DOI/page metadata.
-/

set_option autoImplicit false

namespace TesslerTenenbaumGoodman2022

open Semantics.Quantification.Syllogistic
  (Region VennState AristQuant Syllogism Conclusion
   hasA hasB hasC syllAll syllSome syllSomeNot syllNone
   barbara allAB_allCB someSome
   state_AB_BC state_ABC state_A_AC)

-- ============================================================================
-- §1. Tessler's Aristotelian All (footnote 2)
-- ============================================================================

/-- The paper's Aristotelian "All": existential import on the restrictor.
    "All Xs are Ys" presupposes that some X exists, per footnote 2:
    "All As are Bs is false if there are no As." -/
def tesslerAll (s : VennState) (X Y : Region → Bool) : Bool :=
  syllAll s X Y && decide (∃ r : Region, s r = true ∧ X r = true)

/-- Paper-specific quantifier eval: Aristotelian on All, modern on the others. -/
def tesslerSyllQuantEval (q : AristQuant) (s : VennState)
    (X Y : Region → Bool) : Bool :=
  match q with
  | .all     => tesslerAll s X Y
  | .some    => syllSome s X Y
  | .someNot => syllSomeNot s X Y
  | .no      => syllNone s X Y

/-- Truth value of premise 1 in state s (Tessler-Aristotelian). -/
def premise1Truth (syl : Syllogism) (s : VennState) : Bool :=
  if syl.order1AB then tesslerSyllQuantEval syl.q1 s hasA hasB
  else tesslerSyllQuantEval syl.q1 s hasB hasA

/-- Truth value of premise 2 in state s (Tessler-Aristotelian). -/
def premise2Truth (syl : Syllogism) (s : VennState) : Bool :=
  if syl.order2BC then tesslerSyllQuantEval syl.q2 s hasB hasC
  else tesslerSyllQuantEval syl.q2 s hasC hasB

/-- Literal meaning of each conclusion in a Venn state, using Tessler-Aristotelian
    All. NVC ("nothing follows") is the vacuous utterance, true everywhere. -/
def concMeaning : Conclusion → VennState → Bool
  | .allAC, s      => tesslerAll s hasA hasC
  | .allCA, s      => tesslerAll s hasC hasA
  | .someAC, s     => syllSome s hasA hasC
  | .someCA, s     => syllSome s hasC hasA
  | .someNotAC, s  => syllSomeNot s hasA hasC
  | .someNotCA, s  => syllSomeNot s hasC hasA
  | .noAC, s       => syllNone s hasA hasC
  | .noCA, s       => syllNone s hasC hasA
  | .nvc, _        => true

/-- "Nothing follows" is always true. -/
@[simp] theorem nvc_always_true (s : VennState) :
    concMeaning .nvc s = true := rfl

-- ============================================================================
-- §2. Noisy Semantics via RSA.Noise.noiseChannel
-- ============================================================================

/-- Noisy semantics ℒ(u, s): a small probability φ of misjudging truth value.
    Directly instantiates `RSA.Noise.noiseChannel(1−φ, φ, ⟦u⟧)`. -/
def noisyConcMeaning (φ : ℚ) (c : Conclusion) (s : VennState) : ℚ :=
  RSA.Noise.noiseChannel (1 - φ) φ (if concMeaning c s then 1 else 0)

/-- Noise zero ⇒ noisy meaning is literal meaning. -/
theorem noisyConcMeaning_zero (c : Conclusion) (s : VennState) :
    noisyConcMeaning 0 c s = if concMeaning c s then 1 else 0 := by
  simp only [noisyConcMeaning, RSA.Noise.noiseChannel]
  split <;> ring

/-- NVC's noisy meaning is `1 − φ` everywhere — hearing "nothing follows"
    does not update the listener's beliefs. -/
theorem noisyConcMeaning_nvc (φ : ℚ) (s : VennState) :
    noisyConcMeaning φ .nvc s = 1 - φ := by
  simp only [noisyConcMeaning, concMeaning, RSA.Noise.noiseChannel, ↓reduceIte]
  ring

-- ============================================================================
-- §3. L₀ Premise Interpretation
-- ============================================================================

/-- L₀ joint likelihood of two premises in state s (unnormalized).
    The uniform prior θ = 0.5 cancels in normalization (eq. 2). -/
def l0PremiseLikelihood (φ : ℚ) (p1 p2 : VennState → Bool)
    (s : VennState) : ℚ :=
  RSA.Noise.noiseChannel (1 - φ) φ (if p1 s then 1 else 0) *
  RSA.Noise.noiseChannel (1 - φ) φ (if p2 s then 1 else 0)

-- ============================================================================
-- §4. Speaker Models (eqs. 3, 4, 6)
-- ============================================================================

/-- **S₀ (Literal Speaker, eq. 3)**: scores conclusions by expected literal
    truth under the reasoner's posterior.

    `S₀(u₃ | u₁,u₂) ∝ exp[α · Σ_s ℒ(u₃,s) · L₀(s|u₁,u₂)]` -/
noncomputable def literalSpeakerScore
    (premPost : VennState → ℝ) (α : ℝ) (c : Conclusion) : ℝ :=
  Real.exp (α * ∑ s : VennState,
    (if concMeaning c s then (1 : ℝ) else 0) * premPost s)

/-- **State Communication (S₁, eq. 4)**: standard RSA informativity.

    `S₁(u₃ | u₁,u₂) ∝ exp[α · Σ_s L₀(s|u₁,u₂) · ln L₀(s|u₃)]` -/
noncomputable def stateComScore
    (premPost : VennState → ℝ) (naivePost : Conclusion → VennState → ℝ)
    (α : ℝ) (c : Conclusion) : ℝ :=
  Real.exp (α * ∑ s : VennState,
    premPost s * Real.log (naivePost c s))

/-- **Belief Alignment (S₁, eq. 6)** — the paper's winning model.

    `S₁(u₃ | u₁,u₂) ∝ exp[α · −KL(L₀(·|u₁,u₂) ‖ L₀(·|u₃))]`

    Uses `RSA.Divergence.klDivergence` directly. -/
noncomputable def beliefAlignmentScore
    (premPost : VennState → ℝ) (naivePost : Conclusion → VennState → ℝ)
    (α : ℝ) (c : Conclusion) : ℝ :=
  Real.exp (α * (-RSA.Divergence.klDivergence premPost (naivePost c)))

-- ============================================================================
-- §5. State Communication ≡ Belief Alignment (per-syllogism)
-- ============================================================================

/-- State Communication and Belief Alignment differ by a multiplicative factor
    `exp(α · H(premPost))` that depends only on the reasoner's premise posterior,
    not on the conclusion. **Within** a single syllogism's softmax over
    conclusions, this factor cancels — the two models predict identical
    conclusion distributions. **Between** syllogisms, `H(premPost)` varies,
    so the same conclusion-distribution data is fit by *different* α values
    under SC vs BA — explaining the paper's distinct fit statistics
    (r = .67 vs .82) without any difference in functional form.

    Derivation via `kl_eq_neg_crossEntropy_plus_negEntropy`:
      KL(P ∥ Q) = Σ P·log P − Σ P·log Q
      −KL(P ∥ Q) = Σ P·log Q − Σ P·log P = [SC utility] + H(P)  -/
theorem stateCom_eq_beliefAlignment
    (premPost : VennState → ℝ) (naivePost : Conclusion → VennState → ℝ)
    (α : ℝ) (c : Conclusion)
    (hQ : ∀ s, 0 < naivePost c s) :
    beliefAlignmentScore premPost naivePost α c =
    Real.exp (α * (-(∑ s : VennState, premPost s * Real.log (premPost s)))) *
    stateComScore premPost naivePost α c := by
  simp only [beliefAlignmentScore, stateComScore]
  rw [RSA.Divergence.kl_eq_neg_crossEntropy_plus_negEntropy premPost
    (naivePost c) hQ]
  rw [show α * -((_ : ℝ) - _) = α * -(∑ s, premPost s * Real.log (premPost s))
    + α * ∑ s, premPost s * Real.log (naivePost c s) from by ring]
  rw [Real.exp_add]

/-- The Belief Alignment score for NVC, when the naive listener for NVC
    receives the prior, is `exp(α · −KL(post ‖ prior))`. When premises are
    uninformative (posterior ≈ prior), KL ≈ 0, so the NVC score approaches
    `exp(0) = 1`, the maximum — explaining the model's preference for NVC
    on uninformative premise combinations. -/
theorem beliefAlignment_nvc_uninformative
    (post prior : VennState → ℝ) (α : ℝ) :
    beliefAlignmentScore post (fun c => if c = .nvc then prior else fun _ => 0) α .nvc =
    Real.exp (α * (-RSA.Divergence.klDivergence post prior)) := by
  simp [beliefAlignmentScore]

-- ============================================================================
-- §6. Subalternation: "All A-C" entails "Some A-C"
-- ============================================================================

/-- "All A-C" entails "Some A-C" under Tessler-Aristotelian All (existential
    import is built into `tesslerAll` so the witness is free). With the
    substrate's modern `syllAll` this would require an explicit `∃A` hypothesis. -/
theorem all_entails_some_AC (s : VennState)
    (h : concMeaning .allAC s = true) :
    concMeaning .someAC s = true := by
  simp only [concMeaning, tesslerAll, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hAll, ⟨r, hsr, hAr⟩⟩ := h
  unfold concMeaning syllSome
  simp only [decide_eq_true_eq]
  refine ⟨r, ⟨hsr, hAr⟩, ?_⟩
  rw [Semantics.Quantification.Syllogistic.syllAll_eq_true_iff] at hAll
  exact hAll r ⟨hsr, hAr⟩

/-- Strict informativity: "All A-C" is compatible with strictly fewer states
    than "Some A-C". Witness: `state_A_AC`. -/
theorem all_strictly_stronger_than_some :
    concMeaning .someAC state_A_AC = true ∧
    concMeaning .allAC state_A_AC = false := by
  decide

-- ============================================================================
-- §7. L₀ Posterior (Computable in ℚ via `Finset.univ`)
-- ============================================================================

/-- Unnormalized L₀ likelihood for a syllogism in state s. -/
def l0Unnorm (φ : ℚ) (syl : Syllogism) (s : VennState) : ℚ :=
  l0PremiseLikelihood φ (premise1Truth syl) (premise2Truth syl) s

/-- Normalization constant: Σ_s L₀_unnorm(s) over all 128 Venn states.
    Uses `Finset.univ` over `VennState = Region → Bool` via `Pi.fintype`. -/
def l0Z (φ : ℚ) (syl : Syllogism) : ℚ :=
  ∑ s : VennState, l0Unnorm φ syl s

/-- Normalized L₀ posterior: L₀(s|premises) = L₀_unnorm(s) / Z. -/
def l0Post (φ : ℚ) (syl : Syllogism) (s : VennState) : ℚ :=
  l0Unnorm φ syl s / l0Z φ syl

/-- Normalization constant for naive L₀ on a single conclusion. -/
def naiveL0Z (φ : ℚ) (c : Conclusion) : ℚ :=
  ∑ s : VennState, noisyConcMeaning φ c s

/-- Naive L₀ posterior for a conclusion: L₀(s|c) ∝ ℒ(c,s).
    The naive listener has heard only the conclusion, not the premises. -/
def naiveL0Post (φ : ℚ) (c : Conclusion) (s : VennState) : ℚ :=
  noisyConcMeaning φ c s / naiveL0Z φ c

-- ============================================================================
-- §8. Figural Bias and Full Belief Alignment Pipeline
-- ============================================================================

/-- Figural bias prior weight, determined by which of A, C appears in subject
    position of one of the premises (per the paper's figural-effects discussion).

    - Both premises in A-B/B-C order (Figure 1): only A appears in subject
      position (of P1) → A-C conclusions get weight β.
    - Both in B-A/C-B order (Figure 4): only C in subject (of P2) → C-A
      conclusions get weight β.
    - Mixed (Figures 2 & 3): both or neither of A, C appear in subject
      position → no figural bias (weight 1 for all conclusions).

    NVC always gets weight 1. The paper fits β ≈ 2.01 (MAP). -/
def figuralWeight (β : ℚ) (syl : Syllogism) (c : Conclusion) : ℚ :=
  if c = .nvc then 1
  else if syl.order1AB && syl.order2BC then      -- Figure 1: prefer A-C
    if Semantics.Quantification.Syllogistic.Conclusion.isAC c then β else 1
  else if !syl.order1AB && !syl.order2BC then    -- Figure 4: prefer C-A
    if !Semantics.Quantification.Syllogistic.Conclusion.isAC c then β else 1
  else 1                                          -- Figures 2 & 3: no bias

/-- Belief Alignment score for conclusion c given syllogism syl.
    Parameters: α (rationality), φ (noise), β (figural bias). -/
noncomputable def baScore (α : ℝ) (φ β : ℚ) (syl : Syllogism)
    (c : Conclusion) : ℝ :=
  (figuralWeight β syl c : ℝ) *
  Real.exp (α * (-RSA.Divergence.klDivergence
    (fun s => (l0Post φ syl s : ℝ))
    (fun s => (naiveL0Post φ c s : ℝ))))

/-- Conclusion probability: `P(c|syl) = baScore(c) / Σ_c' baScore(c')`. -/
noncomputable def conclusionProb (α : ℝ) (φ β : ℚ) (syl : Syllogism)
    (c : Conclusion) : ℝ :=
  baScore α φ β syl c / ∑ c' : Conclusion, baScore α φ β syl c'

-- ============================================================================
-- §9. Fitted Parameters (MAP from Ragni et al. 2019 dataset)
-- ============================================================================

/-- MAP estimates from the Bayesian data analysis. α ≈ 6.88, φ ≈ 0.06,
    β ≈ 2.01. Numerical evaluation of `conclusionProb` at these parameters
    is not performed in-Lean (would require Float, banned project-wide);
    the paper's reported predictions can be reproduced via the model code
    at https://github.com/mhtessler/syllogism-paper. -/
noncomputable def α_fit : ℝ := 688 / 100
def φ_fit : ℚ := 6 / 100
def β_fit : ℚ := 201 / 100

-- ============================================================================
-- §10. L₀ Posterior Concentration
-- ============================================================================

/-- For Barbara, every state where both premises are literally true also
    satisfies "All A-C" — the L₀ posterior concentrates on All-A-C states.
    Reduces to `barbara_premises_imply_allAC` from the substrate plus the
    Tessler-Aristotelian `concMeaning` wrapping. -/
theorem barbara_l0_concentrates_on_allAC (s : VennState) :
    premise1Truth barbara s = true →
    premise2Truth barbara s = true →
    concMeaning .allAC s = true := by
  intro h1 h2
  simp only [premise1Truth, premise2Truth, barbara, ↓reduceIte,
             tesslerSyllQuantEval, tesslerAll,
             Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  obtain ⟨hAB, hExA⟩ := h1
  obtain ⟨hBC, _⟩ := h2
  unfold concMeaning tesslerAll
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, hExA⟩
  exact Semantics.Quantification.Syllogistic.barbara_valid s hAB hBC

/-- For the invalid syllogism (All A-B, All C-B), the L₀ posterior does NOT
    concentrate on any single conclusion — some consistent states satisfy
    "All A-C" while others falsify it. -/
theorem allAB_allCB_l0_does_not_concentrate :
    (premise1Truth allAB_allCB state_ABC = true ∧
     premise2Truth allAB_allCB state_ABC = true ∧
     concMeaning .allAC state_ABC = true) ∧
    (premise1Truth allAB_allCB state_AB_BC = true ∧
     premise2Truth allAB_allCB state_AB_BC = true ∧
     concMeaning .allAC state_AB_BC = false) := by
  decide

-- ============================================================================
-- §11. Probabilistic-Aristotelian constraints on the L₀ posterior
-- ============================================================================

/-- "All A-C" *properly* subalternates "Some A-C" in the Tessler-Aristotelian
    reading: All entails Some (via existential import in `tesslerAll`), and
    `state_A_AC` witnesses that the converse fails (Some without All). -/
theorem allAC_subaltern_someAC :
    Core.Opposition.Subaltern (concMeaning .allAC) (concMeaning .someAC) := by
  refine ⟨fun s h => all_entails_some_AC s h, ?_⟩
  intro hConv
  have hSome : concMeaning .someAC state_A_AC = true :=
    all_strictly_stronger_than_some.1
  have hAll : concMeaning .allAC state_A_AC = false :=
    all_strictly_stronger_than_some.2
  have := hConv state_A_AC hSome
  rw [hAll] at this
  exact Bool.noConfusion this

/-- **Probabilistic subalternation on the L₀ posterior.** Tessler's Bayesian
    listener model assigns to every conclusion `c` an L₀ posterior probability
    `μ({s | concMeaning c s = true})`. Aristotelian subalternation lifts to
    this probabilistic level: under any μ, `P_μ[allAC] ≤ P_μ[someAC]`.

    The lift is automatic via `Core.Opposition.Subaltern.toProb` once
    `allAC_subaltern_someAC` is established. The probabilistic Aristotelian
    diagram (Demey-Smessaert 2018-style, with the convex generalization in
    `Probabilistic.lean`) is implicitly the framework Tessler's Bayesian
    listener computes within. -/
theorem prob_subaltern_allAC_someAC (μ : PMF VennState) :
    Core.Opposition.ProbSubaltern μ (concMeaning .allAC) (concMeaning .someAC) :=
  allAC_subaltern_someAC.toProb μ

end TesslerTenenbaumGoodman2022
