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

Three speaker models are compared: Literal Speaker (S₀), State Communication
(standard RSA informativity), and **Belief Alignment** (utility = −KL divergence
between reasoner's posterior and naive listener's posterior). Belief Alignment
wins decisively (r = .82, 3 parameters: α, φ, β).

## Grounding in Linglib

- Syllogistic quantifiers grounded in `every_sem`/`some_sem`/`no_sem`
  from `Quantifier.lean` — applied to Venn diagram regions as entities
- Noisy semantics via `RSA.Noise.noiseChannel`
- Belief Alignment utility via `Core.Divergence.klDivergence`
- "Nothing follows" as vacuous utterance (true in every state)
- Barbara validity connects to GQ properties (`every_transitive`)
- Preference for "All" over "Some" connects to Aristotelian subalternation
-/

set_option autoImplicit false

namespace Phenomena.Quantification.Studies.TesslerTenenbaumGoodman2022

open Semantics.Lexical.Determiner.Quantifier (every_sem some_sem no_sem FiniteModel)
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
-- §3. Conclusion Space
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

    Proof: if region r is populated and has A, then by premise 1 it has B,
    and by premise 2 it has C. This is transitivity of the subset relation
    among populated regions — the same structural property captured by
    `every_transitive` in `Quantifier.lean`, applied to the region model. -/
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
    This connects to `subalternation_a_i` from `Quantifier.lean`:
    the A-form entails the I-form when the restrictor is non-empty. -/
theorem barbara_some_valid (s : VennState)
    (h1 : syllAll s hasA hasB = true)
    (h2 : syllAll s hasB hasC = true)
    (hA : syllSome s hasA hasA = true) :
    syllSome s hasA hasC = true := by
  unfold syllAll syllSome every_sem some_sem at *
  simp only [FiniteModel.elements] at *
  rw [List.all_eq_true] at h1 h2
  rw [List.any_eq_true] at hA ⊢
  obtain ⟨r, hr, hpred⟩ := hA
  exact ⟨r, hr, by
    have := h1 r hr; have := h2 r hr
    cases r <;> simp_all [hasA, hasB, hasC]⟩

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
    Directly instantiates `RSA.Noise.noiseChannel(1−φ, φ, ⟦u⟧)`.
    This is the first deep integration of `Noise.lean` into an RSA meaning
    function — establishing a reusable pattern. -/
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
    The literal listener updates beliefs by multiplying noisy semantics
    of both premises. Uses Bernoulli(θ) prior per region. -/
def l0PremiseLikelihood (φ : ℚ) (p1 p2 : VennState → Bool)
    (s : VennState) : ℚ :=
  RSA.Noise.noiseChannel (1 - φ) φ (if p1 s then 1 else 0) *
  RSA.Noise.noiseChannel (1 - φ) φ (if p2 s then 1 else 0)

-- ============================================================================
-- §8. Belief Alignment Speaker Model
-- ============================================================================

/-- Belief Alignment speaker score: the utility of conclusion c is
    −KL(reasoner's posterior ‖ naive listener's posterior given c).

    The reasoner selects the conclusion that would best convey their
    entire belief distribution to a naive listener. This is the first
    use of `Core.Divergence.klDivergence` as an RSA speaker utility.

    The `premPost` parameter is the reasoner's posterior over states
    (computed from L₀ premise interpretation in phase 1). The naive
    listener's posterior given conclusion c is `naivePost c`. -/
noncomputable def beliefAlignmentScore
    (premPost : VennState → ℝ) (naivePost : Conclusion → VennState → ℝ)
    (α : ℝ) (c : Conclusion) : ℝ :=
  Real.exp (α * (-Core.Divergence.klDivergence premPost (naivePost c)))

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
-- §9. Informativity: "All" More Informative Than "Some"
-- ============================================================================

/-- The set of states compatible with "All A are C" is a subset of those
    compatible with "Some A are C" (when there are As). This is the
    region-model instance of Aristotelian subalternation (A → I),
    which is already proved generically in `Quantifier.lean` as
    `subalternation_a_i`.

    For the Belief Alignment model, this means "All A-C" produces a
    more peaked L₀ posterior than "Some A-C", yielding lower KL
    divergence and hence higher speaker utility — explaining why
    Barbara participants prefer "All" over the also-valid "Some". -/
theorem all_entails_some_AC (s : VennState)
    (hA : syllSome s hasA hasA = true)
    (h : concMeaning .allAC s = true) :
    concMeaning .someAC s = true := by
  simp only [concMeaning] at *
  unfold syllAll syllSome every_sem some_sem at *
  simp only [FiniteModel.elements] at *
  rw [List.all_eq_true] at h
  rw [List.any_eq_true] at hA ⊢
  obtain ⟨r, hr, hpred⟩ := hA
  exact ⟨r, hr, by have := h r hr; cases r <;> simp_all [hasA, hasC]⟩

/-- Strict informativity: "All A-C" is compatible with strictly fewer states.
    Witness: s with only AC populated satisfies "Some A-C" but not "All A-C"
    (region A has property A but not C — wait, .AC has A and C; we need a
    state where .A is populated). -/
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
