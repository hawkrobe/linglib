import Linglib.Theories.Semantics.Modality.EpistemicLogic
import Linglib.Theories.Semantics.Modality.EpistemicProbability
import Mathlib.Data.Fintype.Basic

/-!
# Knowledge-Probability Structures

@cite{fagin-halpern-1994}

Bridges Boolean epistemic logic (`EpistemicLogic.lean`) and graded
probability operators (`EpistemicProbability.lean`) by defining
*Kripke probability structures* — the combined framework from
@cite{fagin-halpern-1994} where agents have both an information partition
(S5 accessibility) and a probability assignment at each state.

## Key contributions

1. **`KripkeKP`**: bundles `BAgentAccessRel` (knowledge) + `WorldCredence`
   (probability) into a single structure.

2. **Structural conditions**: CONS, OBJ, UNIF, SDP as predicates on
   `KripkeKP`, capturing how probability assignments interact with
   information partitions.

3. **Bridge theorem**: under CONS + normalization, Boolean knowledge
   (`K_i φ`) implies probability-1 belief (`w_i(φ) = 1`), which is
   @cite{fagin-halpern-1994}'s axiom W7.

4. **Probabilistic group operators**: `E_G^b` (everyone assigns probability
   ≥ b) and `C_G^b` (common probabilistic knowledge), generalizing the
   Boolean operators from `EpistemicLogic.lean`. Probabilistic CK uses
   @cite{fagin-halpern-1994}'s `F_G^b` operator (Section 5), NOT the
   naive iteration `(E_G^b)^n`.

5. **Condition hierarchy**: `sdp_implies_unif` under S5 — proves
   FH94's observation that W7 + W10 imply W9.

6. **UNIF and introspection**: uniformity yields both positive and
   negative introspection for probabilistic beliefs (axiom W9).

## Connection to the Epistemic Scale Hierarchy

The indirect path from Kratzer ordering to RSA worldPrior goes through
@cite{holliday-icard-2013}'s epistemic likelihood hierarchy:

    Kratzer ordering → l-lifting → EpistemicSystemW → ... → RSA worldPrior

`KnowledgeProbability` provides @cite{fagin-halpern-1994}'s more direct
path: a `KripkeKP` structure already packages both the accessibility
relation (for knowledge operators) and the probability assignment
(for RSA). Under CONS, the two are coherently linked.
-/

set_option autoImplicit false

namespace Semantics.Modality.KnowledgeProbability

open Core.IntensionalLogic
  (AgentAccessRel AccessRel boxR Refl Eucl refl_eucl_symm refl_eucl_trans)
open Semantics.Modality.EpistemicLogic (knows everyoneKnows)
open Semantics.Modality.EpistemicProbability (WorldCredence nestedThreshold)

-- ============================================================================
-- §1. Kripke Probability Structures
-- ============================================================================

/-- A Kripke probability structure: agents have both an information
    partition (S5 accessibility) and a probability assignment at each state.

    This is M = (S, π, K₁,...,Kₙ, P), where:
    - `accessRel` = the accessibility relations Kᵢ (information partitions)
    - `worldCredence` = the probability assignment P mapping (i, s) to Pᵢ,ₛ

    The truth assignment π is implicit in our framework (handled by `W → Bool`).
    Structural conditions (CONS, UNIF, etc.) are separate predicates. -/
structure KripkeKP (W E : Type*) where
  /-- Agent-indexed accessibility relation (information partition) -/
  accessRel : AgentAccessRel W E
  /-- World-dependent agent credence (probability spaces) -/
  worldCredence : WorldCredence E W

-- ============================================================================
-- §2. Structural Conditions
-- ============================================================================

/-- **CONS** (Consistency): each agent's probability is concentrated on
    their accessible worlds. Two propositions agreeing on all
    i-accessible worlds from w receive the same credence.

    literal CONS (p. 350) says the sample space
    Sᵢ,ₛ is a subset of Kᵢ(s). Since our `WorldCredence` abstraction does
    not model explicit sample spaces, we capture the operational consequence:
    propositions agreeing on accessible worlds receive equal credence.
    This is equivalent to CONS for finite models where all subsets are
    measurable.

    This is the key condition connecting knowledge and probability:
    it ensures the agent's probability measure "respects" their
    information partition. Without CONS, an agent could assign positive
    probability to worlds they "know" are impossible. -/
def CONS {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i : E) (w : W) (φ ψ : (W → Bool)),
    (∀ v, kp.accessRel i w v → φ v = ψ v) →
    kp.worldCredence i w φ = kp.worldCredence i w ψ

/-- **OBJ** (Objectivity): all agents share the same probability at
    each state. Probability differences arise only from different
    information sets, not from different priors.

    OBJ (p. 350): Pᵢ,ₛ = Pⱼ,ₛ for all
    i, j, and s. Axiomatized by W8. -/
def OBJ {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i j : E) (w : W) (φ : (W → Bool)),
    kp.worldCredence i w φ = kp.worldCredence j w φ

/-- **UNIF** (Uniformity): agents assign the same probability at
    indistinguishable states. If w' is accessible from w, credence
    is the same at w and w'.

    Under S5 (equivalence relations), probability is constant within
    each information cell.

    Note: distinguishes UNIF (t ∈ Sᵢ,ₛ, the
    *sample space*) from SDP (t ∈ Kᵢ(s), the *accessible worlds*).
    Since our `WorldCredence` abstraction does not model explicit sample
    spaces, this definition uses accessibility (Kᵢ) and thus corresponds
    to SDP restricted to a single agent
    rather than their literal UNIF. For finite models where Sᵢ,ₛ = Kᵢ(s)
    (which holds under CONS when the sample space equals the accessible
    worlds), the two are equivalent. Axiomatized by W9. -/
def UNIF {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i : E) (w w' : W),
    kp.accessRel i w w' →
    ∀ (φ : (W → Bool)), kp.worldCredence i w φ = kp.worldCredence i w' φ

/-- **SDP** (State-determined probability): the probability distribution
    is determined by the information set.

    SDP (p. 351) is a single-agent condition:
    for all i, s, t, if t ∈ Kᵢ(s) then Pᵢ,ₛ = Pᵢ,ₜ. Our formulation
    generalizes to the multi-agent case: if two (agent, state) pairs have
    the same accessible worlds, they have the same credence. This captures
    both FH94's SDP (set i = j) and OBJ (when agents share accessibility).
    Axiomatized by W10. -/
def SDP {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i j : E) (w w' : W),
    (∀ v, kp.accessRel i w v ↔ kp.accessRel j w' v) →
    ∀ (φ : (W → Bool)), kp.worldCredence i w φ = kp.worldCredence j w' φ

-- ============================================================================
-- §3. Knowledge-Probability Bridge
-- ============================================================================

/-- Normalization: the credence function assigns 1 to the trivially
    true proposition. This is axiom W2. -/
def Normalized {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i : E) (w : W), kp.worldCredence i w (fun _ => true) = 1

/-- Nonnegativity: credences are non-negative.
    This is axiom W1. -/
def Nonnegative {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i : E) (w : W) (φ : (W → Bool)), 0 ≤ kp.worldCredence i w φ

/-- Measure monotonicity for world-dependent credence: each agent's
    credence function at each world is `Monotone` (from Mathlib) under
    the pointwise Bool ordering on `(W → Bool)`.

    Since `Bool` is ordered `false ≤ true`, `φ ≤ ψ` in `W → Bool`
    means `∀ v, φ v = true → ψ v = true` — i.e., set inclusion.
    So `Monotone (wcr i w)` says: if φ ⊆ ψ then P(φ) ≤ P(ψ).

    This is a standard property of probability measures, following from
    nonnegativity + additivity (W1 + W3 of).
    It is the hypothesis needed for `probCKIter_monotone`.

    By reducing to Mathlib's `Monotone`, this connects to the same
    abstract notion used throughout linglib:

    - `IsUpwardEntailing = Monotone` (`Entailment/Polarity.lean`)
    - `ScopeUpwardMono ↔ ∀ R, Monotone (q R)` (`Core/Quantification.lean`)
    - `IsSumHom.monotone : Monotone f` (`Core/Mereology.lean`)
    - `MeasureMonotone ↔ ∀ i w, Monotone (wcr i w)` (this definition)

    The world-independent special case `isProbabilistic` from
    `EpistemicThreshold.lean` is identical in structure (`∀ a, Monotone`);
    `measureMonotone_isProbabilistic` projects to a fixed world. -/
def MeasureMonotone {W E : Type*} (wcr : WorldCredence E W) : Prop :=
  ∀ (i : E) (w : W), Monotone (wcr i w)

/-- `MeasureMonotone` implies `isProbabilistic` when projected to any
    fixed world. Both are `Monotone` — this just fixes the world parameter.

    This connects the FH94 probability axioms (world-dependent) to the
    LaBToM threshold semantics (world-independent via `liftCredence`). -/
theorem measureMonotone_isProbabilistic {E W : Type*}
    (wcr : WorldCredence E W) (hMono : MeasureMonotone wcr) (w : W) :
    Semantics.Attitudes.EpistemicThreshold.isProbabilistic
      (fun (i : E) (φ : (W → Bool)) => wcr i w φ) :=
  fun a => hMono a w

/-- Under CONS + normalization, knowledge implies probability 1.

    K_i(φ)(w) → w_i(φ)(w) = 1

    If φ is true at all i-accessible worlds, and probability is
    concentrated on accessible worlds, then φ is indistinguishable
    from truth — hence has probability 1.

    This is axiom W7:
    K_i φ ⇒ (w_i(φ) = 1). -/
theorem knows_implies_prob_one {W E : Type*} [Fintype W]
    (kp : KripkeKP W E) (hCONS : CONS kp) (hNorm : Normalized kp)
    (i : E) (φ : (W → Bool)) (w : W)
    (hK : knows kp.accessRel i (fun v => φ v = true) w) :
    kp.worldCredence i w φ = 1 := by
  rw [hCONS i w φ (fun _ => true) (fun v hv => by
    have : φ v = true := hK v hv
    simp [this])]
  exact hNorm i w

-- ============================================================================
-- §4. Probabilistic Group Operators
-- ============================================================================

/-- Probabilistic "everyone knows": every agent in the group assigns
    probability ≥ b to φ at world w.

    E_G^b(φ)(w) = ∧_{i∈G} [w_i(φ)(w) ≥ b]

    When b = 1, coincides with Boolean `everyoneKnows` (under CONS).
    This is E_G^b operator (Section 5). -/
def everyoneProbably {W E : Type*} (wcr : WorldCredence E W)
    (group : List E) (b : ℚ) (φ : (W → Bool)) (w : W) : Bool :=
  group.all fun i => nestedThreshold wcr b i φ w

/-- F_G^b iteration for probabilistic common
    knowledge (Section 5). Unlike the naive iteration `(E_G^b)^n`, each
    level conjoins φ with the previous level before applying E_G^b:

    (F_G^b)^0(φ) = true
    (F_G^b)^{k+1}(φ) = E_G^b(φ ∧ (F_G^b)^k(φ))

    FH94 shows that the naive definition using `(E_G^b)^k` fails:
    a 4-state counterexample (Figure 1) satisfies
    E_G^{1/2} p ∧ (E_G^{1/2})² p ∧ ⋯ at s₁ but NOT the correct
    F_G^b-based C_G^{1/2} p. The F_G^b operator correctly maintains
    φ at each iteration level, preventing this false positive. -/
def probCKIter {W E : Type*} (wcr : WorldCredence E W)
    (group : List E) (b : ℚ) (φ : (W → Bool)) : ℕ → (W → Bool)
  | .zero => fun _ => true
  | .succ n => everyoneProbably wcr group b
      (fun w => φ w && probCKIter wcr group b φ n w)

/-- Probabilistic common knowledge: C_G^b(φ)(w) iff (F_G^b)^k(φ)(w)
    for all k = 1, ..., bound.

    C_G^b is the greatest fixed point of
    X ⟺ E_G^b(φ ∧ X) (Lemma 5.1). The iteration `probCKIter` (F_G^b)^k
    converges to this fixed point from above.

    Unlike Boolean common knowledge, C_G^b(φ) does NOT imply φ for b < 1.
    Probabilistic CK only asserts recursive confidence: everyone assigns
    probability ≥ b to φ, everyone assigns probability ≥ b that everyone
    assigns probability ≥ b to φ, etc. -/
def commonProbKnowledge {W E : Type*} (wcr : WorldCredence E W)
    (group : List E) (b : ℚ) (φ : (W → Bool))
    (bound : ℕ) (w : W) : Bool :=
  (List.range bound).all fun n => probCKIter wcr group b φ (n + 1) w

/-- The F_G^b iterates are monotonically decreasing:
    (F_G^b)^{k+1}(φ) ⟹ (F_G^b)^k(φ).

    This follows because φ ∧ F^k ⊆ φ ∧ F^{k-1} (by induction) and
    probability is monotone (P(A) ≤ P(B) when A ⊆ B).
    Consequently, checking C_G^b with bound n is equivalent to checking
    just the highest level (F_G^b)^n(φ).

    The `MeasureMonotone` hypothesis requires that credence respects
    set inclusion — a standard property of probability measures that
    follows from nonnegativity + additivity (W1 + W3). -/
theorem probCKIter_monotone {W E : Type*}
    (wcr : WorldCredence E W)
    (hMono : MeasureMonotone wcr)
    (group : List E) (b : ℚ) (φ : (W → Bool)) :
    ∀ (k : ℕ) (w : W), probCKIter wcr group b φ (k + 1) w = true →
      probCKIter wcr group b φ k w = true := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ m ih =>
    intro w h
    unfold probCKIter at h ⊢
    unfold everyoneProbably at h ⊢
    rw [List.all_eq_true] at h ⊢
    intro i hi
    simp only [nestedThreshold, decide_eq_true_eq] at h ⊢
    have h_i := h i hi
    have hSub : (fun v => φ v && probCKIter wcr group b φ (m + 1) v) ≤
                (fun v => φ v && probCKIter wcr group b φ m v) :=
      fun v => by
        show (φ v && probCKIter wcr group b φ (m + 1) v) ≤
             (φ v && probCKIter wcr group b φ m v)
        cases φ v with
        | false => exact le_refl _
        | true =>
          simp only [Bool.true_and]
          cases hF : probCKIter wcr group b φ (m + 1) v with
          | false => exact Bool.false_le _
          | true => exact le_of_eq (ih v hF).symm
    linarith [hMono i w hSub]

-- ============================================================================
-- §5. Condition Hierarchy
-- ============================================================================

/-- Under S5 (reflexive + Euclidean), accessible worlds from w and w'
    coincide whenever w' is accessible from w. This is the key property
    that makes S5 relations equivalence relations: accessibility classes
    are either identical or disjoint. -/
private theorem s5_access_eq {W : Type*} {R : AccessRel W}
    (hRefl : Refl R) (hEucl : Eucl R)
    {w w' : W} (hAcc : R w w') :
    ∀ v, R w v ↔ R w' v := by
  have hSymm := refl_eucl_symm hRefl hEucl
  have hTrans := refl_eucl_trans hRefl hEucl
  intro v
  refine ⟨fun hR => ?_, fun hR' => ?_⟩
  · exact hTrans w' w v (hSymm w w' hAcc) hR
  · exact hTrans w w' v hAcc hR'

/-- SDP implies UNIF under S5 accessibility.

    notes (p. 351) that CONS + SDP together
    imply UNIF. Under S5 (reflexive + Euclidean), if w' is accessible
    from w then w and w' have the same accessible worlds, so SDP with
    i = j directly gives UNIF.

    This is the semantic content of the paper's observation that
    W7 + W10 imply W9 (CONS + SDP axioms imply the UNIF axiom). -/
theorem sdp_implies_unif {W E : Type*}
    (kp : KripkeKP W E)
    (hSDP : SDP kp)
    (hS5 : ∀ i, Refl (kp.accessRel i) ∧ Eucl (kp.accessRel i)) :
    UNIF kp := by
  intro i w w' hAcc φ
  exact hSDP i i w w' (s5_access_eq (hS5 i).1 (hS5 i).2 hAcc) φ

-- ============================================================================
-- §6. Boolean-Probabilistic Bridge
-- ============================================================================

/-- Under CONS + normalization, Boolean everyone-knows implies
    probabilistic everyone-probably at threshold 1. -/
theorem everyoneKnows_implies_everyoneProbOne {W E : Type*} [Fintype W]
    (kp : KripkeKP W E) (hCONS : CONS kp) (hNorm : Normalized kp)
    (group : List E) (φ : (W → Bool)) (w : W)
    (h : everyoneKnows kp.accessRel group (fun v => φ v = true) w) :
    everyoneProbably kp.worldCredence group 1 φ w = true := by
  unfold everyoneProbably
  rw [List.all_eq_true]
  intro i hi
  simp only [nestedThreshold, decide_eq_true_eq]
  linarith [knows_implies_prob_one kp hCONS hNorm i φ w
    (EpistemicLogic.everyoneKnows_implies_knows kp.accessRel group _ w i hi h)]

-- ============================================================================
-- §7. UNIF and Introspection
-- ============================================================================

/-- Under UNIF, the threshold operator is stable across accessible worlds:
    if w' is accessible from w, `nestedThreshold θ i φ` gives the same
    value at w and w'.

    This is the formal content of observation
    that UNIF enables introspection for probabilistic beliefs. Under UNIF,
    an i-probability formula (w_i(φ) ≥ b) has the same truth value at all
    states within an information cell, which is exactly what this theorem
    states. -/
theorem unif_threshold_stable {W E : Type*}
    (kp : KripkeKP W E) (hUNIF : UNIF kp)
    (i : E) (θ : ℚ) (φ : (W → Bool)) (w w' : W)
    (hAcc : kp.accessRel i w w') :
    nestedThreshold kp.worldCredence θ i φ w =
    nestedThreshold kp.worldCredence θ i φ w' := by
  simp only [nestedThreshold]
  rw [hUNIF i w w' hAcc φ]

/-- Under UNIF, probabilistic belief is positively introspective:
    if the agent assigns probability ≥ θ to φ, the agent *knows* this.

    w_i(φ) ≥ θ → K_i(w_i(φ) ≥ θ)

    This is axiom W9 for the case where
    the formula is a positive i-probability formula. Combined with the
    case where w_i(φ) < θ (which gives K_i(w_i(φ) < θ)), UNIF yields
    Miller's principle: agents are always certain of their own credences.

    This is the probabilistic analogue of KD45 axiom 4 (Bφ → BBφ),
    lifting Boolean introspection to graded credence. -/
theorem unif_positive_introspection {W E : Type*} [Fintype W]
    (kp : KripkeKP W E) (hUNIF : UNIF kp)
    (i : E) (θ : ℚ) (φ : (W → Bool)) (w : W)
    (h : nestedThreshold kp.worldCredence θ i φ w = true) :
    knows kp.accessRel i (fun v => nestedThreshold kp.worldCredence θ i φ v = true) w := by
  intro v hv
  rw [← unif_threshold_stable kp hUNIF i θ φ w v hv]
  exact h

/-- Under UNIF, probabilistic belief is negatively introspective:
    if the agent assigns probability < θ to φ, the agent *knows* this.

    ¬(w_i(φ) ≥ θ) → K_i(¬(w_i(φ) ≥ θ))

    Together with `unif_positive_introspection`, this completes
    axiom W9: under UNIF, every
    i-probability formula or its negation is known by agent i. -/
theorem unif_negative_introspection {W E : Type*} [Fintype W]
    (kp : KripkeKP W E) (hUNIF : UNIF kp)
    (i : E) (θ : ℚ) (φ : (W → Bool)) (w : W)
    (h : nestedThreshold kp.worldCredence θ i φ w = false) :
    knows kp.accessRel i (fun v => !(nestedThreshold kp.worldCredence θ i φ v) = true) w := by
  intro v hv
  have hStable := unif_threshold_stable kp hUNIF i θ φ w v hv
  simp [← hStable, h]

-- ============================================================================
-- §8. Axiom W5 (Null Empty)
-- ============================================================================

/-- The empty proposition has credence 0.
    This is axiom W5: w_i(false) = 0.
    In standard probability, P(∅) = 0 follows from normalization +
    additivity. We state it separately since `WorldCredence` does not
    include additivity as a structural axiom. -/
def NullEmpty {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i : E) (w : W), kp.worldCredence i w (fun _ => false) = 0

-- ============================================================================
-- §9. Miller's Principle
-- ============================================================================

/-- Miller's principle: w_i(φ) ≥ b · w_i(w_i(φ) ≥ b).

    (p. 352): under UNIF, this axiom connecting
    higher-order probabilities to first-order probabilities holds. It says
    that the agent's credence in φ is at least b times the agent's credence
    that the agent's credence in φ is at least b.

    Under UNIF, the i-probability formula (w_i(φ) ≥ b) is constant within
    each information cell (by `unif_threshold_stable`), so the inner
    credence w_i(w_i(φ) ≥ b) is either 0 or 1:

    - If w_i(φ) ≥ b: the formula is true everywhere in the cell, so
      w_i(w_i(φ) ≥ b) = 1 (by CONS + Normalized), and RHS = b ≤ w_i(φ). ✓
    - If w_i(φ) < b: the formula is false everywhere in the cell, so
      w_i(w_i(φ) ≥ b) = 0 (by CONS + NullEmpty), and RHS = 0 ≤ w_i(φ). ✓

    Miller's principle completely characterizes uniform structures
    (citing Halpern 1991). It is the
    probabilistic analogue of the KD45 introspection axioms. -/
theorem miller_principle {W E : Type*}
    (kp : KripkeKP W E)
    (hUNIF : UNIF kp) (hCONS : CONS kp)
    (hNorm : Normalized kp) (hNull : NullEmpty kp)
    (hNonneg : Nonnegative kp)
    (i : E) (b : ℚ) (φ : (W → Bool)) (w : W) :
    kp.worldCredence i w φ ≥
      b * kp.worldCredence i w (nestedThreshold kp.worldCredence b i φ) := by
  cases h : nestedThreshold kp.worldCredence b i φ w with
  | false =>
    -- threshold is false at w, hence at all accessible worlds (UNIF)
    have hAgree : ∀ v, kp.accessRel i w v →
        nestedThreshold kp.worldCredence b i φ v = (fun _ => false) v := by
      intro v hv
      have := unif_threshold_stable kp hUNIF i b φ w v hv
      simp only [h] at this; exact this.symm
    rw [hCONS i w _ _ hAgree, hNull i w, mul_zero]
    exact hNonneg i w φ
  | true =>
    -- threshold is true at w, hence at all accessible worlds (UNIF)
    have hAgree : ∀ v, kp.accessRel i w v →
        nestedThreshold kp.worldCredence b i φ v = (fun _ => true) v := by
      intro v hv
      have := unif_threshold_stable kp hUNIF i b φ w v hv
      simp only [h] at this; exact this.symm
    rw [hCONS i w _ _ hAgree, hNorm i w, mul_one]
    simp only [nestedThreshold, decide_eq_true_eq] at h
    linarith

-- ============================================================================
-- §10. Lemma 5.1: C_G^b is the Greatest Pre-Fixed-Point
-- ============================================================================

/-- **Lemma 5.1** (Section 5):
    C_G^b(φ) is the greatest fixed-point solution of
    X ⟺ E_G^b(φ ∧ X).

    This theorem proves the "greatest" direction: if ψ is a
    pre-fixed-point of the operator X ↦ E_G^b(φ ∧ X), meaning
    ψ(w) → E_G^b(φ ∧ ψ)(w), then ψ ≤ (F_G^b)^k(φ) for all k.

    Together with the trivial observation that `probCKIter` is itself
    a fixed point (by definition), this characterizes `commonProbKnowledge`
    as the greatest pre-fixed-point.

    The proof is by induction on k. The base case (k=0) is trivial since
    (F_G^b)⁰ = true. The inductive step uses `MeasureMonotone`: since
    ψ ≤ (F_G^b)^k (by IH), we have φ ∧ ψ ≤ φ ∧ (F_G^b)^k, and
    monotonicity of credence gives E_G^b(φ ∧ ψ) ≤ E_G^b(φ ∧ (F_G^b)^k)
    = (F_G^b)^{k+1}. Combined with the pre-fixed-point hypothesis
    ψ ≤ E_G^b(φ ∧ ψ), we get ψ ≤ (F_G^b)^{k+1}. -/
theorem probCK_greatest_prefixedpoint {W E : Type*}
    (wcr : WorldCredence E W) (hMono : MeasureMonotone wcr)
    (group : List E) (b : ℚ) (φ ψ : (W → Bool))
    (hPFP : ∀ w, ψ w = true →
      everyoneProbably wcr group b (fun v => φ v && ψ v) w = true) :
    ∀ k w, ψ w = true → probCKIter wcr group b φ k w = true := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ m ih =>
    intro w hψ
    unfold probCKIter everyoneProbably
    rw [List.all_eq_true]
    intro i hi
    simp only [nestedThreshold, decide_eq_true_eq]
    have hSub : (fun v => φ v && ψ v) ≤
                (fun v => φ v && probCKIter wcr group b φ m v) :=
      fun v => by
        show (φ v && ψ v) ≤ (φ v && probCKIter wcr group b φ m v)
        cases φ v with
        | false => exact le_refl _
        | true =>
          simp only [Bool.true_and]
          cases hψv : ψ v with
          | false => exact Bool.false_le _
          | true => exact le_of_eq (ih v hψv).symm
    have hPFP_i : wcr i w (fun v => φ v && ψ v) ≥ b := by
      have := hPFP w hψ
      unfold everyoneProbably at this
      have := List.all_eq_true.mp this i hi
      simp only [nestedThreshold, decide_eq_true_eq] at this
      exact this
    linarith [hMono i w hSub]

-- ============================================================================
-- §11. Figure 1 Counterexample: Naive Iteration ≠ F_G^b
-- ============================================================================

/-! ### Figure 1 Counterexample

(Section 5) shows that the "obvious" definition
of probabilistic common knowledge C_G^b as the infinite conjunction
E_G^b φ ∧ (E_G^b)² φ ∧ ··· is **incorrect**. Their 4-state counterexample
(Figure 1) demonstrates a structure where the naive iteration succeeds at
all levels but the correct F_G^b-based definition fails.

The structure M has states s₁, s₂, s₃, s₄ (encoded as Fin 4 = 0, 1, 2, 3):
- Agent 1 partitions worlds into {s₁,s₂} | {s₃,s₄}
- Agent 2 partitions worlds into {s₁,s₃} | {s₂,s₄}
- p = true at s₂ and s₃ (false at s₁ and s₄)
- Probability: uniform within first cell, all mass on s₄ in second cell

At s₁:
- E_G^{1/2} p holds (both agents assign probability 1/2 to p)
- The naive (E_G^{1/2})^k p holds for all k (stabilizes at {s₁})
- But p is FALSE at s₁, so p ∧ E_G^{1/2} p = ∅
- Therefore (F_G^{1/2})² p = E_G^{1/2}(∅) = false
- The correct C_G^{1/2} p is false at s₁ -/

section Figure1

/-- Proposition p from Figure 1: true at s₂ (1) and s₃ (2). -/
private def fig1P : (Fin 4 → Bool) := fun w =>
  match w.val with
  | 1 | 2 => true
  | _ => false

/-- Figure 1 credence function (SDP structure).
    Agent 0 at s₁,s₂: uniform on {s₁, s₂}
    Agent 0 at s₃,s₄: mass 1 on s₄
    Agent 1 at s₁,s₃: uniform on {s₁, s₃}
    Agent 1 at s₂,s₄: mass 1 on s₄ -/
private def fig1Credence : WorldCredence (Fin 2) (Fin 4) :=
  fun agent world φ =>
    let b (w : Fin 4) : ℚ := if φ w then 1 else 0
    match agent.val, world.val with
    | 0, 0 | 0, 1 => 1/2 * b 0 + 1/2 * b 1
    | 0, _ => b 3
    | _, 0 | _, 2 => 1/2 * b 0 + 1/2 * b 2
    | _, _ => b 3

private def fig1Group : List (Fin 2) := [0, 1]

/-- Naive iteration (E_G^b)^k: just iterates everyoneProbably without
    conjoining φ at each level. This is the **incorrect** definition
    that shows fails for probabilistic CK.
    Compare with `probCKIter` which uses the correct F_G^b operator. -/
def naiveIter {W E : Type*} (wcr : WorldCredence E W)
    (group : List E) (b : ℚ) (φ : (W → Bool)) : ℕ → (W → Bool)
  | .zero => φ
  | .succ n => everyoneProbably wcr group b (naiveIter wcr group b φ n)

/-- At s₁, the naive iteration succeeds at level 1: E_G^{1/2} p is true. -/
theorem fig1_naive_level1 :
    naiveIter fig1Credence fig1Group (1/2) fig1P 1 0 = true := by native_decide

/-- At s₁, the naive iteration succeeds at level 2: (E_G^{1/2})² p is true. -/
theorem fig1_naive_level2 :
    naiveIter fig1Credence fig1Group (1/2) fig1P 2 0 = true := by native_decide

/-- The naive iteration stabilizes after level 1 (pointwise on all worlds). -/
private theorem fig1_naive_stable :
    ∀ w : Fin 4,
      naiveIter fig1Credence fig1Group (1/2) fig1P 2 w =
      naiveIter fig1Credence fig1Group (1/2) fig1P 1 w := by native_decide

/-- All naive levels ≥ 1 agree pointwise with level 1. -/
private theorem fig1_naive_eq_one :
    ∀ k, naiveIter fig1Credence fig1Group (1/2) fig1P (k + 1) =
         naiveIter fig1Credence fig1Group (1/2) fig1P 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ m ih =>
    show everyoneProbably fig1Credence fig1Group (1/2)
      (naiveIter fig1Credence fig1Group (1/2) fig1P (m + 1)) =
      naiveIter fig1Credence fig1Group (1/2) fig1P 1
    rw [ih]
    exact funext fig1_naive_stable

/-- The naive iteration succeeds at s₁ for ALL levels k ≥ 1.
    Since levels 1 and 2 agree pointwise, all higher levels also agree. -/
theorem fig1_naive_all_levels :
    ∀ k, naiveIter fig1Credence fig1Group (1/2) fig1P (k + 1) 0 = true := by
  intro k
  rw [show naiveIter fig1Credence fig1Group (1/2) fig1P (k + 1) =
          naiveIter fig1Credence fig1Group (1/2) fig1P 1 from fig1_naive_eq_one k]
  native_decide

/-- At s₁, the CORRECT F_G^{1/2} iteration fails at level 2.
    This is because p ∧ E_G^{1/2} p = ∅ (p is false at s₁,
    the only world where E_G^{1/2} p holds). -/
theorem fig1_correct_level2_false :
    probCKIter fig1Credence fig1Group (1/2) fig1P 2 0 = false := by native_decide

/-- **The core counterexample**: the naive iteration succeeds at s₁ where
    the correct F_G^b-based definition fails. This proves that the
    definitions are genuinely different and justifies FH94's use of the
    F_G^b operator for probabilistic common knowledge. -/
theorem fig1_naive_vs_correct :
    (∀ k, naiveIter fig1Credence fig1Group (1/2) fig1P (k + 1) 0 = true) ∧
    probCKIter fig1Credence fig1Group (1/2) fig1P 2 0 = false :=
  ⟨fig1_naive_all_levels, fig1_correct_level2_false⟩

end Figure1

end Semantics.Modality.KnowledgeProbability
