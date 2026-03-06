import Linglib.Theories.Semantics.Modality.EpistemicLogic
import Linglib.Theories.Semantics.Modality.EpistemicProbability

/-!
# Knowledge-Probability Structures

@cite{fagin-halpern-1994}

Bridges Boolean epistemic logic (`EpistemicLogic.lean`) and graded
probability operators (`EpistemicProbability.lean`) by defining
*Kripke probability structures* — the combined framework from
@cite{fagin-halpern-1994} where agents have both an information partition
(S5 accessibility) and a probability assignment at each state.

## Key contributions

1. **`KripkeKP`**: bundles `AgentAccessRel` (knowledge) + `WorldCredence`
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

## Connection to the Kratzer Pipeline

`KratzerEpistemicRSA.lean` traces the indirect path:

    Kratzer ordering → l-lifting → EpistemicSystemW → ... → RSA worldPrior

`KnowledgeProbability` provides @cite{fagin-halpern-1994}'s more direct
path: a `KripkeKP` structure already packages both the accessibility
relation (for knowledge operators) and the probability assignment
(for RSA). Under CONS, the two are coherently linked.
-/

set_option autoImplicit false

namespace Semantics.Modality.KnowledgeProbability

open Core.Proposition (BProp FiniteWorlds)
open Core.ModalLogic (AgentAccessRel AccessRel kripkeEval)
open Semantics.Modality.EpistemicLogic (knows everyoneKnows)
open Semantics.Modality.EpistemicProbability (WorldCredence nestedThreshold)

-- ============================================================================
-- §1. Kripke Probability Structures
-- ============================================================================

/-- A Kripke probability structure: agents have both an information
    partition (S5 accessibility) and a probability assignment at each state.

    This is @cite{fagin-halpern-1994}'s M = (S, π, K₁,...,Kₙ, P), where:
    - `accessRel` = the accessibility relations Kᵢ (information partitions)
    - `worldCredence` = the probability assignment P mapping (i, s) to Pᵢ,ₛ

    The truth assignment π is implicit in our framework (handled by `BProp`).
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

    @cite{fagin-halpern-1994}'s literal CONS (p. 350) says the sample space
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
  ∀ (i : E) (w : W) (φ ψ : BProp W),
    (∀ v, kp.accessRel i w v = true → φ v = ψ v) →
    kp.worldCredence i w φ = kp.worldCredence i w ψ

/-- **OBJ** (Objectivity): all agents share the same probability at
    each state. Probability differences arise only from different
    information sets, not from different priors.

    @cite{fagin-halpern-1994}'s OBJ (p. 350): Pᵢ,ₛ = Pⱼ,ₛ for all
    i, j, and s. Axiomatized by W8. -/
def OBJ {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i j : E) (w : W) (φ : BProp W),
    kp.worldCredence i w φ = kp.worldCredence j w φ

/-- **UNIF** (Uniformity): agents assign the same probability at
    indistinguishable states. If w' is accessible from w, credence
    is the same at w and w'.

    Under S5 (equivalence relations), probability is constant within
    each information cell.

    Note: @cite{fagin-halpern-1994} distinguishes UNIF (t ∈ Sᵢ,ₛ, the
    *sample space*) from SDP (t ∈ Kᵢ(s), the *accessible worlds*).
    Since our `WorldCredence` abstraction does not model explicit sample
    spaces, this definition uses accessibility (Kᵢ) and thus corresponds
    to @cite{fagin-halpern-1994}'s SDP restricted to a single agent
    rather than their literal UNIF. For finite models where Sᵢ,ₛ = Kᵢ(s)
    (which holds under CONS when the sample space equals the accessible
    worlds), the two are equivalent. Axiomatized by W9. -/
def UNIF {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i : E) (w w' : W),
    kp.accessRel i w w' = true →
    ∀ (φ : BProp W), kp.worldCredence i w φ = kp.worldCredence i w' φ

/-- **SDP** (State-determined probability): the probability distribution
    is determined by the information set.

    @cite{fagin-halpern-1994}'s SDP (p. 351) is a single-agent condition:
    for all i, s, t, if t ∈ Kᵢ(s) then Pᵢ,ₛ = Pᵢ,ₜ. Our formulation
    generalizes to the multi-agent case: if two (agent, state) pairs have
    the same accessible worlds, they have the same credence. This captures
    both FH94's SDP (set i = j) and OBJ (when agents share accessibility).
    Axiomatized by W10. -/
def SDP {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i j : E) (w w' : W),
    (∀ v, kp.accessRel i w v = kp.accessRel j w' v) →
    ∀ (φ : BProp W), kp.worldCredence i w φ = kp.worldCredence j w' φ

-- ============================================================================
-- §3. Knowledge-Probability Bridge
-- ============================================================================

/-- Normalization: the credence function assigns 1 to the trivially
    true proposition. This is @cite{fagin-halpern-1994}'s axiom W2. -/
def Normalized {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i : E) (w : W), kp.worldCredence i w (fun _ => true) = 1

/-- Nonnegativity: credences are non-negative.
    This is @cite{fagin-halpern-1994}'s axiom W1. -/
def Nonnegative {W E : Type*} (kp : KripkeKP W E) : Prop :=
  ∀ (i : E) (w : W) (φ : BProp W), 0 ≤ kp.worldCredence i w φ

/-- Measure monotonicity for world-dependent credence: each agent's
    credence function at each world is `Monotone` (from Mathlib) under
    the pointwise Bool ordering on `BProp W`.

    Since `Bool` is ordered `false ≤ true`, `φ ≤ ψ` in `W → Bool`
    means `∀ v, φ v = true → ψ v = true` — i.e., set inclusion.
    So `Monotone (wcr i w)` says: if φ ⊆ ψ then P(φ) ≤ P(ψ).

    This is a standard property of probability measures, following from
    nonnegativity + additivity (W1 + W3 of @cite{fagin-halpern-1994}).
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
      (fun (i : E) (φ : BProp W) => wcr i w φ) :=
  fun a => hMono a w

/-- Under CONS + normalization, knowledge implies probability 1.

    K_i(φ)(w) → w_i(φ)(w) = 1

    If φ is true at all i-accessible worlds, and probability is
    concentrated on accessible worlds, then φ is indistinguishable
    from truth — hence has probability 1.

    This is @cite{fagin-halpern-1994}'s axiom W7:
    K_i φ ⇒ (w_i(φ) = 1). -/
theorem knows_implies_prob_one {W E : Type*} [FiniteWorlds W]
    (kp : KripkeKP W E) (hCONS : CONS kp) (hNorm : Normalized kp)
    (i : E) (φ : BProp W) (w : W)
    (hK : knows kp.accessRel i φ w = true) :
    kp.worldCredence i w φ = 1 := by
  rw [hCONS i w φ (fun _ => true) (fun v hv => by
    unfold knows kripkeEval at hK
    exact List.all_eq_true.mp hK v
      (List.mem_filter.mpr ⟨FiniteWorlds.complete v, hv⟩))]
  exact hNorm i w

-- ============================================================================
-- §4. Probabilistic Group Operators
-- ============================================================================

/-- Probabilistic "everyone knows": every agent in the group assigns
    probability ≥ b to φ at world w.

    E_G^b(φ)(w) = ∧_{i∈G} [w_i(φ)(w) ≥ b]

    When b = 1, coincides with Boolean `everyoneKnows` (under CONS).
    This is @cite{fagin-halpern-1994}'s E_G^b operator (Section 5). -/
def everyoneProbably {W E : Type*} (wcr : WorldCredence E W)
    (group : List E) (b : ℚ) (φ : BProp W) (w : W) : Bool :=
  group.all fun i => nestedThreshold wcr b i φ w

/-- @cite{fagin-halpern-1994}'s F_G^b iteration for probabilistic common
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
    (group : List E) (b : ℚ) (φ : BProp W) : ℕ → BProp W
  | .zero => fun _ => true
  | .succ n => everyoneProbably wcr group b
      (fun w => φ w && probCKIter wcr group b φ n w)

/-- Probabilistic common knowledge: C_G^b(φ)(w) iff (F_G^b)^k(φ)(w)
    for all k = 1, ..., bound.

    @cite{fagin-halpern-1994}'s C_G^b is the greatest fixed point of
    X ⟺ E_G^b(φ ∧ X) (Lemma 5.1). The iteration `probCKIter` (F_G^b)^k
    converges to this fixed point from above.

    Unlike Boolean common knowledge, C_G^b(φ) does NOT imply φ for b < 1.
    Probabilistic CK only asserts recursive confidence: everyone assigns
    probability ≥ b to φ, everyone assigns probability ≥ b that everyone
    assigns probability ≥ b to φ, etc. -/
def commonProbKnowledge {W E : Type*} (wcr : WorldCredence E W)
    (group : List E) (b : ℚ) (φ : BProp W)
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
    (group : List E) (b : ℚ) (φ : BProp W) :
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
    (hRefl : Core.ModalLogic.Refl R) (hEucl : Core.ModalLogic.Eucl R)
    {w w' : W} (hAcc : R w w' = true) :
    ∀ v, R w v = R w' v := by
  have hSymm := Core.ModalLogic.refl_eucl_symm hRefl hEucl
  have hTrans := Core.ModalLogic.refl_eucl_trans hRefl hEucl
  intro v
  cases hR : R w v <;> cases hR' : R w' v
  · rfl
  · exact absurd (hTrans w w' v hAcc hR') (by simp [hR])
  · exact absurd (hTrans w' w v (hSymm w w' hAcc) hR) (by simp [hR'])
  · rfl

/-- SDP implies UNIF under S5 accessibility.

    @cite{fagin-halpern-1994} notes (p. 351) that CONS + SDP together
    imply UNIF. Under S5 (reflexive + Euclidean), if w' is accessible
    from w then w and w' have the same accessible worlds, so SDP with
    i = j directly gives UNIF.

    This is the semantic content of the paper's observation that
    W7 + W10 imply W9 (CONS + SDP axioms imply the UNIF axiom). -/
theorem sdp_implies_unif {W E : Type*}
    (kp : KripkeKP W E)
    (hSDP : SDP kp)
    (hS5 : ∀ i, Core.ModalLogic.Refl (kp.accessRel i) ∧
                  Core.ModalLogic.Eucl (kp.accessRel i)) :
    UNIF kp := by
  intro i w w' hAcc φ
  exact hSDP i i w w' (s5_access_eq (hS5 i).1 (hS5 i).2 hAcc) φ

-- ============================================================================
-- §6. Boolean-Probabilistic Bridge
-- ============================================================================

/-- Under CONS + normalization, Boolean everyone-knows implies
    probabilistic everyone-probably at threshold 1. -/
theorem everyoneKnows_implies_everyoneProbOne {W E : Type*} [FiniteWorlds W]
    (kp : KripkeKP W E) (hCONS : CONS kp) (hNorm : Normalized kp)
    (group : List E) (φ : BProp W) (w : W)
    (h : everyoneKnows kp.accessRel group φ w = true) :
    everyoneProbably kp.worldCredence group 1 φ w = true := by
  unfold everyoneProbably
  rw [List.all_eq_true]
  intro i hi
  simp only [nestedThreshold, decide_eq_true_eq]
  linarith [knows_implies_prob_one kp hCONS hNorm i φ w
    (EpistemicLogic.everyoneKnows_implies_knows kp.accessRel group φ w i hi h)]

-- ============================================================================
-- §7. UNIF and Introspection
-- ============================================================================

/-- Under UNIF, the threshold operator is stable across accessible worlds:
    if w' is accessible from w, `nestedThreshold θ i φ` gives the same
    value at w and w'.

    This is the formal content of @cite{fagin-halpern-1994}'s observation
    that UNIF enables introspection for probabilistic beliefs. Under UNIF,
    an i-probability formula (w_i(φ) ≥ b) has the same truth value at all
    states within an information cell, which is exactly what this theorem
    states. -/
theorem unif_threshold_stable {W E : Type*}
    (kp : KripkeKP W E) (hUNIF : UNIF kp)
    (i : E) (θ : ℚ) (φ : BProp W) (w w' : W)
    (hAcc : kp.accessRel i w w' = true) :
    nestedThreshold kp.worldCredence θ i φ w =
    nestedThreshold kp.worldCredence θ i φ w' := by
  simp only [nestedThreshold]
  rw [hUNIF i w w' hAcc φ]

/-- Under UNIF, probabilistic belief is positively introspective:
    if the agent assigns probability ≥ θ to φ, the agent *knows* this.

    w_i(φ) ≥ θ → K_i(w_i(φ) ≥ θ)

    This is @cite{fagin-halpern-1994}'s axiom W9 for the case where
    the formula is a positive i-probability formula. Combined with the
    case where w_i(φ) < θ (which gives K_i(w_i(φ) < θ)), UNIF yields
    Miller's principle: agents are always certain of their own credences.

    This is the probabilistic analogue of KD45 axiom 4 (Bφ → BBφ),
    lifting Boolean introspection to graded credence. -/
theorem unif_positive_introspection {W E : Type*} [FiniteWorlds W]
    (kp : KripkeKP W E) (hUNIF : UNIF kp)
    (i : E) (θ : ℚ) (φ : BProp W) (w : W)
    (h : nestedThreshold kp.worldCredence θ i φ w = true) :
    knows kp.accessRel i (nestedThreshold kp.worldCredence θ i φ) w = true := by
  unfold knows kripkeEval
  rw [List.all_eq_true]
  intro v hv
  rw [← unif_threshold_stable kp hUNIF i θ φ w v (List.mem_filter.mp hv).2]
  exact h

/-- Under UNIF, probabilistic belief is negatively introspective:
    if the agent assigns probability < θ to φ, the agent *knows* this.

    ¬(w_i(φ) ≥ θ) → K_i(¬(w_i(φ) ≥ θ))

    Together with `unif_positive_introspection`, this completes
    @cite{fagin-halpern-1994}'s axiom W9: under UNIF, every
    i-probability formula or its negation is known by agent i. -/
theorem unif_negative_introspection {W E : Type*} [FiniteWorlds W]
    (kp : KripkeKP W E) (hUNIF : UNIF kp)
    (i : E) (θ : ℚ) (φ : BProp W) (w : W)
    (h : nestedThreshold kp.worldCredence θ i φ w = false) :
    knows kp.accessRel i (fun v => !(nestedThreshold kp.worldCredence θ i φ v)) w = true := by
  unfold knows kripkeEval
  rw [List.all_eq_true]
  intro v hv
  have := unif_threshold_stable kp hUNIF i θ φ w v (List.mem_filter.mp hv).2
  simp [← this, h]

end Semantics.Modality.KnowledgeProbability
