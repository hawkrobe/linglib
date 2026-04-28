import Linglib.Theories.Semantics.Modality.Orthologic.Frames
import Linglib.Theories.Semantics.Modality.Orthologic.Modal
import Linglib.Theories.Semantics.Modality.Orthologic.RegularProp
import Linglib.Phenomena.Modality.Studies.Yalcin2007
import Linglib.Phenomena.Modality.Studies.Mandelkern2019
import Linglib.Phenomena.Modality.Studies.KlinedinstRothschild2012

/-!
# @cite{holliday-mandelkern-2024}: Possibility-Semantics Case Studies

@cite{holliday-mandelkern-2024}

Concrete instantiations and paper-specific theorems from H&M 2024
"The Orthologic of Epistemic Modals" (JPL 2024). The general substrate
(compatibility frames, ortholattice of regular sets, modal compat frames,
T/epistemic frames) lives in
`Linglib/Theories/Semantics/Modality/Orthologic/{Frames,Modal}.lean`
(plus `Linglib/Core/Order/Ortholattice.lean` for the abstract typeclass);
this file collects the paper's worked examples and the decide-checked
predictions that depend on them.

## What's formalized

- The five-possibility path frame `Poss5` (Example 4.11, Figure 7).
- The Epistemic Scale `epistemicScale` over `Poss5` (Example 4.30, Figure 12;
  Example 4.33, Figure 13).
- Ortholattice properties of the path-frame regular subsets:
  De Morgan-style negations, double negation, excluded middle,
  non-contradiction, the canonical distributivity failure at x₃.
- Epistemic-scale predictions for `p`, `□p`, `◇p` and their negations.
- Wittgenstein's Law instantiated on the Epistemic Scale (Proposition 4.27).
- Disjunctive-syllogism failure, orthomodularity failure,
  pseudocomplementation failure (paper §2 desiderata, §3.1.1 algebraic
  counterexamples re-derived in possibility semantics).
- Within-level Boolean classicality vs. cross-level failure (§3.2.4).
- Lifting from the two-world Boolean model `W = {0, 1}, V(p) = {0}`
  (Example 5.3, Lemma 5.4): `worldlyA0`/`worldlyA1`/`worldlyI0`/`worldlyI1`
  + agreement of derived compat/access with `pathFrame`/`epistemicScale`
  + truth of `p`/`□p`/`◇p` from world membership in `A`/`I`.

## Out of scope (deferred)

- General lifting from arbitrary Boolean algebra `B` (Definition 5.1).
  The current file specializes `B = ℘({0, 1})`; the construction
  `B^e = ⟨S, ◇, R⟩` for arbitrary `B` is unformalized and would belong
  in `Theories/Semantics/Modality/Orthologic/Lifting.lean` once added.
- Modal ortho-Boolean lattice typeclasses (Definitions 3.15-3.32) that
  would let `within_level_distrib` derive from the algebraic structure
  rather than `decide` on `Poss5`.
- Comparison theorems against `Phenomena/Modality/FreeChoice.lean`
  (the orthogonal phenomenon HM 2024 also addresses; HM's account
  predicts free-choice failure at x₁ — `free_choice_fails_at_x1` — but
  the cross-paper agreement bridge is unwritten).
-/

namespace Phenomena.Modality.Studies.HollidayMandelkern2024

open Semantics.Modality.Orthologic

-- ════════════════════════════════════════════════════
-- § 1. The Five-Possibility Path Frame (Example 4.11, Figure 7)
-- ════════════════════════════════════════════════════

/-- Five possibilities arranged in a path: x₁—x₂—x₃—x₄—x₅.
    The canonical 5-possibility example used by H&M for epistemic-modal
    applications. Note: Example 4.12 shows a strictly smaller (4-element)
    frame whose ortholattice is also non-Boolean — the path frame is the
    canonical illustrative example, not the smallest non-Boolean instance.
    @cite{holliday-mandelkern-2024} Example 4.11, Figure 7. -/
inductive Poss5 where
  | x1 | x2 | x3 | x4 | x5
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Poss5 where
  elems := {.x1, .x2, .x3, .x4, .x5}
  complete := fun w => by cases w <;> simp

/-- Compatibility on the path frame: a possibility is compatible with itself
    and with each of its two neighbors. -/
def Poss5.compat : Poss5 → Poss5 → Prop
  | .x1, .x1 | .x1, .x2 | .x2, .x1
  | .x2, .x2 | .x2, .x3 | .x3, .x2
  | .x3, .x3 | .x3, .x4 | .x4, .x3
  | .x4, .x4 | .x4, .x5 | .x5, .x4
  | .x5, .x5 => True
  | _, _ => False

instance : DecidableRel Poss5.compat := fun a b => by
  cases a <;> cases b <;> simp only [Poss5.compat] <;> infer_instance

/-- The path compatibility frame: adjacent possibilities are compatible. -/
def pathFrame : CompatFrame Poss5 where
  compat := Poss5.compat
  compat_refl := fun x => by cases x <;> simp [Poss5.compat]
  compat_symm := fun x y => by cases x <;> cases y <;> simp [Poss5.compat]

instance : DecidableRel pathFrame.compat :=
  inferInstanceAs (DecidableRel Poss5.compat)

-- Propositions in the path frame ortholattice (typed as Set so substrate
-- Decidable instances `[DecidablePred (· ∈ A)]` resolve cleanly).
private def pLeft : Set Poss5 := fun x => match x with | .x1 | .x2 => True | _ => False
private def pRight : Set Poss5 := fun x => match x with | .x4 | .x5 => True | _ => False
private def pMid : Set Poss5 := fun x => match x with | .x3 => True | _ => False

private instance pLeft_dec : DecidablePred pLeft := fun x => by
  cases x <;> (unfold pLeft; first | exact isTrue trivial | exact isFalse id)
private instance pRight_dec : DecidablePred pRight := fun x => by
  cases x <;> (unfold pRight; first | exact isTrue trivial | exact isFalse id)
private instance pMid_dec : DecidablePred pMid := fun x => by
  cases x <;> (unfold pMid; first | exact isTrue trivial | exact isFalse id)

-- ════════════════════════════════════════════════════
-- § 2. Path-Frame Ortholattice Properties
-- ════════════════════════════════════════════════════


/-- Negation: ¬{x₁,x₂} = {x₄,x₅}. -/
theorem neg_left (x : Poss5) : orthoNeg pathFrame pLeft x ↔ pRight x := by
  cases x <;> decide

/-- Negation: ¬{x₄,x₅} = {x₁,x₂}. -/
theorem neg_right (x : Poss5) : orthoNeg pathFrame pRight x ↔ pLeft x := by
  cases x <;> decide

/-- Negation: ¬{x₃} = {x₁,x₅}. The "partial" possibility x₃ has a
    non-trivial negation — neither left nor right, but the two endpoints. -/
private def pEndpoints : Set Poss5 := fun x =>
    match x with | .x1 | .x5 => True | _ => False

private instance pEndpoints_dec : DecidablePred pEndpoints := fun x => by
  cases x <;> (unfold pEndpoints; first | exact isTrue trivial | exact isFalse id)

theorem neg_mid (x : Poss5) : orthoNeg pathFrame pMid x ↔ pEndpoints x := by
  cases x <;> decide

/-- Double negation: ¬¬A = A (involutive on regular sets). -/
theorem doubleNeg_left (x : Poss5) :
    orthoNeg pathFrame (orthoNeg pathFrame pLeft) x ↔ pLeft x := by
  cases x <;> decide

/-- Excluded middle: A ∨ ¬A = S (every possibility verifies it). -/
theorem excludedMiddle_left (x : Poss5) :
    disj pathFrame pLeft (orthoNeg pathFrame pLeft) x := by
  cases x <;> decide

/-- Non-contradiction: A ∧ ¬A = ∅ (no possibility verifies it). -/
theorem nonContradiction_left (x : Poss5) :
    ¬ conj pLeft (orthoNeg pathFrame pLeft) x := by
  cases x <;> decide

/-- **Distributivity failure.** The key result of possibility semantics.
    C ∧ (A ∨ B) ≠ (C ∧ A) ∨ (C ∧ B), where C = {x₃}, A = {x₁,x₂}, B = {x₄,x₅}.
    Possibility x₃ is compatible with both A and B worlds, so it makes
    A ∨ B true; but it doesn't commit to either disjunct, so neither
    C ∧ A nor C ∧ B is non-empty.
    @cite{holliday-mandelkern-2024} Example 4.33 (the path-frame
    instantiation; the algebraic version is Example 3.20, Figure 3).
    Figure 8 enumerates the ten ◇-regular subsets of `pathFrame`;
    the distributivity discussion appears in the prose following
    Proposition 4.27. -/
theorem distributivity_failure :
    conj pMid (disj pathFrame pLeft pRight) .x3 ∧
    ¬ disj pathFrame (conj pMid pLeft) (conj pMid pRight) .x3 := by decide

/-- The LHS of distributivity at x₃: true (x₃ makes C ∧ (A ∨ B) true). -/
theorem distrib_lhs_at_x3 :
    conj pMid (disj pathFrame pLeft pRight) .x3 := by decide

/-- The RHS of distributivity at x₃: false (x₃ fails (C∧A) ∨ (C∧B)). -/
theorem distrib_rhs_at_x3 :
    ¬ disj pathFrame (conj pMid pLeft) (conj pMid pRight) .x3 := by decide

-- ════════════════════════════════════════════════════
-- § 3. Worlds and Regularity on the Path Frame
-- ════════════════════════════════════════════════════

/-- x₁ is a world (maximal possibility). -/
theorem x1_is_world : isWorld pathFrame .x1 := by decide

/-- x₅ is a world. -/
theorem x5_is_world : isWorld pathFrame .x5 := by decide

/-- x₃ is NOT a world — it's a partial possibility, compatible with
    possibilities on both sides without being a refinement of either. -/
theorem x3_not_world : ¬ isWorld pathFrame .x3 := by decide

/-- All propositions in the ortholattice are regular. -/
theorem regular_left : isRegular pathFrame pLeft := by decide
theorem regular_right : isRegular pathFrame pRight := by decide
theorem regular_mid : isRegular pathFrame pMid := by decide

theorem regular_empty : isRegular pathFrame (∅ : Set Poss5) := by
  intro x
  exact Or.inr ⟨x, pathFrame.compat_refl x, fun _ _ h => h⟩
theorem regular_full : isRegular pathFrame (Set.univ : Set Poss5) := by
  intro x
  exact Or.inl trivial

-- ════════════════════════════════════════════════════
-- § 3a. Lifting to RegularProp (typeclass-level reasoning)
-- ════════════════════════════════════════════════════

/-! Pack the path-frame regular sets as `RegularProp pathFrame` elements
    and demonstrate that the abstract `OrthocomplementedLattice` instance
    immediately delivers the De Morgan / excluded-middle / non-contradiction
    laws that are otherwise proved pointwise via `decide`. The set-membership
    theorems above remain available as the user-facing API; the `…Reg`
    versions below are the same propositions phrased in lattice notation. -/

/-- `{x₁, x₂}` packaged as a regular proposition. -/
def pLeftReg : RegularProp pathFrame := ⟨pLeft, regular_left⟩

/-- `{x₄, x₅}` packaged as a regular proposition. -/
def pRightReg : RegularProp pathFrame := ⟨pRight, regular_right⟩

/-- `{x₃}` packaged as a regular proposition. -/
def pMidReg : RegularProp pathFrame := ⟨pMid, regular_mid⟩

open OrthocomplementedLattice in
/-- Double negation on `pLeftReg` from the typeclass: `(pLeftReg)ᶜᶜ = pLeftReg`.
    Replaces the pointwise `doubleNeg_left` proof — abstract typeclass result,
    no `decide` on Poss5. -/
theorem pLeftReg_compl_compl : (pLeftRegᶜ)ᶜ = pLeftReg :=
  OrthocomplementedLattice.compl_compl pLeftReg

open OrthocomplementedLattice in
/-- Excluded middle on `pLeftReg` from the typeclass: `pLeftReg ⊔ pLeftRegᶜ = ⊤`.
    Replaces the pointwise `excludedMiddle_left` proof. -/
theorem pLeftReg_sup_compl : pLeftReg ⊔ pLeftRegᶜ = ⊤ :=
  sup_compl_eq_top pLeftReg

open OrthocomplementedLattice in
/-- Non-contradiction on `pLeftReg` from the typeclass: `pLeftReg ⊓ pLeftRegᶜ = ⊥`.
    Replaces the pointwise `nonContradiction_left` proof. -/
theorem pLeftReg_inf_compl : pLeftReg ⊓ pLeftRegᶜ = ⊥ :=
  inf_compl_eq_bot pLeftReg

/-- The orthocomplement of `pLeftReg` is `pRightReg`: `(pLeftReg)ᶜ = pRightReg`.
    Lattice-level statement of the pointwise `neg_left` theorem. -/
theorem pLeftReg_compl_eq : pLeftRegᶜ = pRightReg := by
  apply SetLike.coe_injective
  ext x
  exact neg_left x

-- ════════════════════════════════════════════════════
-- § 4. The Epistemic Scale (Examples 4.30, 4.33)
-- ════════════════════════════════════════════════════

/-! The Epistemic Scale is constructed from a 2-world model W = {0, 1}
    with V(p) = {0}. The possibilities are pairs (A, I) where
    ∅ ≠ A ⊆ I ⊆ W:
    - x₁ = ({0}, {0})     — settled that p, knows p
    - x₂ = ({0}, {0,1})   — settled that p, doesn't know
    - x₃ = ({0,1}, {0,1}) — nothing settled (full uncertainty)
    - x₄ = ({1}, {0,1})   — settled that ¬p, doesn't know
    - x₅ = ({1}, {1})     — settled that ¬p, knows ¬p

    Compatibility: (a,i) ◇ (a',i') iff a ∩ a' ≠ ∅ ∧ a ⊆ i' ∧ a' ⊆ i.
    Accessibility: (a,i) R (a',i') iff a ⊆ a' ∧ i' ⊆ i.
    @cite{holliday-mandelkern-2024} Definition 5.1, Example 5.3. -/

/-- Epistemic accessibility for the Epistemic Scale.
    R(x₁) = {x₁}, R(x₂) = {x₁,x₂,x₃}, R(x₃) = {x₃},
    R(x₄) = {x₃,x₄,x₅}, R(x₅) = {x₅}. -/
def Poss5.epistAccess : Poss5 → Poss5 → Prop
  | .x1, .x1
  | .x2, .x1 | .x2, .x2 | .x2, .x3
  | .x3, .x3
  | .x4, .x3 | .x4, .x4 | .x4, .x5
  | .x5, .x5 => True
  | _, _ => False

instance : DecidableRel Poss5.epistAccess := fun a b => by
  cases a <;> cases b <;> simp only [Poss5.epistAccess] <;> infer_instance

/-- The epistemic scale frame. Compatibility is the path graph;
    accessibility captures epistemic access (refining information).
    @cite{holliday-mandelkern-2024} Example 4.30, Example 4.33. -/
def epistemicScale : ModalCompatFrame Poss5 where
  toCompatFrame := pathFrame
  access := Poss5.epistAccess
  access_refl := fun x => by cases x <;> simp [Poss5.epistAccess]

instance : DecidableRel epistemicScale.access :=
  inferInstanceAs (DecidableRel Poss5.epistAccess)

instance : DecidableRel epistemicScale.toCompatFrame.compat :=
  inferInstanceAs (DecidableRel Poss5.compat)

-- The proposition p: true at x₁ and x₂ (those with A ⊆ V(p) = {0}).
def propP : Set Poss5 := fun x => match x with | .x1 | .x2 => True | _ => False

instance propP_dec : DecidablePred propP := fun x => by
  cases x <;> (unfold propP; first | exact isTrue trivial | exact isFalse id)

-- ════════════════════════════════════════════════════
-- § 5. Epistemic Scale Predictions (Example 4.33)
-- ════════════════════════════════════════════════════

/-! Verification of the truth values listed in Example 4.33 / Figure 13. -/

private def boxP : Set Poss5 := fun x => match x with | .x1 => True | _ => False
private def negP : Set Poss5 := fun x => match x with | .x4 | .x5 => True | _ => False
private def boxNegP : Set Poss5 := fun x => match x with | .x5 => True | _ => False
private def diamP : Set Poss5 := fun x => match x with | .x1 | .x2 | .x3 => True | _ => False
private def diamNegP : Set Poss5 := fun x => match x with | .x3 | .x4 | .x5 => True | _ => False

private instance boxP_dec : DecidablePred boxP := fun x => by
  cases x <;> (unfold boxP; first | exact isTrue trivial | exact isFalse id)
private instance negP_dec : DecidablePred negP := fun x => by
  cases x <;> (unfold negP; first | exact isTrue trivial | exact isFalse id)
private instance boxNegP_dec : DecidablePred boxNegP := fun x => by
  cases x <;> (unfold boxNegP; first | exact isTrue trivial | exact isFalse id)
private instance diamP_dec : DecidablePred diamP := fun x => by
  cases x <;> (unfold diamP; first | exact isTrue trivial | exact isFalse id)
private instance diamNegP_dec : DecidablePred diamNegP := fun x => by
  cases x <;> (unfold diamNegP; first | exact isTrue trivial | exact isFalse id)

/-- □p = {x₁}: only x₁ knows p (R(x₁) = {x₁} ⊆ V(p)). -/
theorem box_p (x : Poss5) : box epistemicScale propP x ↔ boxP x := by
  cases x <;> decide

/-- ¬p = {x₄, x₅}: the orthocomplement of V(p). -/
theorem neg_p (x : Poss5) : orthoNeg pathFrame propP x ↔ negP x := by
  cases x <;> decide

/-- □¬p = {x₅}: only x₅ knows ¬p. -/
theorem box_neg_p (x : Poss5) : box epistemicScale (orthoNeg pathFrame propP) x ↔ boxNegP x := by
  cases x <;> decide

/-- ◇p = {x₁, x₂, x₃}: p might be true at x₁, x₂, and x₃. -/
theorem diamond_p (x : Poss5) : diamond epistemicScale propP x ↔ diamP x := by
  cases x <;> decide

/-- ◇¬p = {x₃, x₄, x₅}: ¬p might be true at x₃, x₄, and x₅. -/
theorem diamond_neg_p (x : Poss5) :
    diamond epistemicScale (orthoNeg pathFrame propP) x ↔ diamNegP x := by
  cases x <;> decide

/-- ◇p ∧ ◇¬p = {x₃}: only the point of full uncertainty. -/
theorem uncertainty_at_x3 :
    conj (diamond epistemicScale propP)
         (diamond epistemicScale (orthoNeg pathFrame propP)) .x3 := by decide

-- ════════════════════════════════════════════════════
-- § 6. Core Epistemic Failures
-- ════════════════════════════════════════════════════

/-! The motivating examples from §1–2 of the paper: epistemic possibility
    does not collapse to classical negation, and truth does not collapse
    to knowledge. -/

/-- ◇¬p does NOT entail ¬p: x₃ makes "it might not be raining" true
    but does not settle "it's not raining." This is the core motivation
    for the entire paper — in classical logic, ◇¬p → ¬p, but this fails
    in possibility semantics. @cite{holliday-mandelkern-2024} §1. -/
theorem diamond_neg_not_entail_neg :
    diamond epistemicScale (orthoNeg pathFrame propP) .x3 ∧
    ¬ orthoNeg pathFrame propP .x3 := by decide

/-- p does NOT entail □p: x₂ makes p true without knowing p. "It's
    raining" does not mean "It must be raining." Failure of necessitation
    for non-logical truths. @cite{holliday-mandelkern-2024} §2. -/
theorem p_not_entail_box_p :
    propP .x2 ∧ ¬ box epistemicScale propP .x2 := by decide

-- ════════════════════════════════════════════════════
-- § 7. Wittgenstein Sentences (Proposition 4.27)
-- ════════════════════════════════════════════════════

/-! **Wittgenstein's Law**: ¬A ∧ ◇A = ∅.
    "It's raining and it might not be raining" is contradictory.
    In possibility semantics, if x settles ¬A (all compatible possibilities
    fail A), then x cannot also make ◇A true (which requires a compatible
    possibility in □¬A's complement).
    @cite{holliday-mandelkern-2024} Proposition 4.27. -/

/-- ¬p ∧ ◇p = ∅: "p is false and p might be true" is contradictory. -/
theorem wittgenstein_p (x : Poss5) :
    ¬ conj (orthoNeg pathFrame propP) (diamond epistemicScale propP) x := by
  cases x <;> decide

/-- p ∧ ◇¬p = ∅: "p is true and ¬p might be true" is contradictory.
    Uses double negation: p = ¬¬p. -/
theorem wittgenstein_neg_p (x : Poss5) :
    ¬ conj (orthoNeg pathFrame (orthoNeg pathFrame propP))
           (diamond epistemicScale (orthoNeg pathFrame propP)) x := by
  cases x <;> decide

-- ════════════════════════════════════════════════════
-- § 8. Epistemic Distributivity Failure (Example 4.33)
-- ════════════════════════════════════════════════════

/-- Distributivity fails across epistemic levels: (p ∨ ¬p) ∧ (◇p ∧ ◇¬p)
    is true at x₃, but (p ∧ ◇p ∧ ◇¬p) ∨ (¬p ∧ ◇p ∧ ◇¬p) is not.
    The partial possibility x₃ verifies the disjunction without
    committing to either disjunct — both disjuncts are empty by
    Wittgenstein's Law (p ∧ ◇¬p = ∅ and ¬p ∧ ◇p = ∅).
    @cite{holliday-mandelkern-2024} Example 3.20 (algebraic), Example 4.33
    (possibility-semantic instantiation). -/
theorem epistemic_distrib_failure :
    let pDisj := disj pathFrame propP (orthoNeg pathFrame propP)
    let uncertainty := conj (diamond epistemicScale propP)
                            (diamond epistemicScale (orthoNeg pathFrame propP))
    let lhs := conj pDisj uncertainty
    let rhs := disj pathFrame
      (conj propP uncertainty)
      (conj (orthoNeg pathFrame propP) uncertainty)
    lhs .x3 ∧ ¬ rhs .x3 := by decide

-- ════════════════════════════════════════════════════
-- § 9. Free Choice
-- ════════════════════════════════════════════════════

/-! **Free choice disjunction**: ◇(A ∨ B) entails ◇A ∧ ◇B.

    The full free choice entailment holds for propositions in the image
    of the embedding e_B in epistemic extensions of Boolean algebras
    (paper §5 inheritance principles). The path frame is non-Boolean
    (distributivity fails), so free choice does NOT hold in general
    in the epistemic scale.

    It does hold at x₃ (full uncertainty), where both p and ¬p remain
    epistemically possible. It fails at x₁ (knows p), where ◇(p ∨ ¬p)
    is trivially true but ◇¬p is false. -/

/-- Free choice holds at x₃: ◇(p ∨ ¬p) → ◇p ∧ ◇¬p. -/
theorem free_choice_at_x3 :
    diamond epistemicScale (disj pathFrame propP (orthoNeg pathFrame propP)) .x3 →
    conj (diamond epistemicScale propP)
         (diamond epistemicScale (orthoNeg pathFrame propP)) .x3 := by
  decide

/-- Free choice FAILS at x₁: ◇(p ∨ ¬p) is true but ◇¬p is false.
    x₁ knows p, so while the disjunction is trivially possible, the
    individual disjunct ¬p is not epistemically accessible. -/
theorem free_choice_fails_at_x1 :
    diamond epistemicScale (disj pathFrame propP (orthoNeg pathFrame propP)) .x1 ∧
    ¬ conj (diamond epistemicScale propP)
           (diamond epistemicScale (orthoNeg pathFrame propP)) .x1 := by
  decide

-- ════════════════════════════════════════════════════
-- § 10. T Axiom
-- ════════════════════════════════════════════════════

/-- T axiom: □A entails A (knowledge is factive).
    @cite{holliday-mandelkern-2024} Proposition 4.25. -/
theorem T_axiom_p (x : Poss5) :
    box epistemicScale propP x → propP x := by
  cases x <;> decide

/-- □p entails ◇p (knowledge implies epistemic possibility). -/
theorem box_implies_diamond (x : Poss5) :
    box epistemicScale propP x → diamond epistemicScale propP x := by
  cases x <;> decide

-- ════════════════════════════════════════════════════
-- § 11. Disjunctive Syllogism Failure
-- ════════════════════════════════════════════════════

/-! **Disjunctive syllogism** ({p ∨ q, ¬q} ⊨ p) fails for epistemic modals:
    "Either the dog is inside or it must be outside; it's not the case that
    it must be outside; therefore it is inside." The tautological first
    premise carries no information.
    @cite{holliday-mandelkern-2024} §2.3. -/

/-- Disjunctive syllogism fails: p ∨ □¬p and ¬□¬p both hold at x₃
    (full uncertainty) but p does not. -/
theorem disjSyllogism_fails :
    let mustNotP := box epistemicScale (orthoNeg pathFrame propP)
    let pOrMustNotP := disj pathFrame propP mustNotP
    let notMustNotP := orthoNeg pathFrame mustNotP
    pOrMustNotP .x3 ∧ notMustNotP .x3 ∧ ¬ propP .x3 := by
  decide

-- ════════════════════════════════════════════════════
-- § 12. Orthomodularity Failure
-- ════════════════════════════════════════════════════

/-! **Orthomodularity** (if φ ⊨ ψ then ψ ⊨ φ ∨ (¬φ ∧ ψ)) fails.
    Since p ⊨ ◇p, orthomodularity would give ◇p ⊨ p ∨ (¬p ∧ ◇p).
    But ¬p ∧ ◇p = ⊥ by Wittgenstein's Law, so this collapses to
    ◇p ⊨ p — absurd.
    @cite{holliday-mandelkern-2024} §2.4. -/

/-- p entails ◇p: truth implies epistemic possibility. -/
theorem p_entails_diamond (x : Poss5) (h : propP x) :
    diamond epistemicScale propP x := by
  cases x <;> first | (revert h; decide) | (exact h.elim)

/-- Orthomodularity fails: ◇p holds at x₃ but p ∨ (¬p ∧ ◇p) does not
    (since ¬p ∧ ◇p = ⊥ by Wittgenstein, this reduces to p). -/
theorem orthomodularity_fails :
    let diamP := diamond epistemicScale propP
    let rhs := disj pathFrame propP (conj (orthoNeg pathFrame propP) diamP)
    diamP .x3 ∧ ¬ rhs .x3 := by decide

-- ════════════════════════════════════════════════════
-- § 13. Pseudocomplementation Failure
-- ════════════════════════════════════════════════════

/-! **Pseudocomplementation** (a ∧ b = 0 → b ≤ ¬a) fails. In a Boolean
    algebra, ¬a is the greatest element disjoint from a. In an ortholattice
    this need not hold: p ∧ ◇¬p = ⊥ (Wittgenstein) but ◇¬p ≰ ¬p.
    This is the algebraic root of why ◇¬p ≠ ¬p.
    @cite{holliday-mandelkern-2024} Lemma 3.6 (algebraic statement),
    Example 3.20 (concrete failure). -/

/-- Pseudocomplementation fails: p ∧ ◇¬p = ⊥ but ◇¬p ≰ ¬p.
    x₃ witnesses ◇¬p (might not be raining) without witnessing ¬p. -/
theorem pseudocomplementation_fails :
    let negP := orthoNeg pathFrame propP
    let diamNegP := diamond epistemicScale negP
    (∀ x : Poss5, ¬ conj propP diamNegP x) ∧
    (diamNegP .x3 ∧ ¬ negP .x3) := by
  exact ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 14. Level-wise Boolean Classicality (§3.2.4)
-- ════════════════════════════════════════════════════

/-! **Level-wise classicality**: classical reasoning is safe *within*
    an epistemic level but dangerous *across* levels. The subortholattice
    B₀ = {⊥, p, ¬p, ⊤} is a four-element Boolean algebra; B₁ (generated
    by applying □ and ◇ to B₀) is an eight-element Boolean algebra.
    Distributivity only fails when mixing levels.
    @cite{holliday-mandelkern-2024} §3.2.4. -/

/-- Within-level distributivity (B₁): ◇p ∧ (◇¬p ∨ ◇p) = (◇p ∧ ◇¬p) ∨ (◇p ∧ ◇p).
    All operands from the same epistemic level → distributivity holds. -/
theorem within_level_distrib (x : Poss5) :
    let dp := diamond epistemicScale propP
    let dnp := diamond epistemicScale (orthoNeg pathFrame propP)
    conj dp (disj pathFrame dnp dp) x ↔
    disj pathFrame (conj dp dnp) (conj dp dp) x := by
  cases x <;> decide

/-- Cross-level failure: ◇p ∧ (p ∨ ¬p) ≠ (◇p ∧ p) ∨ (◇p ∧ ¬p).
    ◇p is from B₁ but p, ¬p are from B₀. At x₃ the LHS is true
    (◇p and excluded middle both hold) but the RHS is false (both
    disjuncts are empty by Wittgenstein's Law). -/
theorem cross_level_distrib_fails :
    let dp := diamond epistemicScale propP
    let negP := orthoNeg pathFrame propP
    let lhs := conj dp (disj pathFrame propP negP)
    let rhs := disj pathFrame (conj dp propP) (conj dp negP)
    lhs .x3 ∧ ¬ rhs .x3 := by decide

-- ════════════════════════════════════════════════════
-- § 15. Lifting from W = {0, 1} (Definition 5.1, Example 5.3)
-- ════════════════════════════════════════════════════

/-! Lifting construction specialized to the two-world Boolean algebra
    `B = ℘({0, 1})` with valuation `V(p) = {0}`. The five possibilities
    are pairs `(A, I)` with `∅ ≠ A ⊆ I ⊆ W`:

    - x₁ = ({0}, {0})     — knows p
    - x₂ = ({0}, {0,1})   — settled p, doesn't know
    - x₃ = ({0,1}, {0,1}) — full uncertainty
    - x₄ = ({1}, {0,1})   — settled ¬p, doesn't know
    - x₅ = ({1}, {1})     — knows ¬p

    Compatibility: (A,I) ◇ (A',I') iff A ∩ A' ≠ ∅ ∧ A ⊆ I' ∧ A' ⊆ I.
    Accessibility: (A,I) R (A',I') iff A ⊆ A' ∧ I' ⊆ I.

    The general lifting from an arbitrary Boolean algebra `B` (Def 5.1)
    is unformalized; this section verifies the agreement of the derived
    `liftedCompat`/`liftedAccess` with the stipulated `pathFrame`/
    `epistemicScale` for the W={0,1} case. -/

/-- World 0 (the p-world) is in the actuality set A(x). -/
def worldlyA0 : Poss5 → Bool
  | .x1 | .x2 | .x3 => true
  | .x4 | .x5 => false

/-- World 1 (the ¬p-world) is in the actuality set A(x). -/
def worldlyA1 : Poss5 → Bool
  | .x3 | .x4 | .x5 => true
  | .x1 | .x2 => false

/-- World 0 is in the information set I(x). -/
def worldlyI0 : Poss5 → Bool
  | .x1 | .x2 | .x3 | .x4 => true
  | .x5 => false

/-- World 1 is in the information set I(x). -/
def worldlyI1 : Poss5 → Bool
  | .x2 | .x3 | .x4 | .x5 => true
  | .x1 => false

/-- Compatibility derived from lifting: (A,I) ◇ (A',I') iff
    A ∩ A' ≠ ∅ ∧ A ⊆ I' ∧ A' ⊆ I.
    @cite{holliday-mandelkern-2024} Definition 5.1.2. -/
def liftedCompat (x y : Poss5) : Bool :=
  -- A ∩ A' ≠ ∅ (share at least one actual world)
  ((worldlyA0 x && worldlyA0 y) || (worldlyA1 x && worldlyA1 y)) &&
  -- A ⊆ I' (x's actual worlds are in y's information)
  ((!worldlyA0 x || worldlyI0 y) && (!worldlyA1 x || worldlyI1 y)) &&
  -- A' ⊆ I (y's actual worlds are in x's information)
  ((!worldlyA0 y || worldlyI0 x) && (!worldlyA1 y || worldlyI1 x))

/-- Accessibility derived from lifting: (A,I) R (A',I') iff
    A ⊆ A' ∧ I' ⊆ I (refining = expanding actuality, shrinking information).
    @cite{holliday-mandelkern-2024} Definition 5.1.3. -/
def liftedAccess (x y : Poss5) : Bool :=
  -- A ⊆ A' (y's actuality contains x's)
  ((!worldlyA0 x || worldlyA0 y) && (!worldlyA1 x || worldlyA1 y)) &&
  -- I' ⊆ I (y's information is contained in x's)
  ((!worldlyI0 y || worldlyI0 x) && (!worldlyI1 y || worldlyI1 x))

/-- The epistemic scale's compatibility matches the lifting construction. -/
theorem compat_from_lifting (x y : Poss5) :
    epistemicScale.compat x y ↔ liftedCompat x y = true := by
  cases x <;> cases y <;> decide

/-- The epistemic scale's accessibility matches the lifting construction. -/
theorem access_from_lifting (x y : Poss5) :
    epistemicScale.access x y ↔ liftedAccess x y = true := by
  cases x <;> cases y <;> decide

-- ════════════════════════════════════════════════════
-- § 16. Truth from Worlds (Lemma 5.4)
-- ════════════════════════════════════════════════════

/-! @cite{holliday-mandelkern-2024} Lemma 5.4: truth at a possibility
    reduces to truth at worlds via the A and I sets.

    - propP x = true  iff  world 1 ∉ A(x)  (all actual worlds satisfy p)
    - □p x = true     iff  world 1 ∉ I(x)  (all information-accessible worlds satisfy p)
    - ◇p x = true     iff  world 0 ∈ A(x)  (some actual world satisfies p)
-/

/-- Truth from worlds: p holds at x iff the ¬p-world is not actual. -/
theorem boolean_truth_from_worlds (x : Poss5) :
    propP x ↔ worldlyA1 x = false := by
  cases x <;> decide

/-- Box truth from worlds: □p holds at x iff the ¬p-world is not
    information-accessible. -/
theorem box_truth_from_worlds (x : Poss5) :
    box epistemicScale propP x ↔ worldlyI1 x = false := by
  cases x <;> decide

/-- Diamond truth from worlds: ◇p holds at x iff the p-world is actual. -/
theorem diamond_truth_from_worlds (x : Poss5) :
    diamond epistemicScale propP x ↔ worldlyA0 x = true := by
  cases x <;> decide

-- ════════════════════════════════════════════════════
-- § 17. Cross-Paper Agreement Bridges
-- ════════════════════════════════════════════════════

/-! HM 2024's formal predictions agree with the empirical patterns recorded
    in the prior literature. These bridges close the loop between Yalcin's
    embedding diagnostic, Mandelkern's distributivity-failure intuition,
    Klinedinst & Rothschild's disjunctive-syllogism failure, and HM's
    formal theorems on the Epistemic Scale. Each agreement is a one-line
    `:= rfl` because the data files encode the empirical judgments as
    decidable Bool tables. -/

/-- HM 2024 predicts that Wittgenstein sentences are infelicitous —
    matching Yalcin (2007)'s empirical observation. The formal certificates
    are `wittgenstein_p` and `wittgenstein_neg_p` (§7), which prove
    `¬p ∧ ◇p = ∅` and `p ∧ ◇¬p = ∅` on the Epistemic Scale. -/
theorem hm_predicts_wittgenstein_infelicitous :
    Phenomena.Modality.Studies.Yalcin2007.felicitousUnderEmbedding
      .wittgenstein = false := rfl

/-- HM 2024 predicts that classical contradictions are infelicitous —
    matching Yalcin (2007). Trivially: the orthologic of HM 2024 satisfies
    `a ⊓ aᶜ = ⊥` (the `inf_compl_eq_bot` ortholattice axiom on
    `RegularProp pathFrame`). -/
theorem hm_predicts_classical_infelicitous :
    Phenomena.Modality.Studies.Yalcin2007.felicitousUnderEmbedding
      .classical = false := rfl

/-- HM 2024 predicts Mandelkern (2019)'s distributivity-failure pattern:
    LHS felicitous, RHS infelicitous. The formal certificate is
    `epistemic_distrib_failure` (§8), which proves
    `(p ∨ ¬p) ∧ (◇p ∧ ◇¬p)` true at x₃ but
    `(p ∧ ◇p ∧ ◇¬p) ∨ (¬p ∧ ◇p ∧ ◇¬p)` false at x₃ on the Epistemic Scale. -/
theorem hm_predicts_distrib_failure :
    Phenomena.Modality.Studies.Mandelkern2019.distribFailure.lhsFelicitous = true ∧
    Phenomena.Modality.Studies.Mandelkern2019.distribFailure.rhsFelicitous = false :=
  ⟨rfl, rfl⟩

/-- HM 2024 predicts Klinedinst & Rothschild (2012)'s disjunctive-syllogism
    failure: from `p ∨ □¬p` and `¬□¬p`, the conclusion `p` does not follow.
    The formal certificate is `disjSyllogism_fails` (§11), which exhibits
    the witness x₃ where both premises hold but the conclusion fails. -/
theorem hm_predicts_disjSyll_failure :
    Phenomena.Modality.Studies.KlinedinstRothschild2012.disjSyllFailure.valid = false := rfl

end Phenomena.Modality.Studies.HollidayMandelkern2024
