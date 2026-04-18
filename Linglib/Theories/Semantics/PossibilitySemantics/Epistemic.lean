import Linglib.Theories.Semantics.PossibilitySemantics.Basic
import Linglib.Core.IntensionalLogic.RestrictedModality
import Mathlib.Data.Fintype.Pi

/-!
# Epistemic Possibility Semantics
@cite{holliday-mandelkern-2024}

Epistemic extension of possibility semantics. Adds an accessibility relation
R to a compatibility frame, yielding □ and ◇ operators whose ortholattice
validates Wittgenstein's Law (¬A ∧ ◇A = ∅) while invalidating distributivity
across epistemic levels.

## The Epistemic Scale

The central example is the 5-point Epistemic Scale, constructed from
a 2-world possible worlds model by "possibilizing" it. The scale runs:

    □p — p — ◇p ∧ ◇¬p — ¬p — □¬p
    x₁   x₂      x₃      x₄    x₅

Each point represents a degree of epistemic commitment: from certainty
that p, through partial information, to certainty that ¬p. The partial
possibility x₃ verifies ◇p ∧ ◇¬p without verifying either p or ¬p.

## Linguistic applications

- **Wittgenstein sentences**: "It's raining and it might not be" is
  contradictory: ¬A ∩ ◇A = ∅ (Proposition 4.27).
- **Epistemic possibility ≠ negation**: ◇¬p does not entail ¬p. "It might
  not be raining" does not mean "It's not raining" (§1, p. 2).
- **Knowledge ≠ truth**: p does not entail □p. "It's raining" does not mean
  "It must be raining" (§2, p. 3).
- **Distributivity failure**: reasoning by cases fails across epistemic
  levels (Example 3.20, Example 4.33).
-/

namespace Semantics.PossibilitySemantics

open Core.Proposition (FiniteWorlds BProp)

-- ════════════════════════════════════════════════════
-- § 1. Epistemic Compatibility Frames
-- ════════════════════════════════════════════════════

/-- A modal compatibility frame: a compatibility frame equipped with an
    accessibility relation R satisfying reflexivity (Definition 4.24).
    The paper's full Definition 4.20 also requires R-regularity; the
    epistemic compatibility frame (Definition 4.26) adds Knowability.
    Our `epistemicScale` satisfies all three conditions by construction
    (Example 4.30). -/
structure ModalCompatFrame (S : Type*) [FiniteWorlds S] extends CompatFrame S where
  access : S → S → Bool
  access_refl : ∀ x, access x x = true

/-- Box operator: □A = {x | R(x) ⊆ A}.
    eq. (III). -/
def box {S : Type*} [FiniteWorlds S] (F : ModalCompatFrame S) (A : BProp S) : BProp S :=
  fun x => FiniteWorlds.worlds.filter (F.access x) |>.all A

/-- Diamond operator: ◇A = ¬□¬A (via orthocomplement, NOT Boolean dual).
    eq. (IV). -/
def diamond {S : Type*} [FiniteWorlds S] (F : ModalCompatFrame S) (A : BProp S) : BProp S :=
  orthoNeg F.toCompatFrame (box F (orthoNeg F.toCompatFrame A))

-- ════════════════════════════════════════════════════
-- § 2. The Epistemic Scale
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
    Definition 5.1, Example 5.3. -/

/-- The epistemic scale frame. Compatibility is the path graph;
    accessibility captures epistemic access (refining information).
    Example 4.30, Example 4.33. -/
def epistemicScale : ModalCompatFrame Poss5 where
  compat := pathFrame.compat
  compat_refl := pathFrame.compat_refl
  compat_symm := pathFrame.compat_symm
  -- R(x₁) = {x₁}, R(x₂) = {x₁,x₂,x₃}, R(x₃) = {x₃},
  -- R(x₄) = {x₃,x₄,x₅}, R(x₅) = {x₅}
  access := fun a b => match a, b with
    | .x1, .x1
    | .x2, .x1 | .x2, .x2 | .x2, .x3
    | .x3, .x3
    | .x4, .x3 | .x4, .x4 | .x4, .x5
    | .x5, .x5 => true
    | _, _ => false
  access_refl := fun x => by cases x <;> rfl

-- The proposition p: true at x₁ and x₂ (those with A ⊆ V(p) = {0}).
def propP : BProp Poss5 := fun x => match x with | .x1 | .x2 => true | _ => false

-- ════════════════════════════════════════════════════
-- § 3. Epistemic Scale Predictions
-- ════════════════════════════════════════════════════

/-! Verification of the truth values listed in Example 4.33.
    -/

private def boxP : BProp Poss5 := fun x => match x with | .x1 => true | _ => false
private def negP : BProp Poss5 := fun x => match x with | .x4 | .x5 => true | _ => false
private def boxNegP : BProp Poss5 := fun x => match x with | .x5 => true | _ => false
private def diamP : BProp Poss5 := fun x => match x with | .x1 | .x2 | .x3 => true | _ => false
private def diamNegP : BProp Poss5 := fun x => match x with | .x3 | .x4 | .x5 => true | _ => false

/-- □p = {x₁}: only x₁ knows p (R(x₁) = {x₁} ⊆ V(p)). -/
theorem box_p : box epistemicScale propP = boxP := by
  funext x; cases x <;> native_decide

/-- ¬p = {x₄, x₅}: the orthocomplement of V(p). -/
theorem neg_p : orthoNeg pathFrame propP = negP := by
  funext x; cases x <;> native_decide

/-- □¬p = {x₅}: only x₅ knows ¬p. -/
theorem box_neg_p : box epistemicScale (orthoNeg pathFrame propP) = boxNegP := by
  funext x; cases x <;> native_decide

/-- ◇p = {x₁, x₂, x₃}: p might be true at x₁, x₂, and x₃. -/
theorem diamond_p : diamond epistemicScale propP = diamP := by
  funext x; cases x <;> native_decide

/-- ◇¬p = {x₃, x₄, x₅}: ¬p might be true at x₃, x₄, and x₅. -/
theorem diamond_neg_p : diamond epistemicScale (orthoNeg pathFrame propP) = diamNegP := by
  funext x; cases x <;> native_decide

/-- ◇p ∧ ◇¬p = {x₃}: only the point of full uncertainty. -/
theorem uncertainty_at_x3 :
    conj (diamond epistemicScale propP)
         (diamond epistemicScale (orthoNeg pathFrame propP)) .x3 = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Core Epistemic Failures
-- ════════════════════════════════════════════════════

/-! The motivating examples from §1–2 of the paper: epistemic possibility
    does not collapse to classical negation, and truth does not collapse
    to knowledge. -/

/-- ◇¬p does NOT entail ¬p: x₃ makes "it might not be raining" true
    but does not settle "it's not raining." This is the core motivation
    for the entire paper — in classical logic, ◇¬p → ¬p, but this fails
    in possibility semantics. §1, p. 2. -/
theorem diamond_neg_not_entail_neg :
    diamond epistemicScale (orthoNeg pathFrame propP) .x3 = true ∧
    orthoNeg pathFrame propP .x3 = false := by native_decide

/-- p does NOT entail □p: x₂ makes p true without knowing p. "It's
    raining" does not mean "It must be raining." Failure of necessitation
    for non-logical truths. §2, p. 3. -/
theorem p_not_entail_box_p :
    propP .x2 = true ∧ box epistemicScale propP .x2 = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Wittgenstein Sentences
-- ════════════════════════════════════════════════════

/-! **Wittgenstein's Law**: ¬A ∧ ◇A = ∅.
    "It's raining and it might not be raining" is contradictory.
    In possibility semantics, if x settles ¬A (all compatible possibilities
    fail A), then x cannot also make ◇A true (which requires a compatible
    possibility in □¬A's complement).
    Proposition 4.27. -/

/-- ¬p ∧ ◇p = ∅: "p is false and p might be true" is contradictory. -/
theorem wittgenstein_p (x : Poss5) :
    conj (orthoNeg pathFrame propP) (diamond epistemicScale propP) x = false := by
  cases x <;> native_decide

/-- p ∧ ◇¬p = ∅: "p is true and ¬p might be true" is contradictory.
    Uses double negation: p = ¬¬p. -/
theorem wittgenstein_neg_p (x : Poss5) :
    conj (orthoNeg pathFrame (orthoNeg pathFrame propP))
         (diamond epistemicScale (orthoNeg pathFrame propP)) x = false := by
  cases x <;> native_decide

/-- Wittgenstein's Law for ALL regular propositions in the epistemic
    scale: ¬A ∧ ◇A = ∅. There are 2⁵ = 32 Boolean functions on Poss5,
    of which 10 are ◇-regular (Figure 8); the theorem checks all 160 cases.
    Proposition 4.27. -/
theorem wittgenstein_general (A : Poss5 → Bool) (x : Poss5)
    (hReg : isRegular pathFrame A = true) :
    conj (orthoNeg pathFrame A) (diamond epistemicScale A) x = false := by
  revert hReg; revert x; revert A; decide

-- ════════════════════════════════════════════════════
-- § 6. Epistemic Distributivity Failure
-- ════════════════════════════════════════════════════

/-- Distributivity fails across epistemic levels: (p ∨ ¬p) ∧ (◇p ∧ ◇¬p)
    is true at x₃, but (p ∧ ◇p ∧ ◇¬p) ∨ (¬p ∧ ◇p ∧ ◇¬p) is not.
    The partial possibility x₃ verifies the disjunction without
    committing to either disjunct — both disjuncts are empty by
    Wittgenstein's Law (p ∧ ◇¬p = ∅ and ¬p ∧ ◇p = ∅).
    Example 3.20, Example 4.33. -/
theorem epistemic_distrib_failure :
    let pDisj := disj pathFrame propP (orthoNeg pathFrame propP)
    let uncertainty := conj (diamond epistemicScale propP)
                            (diamond epistemicScale (orthoNeg pathFrame propP))
    let lhs := conj pDisj uncertainty
    let rhs := disj pathFrame
      (conj propP uncertainty)
      (conj (orthoNeg pathFrame propP) uncertainty)
    lhs .x3 = true ∧ rhs .x3 = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. Free Choice
-- ════════════════════════════════════════════════════

/-! **Free choice disjunction**: ◇(A ∨ B) entails ◇A ∧ ◇B.

    The full free choice entailment holds for propositions in the image
    of the embedding e_B in epistemic extensions of Boolean algebras
    (Proposition 5.12.3, inheritance
    principle). The path frame is non-Boolean (distributivity fails),
    so free choice does NOT hold in general in the epistemic scale.

    It does hold at x₃ (full uncertainty), where both p and ¬p remain
    epistemically possible. It fails at x₁ (knows p), where ◇(p ∨ ¬p)
    is trivially true but ◇¬p is false. -/

/-- Free choice holds at x₃: ◇(p ∨ ¬p) → ◇p ∧ ◇¬p. -/
theorem free_choice_at_x3 :
    diamond epistemicScale (disj pathFrame propP (orthoNeg pathFrame propP)) .x3 = true →
    conj (diamond epistemicScale propP)
         (diamond epistemicScale (orthoNeg pathFrame propP)) .x3 = true := by
  native_decide

/-- Free choice FAILS at x₁: ◇(p ∨ ¬p) is true but ◇¬p is false.
    x₁ knows p, so while the disjunction is trivially possible, the
    individual disjunct ¬p is not epistemically accessible.
    Proposition 5.12.3. -/
theorem free_choice_fails_at_x1 :
    diamond epistemicScale (disj pathFrame propP (orthoNeg pathFrame propP)) .x1 = true ∧
    conj (diamond epistemicScale propP)
         (diamond epistemicScale (orthoNeg pathFrame propP)) .x1 = false := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 8. T Axiom and Modal Properties
-- ════════════════════════════════════════════════════

/-- T axiom: □A entails A (knowledge is factive).
    Proposition 4.25. -/
theorem T_axiom_p (x : Poss5) :
    box epistemicScale propP x = true → propP x = true := by
  cases x <;> native_decide

/-- □p entails ◇p (knowledge implies epistemic possibility). -/
theorem box_implies_diamond (x : Poss5) :
    box epistemicScale propP x = true → diamond epistemicScale propP x = true := by
  cases x <;> native_decide

-- ════════════════════════════════════════════════════
-- § 9. T Axiom for Reflexive Frames
-- ════════════════════════════════════════════════════

/-- The T axiom for modal compatibility frames: reflexive accessibility
    means every world accesses itself, so □A at x forces A at x. -/
theorem T_axiom_general {S : Type*} [FiniteWorlds S]
    (F : ModalCompatFrame S) (A : BProp S) (x : S)
    (h : box F A x = true) : A x = true := by
  unfold box at h
  rw [List.all_eq_true] at h
  exact h x (List.mem_filter.mpr ⟨FiniteWorlds.complete x, F.access_refl x⟩)

-- ════════════════════════════════════════════════════
-- § 10. Disjunctive Syllogism Failure
-- ════════════════════════════════════════════════════

/-! **Disjunctive syllogism** ({p ∨ q, ¬q} ⊨ p) fails for epistemic modals:
    "Either the dog is inside or it must be outside; it's not the case that
    it must be outside; therefore it is inside." The tautological first
    premise carries no information.
    §2.3. -/

/-- Disjunctive syllogism fails: p ∨ □¬p and ¬□¬p both hold at x₃
    (full uncertainty) but p does not. -/
theorem disjSyllogism_fails :
    let mustNotP := box epistemicScale (orthoNeg pathFrame propP)
    let pOrMustNotP := disj pathFrame propP mustNotP
    let notMustNotP := orthoNeg pathFrame mustNotP
    pOrMustNotP .x3 = true ∧ notMustNotP .x3 = true ∧ propP .x3 = false := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 11. Orthomodularity Failure
-- ════════════════════════════════════════════════════

/-! **Orthomodularity** (if φ ⊨ ψ then ψ ⊨ φ ∨ (¬φ ∧ ψ)) fails.
    Since p ⊨ ◇p, orthomodularity would give ◇p ⊨ p ∨ (¬p ∧ ◇p).
    But ¬p ∧ ◇p = ⊥ by Wittgenstein's Law, so this collapses to
    ◇p ⊨ p — absurd.
    §2.4. -/

/-- p entails ◇p: truth implies epistemic possibility. -/
theorem p_entails_diamond (x : Poss5) (h : propP x = true) :
    diamond epistemicScale propP x = true := by
  cases x <;> (first | exact h | native_decide)

/-- Orthomodularity fails: ◇p holds at x₃ but p ∨ (¬p ∧ ◇p) does not
    (since ¬p ∧ ◇p = ⊥ by Wittgenstein, this reduces to p). -/
theorem orthomodularity_fails :
    let diamP := diamond epistemicScale propP
    let rhs := disj pathFrame propP (conj (orthoNeg pathFrame propP) diamP)
    diamP .x3 = true ∧ rhs .x3 = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 12. Pseudocomplementation Failure
-- ════════════════════════════════════════════════════

/-! **Pseudocomplementation** (a ∧ b = 0 → b ≤ ¬a) fails. In a Boolean
    algebra, ¬a is the greatest element disjoint from a. In an ortholattice
    this need not hold: p ∧ ◇¬p = ⊥ (Wittgenstein) but ◇¬p ≰ ¬p.
    This is the algebraic root of why ◇¬p ≠ ¬p.
    Proposition 3.7. -/

/-- Pseudocomplementation fails: p ∧ ◇¬p = ⊥ but ◇¬p ≰ ¬p.
    x₃ witnesses ◇¬p (might not be raining) without witnessing ¬p. -/
theorem pseudocomplementation_fails :
    let negP := orthoNeg pathFrame propP
    let diamNegP := diamond epistemicScale negP
    (∀ x : Poss5, conj propP diamNegP x = false) ∧
    (diamNegP .x3 = true ∧ negP .x3 = false) := by
  exact ⟨by decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 13. Level-wise Boolean Classicality
-- ════════════════════════════════════════════════════

/-! **Level-wise classicality**: classical reasoning is safe *within*
    an epistemic level but dangerous *across* levels. The subortholattice
    B₀ = {⊥, p, ¬p, ⊤} is a four-element Boolean algebra; B₁ (generated
    by applying □ and ◇ to B₀) is an eight-element Boolean algebra.
    Distributivity only fails when mixing levels.
    §3.2.4. -/

/-- Within-level distributivity (B₁): ◇p ∧ (◇¬p ∨ ◇p) = (◇p ∧ ◇¬p) ∨ (◇p ∧ ◇p).
    All operands from the same epistemic level → distributivity holds. -/
theorem within_level_distrib (x : Poss5) :
    let dp := diamond epistemicScale propP
    let dnp := diamond epistemicScale (orthoNeg pathFrame propP)
    conj dp (disj pathFrame dnp dp) x =
    disj pathFrame (conj dp dnp) (conj dp dp) x := by
  cases x <;> native_decide

/-- Cross-level failure: ◇p ∧ (p ∨ ¬p) ≠ (◇p ∧ p) ∨ (◇p ∧ ¬p).
    ◇p is from B₁ but p, ¬p are from B₀. At x₃ the LHS is true
    (◇p and excluded middle both hold) but the RHS is false (both
    disjuncts are empty by Wittgenstein's Law). -/
theorem cross_level_distrib_fails :
    let dp := diamond epistemicScale propP
    let negP := orthoNeg pathFrame propP
    let lhs := conj dp (disj pathFrame propP negP)
    let rhs := disj pathFrame (conj dp propP) (conj dp negP)
    lhs .x3 = true ∧ rhs .x3 = false := by native_decide

end Semantics.PossibilitySemantics
