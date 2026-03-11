import Linglib.Theories.Semantics.PossibilitySemantics.Basic
import Linglib.Core.Logic.ModalLogic
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
    (Example 4.30). @cite{holliday-mandelkern-2024} -/
structure ModalCompatFrame (S : Type*) [FiniteWorlds S] extends CompatFrame S where
  access : S → S → Bool
  access_refl : ∀ x, access x x = true

/-- Box operator: □A = {x | R(x) ⊆ A}.
    @cite{holliday-mandelkern-2024} eq. (III). -/
def box {S : Type*} [FiniteWorlds S] (F : ModalCompatFrame S) (A : BProp S) : BProp S :=
  fun x => FiniteWorlds.worlds.filter (F.access x) |>.all A

/-- Diamond operator: ◇A = ¬□¬A (via orthocomplement, NOT Boolean dual).
    @cite{holliday-mandelkern-2024} eq. (IV). -/
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
    @cite{holliday-mandelkern-2024} Definition 5.1, Example 5.3. -/

/-- The epistemic scale frame. Compatibility is the path graph;
    accessibility captures epistemic access (refining information).
    @cite{holliday-mandelkern-2024} Example 4.30, Example 4.33. -/
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
    @cite{holliday-mandelkern-2024} -/

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
    to knowledge. @cite{holliday-mandelkern-2024} -/

/-- ◇¬p does NOT entail ¬p: x₃ makes "it might not be raining" true
    but does not settle "it's not raining." This is the core motivation
    for the entire paper — in classical logic, ◇¬p → ¬p, but this fails
    in possibility semantics. @cite{holliday-mandelkern-2024} §1, p. 2. -/
theorem diamond_neg_not_entail_neg :
    diamond epistemicScale (orthoNeg pathFrame propP) .x3 = true ∧
    orthoNeg pathFrame propP .x3 = false := by native_decide

/-- p does NOT entail □p: x₂ makes p true without knowing p. "It's
    raining" does not mean "It must be raining." Failure of necessitation
    for non-logical truths. @cite{holliday-mandelkern-2024} §2, p. 3. -/
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
    @cite{holliday-mandelkern-2024} Proposition 4.27. -/

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
    @cite{holliday-mandelkern-2024} Proposition 4.27. -/
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
    @cite{holliday-mandelkern-2024} Example 3.20, Example 4.33. -/
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
    (@cite{holliday-mandelkern-2024} Proposition 5.12.3, inheritance
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
    @cite{holliday-mandelkern-2024} Proposition 5.12.3. -/
theorem free_choice_fails_at_x1 :
    diamond epistemicScale (disj pathFrame propP (orthoNeg pathFrame propP)) .x1 = true ∧
    conj (diamond epistemicScale propP)
         (diamond epistemicScale (orthoNeg pathFrame propP)) .x1 = false := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 8. T Axiom and Modal Properties
-- ════════════════════════════════════════════════════

/-- T axiom: □A entails A (knowledge is factive).
    @cite{holliday-mandelkern-2024} Proposition 4.25. -/
theorem T_axiom_p (x : Poss5) :
    box epistemicScale propP x = true → propP x = true := by
  cases x <;> native_decide

/-- □p entails ◇p (knowledge implies epistemic possibility). -/
theorem box_implies_diamond (x : Poss5) :
    box epistemicScale propP x = true → diamond epistemicScale propP x = true := by
  cases x <;> native_decide

-- ════════════════════════════════════════════════════
-- § 9. Bridge to Kripke Semantics
-- ════════════════════════════════════════════════════

/-! When the compatibility relation is identity (every possibility is a
    world), the modal operators reduce to standard Kripke semantics
    from `Core.ModalLogic`. The compat relation only affects negation
    (orthocomplement) — box is Kripke necessity regardless.

    Conceptual parallel to `Semantics.Supervaluation`: supervaluation's
    D operator is □ with universal access among specification points,
    and its fidelity theorem shows that singleton specification spaces
    yield classical logic. Here, when all possibilities are worlds
    (compat = identity), the ortholattice collapses to a Boolean algebra
    — the same classical-collapse phenomenon from opposite directions.
    @cite{holliday-mandelkern-2024} Remark 4.9. -/

/-- Box = Kripke necessity: the compatibility frame's box operator is
    definitionally Kripke necessity evaluation. The compat relation
    only affects negation, not the modal operators themselves. -/
theorem box_eq_kripkeEval {S : Type*} [FiniteWorlds S]
    (F : ModalCompatFrame S) (A : BProp S) (x : S) :
    box F A x = Core.ModalLogic.kripkeEval F.access .necessity A x := rfl

/-- Diamond = Kripke possibility when compat = identity. The
    orthocomplement reduces to Boolean negation, so ◇A = ¬□¬A
    becomes the standard ¬∀¬ = ∃ dual.
    @cite{holliday-mandelkern-2024} Remark 4.9. -/
theorem diamond_eq_kripkeEval_classical {S : Type*} [FiniteWorlds S] [DecidableEq S]
    (F : ModalCompatFrame S)
    (hClassical : ∀ x y, F.compat x y = true → x = y)
    (A : BProp S) (x : S) :
    diamond F A x = Core.ModalLogic.kripkeEval F.access .possibility A x := by
  have inner : orthoNeg F.toCompatFrame A = fun y => !A y :=
    funext (fun y => orthoNeg_classical F.toCompatFrame hClassical A y)
  unfold diamond; rw [inner]
  rw [orthoNeg_classical F.toCompatFrame hClassical (box F (fun y => !A y)) x]
  -- !(box F (!A) x) = kripkeEval .possibility A x
  -- Reduce both sides to list operations via rfl
  have lhs : box F (fun y => !A y) x =
      (FiniteWorlds.worlds.filter (F.access x)).all (fun y => !A y) := rfl
  have rhs : Core.ModalLogic.kripkeEval F.access .possibility A x =
      (FiniteWorlds.worlds.filter (F.access x)).any A := rfl
  rw [lhs, rhs]
  -- !(filter.all (!A)) = filter.any A
  generalize FiniteWorlds.worlds.filter (F.access x) = ws
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have h1 : (w :: ws).all (fun y => !A y) = (!A w && ws.all (fun y => !A y)) := rfl
    have h2 : (w :: ws).any A = (A w || ws.any A) := rfl
    rw [h1, h2]; cases A w <;> simp [ih]

/-- The T axiom for modal compatibility frames follows from the general
    Kripke T axiom (`Core.ModalLogic.T_of_refl`). Reflexive accessibility
    + any compat relation → □A entails A. -/
theorem T_axiom_general {S : Type*} [FiniteWorlds S]
    (F : ModalCompatFrame S) (A : BProp S) (x : S)
    (h : box F A x = true) : A x = true :=
  Core.ModalLogic.T_of_refl F.access_refl A x h

end Semantics.PossibilitySemantics
