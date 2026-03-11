import Linglib.Core.Semantics.Proposition

/-!
# Possibility Semantics
@cite{holliday-mandelkern-2024}

Possibility semantics generalizes possible world semantics by replacing
maximal possible worlds with partial *possibilities* ordered by refinement.
A possibility can verify a disjunction without verifying either disjunct.

## Key differences from possible world semantics

- **Propositions** are not arbitrary sets of possibilities but only
  *regular* sets — those satisfying a closure condition.
- **Negation** is orthocomplement: ¬A = {x | ∀y ◇ x, y ∉ A}.
- **Disjunction** is weaker than union: A ∨ B = ¬(¬A ∧ ¬B).
- The resulting algebra of propositions is an **ortholattice**, not
  a Boolean algebra.

## What validates and what fails

Validated: excluded middle, non-contradiction, double negation, De Morgan,
contraposition. Failed: **distributivity** — a possibility can verify
A ∧ (B ∨ C) without verifying either A ∧ B or A ∧ C. This is the key
departure from classical logic and the source of linguistic applications
(epistemic contradictions, free choice disjunction).

## Architecture

- `Basic.lean` (this file): compatibility frames, orthocomplement, regularity
- `Epistemic.lean`: epistemic modals, Wittgenstein sentences, free choice
-/

namespace Semantics.PossibilitySemantics

open Core.Proposition (FiniteWorlds BProp)

-- ════════════════════════════════════════════════════
-- § 1. Compatibility Frames
-- ════════════════════════════════════════════════════

/-- A compatibility frame: a set of possibilities with a reflexive,
    symmetric compatibility relation. Two possibilities are compatible
    if neither settles as true anything the other settles as false.
    @cite{holliday-mandelkern-2024} Definition 4.1. -/
structure CompatFrame (S : Type*) where
  compat : S → S → Bool
  compat_refl : ∀ x, compat x x = true
  compat_symm : ∀ x y, compat x y = compat y x

-- ════════════════════════════════════════════════════
-- § 2. Orthocomplement Negation
-- ════════════════════════════════════════════════════

/-- Orthocomplement negation. ¬A = {x | ∀y compatible with x, y ∉ A}.
    A possibility x makes ¬A true iff no compatible possibility makes A
    true — i.e., x's information *settles* ¬A.
    @cite{holliday-mandelkern-2024} Proposition 4.8, eq. (I). -/
def orthoNeg {S : Type*} [FiniteWorlds S] (F : CompatFrame S) (A : BProp S) : BProp S :=
  fun x => FiniteWorlds.worlds.filter (F.compat x) |>.all (fun y => !A y)

/-- Conjunction is intersection (same as classical). -/
def conj {S : Type*} (A B : BProp S) : BProp S := fun x => A x && B x

/-- Disjunction via De Morgan: A ∨ B = ¬(¬A ∧ ¬B).
    Weaker than set-theoretic union. A possibility x makes A ∨ B true iff
    every y compatible with x is itself compatible with some z that makes
    A or B true.
    @cite{holliday-mandelkern-2024} eq. (II). -/
def disj {S : Type*} [FiniteWorlds S] (F : CompatFrame S) (A B : BProp S) : BProp S :=
  orthoNeg F (conj (orthoNeg F A) (orthoNeg F B))

-- ════════════════════════════════════════════════════
-- § 3. Regularity
-- ════════════════════════════════════════════════════

/-- A set A is ◇-regular iff: whenever x ∉ A, there exists y compatible
    with x such that all z compatible with y are also not in A.
    Regularity = "indeterminacy implies compatibility with falsity."
    Only regular sets count as propositions.
    @cite{holliday-mandelkern-2024} Definition 4.3. -/
def isRegular {S : Type*} [FiniteWorlds S] (F : CompatFrame S) (A : BProp S) : Bool :=
  FiniteWorlds.worlds.all fun x =>
    A x || FiniteWorlds.worlds.any fun y =>
      F.compat x y && (FiniteWorlds.worlds.filter (F.compat y)).all (fun z => !A z)

-- ════════════════════════════════════════════════════
-- § 4. Refinement and Worlds
-- ════════════════════════════════════════════════════

/-- Refinement: y ⊑ x iff every possibility compatible with y is also
    compatible with x. A refinement carries at least as much information.
    @cite{holliday-mandelkern-2024} Lemma 4.4, condition 2. -/
def refines {S : Type*} [FiniteWorlds S] (F : CompatFrame S) (y x : S) : Bool :=
  FiniteWorlds.worlds.all fun z => !F.compat y z || F.compat x z

/-- A world is a possibility that refines everything it is compatible
    with — the most informative kind of possibility.
    @cite{holliday-mandelkern-2024} Definition 4.6. -/
def isWorld {S : Type*} [FiniteWorlds S] (F : CompatFrame S) (w : S) : Bool :=
  FiniteWorlds.worlds.all fun x => !F.compat w x || refines F w x

-- ════════════════════════════════════════════════════
-- § 5. The Five-Possibility Path Frame
-- ════════════════════════════════════════════════════

/-- Five possibilities arranged in a path: x₁—x₂—x₃—x₄—x₅.
    The simplest frame whose ortholattice is non-Boolean.
    @cite{holliday-mandelkern-2024} Example 4.11, Figure 7. -/
inductive Poss5 where
  | x1 | x2 | x3 | x4 | x5
  deriving DecidableEq, BEq, Repr, Inhabited

instance : FiniteWorlds Poss5 where
  worlds := [.x1, .x2, .x3, .x4, .x5]
  complete := fun w => by cases w <;> simp

instance : Fintype Poss5 where
  elems := {.x1, .x2, .x3, .x4, .x5}
  complete := fun w => by cases w <;> simp

/-- The path compatibility frame: adjacent possibilities are compatible. -/
def pathFrame : CompatFrame Poss5 where
  compat := fun a b => match a, b with
    | .x1, .x1 | .x1, .x2 | .x2, .x1
    | .x2, .x2 | .x2, .x3 | .x3, .x2
    | .x3, .x3 | .x3, .x4 | .x4, .x3
    | .x4, .x4 | .x4, .x5 | .x5, .x4
    | .x5, .x5 => true
    | _, _ => false
  compat_refl := fun x => by cases x <;> rfl
  compat_symm := fun x y => by cases x <;> cases y <;> rfl

-- Propositions in the path frame ortholattice
private def pLeft : BProp Poss5 := fun x => match x with | .x1 | .x2 => true | _ => false
private def pRight : BProp Poss5 := fun x => match x with | .x4 | .x5 => true | _ => false
private def pMid : BProp Poss5 := fun x => match x with | .x3 => true | _ => false

-- ════════════════════════════════════════════════════
-- § 6. Ortholattice Properties
-- ════════════════════════════════════════════════════

/-- Negation: ¬{x₁,x₂} = {x₄,x₅}. -/
theorem neg_left : orthoNeg pathFrame pLeft = pRight := by
  funext x; cases x <;> native_decide

/-- Negation: ¬{x₄,x₅} = {x₁,x₂}. -/
theorem neg_right : orthoNeg pathFrame pRight = pLeft := by
  funext x; cases x <;> native_decide

/-- Negation: ¬{x₃} = {x₁,x₅}. The "partial" possibility x₃ has a
    non-trivial negation — neither left nor right, but the two endpoints. -/
private def pEndpoints : BProp Poss5 := fun x =>
    match x with | .x1 | .x5 => true | _ => false
theorem neg_mid : orthoNeg pathFrame pMid = pEndpoints := by
  funext x; cases x <;> native_decide

/-- Double negation: ¬¬A = A (involutive on regular sets). -/
theorem doubleNeg_left : orthoNeg pathFrame (orthoNeg pathFrame pLeft) = pLeft := by
  funext x; cases x <;> native_decide

/-- Excluded middle: A ∨ ¬A = S (every possibility verifies it). -/
theorem excludedMiddle_left (x : Poss5) :
    disj pathFrame pLeft (orthoNeg pathFrame pLeft) x = true := by
  cases x <;> native_decide

/-- Non-contradiction: A ∧ ¬A = ∅ (no possibility verifies it). -/
theorem nonContradiction_left (x : Poss5) :
    conj pLeft (orthoNeg pathFrame pLeft) x = false := by
  cases x <;> native_decide

/-- **Distributivity failure.** The key result of possibility semantics.
    C ∧ (A ∨ B) ≠ (C ∧ A) ∨ (C ∧ B), where C = {x₃}, A = {x₁,x₂}, B = {x₄,x₅}.
    Possibility x₃ is compatible with both A and B worlds, so it makes
    A ∨ B true; but it doesn't commit to either disjunct, so neither
    C ∧ A nor C ∧ B is non-empty.
    @cite{holliday-mandelkern-2024} Example 4.11, Figure 8. -/
theorem distributivity_failure :
    conj pMid (disj pathFrame pLeft pRight) .x3 ≠
    disj pathFrame (conj pMid pLeft) (conj pMid pRight) .x3 := by native_decide

/-- The LHS of distributivity at x₃: true (x₃ makes C ∧ (A ∨ B) true). -/
theorem distrib_lhs_at_x3 :
    conj pMid (disj pathFrame pLeft pRight) .x3 = true := by native_decide

/-- The RHS of distributivity at x₃: false (x₃ fails (C∧A) ∨ (C∧B)). -/
theorem distrib_rhs_at_x3 :
    disj pathFrame (conj pMid pLeft) (conj pMid pRight) .x3 = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. Worlds and Regularity
-- ════════════════════════════════════════════════════

/-- x₁ is a world (maximal possibility). -/
theorem x1_is_world : isWorld pathFrame .x1 = true := by native_decide

/-- x₅ is a world. -/
theorem x5_is_world : isWorld pathFrame .x5 = true := by native_decide

/-- x₃ is NOT a world — it's a partial possibility, compatible with
    possibilities on both sides without being a refinement of either. -/
theorem x3_not_world : isWorld pathFrame .x3 = false := by native_decide

/-- All propositions in the ortholattice are regular. -/
theorem regular_left : isRegular pathFrame pLeft = true := by native_decide
theorem regular_right : isRegular pathFrame pRight = true := by native_decide
theorem regular_mid : isRegular pathFrame pMid = true := by native_decide

private def pEmpty : BProp Poss5 := fun _ => false
private def pFull : BProp Poss5 := fun _ => true
theorem regular_empty : isRegular pathFrame pEmpty = true := by native_decide
theorem regular_full : isRegular pathFrame pFull = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. Classical Collapse
-- ════════════════════════════════════════════════════

/-- When compatibility is identity (every possibility is a world),
    orthocomplement reduces to Boolean negation and the ortholattice is
    Boolean. This is the sense in which possible-world semantics is a
    special case of possibility semantics.
    @cite{holliday-mandelkern-2024} Remark 4.9. -/
theorem orthoNeg_classical {S : Type*} [FiniteWorlds S] [DecidableEq S]
    (F : CompatFrame S)
    (hClassical : ∀ x y, F.compat x y = true → x = y)
    (A : BProp S) (x : S) :
    orthoNeg F A x = !A x := by
  unfold orthoNeg
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact List.all_eq_true.mp h x
      (List.mem_filter.mpr ⟨FiniteWorlds.complete x, F.compat_refl x⟩)
  · intro h
    apply List.all_eq_true.mpr
    intro y hy
    have heq := hClassical x y (List.mem_filter.mp hy).2
    subst heq; exact h

/-- The identity compatibility frame: compat x y ↔ x = y. -/
def identityFrame {S : Type*} [DecidableEq S] : CompatFrame S where
  compat := fun x y => decide (x = y)
  compat_refl := fun x => by simp
  compat_symm := fun x y => by simp [eq_comm]

/-- In the identity frame, orthoNeg is pointwise Boolean negation. -/
theorem identityFrame_classical {S : Type*} [FiniteWorlds S] [DecidableEq S]
    (A : BProp S) (x : S) :
    orthoNeg (identityFrame (S := S)) A x = !A x :=
  orthoNeg_classical identityFrame
    (fun a b h => by simp [identityFrame, decide_eq_true_eq] at h; exact h) A x

end Semantics.PossibilitySemantics
