import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.Closure

/-!
# Compatibility Frames (Possibility Semantics for Orthologic)
@cite{holliday-mandelkern-2024}

Possibility semantics generalizes possible-worlds semantics by replacing
maximal possible worlds with partial *possibilities* ordered by refinement.
A possibility can verify a disjunction without verifying either disjunct.

## Key differences from possible-world semantics

- **Propositions** are not arbitrary sets of possibilities but only
  *regular* sets — those satisfying a closure condition.
- **Negation** is orthocomplement: `¬A = {x | ∀y ◇ x, y ∉ A}`.
- **Disjunction** is De Morgan from orthonegation, weaker than union.
- The resulting algebra of regular propositions is an **ortholattice**,
  not a Boolean algebra. Distributivity, pseudocomplementation, and
  orthomodularity all fail.

## Architecture

This file (`Frames.lean`) is the substrate: compatibility frames,
orthonegation, regularity, refinement, worlds, and the classical-collapse
theorem under identity compatibility. The modal extension (□, ◇, T-axiom)
lives in `Modal.lean`; the abstract `OrthocomplementedLattice` typeclass
is upstream substrate at `Linglib.Core.Order.Ortholattice`; the
`OrthocomplementedLattice` instance for the regular subsets of a frame
lives in `RegularProp.lean`.

Paper-specific instantiations of the substrate (the five-possibility
path frame `Poss5`, the Epistemic Scale, ortholattice failures of
distributivity / orthomodularity / pseudocomplementation, and the
two-world lifting) live in
`Phenomena/Modality/Studies/HollidayMandelkern2024.lean`.

## Conventions

- **Carrier**: propositions are `Set S`. Set-membership notation
  (`x ∈ A`, `A ⊆ B`, `A ∩ B`, `Aᶜ`) is preferred over functional-application
  notation. `Set α` is definitionally `α → Prop`.
- **Decidability**: `CompatFrame` does not bundle `DecidableRel compat`;
  use sites take `[DecidableRel F.compat]` (mathlib idiom — cf.
  `SimpleGraph` + `[DecidableRel G.Adj]`).
- **Finiteness**: `[Fintype S]` only appears on instances/theorems that
  need it (decidability of universally-quantified propositions); raw
  definitions stay Fintype-free.
-/

namespace Semantics.Modality.Orthologic

-- ════════════════════════════════════════════════════
-- § 1. Compatibility Frames
-- ════════════════════════════════════════════════════

/-- A compatibility frame: a set of possibilities with a reflexive,
    symmetric compatibility relation. Two possibilities are compatible
    if neither settles as true anything the other settles as false.
    @cite{holliday-mandelkern-2024} Definition 4.1.

    Decidability of `compat` is *not* bundled — provide a `DecidableRel`
    instance separately for each concrete frame. -/
structure CompatFrame (S : Type*) where
  compat : S → S → Prop
  compat_refl : ∀ x, compat x x
  compat_symm : ∀ x y, compat x y ↔ compat y x

-- ════════════════════════════════════════════════════
-- § 2. Orthocomplement Negation
-- ════════════════════════════════════════════════════

/-- Orthocomplement negation. `¬A = {x | ∀y compatible with x, y ∉ A}`.
    A possibility x makes ¬A true iff no compatible possibility makes A
    true — i.e., x's information *settles* ¬A.
    @cite{holliday-mandelkern-2024} Proposition 4.8, eq. (1). -/
def orthoNeg {S : Type*} (F : CompatFrame S) (A : Set S) : Set S :=
  { x | ∀ y : S, F.compat x y → y ∉ A }

@[simp] theorem mem_orthoNeg {S : Type*} (F : CompatFrame S) (A : Set S) (x : S) :
    x ∈ orthoNeg F A ↔ ∀ y : S, F.compat x y → y ∉ A := Iff.rfl

instance {S : Type*} [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (A : Set S) [DecidablePred (· ∈ A)] (x : S) : Decidable (x ∈ orthoNeg F A) := by
  show Decidable (∀ y : S, F.compat x y → y ∉ A); infer_instance

/-- Application-form alias of the membership-form `Decidable` instance,
    for goals that reduce `orthoNeg F A x` instead of `x ∈ orthoNeg F A`.
    Uses `DecidablePred A` (not `DecidablePred (· ∈ A)`) so it synthesises
    from the standard `instance : DecidablePred A` users define. -/
instance orthoNeg_apply_decidable {S : Type*} [Fintype S] (F : CompatFrame S)
    [DecidableRel F.compat] (A : Set S) [DecidablePred A] (x : S) :
    Decidable (orthoNeg F A x) := by
  show Decidable (∀ y : S, F.compat x y → y ∉ A)
  have : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  infer_instance

/-- Conjunction is intersection (transparent alias for `Set.inter`).
    Kept as a named operation for symmetry with `disj` in study-file
    theorems; `conj A B = A ∩ B` definitionally. -/
abbrev conj {S : Type*} (A B : Set S) : Set S := A ∩ B

/-- Disjunction via De Morgan: `A ∨ B = ¬(¬A ∩ ¬B)`.
    Strictly weaker than set-theoretic union: a possibility x makes A ∨ B
    true iff every y compatible with x is itself compatible with some z
    that makes A or B true (the unpacked form, paper eq. (2)).
    @cite{holliday-mandelkern-2024} Proposition 4.8, eq. (2). -/
def disj {S : Type*} (F : CompatFrame S) (A B : Set S) : Set S :=
  orthoNeg F (orthoNeg F A ∩ orthoNeg F B)

instance {S : Type*} [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (A B : Set S) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (x : S) :
    Decidable (x ∈ disj F A B) := by
  unfold disj; infer_instance

instance disj_apply_decidable {S : Type*} [Fintype S] (F : CompatFrame S)
    [DecidableRel F.compat] (A B : Set S) [DecidablePred A] [DecidablePred B]
    (x : S) : Decidable (disj F A B x) := by
  show Decidable (∀ y : S, F.compat x y → y ∉ orthoNeg F A ∩ orthoNeg F B)
  have hA : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  have hB : DecidablePred (· ∈ B) := inferInstanceAs (DecidablePred B)
  infer_instance

instance conj_apply_decidable {S : Type*} (A B : Set S)
    [DecidablePred A] [DecidablePred B] (x : S) :
    Decidable (conj A B x) :=
  inferInstanceAs (Decidable (A x ∧ B x))

-- ════════════════════════════════════════════════════
-- § 3. Regularity
-- ════════════════════════════════════════════════════

/-- A set A is ◇-regular iff: whenever x ∉ A, there exists y compatible
    with x such that all z compatible with y are also not in A.
    Regularity = "indeterminacy implies compatibility with falsity."
    Only regular sets count as propositions.
    @cite{holliday-mandelkern-2024} Definition 4.3. -/
def isRegular {S : Type*} (F : CompatFrame S) (A : Set S) : Prop :=
  ∀ x : S, x ∈ A ∨ ∃ y : S, F.compat x y ∧ ∀ z : S, F.compat y z → z ∉ A

instance {S : Type*} [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (A : Set S) [DecidablePred (· ∈ A)] : Decidable (isRegular F A) := by
  unfold isRegular; infer_instance

/-- Application-form alias for `isRegular` so `decide` finds it from
    `[DecidablePred A]` instances directly. -/
instance isRegular_apply_decidable {S : Type*} [Fintype S] (F : CompatFrame S)
    [DecidableRel F.compat] (A : Set S) [DecidablePred A] : Decidable (isRegular F A) := by
  unfold isRegular
  have : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  infer_instance

-- ════════════════════════════════════════════════════
-- § 4. Refinement and Worlds
-- ════════════════════════════════════════════════════

/-- Refinement: y ⊑ x iff every possibility compatible with y is also
    compatible with x. A refinement carries at least as much information.
    @cite{holliday-mandelkern-2024} Lemma 4.4, condition 2. -/
def refines {S : Type*} (F : CompatFrame S) (y x : S) : Prop :=
  ∀ z : S, F.compat y z → F.compat x z

instance {S : Type*} [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (y x : S) : Decidable (refines F y x) := by
  unfold refines; infer_instance

/-- A world is a possibility that refines everything it is compatible
    with — the most informative kind of possibility.
    @cite{holliday-mandelkern-2024} Definition 4.6. -/
def isWorld {S : Type*} (F : CompatFrame S) (w : S) : Prop :=
  ∀ x : S, F.compat w x → refines F w x

instance {S : Type*} [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (w : S) : Decidable (isWorld F w) := by
  unfold isWorld; infer_instance

-- ════════════════════════════════════════════════════
-- § 5. Classical Collapse
-- ════════════════════════════════════════════════════

/-- When compatibility is identity (every possibility is a world),
    orthocomplement reduces to Boolean negation and the ortholattice is
    Boolean. This is the sense in which possible-world semantics is a
    special case of possibility semantics.
    @cite{holliday-mandelkern-2024} Remark 4.9 characterizes Boolean
    collapse as compatibility-implies-compossibility; the identity frame
    below is the simplest instance of that condition. -/
theorem orthoNeg_classical {S : Type*}
    (F : CompatFrame S)
    (hClassical : ∀ x y, F.compat x y → x = y)
    (A : Set S) (x : S) :
    x ∈ orthoNeg F A ↔ x ∉ A := by
  simp only [mem_orthoNeg]
  constructor
  · intro h hAx
    exact h x (F.compat_refl x) hAx
  · intro hNotA y hcompat hAy
    have heq := hClassical x y hcompat
    subst heq; exact hNotA hAy

/-- The identity compatibility frame: compat x y ↔ x = y. -/
def identityFrame {S : Type*} [DecidableEq S] : CompatFrame S where
  compat := fun x y => x = y
  compat_refl := fun _ => rfl
  compat_symm := fun _ _ => eq_comm

instance {S : Type*} [DecidableEq S] :
    DecidableRel (identityFrame (S := S)).compat := fun a b => by
  show Decidable (a = b); infer_instance

/-- In the identity frame, orthoNeg is pointwise negation. -/
theorem identityFrame_classical {S : Type*} [DecidableEq S]
    (A : Set S) (x : S) :
    x ∈ orthoNeg (identityFrame (S := S)) A ↔ x ∉ A :=
  orthoNeg_classical identityFrame (fun _ _ h => h) A x

-- ════════════════════════════════════════════════════
-- § 6. The c_◇ Closure Operator
-- ════════════════════════════════════════════════════

/-- The c_◇ closure operator on `Set S` for a compatibility frame `F`,
    mapping `A ↦ {x | ∀ y ◇ x, ∃ z ◇ y, z ∈ A}`. The fixed points of
    `regularClosure F` are precisely the ◇-regular sets — making
    `RegularProp F = (regularClosure F).fixedPoints` a mathlib-typed
    closure-operator-based construction.
    @cite{holliday-mandelkern-2024} footnote 19 (page 858 of the
    published JPL version). -/
def regularClosure {S : Type*} (F : CompatFrame S) : ClosureOperator (Set S) where
  toFun A := { x | ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A }
  monotone' _ _ hAB _ hx y hy := by
    obtain ⟨z, hyz, hz⟩ := hx y hy; exact ⟨z, hyz, hAB hz⟩
  le_closure' _ x hx _ hy := ⟨x, (F.compat_symm _ _).mp hy, hx⟩
  idempotent' A := by
    apply Set.eq_of_subset_of_subset
    · intro x hx y hy
      obtain ⟨z, hyz, hz⟩ := hx y hy
      have hzy : F.compat z y := (F.compat_symm _ _).mp hyz
      obtain ⟨w, hyw, hwA⟩ := hz y hzy
      exact ⟨w, hyw, hwA⟩
    · intro x hx y hy
      obtain ⟨z, hyz, hz⟩ := hx y hy
      exact ⟨z, hyz, fun y' hy' => ⟨z, (F.compat_symm _ _).mp hy', hz⟩⟩
  IsClosed A := isRegular F A
  isClosed_iff {A} := by
    constructor
    · -- isRegular F A → c_◇(A) = A
      intro hReg
      apply Set.eq_of_subset_of_subset
      · intro x hx
        rcases hReg x with hxA | ⟨y, hxy, hy⟩
        · exact hxA
        · exfalso
          obtain ⟨z, hyz, hzA⟩ := hx y hxy
          exact hy z hyz hzA
      · intro x hx _ hy
        exact ⟨x, (F.compat_symm _ _).mp hy, hx⟩
    · -- c_◇(A) = A → isRegular F A
      intro hEq x
      by_cases h : x ∈ A
      · exact Or.inl h
      · right
        -- x ∉ A = c_◇(A), so ¬(∀ y ◇ x, ∃ z ◇ y, z ∈ A)
        have hNot : ¬ ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A := by
          intro habs
          apply h
          rw [← hEq]
          exact habs
        push_neg at hNot
        obtain ⟨y, hxy, hy⟩ := hNot
        refine ⟨y, hxy, fun z hyz hzA => ?_⟩
        exact hy z hyz hzA

@[simp] theorem mem_regularClosure {S : Type*} (F : CompatFrame S) (A : Set S) (x : S) :
    x ∈ regularClosure F A ↔ ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A :=
  Iff.rfl

theorem regularClosure_isClosed_iff_isRegular {S : Type*} (F : CompatFrame S) (A : Set S) :
    (regularClosure F).IsClosed A ↔ isRegular F A := Iff.rfl

end Semantics.Modality.Orthologic
