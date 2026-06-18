import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Closure

/-!
# Compatibility Frames (Possibility Semantics for Orthologic)
[holliday-mandelkern-2024]

Possibility semantics generalizes possible-worlds semantics by replacing
maximal worlds with partial *possibilities* ordered by refinement: a
possibility can verify a disjunction without verifying either disjunct.
Propositions are the *regular* sets, negation is orthocomplement, and the
resulting algebra of regular propositions is an ortholattice — not a Boolean
algebra (distributivity, pseudocomplementation, and orthomodularity all fail).

## Main definitions

* `CompatFrame` — a set of possibilities with a reflexive, symmetric
  compatibility relation.
* `orthoNeg`, `conj`, `disj` — orthocomplement negation and the De Morgan
  connectives.
* `IsRegular`, `refines`, `IsWorld` — regularity, the refinement order, and
  worlds (maximally informative possibilities).
* `regularClosure` — the `c_◇` closure operator whose fixed points are the
  regular sets.
* `orthoNeg_classical`, `identityFrame` — the classical collapse under
  identity compatibility.

## Implementation notes

This file is substrate. The modal extension (□, ◇, T-axiom) lives in
`Modal.lean`; the bundled ortholattice of regular propositions in
`RegularProp.lean`; the abstract `OrthocomplementedLattice` class in
`Core.Order.Ortholattice`; and the paper's concrete instantiations (the
`Poss5` path frame, the Epistemic Scale, the ortholattice failures) in
`Studies.HollidayMandelkern2024`.

Propositions are `Set S`, with set-membership notation preferred.
Decidability of `compat` is not bundled — use sites take
`[DecidableRel F.compat]` (mathlib's `SimpleGraph` + `[DecidableRel G.Adj]`
idiom), and `[Fintype S]` appears only where decidability of universally
quantified propositions needs it.
-/

namespace Orthologic

variable {S : Type*}

/-! ### Compatibility frames -/

/-- A compatibility frame: a set of possibilities with a reflexive,
    symmetric compatibility relation. Two possibilities are compatible
    if neither settles as true anything the other settles as false.
    [holliday-mandelkern-2024] Definition 4.1.

    Decidability of `compat` is *not* bundled — provide a `DecidableRel`
    instance separately for each concrete frame. -/
structure CompatFrame (S : Type*) where
  compat : S → S → Prop
  compat_refl : Std.Refl compat
  compat_symm : Std.Symm compat

namespace CompatFrame

/-- Compatibility is reflexive (accessor for the bundled `Std.Refl`). -/
theorem refl (F : CompatFrame S) (x : S) : F.compat x x := F.compat_refl.refl x

/-- Compatibility is symmetric: `h.symm : F.compat y x` for `h : F.compat x y`
    (mirrors `SimpleGraph.Adj.symm`). -/
theorem compat.symm {F : CompatFrame S} {x y : S} (h : F.compat x y) : F.compat y x :=
  F.compat_symm.symm x y h

end CompatFrame

/-! ### Orthocomplement negation and connectives -/

/-- Orthocomplement negation. `¬A = {x | ∀y compatible with x, y ∉ A}`.
    A possibility x makes ¬A true iff no compatible possibility makes A
    true — i.e., x's information *settles* ¬A.
    [holliday-mandelkern-2024] Proposition 4.8, eq. (1). -/
def orthoNeg (F : CompatFrame S) (A : Set S) : Set S :=
  { x | ∀ y : S, F.compat x y → y ∉ A }

@[simp] theorem mem_orthoNeg (F : CompatFrame S) (A : Set S) (x : S) :
    x ∈ orthoNeg F A ↔ ∀ y : S, F.compat x y → y ∉ A := Iff.rfl

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (A : Set S) [DecidablePred (· ∈ A)] (x : S) : Decidable (x ∈ orthoNeg F A) := by
  show Decidable (∀ y : S, F.compat x y → y ∉ A); infer_instance

/-- Application-form alias of the membership-form `Decidable` instance,
    for goals that reduce `orthoNeg F A x` instead of `x ∈ orthoNeg F A`.
    Uses `DecidablePred A` (not `DecidablePred (· ∈ A)`) so it synthesises
    from the standard `instance : DecidablePred A` users define. -/
instance orthoNeg_apply_decidable [Fintype S] (F : CompatFrame S)
    [DecidableRel F.compat] (A : Set S) [DecidablePred A] (x : S) :
    Decidable (orthoNeg F A x) := by
  show Decidable (∀ y : S, F.compat x y → y ∉ A)
  have : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  infer_instance

/-- Conjunction is intersection (transparent alias for `Set.inter`).
    Kept as a named operation for symmetry with `disj` in study-file
    theorems; `conj A B = A ∩ B` definitionally. -/
abbrev conj (A B : Set S) : Set S := A ∩ B

/-- Disjunction via De Morgan: `A ∨ B = ¬(¬A ∩ ¬B)`.
    Strictly weaker than set-theoretic union: a possibility x makes A ∨ B
    true iff every y compatible with x is itself compatible with some z
    that makes A or B true (the unpacked form, paper eq. (2)).
    [holliday-mandelkern-2024] Proposition 4.8, eq. (2). -/
def disj (F : CompatFrame S) (A B : Set S) : Set S :=
  orthoNeg F (orthoNeg F A ∩ orthoNeg F B)

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (A B : Set S) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (x : S) :
    Decidable (x ∈ disj F A B) := by
  unfold disj; infer_instance

instance disj_apply_decidable [Fintype S] (F : CompatFrame S)
    [DecidableRel F.compat] (A B : Set S) [DecidablePred A] [DecidablePred B]
    (x : S) : Decidable (disj F A B x) := by
  show Decidable (∀ y : S, F.compat x y → y ∉ orthoNeg F A ∩ orthoNeg F B)
  have hA : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  have hB : DecidablePred (· ∈ B) := inferInstanceAs (DecidablePred B)
  infer_instance

instance conj_apply_decidable (A B : Set S)
    [DecidablePred A] [DecidablePred B] (x : S) :
    Decidable (conj A B x) :=
  inferInstanceAs (Decidable (A x ∧ B x))

/-! ### Regularity -/

/-- A set A is ◇-regular iff: whenever x ∉ A, there exists y compatible
    with x such that all z compatible with y are also not in A.
    Regularity = "indeterminacy implies compatibility with falsity."
    Only regular sets count as propositions.
    [holliday-mandelkern-2024] Definition 4.3. -/
def IsRegular (F : CompatFrame S) (A : Set S) : Prop :=
  ∀ x : S, x ∈ A ∨ ∃ y : S, F.compat x y ∧ ∀ z : S, F.compat y z → z ∉ A

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (A : Set S) [DecidablePred (· ∈ A)] : Decidable (IsRegular F A) := by
  unfold IsRegular; infer_instance

/-- Application-form alias for `IsRegular` so `decide` finds it from
    `[DecidablePred A]` instances directly. -/
instance isRegular_apply_decidable [Fintype S] (F : CompatFrame S)
    [DecidableRel F.compat] (A : Set S) [DecidablePred A] : Decidable (IsRegular F A) := by
  unfold IsRegular
  have : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  infer_instance

/-! ### Refinement and worlds -/

/-- Refinement: y ⊑ x iff every possibility compatible with y is also
    compatible with x. A refinement carries at least as much information.
    [holliday-mandelkern-2024] Lemma 4.4, condition 2. -/
def refines (F : CompatFrame S) (y x : S) : Prop :=
  ∀ z : S, F.compat y z → F.compat x z

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (y x : S) : Decidable (refines F y x) := by
  unfold refines; infer_instance

/-- A world is a possibility that refines everything it is compatible
    with — the most informative kind of possibility.
    [holliday-mandelkern-2024] Definition 4.6. -/
def IsWorld (F : CompatFrame S) (w : S) : Prop :=
  ∀ x : S, F.compat w x → refines F w x

instance [Fintype S] (F : CompatFrame S) [DecidableRel F.compat]
    (w : S) : Decidable (IsWorld F w) := by
  unfold IsWorld; infer_instance

/-! ### Classical collapse -/

/-- When compatibility is identity (every possibility is a world),
    orthocomplement reduces to Boolean negation and the ortholattice is
    Boolean. This is the sense in which possible-world semantics is a
    special case of possibility semantics.
    [holliday-mandelkern-2024] Remark 4.9 characterizes Boolean
    collapse as compatibility-implies-compossibility; the identity frame
    below is the simplest instance of that condition. -/
theorem orthoNeg_classical
    (F : CompatFrame S)
    (hClassical : ∀ x y, F.compat x y → x = y)
    (A : Set S) (x : S) :
    x ∈ orthoNeg F A ↔ x ∉ A := by
  simp only [mem_orthoNeg]
  constructor
  · intro h hAx
    exact h x (F.refl x) hAx
  · intro hNotA y hcompat hAy
    have heq := hClassical x y hcompat
    subst heq; exact hNotA hAy

/-- The identity compatibility frame: compat x y ↔ x = y. -/
def identityFrame [DecidableEq S] : CompatFrame S where
  compat := λ x y => x = y
  compat_refl := ⟨λ _ => rfl⟩
  compat_symm := ⟨λ _ _ h => h.symm⟩

instance [DecidableEq S] :
    DecidableRel (identityFrame (S := S)).compat := λ a b => by
  show Decidable (a = b); infer_instance

/-- In the identity frame, orthoNeg is pointwise negation. -/
theorem identityFrame_classical [DecidableEq S]
    (A : Set S) (x : S) :
    x ∈ orthoNeg (identityFrame (S := S)) A ↔ x ∉ A :=
  orthoNeg_classical identityFrame (λ _ _ h => h) A x

/-! ### The c_◇ closure operator -/

/-- The c_◇ closure operator on `Set S` for a compatibility frame `F`,
    mapping `A ↦ {x | ∀ y ◇ x, ∃ z ◇ y, z ∈ A}`. Its fixed points are precisely the
    `◇`-regular sets (`IsRegular F`), i.e. the underlying sets of `CompatFrame.Regular`.
    [holliday-mandelkern-2024] footnote 19 (page 858 of the
    published JPL version). -/
def regularClosure (F : CompatFrame S) : ClosureOperator (Set S) where
  toFun A := { x | ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A }
  monotone' _ _ hAB _ hx y hy := by
    obtain ⟨z, hyz, hz⟩ := hx y hy; exact ⟨z, hyz, hAB hz⟩
  le_closure' _ x hx _ hy := ⟨x, hy.symm, hx⟩
  idempotent' A := by
    apply Set.eq_of_subset_of_subset
    · intro x hx y hy
      obtain ⟨z, hyz, hz⟩ := hx y hy
      have hzy : F.compat z y := hyz.symm
      obtain ⟨w, hyw, hwA⟩ := hz y hzy
      exact ⟨w, hyw, hwA⟩
    · intro x hx y hy
      obtain ⟨z, hyz, hz⟩ := hx y hy
      exact ⟨z, hyz, λ y' hy' => ⟨z, hy'.symm, hz⟩⟩
  IsClosed A := IsRegular F A
  isClosed_iff {A} := by
    constructor
    · -- IsRegular F A → c_◇(A) = A
      intro hReg
      apply Set.eq_of_subset_of_subset
      · intro x hx
        rcases hReg x with hxA | ⟨y, hxy, hy⟩
        · exact hxA
        · exfalso
          obtain ⟨z, hyz, hzA⟩ := hx y hxy
          exact hy z hyz hzA
      · intro x hx _ hy
        exact ⟨x, hy.symm, hx⟩
    · -- c_◇(A) = A → IsRegular F A
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
        push Not at hNot
        obtain ⟨y, hxy, hy⟩ := hNot
        exact ⟨y, hxy, hy⟩

@[simp] theorem mem_regularClosure (F : CompatFrame S) (A : Set S) (x : S) :
    x ∈ regularClosure F A ↔ ∀ y, F.compat x y → ∃ z, F.compat y z ∧ z ∈ A :=
  Iff.rfl

theorem regularClosure_isClosed_iff_isRegular (F : CompatFrame S) (A : Set S) :
    (regularClosure F).IsClosed A ↔ IsRegular F A := Iff.rfl

end Orthologic
