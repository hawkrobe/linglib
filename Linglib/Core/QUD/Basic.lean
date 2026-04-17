import Mathlib.Data.Set.Basic

/-!
# QUD: Equivalence-Relation Partitioning of a Meaning Space
@cite{roberts-2012}

A `QUD M` partitions a meaning space `M` via an equivalence relation: two
meanings are equivalent iff they "answer the question the same way."

This file is the algebraic core: the `QUD` structure, its `Setoid` view,
constructors (`trivial`, `compose`, `ofProject`, `ofDecEq`, `exact`),
equivalence-class cells, and the `ProductQUD` projections. Inquisitive
content (`Issue`, `InfoState`) lives in `Core/Inquisitive.lean`; Roberts 2012
relevance machinery in `Core/QUD/Relevance.lean`.
-/

/-- A QUD partitions the meaning space via an equivalence relation.
Two meanings are equivalent if they "answer the question the same way." -/
structure QUD (M : Type*) where
  /-- Are two meanings equivalent under this QUD? -/
  sameAnswer : M → M → Bool
  /-- Equivalence must be reflexive -/
  refl : ∀ m, sameAnswer m m = true
  /-- Equivalence must be symmetric -/
  symm : ∀ m1 m2, sameAnswer m1 m2 = sameAnswer m2 m1
  /-- Equivalence must be transitive -/
  trans : ∀ m1 m2 m3, sameAnswer m1 m2 = true → sameAnswer m2 m3 = true → sameAnswer m1 m3 = true
  /-- Name for display/debugging -/
  name : String := ""

namespace QUD

variable {M : Type*}

section EquivalenceProperties

variable (q : QUD M)

/-- Reflexivity is guaranteed by construction -/
theorem isReflexive : ∀ m, q.sameAnswer m m = true := q.refl

/-- Symmetry is guaranteed by construction -/
theorem isSymmetric : ∀ m1 m2, q.sameAnswer m1 m2 = q.sameAnswer m2 m1 := q.symm

/-- Transitivity is guaranteed by construction -/
theorem isTransitive : ∀ m1 m2 m3,
    q.sameAnswer m1 m2 = true → q.sameAnswer m2 m3 = true → q.sameAnswer m1 m3 = true := q.trans

end EquivalenceProperties

/-- Convert QUD's equivalence relation to a Mathlib `Setoid`.

This enables `Finpartition.ofSetoid` for partition-based expected utility
decomposition, replacing ~200 lines of custom foldl arithmetic. -/
def toSetoid (q : QUD M) : Setoid M where
  r := λ a b => q.sameAnswer a b = true
  iseqv := {
    refl := λ a => q.refl a
    symm := λ {a b} h => by rw [q.symm] at h; exact h
    trans := λ {a b c} h1 h2 => q.trans a b c h1 h2
  }

instance decidableRel_toSetoid (q : QUD M) : DecidableRel q.toSetoid.r :=
  λ a b => inferInstanceAs (Decidable (q.sameAnswer a b = true))

/-- Trivial QUD: all meanings are equivalent (speaker doesn't care about this dimension). -/
def trivial : QUD M where
  sameAnswer _ _ := true
  refl _ := rfl
  symm _ _ := rfl
  trans _ _ _ _ _ := rfl
  name := "trivial"

@[simp] theorem trivial_sameAnswer (m1 m2 : M) :
    (trivial : QUD M).sameAnswer m1 m2 = true := rfl

/-- Compose two QUDs: equivalent iff equivalent under both. -/
def compose (q1 q2 : QUD M) : QUD M where
  sameAnswer m1 m2 := q1.sameAnswer m1 m2 && q2.sameAnswer m1 m2
  refl m := by simp [q1.refl, q2.refl]
  symm m1 m2 := by rw [q1.symm, q2.symm, Bool.and_comm]
  trans m1 m2 m3 h12 h23 := by
    simp only [Bool.and_eq_true] at *
    exact ⟨q1.trans m1 m2 m3 h12.1 h23.1, q2.trans m1 m2 m3 h12.2 h23.2⟩
  name := s!"{q1.name}∧{q2.name}"

@[simp] theorem compose_sameAnswer (q1 q2 : QUD M) (m1 m2 : M) :
    (compose q1 q2).sameAnswer m1 m2 = (q1.sameAnswer m1 m2 && q2.sameAnswer m1 m2) := rfl

theorem compose_sameAnswer_iff (q1 q2 : QUD M) (m1 m2 : M) :
    (compose q1 q2).sameAnswer m1 m2 = true ↔
    q1.sameAnswer m1 m2 = true ∧ q2.sameAnswer m1 m2 = true := by
  simp only [compose_sameAnswer, Bool.and_eq_true]

instance : Mul (QUD M) where
  mul := compose

@[simp] theorem mul_sameAnswer (q1 q2 : QUD M) (m1 m2 : M) :
    (q1 * q2).sameAnswer m1 m2 = (q1.sameAnswer m1 m2 && q2.sameAnswer m1 m2) := rfl

/-- The equivalence class (partition cell) of a meaning under a QUD. -/
def cell (q : QUD M) (m : M) : Set M :=
  {m' : M | q.sameAnswer m m' = true}

/-- Two meanings are in the same cell iff they have the same answer. -/
theorem mem_cell_iff (q : QUD M) (m m' : M) :
    m' ∈ q.cell m ↔ q.sameAnswer m m' = true := by
  simp only [cell, Set.mem_setOf_eq]

theorem cell_self (q : QUD M) (m : M) : m ∈ q.cell m := by
  simp only [mem_cell_iff]; exact q.refl m

theorem mem_cell_symm (q : QUD M) (m m' : M) :
    m' ∈ q.cell m ↔ m ∈ q.cell m' := by
  simp only [mem_cell_iff]
  rw [q.symm]

@[simp] theorem toSetoid_r (q : QUD M) (a b : M) :
    q.toSetoid.r a b ↔ q.sameAnswer a b = true := Iff.rfl

/-- Build QUD from a projection function using `DecidableEq` on the codomain.
Avoids the need for `BEq` + `LawfulBEq`; useful when the codomain only derives
`DecidableEq` (which is common for inductive types in Lean 4).

Example: `QUD.ofDecEq MagriWorld.grade` partitions by grade value. -/
def ofDecEq {α : Type*} [DecidableEq α] (project : M → α) (name : String := "") : QUD M where
  sameAnswer w v := decide (project w = project v)
  refl w := decide_eq_true_eq.mpr rfl
  symm w v := by
    show decide (project w = project v) = decide (project v = project w)
    congr 1; exact propext ⟨Eq.symm, Eq.symm⟩
  trans w v u h1 h2 := by
    rw [decide_eq_true_eq] at *
    exact h1.trans h2
  name := name

@[simp] theorem ofDecEq_sameAnswer {α : Type*} [DecidableEq α]
    (project : M → α) (name : String) (w v : M) :
    (ofDecEq project name).sameAnswer w v = decide (project w = project v) := rfl

theorem ofDecEq_sameAnswer_iff {α : Type*} [DecidableEq α]
    (project : M → α) (name : String) (w v : M) :
    (ofDecEq project name).sameAnswer w v = true ↔ project w = project v := by
  simp only [ofDecEq_sameAnswer, decide_eq_true_eq]

/-- Build QUD from a projection function with `BEq`/`LawfulBEq` codomain.

This is the primary constructor for QUDs over types with Boolean equality.
`exact`, `binaryPartition`, and `PrecisionProjection.applyToQUD` all
delegate to this. -/
def ofProject {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (name : String := "") : QUD M where
  sameAnswer m1 m2 := f m1 == f m2
  refl m := beq_self_eq_true (f m)
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := name

@[simp] theorem ofProject_sameAnswer {A : Type} [BEq A] [LawfulBEq A]
    (f : M → A) (m1 m2 : M) :
    (ofProject f).sameAnswer m1 m2 = (f m1 == f m2) := rfl

/-- `sameAnswer` for projection QUD iff same image under `f`. -/
theorem ofProject_sameAnswer_iff {A : Type} [BEq A] [LawfulBEq A]
    (f : M → A) (m1 m2 : M) :
    (ofProject f).sameAnswer m1 m2 = true ↔ f m1 = f m2 := by
  simp only [ofProject_sameAnswer, beq_iff_eq]

/-- For projection QUDs, cells are exactly fibers of the projection. -/
theorem ofProject_cell_eq_fiber {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (m : M) :
    (ofProject f).cell m = {m' : M | f m' = f m} := by
  ext m'
  simp only [cell, Set.mem_setOf_eq, ofProject_sameAnswer, beq_iff_eq]
  exact eq_comm

section BEqConstructors
variable [BEq M]

/-- The identity QUD: speaker wants to convey exact meaning.
Each meaning is its own equivalence class. -/
def exact [LawfulBEq M] : QUD M where
  sameAnswer m1 m2 := m1 == m2
  refl m := beq_self_eq_true m
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := "exact"

@[simp] theorem exact_sameAnswer [LawfulBEq M] (m1 m2 : M) :
    (exact : QUD M).sameAnswer m1 m2 = (m1 == m2) := rfl

theorem exact_sameAnswer_iff [LawfulBEq M] (m1 m2 : M) :
    (exact : QUD M).sameAnswer m1 m2 = true ↔ m1 = m2 := by
  simp only [exact_sameAnswer, beq_iff_eq]

end BEqConstructors

end QUD

namespace ProductQUD

variable {A B : Type} [BEq A] [BEq B] [LawfulBEq A] [LawfulBEq B]

/-- QUD that cares only about first component -/
def fst : QUD (A × B) :=
  QUD.ofProject Prod.fst "fst"

/-- QUD that cares only about second component -/
def snd : QUD (A × B) :=
  QUD.ofProject Prod.snd "snd"

/-- QUD that cares about both components (exact) -/
def both : QUD (A × B) :=
  QUD.exact (M := A × B)

omit [BEq B] [LawfulBEq B] in
@[simp] theorem fst_sameAnswer (p1 p2 : A × B) :
    (fst : QUD (A × B)).sameAnswer p1 p2 = (p1.fst == p2.fst) := rfl

omit [BEq B] [LawfulBEq B] in
theorem fst_sameAnswer_iff (p1 p2 : A × B) :
    (fst : QUD (A × B)).sameAnswer p1 p2 = true ↔ p1.fst = p2.fst := by
  simp only [fst_sameAnswer, beq_iff_eq]

omit [BEq A] [LawfulBEq A] in
@[simp] theorem snd_sameAnswer (p1 p2 : A × B) :
    (snd : QUD (A × B)).sameAnswer p1 p2 = (p1.snd == p2.snd) := rfl

omit [BEq A] [LawfulBEq A] in
theorem snd_sameAnswer_iff (p1 p2 : A × B) :
    (snd : QUD (A × B)).sameAnswer p1 p2 = true ↔ p1.snd = p2.snd := by
  simp only [snd_sameAnswer, beq_iff_eq]

@[simp] theorem both_sameAnswer (p1 p2 : A × B) :
    (both : QUD (A × B)).sameAnswer p1 p2 = (p1 == p2) := rfl

theorem both_sameAnswer_iff (p1 p2 : A × B) :
    (both : QUD (A × B)).sameAnswer p1 p2 = true ↔ p1 = p2 := by
  simp only [both_sameAnswer, beq_iff_eq]

end ProductQUD
