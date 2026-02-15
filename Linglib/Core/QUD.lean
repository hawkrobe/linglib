import Mathlib.Data.Set.Basic

/-!
# QUD (Question Under Discussion)

A QUD partitions the meaning space into equivalence classes. Two meanings are
equivalent under a QUD if they "answer the question the same way."

## References

- Roberts (2012). Information structure in discourse.
- Kao et al. (2014). Nonliteral understanding of number words. PNAS.
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

/-- Trivial QUD: all meanings are equivalent (speaker doesn't care about this dimension). -/
def trivial : QUD M where
  sameAnswer _ _ := true
  refl _ := rfl
  symm _ _ := rfl
  trans _ _ _ _ _ := rfl
  name := "trivial"

/-- Compose two QUDs: equivalent iff equivalent under both. -/
def compose (q1 q2 : QUD M) : QUD M where
  sameAnswer m1 m2 := q1.sameAnswer m1 m2 && q2.sameAnswer m1 m2
  refl m := by simp [q1.refl, q2.refl]
  symm m1 m2 := by rw [q1.symm, q2.symm, Bool.and_comm]
  trans m1 m2 m3 h12 h23 := by
    simp only [Bool.and_eq_true] at *
    exact ⟨q1.trans m1 m2 m3 h12.1 h23.1, q2.trans m1 m2 m3 h12.2 h23.2⟩
  name := s!"{q1.name}∧{q2.name}"

instance : Mul (QUD M) where
  mul := compose

/-- The equivalence class (partition cell) of a meaning under a QUD. -/
def cell (q : QUD M) (m : M) : Set M :=
  {m' : M | q.sameAnswer m m' = true}

/-- Two meanings are in the same cell iff they have the same answer. -/
theorem mem_cell_iff (q : QUD M) (m m' : M) :
    m' ∈ q.cell m ↔ q.sameAnswer m m' = true := by
  simp only [cell, Set.mem_setOf_eq]

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

end ProductQUD

/-- Precision projection for numeric meanings (approximate vs exact). -/
structure PrecisionProjection (N : Type) where
  /-- Round/approximate the value -/
  round : N → N
  /-- Name -/
  name : String := ""

namespace PrecisionProjection

/-- Exact precision: no rounding -/
def exact {N : Type} : PrecisionProjection N where
  round := id
  name := "exact"

/-- Round to nearest multiple of k -/
def roundTo (k : Nat) : PrecisionProjection Nat where
  round n := (n / k) * k
  name := s!"round{k}"

/-- Compose precision with a QUD. Delegates to `QUD.ofProject`. -/
def applyToQUD {M N : Type} [BEq N] [LawfulBEq N]
    (prec : PrecisionProjection N) (proj : M → N) : QUD M :=
  QUD.ofProject (prec.round ∘ proj) prec.name

end PrecisionProjection
