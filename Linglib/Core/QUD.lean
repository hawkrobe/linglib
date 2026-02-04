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

variable [BEq M]

/-- The identity QUD: speaker wants to convey exact meaning -/
def exact [LawfulBEq M] : QUD M where
  sameAnswer m1 m2 := m1 == m2
  refl m := beq_self_eq_true m
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := "exact"

/-- Trivial QUD: all meanings are equivalent (speaker doesn't care about this dimension) -/
def trivial : QUD M where
  sameAnswer _ _ := true
  refl _ := rfl
  symm _ _ := rfl
  trans _ _ _ _ _ := rfl
  name := "trivial"

/-- Build QUD from a projection function -/
def ofProject {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (name : String := "") : QUD M where
  sameAnswer m1 m2 := f m1 == f m2
  refl m := beq_self_eq_true (f m)
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := name

/-- Compose two QUDs: equivalent iff equivalent under both -/
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

section ProjectionTheorems

variable {A : Type} [BEq A] [LawfulBEq A]

/-- `sameAnswer` for projection QUD iff same image under `f`. -/
theorem ofProject_sameAnswer_iff (f : M → A) (m1 m2 : M) :
    (ofProject f).sameAnswer m1 m2 = true ↔ f m1 = f m2 := by
  simp only [ofProject, beq_iff_eq]

end ProjectionTheorems

/-- The equivalence class (partition cell) of a meaning under a QUD. -/
def cell (q : QUD M) (m : M) : Set M :=
  {m' : M | q.sameAnswer m m' = true}

/-- For projection QUDs, cells are exactly fibers of the projection. -/
theorem ofProject_cell_eq_fiber {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (m : M) :
    (ofProject f).cell m = {m' : M | f m' = f m} := by
  ext m'
  simp only [cell, Set.mem_setOf_eq, ofProject, beq_iff_eq]
  exact eq_comm

/-- Two meanings are in the same cell iff they have the same answer -/
theorem mem_cell_iff (q : QUD M) (m m' : M) :
    m' ∈ q.cell m ↔ q.sameAnswer m m' = true := by
  simp only [cell, Set.mem_setOf_eq]

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

/-- Compose precision with a QUD -/
def applyToQUD {M N : Type} [BEq N] [LawfulBEq N]
    (prec : PrecisionProjection N) (proj : M → N) : QUD M where
  sameAnswer m1 m2 := prec.round (proj m1) == prec.round (proj m2)
  refl m := beq_self_eq_true (prec.round (proj m))
  symm m1 m2 := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩
  trans m1 m2 m3 h12 h23 := by
    rw [beq_iff_eq] at *
    exact h12.trans h23
  name := prec.name

end PrecisionProjection

namespace QUD

variable {M : Type*}

/-- Goal projection: are two meanings equivalent for the speaker's purpose? -/
def goalEquiv (q : QUD M) (m1 m2 : M) : Bool := q.sameAnswer m1 m2

/-- Goal equivalence is partition membership. -/
theorem goalEquiv_iff_same_cell (q : QUD M) (m1 m2 : M) :
    q.goalEquiv m1 m2 = true ↔ m2 ∈ q.cell m1 := by
  simp only [goalEquiv, cell, Set.mem_setOf_eq]

/-- For projection QUDs, goal equivalence iff same projection. -/
theorem goalEquiv_ofProject_iff {A : Type} [BEq A] [LawfulBEq A] (f : M → A) (m1 m2 : M) :
    (ofProject f).goalEquiv m1 m2 = true ↔ f m1 = f m2 := by
  simp only [goalEquiv, ofProject, beq_iff_eq]

end QUD
