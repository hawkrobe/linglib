import Linglib.Core.Question.Partition.QUD

/-!
# Partition Refinement Lattice
@cite{groenendijk-stokhof-1984} @cite{merin-1999}

Refinement and coarsening order on partitions (`QUD`):

* `refines` (`⊑`) — Q refines Q' iff Q's equivalence classes are subsets of Q''s.
  Equivalent to: knowing the Q-answer determines the Q'-answer.
* `coarsens` — dual of refinement.

## Lattice structure

Partitions form a bounded lattice ordered by refinement:
- Meet (`*` from `Core.Question.Partition.QUD`): coarsest common refinement.
- Top: `exact` (finest).
- Bottom: `trivial` (coarsest).

Antisymmetry holds only up to extensional equivalence of `sameAnswer`; true
propositional antisymmetry would require quotienting.
-/

namespace QUD

variable {M : Type*}

/-- Q refines Q' iff Q's equivalence classes are subsets of Q''s.

Intuitively: knowing the Q-answer tells you the Q'-answer.
If two elements give the same Q-answer, they must give the same Q'-answer.

Forms a partial order on partitions (up to extensional equivalence). -/
def refines (q q' : QUD M) : Prop :=
  ∀ w v, q.sameAnswer w v = true → q'.sameAnswer w v = true

scoped infix:50 " ⊑ " => QUD.refines

/-- Q coarsens Q' iff Q' refines Q (dual of refinement).

Coarsening merges cells: where Q' distinguishes elements, Q may not.
@cite{merin-1999} defines negative attributes in terms of coarsening:
negation is the linguistic device that produces coarsenings on the fly. -/
def coarsens (q q' : QUD M) : Prop := q' ⊑ q

/-- Refinement is reflexive. -/
theorem refines_refl (q : QUD M) : q ⊑ q := λ _ _ h => h

/-- Refinement is transitive. -/
theorem refines_trans {q1 q2 q3 : QUD M} :
    q1 ⊑ q2 → q2 ⊑ q3 → q1 ⊑ q3 :=
  λ h12 h23 w v h1 => h23 w v (h12 w v h1)

/-- Refinement is antisymmetric up to extensional equivalence of `sameAnswer`.

True propositional antisymmetry (`q1 = q2`) would require quotient types;
this is the extensional version. -/
theorem refines_antisymm {q1 q2 : QUD M} :
    q1 ⊑ q2 → q2 ⊑ q1 → (∀ w v, q1.sameAnswer w v = q2.sameAnswer w v) := by
  intro h12 h21 w v
  cases hq1 : q1.sameAnswer w v with
  | false =>
    cases hq2 : q2.sameAnswer w v with
    | false => rfl
    | true => exact absurd (h21 w v hq2) (by simp [hq1])
  | true =>
    exact (h12 w v hq1).symm

/-- All partitions refine (are coarser than or equal to) the trivial partition. -/
theorem all_refine_trivial (q : QUD M) :
    q ⊑ trivial := λ _ _ _ => rfl

/-- The meet (coarsest common refinement) refines the left factor. -/
theorem compose_refines_left (q1 q2 : QUD M) : (q1 * q2) ⊑ q1 := by
  intro w v h
  rw [mul_sameAnswer, Bool.and_eq_true] at h
  exact h.1

/-- The meet (coarsest common refinement) refines the right factor. -/
theorem compose_refines_right (q1 q2 : QUD M) : (q1 * q2) ⊑ q2 := by
  intro w v h
  rw [mul_sameAnswer, Bool.and_eq_true] at h
  exact h.2

/-- The exact (finest) partition refines all partitions. -/
theorem exact_refines_all [BEq M] [LawfulBEq M] (q : QUD M) :
    exact ⊑ q := by
  intro w v h
  rw [exact_sameAnswer_iff] at h
  rw [h]
  exact q.refl v

end QUD
