import Linglib.Core.QUD
import Linglib.Core.DecisionTheory
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Partition Lattice

Refinement, coarsening, and cell enumeration for partitions (`QUD`).

Partitions arise wherever a domain is classified into mutually exclusive,
exhaustive categories. Groenendijk & Stokhof (1984) use them for question
denotations, but the lattice structure is domain-general: it applies equally
to attribute spaces (Carnap 1971, Merin 1999), conceptual categories, and
any classificatory scheme.

## Lattice Structure

Partitions form a bounded lattice ordered by refinement:
- **Refinement** (⊑): Q refines Q' iff Q's cells are subsets of Q''s
- **Coarsening**: dual — Q coarsens Q' iff Q' refines Q
- **Meet** (`*`): coarsest common refinement (`QUD.compose`)
- **Top**: exact partition (finest)
- **Bottom**: trivial partition (coarsest)

## Decision-Theoretic Significance

Merin (1999) argues that partitions are decision-theoretically privileged:
coarsening preserves compositionality of expected value, while arbitrary
restructuring does not. Negative attributes are products of proper coarsening —
an epistemic, syntax-independent characterization of negativity.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Merin (1999). Negative Attributes, Partitions, and Rational Decisions.
- Blackwell (1953). Equivalent Comparisons of Experiments.
- Carnap (1971). A Basic System of Inductive Logic. Part I.
-/

namespace QUD

variable {M : Type*}

/-! ### Refinement and Coarsening -/

/-- Q refines Q' iff Q's equivalence classes are subsets of Q''s.

Intuitively: knowing the Q-answer tells you the Q'-answer.
If two elements give the same Q-answer, they must give the same Q'-answer.

Forms a partial order on partitions (up to extensional equivalence). -/
def refines (q q' : QUD M) : Prop :=
  ∀ w v, q.sameAnswer w v = true → q'.sameAnswer w v = true

scoped infix:50 " ⊑ " => QUD.refines

/-- Q coarsens Q' iff Q' refines Q (dual of refinement).

Coarsening merges cells: where Q' distinguishes elements, Q may not.
Merin (1999) defines negative attributes in terms of coarsening:
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
  simp only [HMul.hMul, Mul.mul, QUD.compose] at h
  cases h1 : q1.sameAnswer w v <;> cases h2 : q2.sameAnswer w v <;> simp_all

/-- The meet (coarsest common refinement) refines the right factor. -/
theorem compose_refines_right (q1 q2 : QUD M) : (q1 * q2) ⊑ q2 := by
  intro w v h
  simp only [HMul.hMul, Mul.mul, QUD.compose] at h
  cases h1 : q1.sameAnswer w v <;> cases h2 : q2.sameAnswer w v <;> simp_all

/-- The exact (finest) partition refines all partitions. -/
theorem exact_refines_all [BEq M] [LawfulBEq M] (q : QUD M) :
    exact ⊑ q := by
  intro w v h
  simp only [exact] at h
  have heq : w = v := by rw [beq_iff_eq] at h; exact h
  rw [heq]; exact q.refl v

/-! ### Finite Partition Cells -/

/-- Compute partition cells as characteristic functions over a finite domain.

Each cell is the set of elements equivalent to a representative. Representatives
are chosen greedily from the input list. -/
def toCells (q : QUD M) (elements : List M) : List (M → Bool) :=
  let representatives := elements.foldl (λ acc w =>
    if acc.any λ r => q.sameAnswer r w then acc else w :: acc
  ) []
  representatives.map λ rep => λ w => q.sameAnswer rep w

/-- Number of cells in the partition over a finite domain. -/
def numCells (q : QUD M) (elements : List M) : Nat :=
  (q.toCells elements).length

/-! #### Representative fold helpers -/

private abbrev stepFn (q : QUD M) : List M → M → List M :=
  fun acc w => if acc.any (fun r => q.sameAnswer r w) then acc else w :: acc

private theorem mem_repFold_of_mem_acc (q : QUD M) (elements : List M)
    (acc : List M) (r : M) (hr : r ∈ acc) :
    r ∈ elements.foldl (stepFn q) acc := by
  induction elements generalizing acc with
  | nil => exact hr
  | cons w ws ih =>
    simp only [List.foldl_cons]; apply ih; simp only [stepFn]
    split <;> [exact hr; exact .tail w hr]

private theorem mem_repFold_sub (q : QUD M) (elements : List M)
    (acc : List M) (r : M)
    (hr : r ∈ elements.foldl (stepFn q) acc) : r ∈ acc ∨ r ∈ elements := by
  induction elements generalizing acc with
  | nil => exact Or.inl hr
  | cons w ws ih =>
    simp only [List.foldl_cons] at hr
    cases ih _ hr with
    | inl h =>
      simp only [stepFn] at h; split at h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (.head ws)
        · exact Or.inl h
    | inr h => exact Or.inr (h.tail w)

private theorem repFold_covers (q : QUD M) (elements : List M)
    (acc : List M) (w : M) (hw : w ∈ elements) :
    ∃ r ∈ elements.foldl (stepFn q) acc, q.sameAnswer r w = true := by
  induction elements generalizing acc with
  | nil => exact absurd hw List.not_mem_nil
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hw with rfl | hmem
    · simp only [stepFn]; split
      case isTrue h =>
        obtain ⟨r, hr_mem, hr_eq⟩ := List.any_eq_true.mp h
        exact ⟨r, mem_repFold_of_mem_acc q xs _ r hr_mem, hr_eq⟩
      case isFalse _ =>
        exact ⟨w, mem_repFold_of_mem_acc q xs _ w (.head acc), q.refl w⟩
    · exact ih _ hmem

private theorem not_covered_mem (q : QUD M) {acc : List M} {r w : M}
    (hncov : ¬ (acc.any (fun s => q.sameAnswer s w) = true))
    (hr : r ∈ acc) : ¬ q.sameAnswer r w = true :=
  fun h => hncov (List.any_eq_true.mpr ⟨r, hr, h⟩)

private theorem stepFn_pairwiseInequiv (q : QUD M) (acc : List M) (w : M)
    (hpw : ∀ r1 ∈ acc, ∀ r2 ∈ acc, q.sameAnswer r1 r2 = true → r1 = r2) :
    ∀ r1 ∈ stepFn q acc w, ∀ r2 ∈ stepFn q acc w,
      q.sameAnswer r1 r2 = true → r1 = r2 := by
  simp only [stepFn]; split
  · exact hpw
  · rename_i hncov
    intro r1 hr1 r2 hr2 heq
    rcases List.mem_cons.mp hr1 with h1 | h1 <;> rcases List.mem_cons.mp hr2 with h2 | h2
    · exact h1.trans h2.symm
    · have heq' : q.sameAnswer r2 w = true := by rw [q.symm, ← h1]; exact heq
      exact absurd heq' (not_covered_mem q hncov h2)
    · have heq' : q.sameAnswer r1 w = true := by rw [← h2]; exact heq
      exact absurd heq' (not_covered_mem q hncov h1)
    · exact hpw r1 h1 r2 h2 heq

private theorem repFold_pairwiseInequiv (q : QUD M) (elements : List M)
    (acc : List M)
    (hpw : ∀ r1 ∈ acc, ∀ r2 ∈ acc, q.sameAnswer r1 r2 = true → r1 = r2) :
    ∀ r1 ∈ elements.foldl (stepFn q) acc,
      ∀ r2 ∈ elements.foldl (stepFn q) acc,
        q.sameAnswer r1 r2 = true → r1 = r2 := by
  induction elements generalizing acc with
  | nil => exact hpw
  | cons w ws ih =>
    simp only [List.foldl_cons]; exact ih _ (stepFn_pairwiseInequiv q acc w hpw)

private theorem repFold_nodup (q : QUD M) (elements : List M)
    (acc : List M) (hacc : acc.Nodup)
    (hpw : ∀ r1 ∈ acc, ∀ r2 ∈ acc, q.sameAnswer r1 r2 = true → r1 = r2) :
    (elements.foldl (stepFn q) acc).Nodup := by
  induction elements generalizing acc with
  | nil => exact hacc
  | cons w ws ih =>
    simp only [List.foldl_cons]; apply ih
    · simp only [stepFn]; split
      · exact hacc
      · rename_i hncov
        exact List.Nodup.cons
          (fun hw => hncov (List.any_eq_true.mpr ⟨w, hw, q.refl w⟩)) hacc
    · exact stepFn_pairwiseInequiv q acc w hpw

private theorem nodup_length_le_of_injOn {α β : Type*}
    (l1 : List α) (l2 : List β) (f : α → β) (hl1 : l1.Nodup)
    (hf_inj : ∀ x ∈ l1, ∀ y ∈ l1, f x = f y → x = y)
    (hf_mem : ∀ x ∈ l1, f x ∈ l2) :
    l1.length ≤ l2.length := by
  have hmap_nd := List.Nodup.map_on hf_inj hl1
  have hmap_sub : ∀ y ∈ l1.map f, y ∈ l2 := by
    intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hf_mem x hx
  calc l1.length = (l1.map f).length := (List.length_map f).symm
    _ ≤ l2.length := (hmap_nd.subperm hmap_sub).length_le

/-- Finer partitions have at least as many cells.

The covering map from q'-representatives to q-representatives is injective
(by pairwise inequivalence and refinement), giving `|q-reps| ≥ |q'-reps|`. -/
theorem refines_numCells_ge (q q' : QUD M) (elements : List M) :
    q ⊑ q' → q.numCells elements >= q'.numCells elements := by
  intro hqq
  unfold numCells toCells
  simp only [List.length_map]
  set reps_q := elements.foldl (stepFn q) []
  set reps_q' := elements.foldl (stepFn q') []
  have hempty : ∀ (r1 : M), r1 ∈ ([] : List M) →
      ∀ r2 ∈ ([] : List M), (q.sameAnswer r1 r2 = true → r1 = r2) :=
    fun _ h1 => absurd h1 List.not_mem_nil
  have hempty' : ∀ (r1 : M), r1 ∈ ([] : List M) →
      ∀ r2 ∈ ([] : List M), (q'.sameAnswer r1 r2 = true → r1 = r2) :=
    fun _ h1 => absurd h1 List.not_mem_nil
  have hsub : ∀ r' ∈ reps_q', r' ∈ elements := by
    intro r' hr'
    rcases mem_repFold_sub q' elements [] r' hr' with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  have hcov : ∀ r' ∈ reps_q', ∃ r ∈ reps_q, q.sameAnswer r r' = true :=
    fun r' hr' => repFold_covers q elements [] r' (hsub r' hr')
  have hpw_q' : ∀ r1 ∈ reps_q', ∀ r2 ∈ reps_q',
      q'.sameAnswer r1 r2 = true → r1 = r2 :=
    repFold_pairwiseInequiv q' elements [] hempty'
  have hnd_q : reps_q.Nodup := repFold_nodup q elements [] List.nodup_nil hempty
  have hnd_q' : reps_q'.Nodup := repFold_nodup q' elements [] List.nodup_nil hempty'
  classical
  choose f hf_mem hf_cover using fun r' (hr' : r' ∈ reps_q') => hcov r' hr'
  let g : M → M := fun r' => if h : r' ∈ reps_q' then f r' h else r'
  exact nodup_length_le_of_injOn reps_q' reps_q g hnd_q'
    (fun r1 hr1 r2 hr2 hg => by
      simp only [g, dif_pos hr1, dif_pos hr2] at hg
      have hc1 := hf_cover r1 hr1; rw [hg] at hc1
      exact hpw_q' r1 hr1 r2 hr2 (hqq r1 r2
        (q.trans r1 (f r2 hr2) r2 (by rw [q.symm]; exact hc1) (hf_cover r2 hr2))))
    (fun x hx => by simp only [g, dif_pos hx]; exact hf_mem x hx)

/-- Cells of a QUD respect the equivalence relation: equivalent worlds
agree on cell membership. If `q.sameAnswer w v = true`, then for any cell
in `q.toCells worlds`, `cell w = cell v`. -/
theorem toCells_sameAnswer_eq (q : QUD M) (worlds : List M) (cell : M → Bool)
    (hcell : cell ∈ q.toCells worlds) (w v : M) (hsame : q.sameAnswer w v = true) :
    cell w = cell v := by
  simp only [toCells, List.mem_map] at hcell
  obtain ⟨rep, _, rfl⟩ := hcell
  have hvw : q.sameAnswer v w = true := by rw [q.symm]; exact hsame
  cases hrepw : q.sameAnswer rep w <;> cases hrepv : q.sameAnswer rep v
  · simp [hrepw, hrepv]
  · exact absurd (q.trans rep v w hrepv hvw) (by simp [hrepw])
  · exact absurd (q.trans rep w v hrepw hsame) (by simp [hrepv])
  · simp [hrepw, hrepv]

/-- Each fine cell is contained in some coarse cell (w.r.t. `toCells`).

If `q` refines `q'` (`q ⊑ q'`, finer partition), then for every fine cell
`c` of `q`, there exists a coarse cell of `q'` containing it. -/
theorem toCells_fine_sub_coarse (q q' : QUD M)
    (worlds : List M) (hRefines : q ⊑ q')
    (c : M → Bool) (hc : c ∈ q.toCells worlds) :
    ∃ c' ∈ q'.toCells worlds, ∀ w, c w = true → c' w = true := by
  simp only [toCells, List.mem_map] at hc ⊢
  obtain ⟨rep, hrep_mem, rfl⟩ := hc
  have hrep_worlds : rep ∈ worlds := by
    rcases mem_repFold_sub q worlds [] rep hrep_mem with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  obtain ⟨rep', hrep'_mem, hrep'_eq⟩ := repFold_covers q' worlds [] rep hrep_worlds
  refine ⟨fun w => q'.sameAnswer rep' w, ⟨rep', hrep'_mem, rfl⟩, fun w hw => ?_⟩
  have h1 : q'.sameAnswer rep' w = true :=
    q'.trans rep' rep w hrep'_eq (hRefines rep w hw)
  exact h1

/-- Each coarse cell contains some fine cell (w.r.t. `toCells`).

If `q'` refines `q` (`q' ⊑ q`, finer partition), then for every coarse cell
`c` of `q`, there exists a fine cell of `q'` contained in it. -/
theorem toCells_coarse_contains_fine (q q' : QUD M)
    (worlds : List M) (hRefines : q' ⊑ q)
    (c : M → Bool) (hc : c ∈ q.toCells worlds) :
    ∃ c' ∈ q'.toCells worlds, ∀ w, c' w = true → c w = true := by
  simp only [toCells, List.mem_map] at hc ⊢
  obtain ⟨rep, hrep_mem, rfl⟩ := hc
  have hrep_worlds : rep ∈ worlds := by
    rcases mem_repFold_sub q worlds [] rep hrep_mem with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  obtain ⟨rep', hrep'_mem, hrep'_eq⟩ := repFold_covers q' worlds [] rep hrep_worlds
  refine ⟨fun w => q'.sameAnswer rep' w, ⟨rep', hrep'_mem, rfl⟩, fun w hw => ?_⟩
  -- hw : q'.sameAnswer rep' w = true
  -- Need: q.sameAnswer rep w = true
  -- By symmetry + transitivity: q'.sameAnswer rep w = true
  have h1 : q'.sameAnswer rep rep' = true := by rw [q'.symm]; exact hrep'_eq
  have h2 : q'.sameAnswer rep w = true := q'.trans rep rep' w h1 hw
  -- By refinement: q' ⊑ q
  exact hRefines rep w h2

/-! ### Proper Coarsening (Merin 1999) -/

/-- Q is a proper coarsening of Q' over a finite domain iff Q coarsens Q'
and has strictly fewer cells.

Merin (1999) defines negative attributes via proper coarsening:
R is a *negative attribute* with respect to partition F iff for some Q ∈ F,
{R, Q} is a proper coarsening of F. This characterization is purely epistemic
and syntax-independent — negativity is a matter of partition kinetics, not
morphological form. -/
def isProperCoarsening (q q' : QUD M) (elements : List M) : Prop :=
  q.coarsens q' ∧ q.numCells elements < q'.numCells elements

/-! ### Binary Partitions (Merin 1999) -/

/-- Binary partition from a Boolean predicate. Two elements are equivalent
 iff the predicate gives the same value on both.

Binary partitions are the building blocks of coarsening: every proper
coarsening can be decomposed into steps that merge exactly two cells,
each corresponding to a binary partition. Merin (1999) characterizes
negative attributes entirely in terms of binary partition coarsening. -/
abbrev binaryPartition (p : M → Bool) : QUD M := ofProject p

/-- Complement predicates induce the same binary partition.

Merin (1999, Fact 1): a proposition and its negation carry exactly the same
information. {P-worlds, ¬P-worlds} = {¬P-worlds, P-worlds} as partitions. -/
theorem complement_same_partition (p : M → Bool) (w v : M) :
    (binaryPartition p).sameAnswer w v =
    (binaryPartition (fun m => !p m)).sameAnswer w v := by
  simp only [ofProject_sameAnswer]
  cases p w <;> cases p v <;> rfl

/-- A binary partition from a predicate that respects q's equivalence classes
is a coarsening of q. Every "coarser" yes/no distinction is a coarsening. -/
theorem binaryPartition_coarsens (q : QUD M) (p : M → Bool)
    (h : ∀ w v, q.sameAnswer w v = true → p w = p v) :
    (binaryPartition p).coarsens q := by
  intro w v hq
  simp only [ofProject_sameAnswer, beq_iff_eq]
  exact h w v hq

/-- A predicate R is a *negative attribute* with respect to partition Q over
a finite domain iff the binary partition of R is a proper coarsening of Q.

Merin (1999): negativity is not a syntactic property (presence of "un-",
"not", etc.) but a partition-kinetic one. R is negative relative to Q when
the R/¬R distinction is strictly coarser than Q's partition — answering
whether R holds loses information that Q distinguishes. -/
def isNegativeAttribute (R : M → Bool) (q : QUD M) (elements : List M) : Prop :=
  isProperCoarsening (binaryPartition R) q elements

/-! ### Coarsest P-Preserving Coarsening (Merin 1999, Fact 3) -/

/-- The coarsest coarsening of Q that preserves predicate P.

Two elements are equivalent iff they are Q-equivalent AND agree on P.
This is the meet of Q with the binary partition of P: the finest partition
that is coarser than both Q and binaryPartition P.

Merin (1999): for any proposition P and partition Q, this is the unique
coarsest partition that refines Q while still distinguishing P-worlds
from ¬P-worlds within each Q-cell. -/
def coarsestPreserving (q : QUD M) (P : M → Bool) : QUD M :=
  q * binaryPartition P

/-- The P-preserving coarsening refines Q (it can only be finer). -/
theorem coarsestPreserving_refines (q : QUD M) (P : M → Bool) :
    coarsestPreserving q P ⊑ q :=
  compose_refines_left q (binaryPartition P)

/-- The P-preserving coarsening respects P: equivalent elements agree on P. -/
theorem coarsestPreserving_preserves_P (q : QUD M) (P : M → Bool)
    (w v : M) (h : (coarsestPreserving q P).sameAnswer w v = true) :
    P w = P v := by
  have hbin := compose_refines_right q (binaryPartition P) w v h
  simp only [ofProject_sameAnswer, beq_iff_eq] at hbin
  exact hbin

/-- Any partition that refines Q and preserves P also refines the
P-preserving coarsening. This is the universality property: `coarsestPreserving`
is the coarsest such partition. -/
theorem coarsestPreserving_universal (q q' : QUD M) (P : M → Bool)
    (hrefines : q' ⊑ q)
    (hpreserves : ∀ w v, q'.sameAnswer w v = true → P w = P v) :
    q' ⊑ coarsestPreserving q P := by
  intro w v h
  unfold coarsestPreserving
  simp only [HMul.hMul, Mul.mul, compose]
  simp only [Bool.and_eq_true]
  exact ⟨hrefines w v h, by simp only [ofProject_sameAnswer, beq_iff_eq]; exact hpreserves w v h⟩

/-! ### Finpartition from QUD -/

/-- The `Finpartition` induced by a QUD over a `Fintype`.

Uses Mathlib's `Finpartition.ofSetoid` — exhaustivity, disjointness, and
non-emptiness of cells come for free from the `Finpartition` structure. -/
def toFinpartition [Fintype M] [DecidableEq M] (q : QUD M) :
    Finpartition (Finset.univ : Finset M) :=
  Finpartition.ofSetoid q.toSetoid

/-! ### EU Compositionality under Coarsening (Merin 1999, Central Theorem) -/

open Core.DecisionTheory in
/-- Expected utility computed via a partition: weight each cell's conditional EU
by the cell's probability.

EU_Q(a) = Σ_{c ∈ cells(Q)} P(c) · EU(a | c)

This is the partition-relative expected utility that Merin (1999) shows is
compositional under coarsening. Uses `Finpartition` for exhaustivity and
disjointness, replacing ~200 lines of custom foldl arithmetic. -/
def partitionEU [Fintype M] [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (q : QUD M) (a : A) : ℚ :=
  q.toFinpartition.parts.sum (fun cell =>
    cell.sum dp.prior * conditionalEU dp cell a)

/-! #### Cell probability cancellation (Finset version) -/

open Core.DecisionTheory in
/-- Cell probability times conditional EU equals the raw weighted sum.

For non-negative priors:
- If `cellProb = 0`: all priors are 0, both sides vanish.
- If `cellProb ≠ 0`: the `cellProb` cancels via `Finset.mul_sum` + `field_simp`. -/
private theorem cellProb_mul_conditionalEU [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (cell : Finset M) (a : A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    cell.sum dp.prior * conditionalEU dp cell a =
    cell.sum (fun w => dp.prior w * dp.utility w a) := by
  simp only [conditionalEU]
  by_cases htot : cell.sum dp.prior = 0
  · simp only [htot, ite_true, mul_zero]
    symm; apply Finset.sum_eq_zero; intro w hw
    have : dp.prior w ≤ cell.sum dp.prior :=
      Finset.single_le_sum (fun x _ => hprior x) hw
    have : dp.prior w = 0 := le_antisymm (by linarith) (hprior w)
    simp [this]
  · simp only [htot, ite_false]
    rw [Finset.mul_sum]
    congr 1; ext w; field_simp

open Core.DecisionTheory in
/-- Law of total expectation for partition-relative EU (Merin 1999).

The unconditional expected utility equals the partition-relative EU for
any partition, because partitions are exhaustive and mutually exclusive.

Uses `Finset.sum_biUnion` with `Finpartition.biUnion_parts` for the
decomposition — disjointness and exhaustivity come free from the
`Finpartition` structure.

**Non-negativity is necessary**: with `prior(w1) = 1, prior(w2) = -1`,
`utility(w1,a) = 1, utility(w2,a) = 0`, and a trivial partition,
`expectedUtility = 1` but `cellProb = 0` forces `partitionEU = 0`. -/
theorem eu_eq_partitionEU [Fintype M] [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (a : A) (q : QUD M)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    expectedUtility dp a = partitionEU dp q a := by
  simp only [expectedUtility, partitionEU]
  set P := q.toFinpartition
  -- Decompose ∑ w : M via Finpartition
  conv_lhs => rw [show (Finset.univ : Finset M) = P.parts.biUnion id from P.biUnion_parts.symm]
  rw [Finset.sum_biUnion P.supIndep.pairwiseDisjoint]
  congr 1; ext cell
  exact (cellProb_mul_conditionalEU dp cell a hprior).symm

open Core.DecisionTheory in
/-- Partition-relative EU is partition-independent (given non-negative priors).

Any two partitions give the same partition-relative EU, because both
equal the unconditional EU (`eu_eq_partitionEU`). -/
theorem coarsening_preserves_eu [Fintype M] [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (q q' : QUD M) (a : A)
    (_hcoarse : q.coarsens q')
    (hprior : ∀ w, dp.prior w ≥ 0) :
    partitionEU dp q a = partitionEU dp q' a :=
  (eu_eq_partitionEU dp a q hprior).symm.trans
    (eu_eq_partitionEU dp a q' hprior)

/-! ### Blackwell Ordering (Blackwell 1953) -/

section BlackwellHelpers

variable {α : Type*}

private lemma foldl_max_mono_init (f : α → ℚ) (xs : List α) {a b : ℚ} (hab : a ≤ b) :
    xs.foldl (fun best x => max best (f x)) a ≤
    xs.foldl (fun best x => max best (f x)) b := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons x xs ih => exact ih (max_le_max_right (f x) hab)

private lemma foldl_max_ge_init (f : α → ℚ) (xs : List α) (init : ℚ) :
    xs.foldl (fun best x => max best (f x)) init ≥ init := by
  induction xs generalizing init with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left _ _) (ih _)

private lemma foldl_max_nonneg (f : α → ℚ) (xs : List α) :
    0 ≤ xs.foldl (fun best x => max best (f x)) 0 :=
  foldl_max_ge_init f xs 0

private lemma le_foldl_max (f : α → ℚ) (xs : List α) {x : α} (hx : x ∈ xs) :
    f x ≤ xs.foldl (fun best a => max best (f a)) 0 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl h => rw [h]; exact le_trans (le_max_right _ _) (foldl_max_ge_init _ _ _)
    | inr hys => exact le_trans (ih hys) (foldl_max_mono_init _ _ (le_max_left _ _))

private lemma foldl_max_le_of_bound (f : α → ℚ) (xs : List α) {init B : ℚ}
    (hinit : init ≤ B) (hf : ∀ a ∈ xs, f a ≤ B) :
    xs.foldl (fun best a => max best (f a)) init ≤ B := by
  induction xs generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hx : x ∈ x :: xs := by simp
    have hrest : ∀ a ∈ xs, a ∈ x :: xs := fun a ha => by simp [ha]
    apply ih (max_le hinit (hf x hx))
    intro a ha; exact hf a (hrest a ha)

/-- Max of (f + g) ≤ max of f + max of g (sub-additivity of foldl-max). -/
private lemma foldl_max_add_le (f g : α → ℚ) (actions : List α) :
    actions.foldl (fun best a => max best (f a + g a)) 0 ≤
    actions.foldl (fun best a => max best (f a)) 0 +
    actions.foldl (fun best a => max best (g a)) 0 := by
  apply foldl_max_le_of_bound
  · linarith [foldl_max_nonneg f actions, foldl_max_nonneg g actions]
  · intro a ha
    linarith [le_foldl_max f actions ha, le_foldl_max g actions ha]

end BlackwellHelpers

/-! #### Finset-based partition cells -/

/-- Partition cells of worlds under QUD q, as a Finset of Finsets.
Each cell is the set of elements in worlds that are q-equivalent to some w. -/
def toCellsFinset [DecidableEq M] (q : QUD M) (worlds : Finset M) : Finset (Finset M) :=
  worlds.image (fun w => worlds.filter (fun v => q.sameAnswer w v))

/-- Every world belongs to some cell in `toCellsFinset`. -/
private lemma toCellsFinset_covers [DecidableEq M] (q : QUD M) (worlds : Finset M) :
    (q.toCellsFinset worlds).biUnion id = worlds := by
  ext w; simp only [Finset.mem_biUnion, id, toCellsFinset, Finset.mem_image]
  constructor
  · rintro ⟨cell, ⟨v, hv, rfl⟩, hw⟩; exact (Finset.mem_filter.mp hw).1
  · intro hw
    exact ⟨worlds.filter (fun v => q.sameAnswer w v),
           ⟨w, hw, rfl⟩, Finset.mem_filter.mpr ⟨hw, q.refl w⟩⟩

/-- Cells from `toCellsFinset` are pairwise disjoint. -/
private lemma toCellsFinset_pairwiseDisjoint [DecidableEq M]
    (q : QUD M) (worlds : Finset M) :
    (q.toCellsFinset worlds : Set (Finset M)).PairwiseDisjoint id := by
  intro c₁ hc₁ c₂ hc₂ hne
  simp only [Function.onFun, id]
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  exfalso; apply hne
  simp only [Finset.mem_coe, toCellsFinset, Finset.mem_image] at hc₁ hc₂
  obtain ⟨w₁, _, rfl⟩ := hc₁; obtain ⟨w₂, _, rfl⟩ := hc₂
  simp only [Finset.mem_filter] at hv₁ hv₂
  have h12 : q.sameAnswer w₁ w₂ = true :=
    q.trans w₁ v w₂ hv₁.2 (by rw [q.symm]; exact hv₂.2)
  ext u; simp only [Finset.mem_filter]
  exact ⟨fun ⟨hu, h1u⟩ => ⟨hu, q.trans w₂ w₁ u (by rw [q.symm]; exact h12) h1u⟩,
         fun ⟨hu, h2u⟩ => ⟨hu, q.trans w₁ w₂ u h12 h2u⟩⟩

/-- Under refinement, each fine cell is a subset of some coarse cell. -/
private lemma fine_cell_sub_coarse_finset [DecidableEq M]
    (q q' : QUD M) (worlds : Finset M) (hrefines : q ⊑ q')
    (c : Finset M) (hc : c ∈ q.toCellsFinset worlds) :
    ∃ c' ∈ q'.toCellsFinset worlds, c ⊆ c' := by
  simp only [toCellsFinset, Finset.mem_image] at hc
  obtain ⟨w, hw, rfl⟩ := hc
  refine ⟨worlds.filter (fun v => q'.sameAnswer w v),
         Finset.mem_image.mpr ⟨w, hw, rfl⟩, ?_⟩
  intro v hv; simp only [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, hrefines w v hv.2⟩

/-- A coarse cell equals the union of fine cells within it. -/
private lemma coarse_eq_biUnion_fine [DecidableEq M]
    (q q' : QUD M) (worlds : Finset M) (hrefines : q ⊑ q')
    (c' : Finset M) (hc' : c' ∈ q'.toCellsFinset worlds) :
    c' = ((q.toCellsFinset worlds).filter (· ⊆ c')).biUnion id := by
  simp only [toCellsFinset, Finset.mem_image] at hc'
  obtain ⟨w', hw', rfl⟩ := hc'
  ext v
  constructor
  · intro hv
    simp only [Finset.mem_filter] at hv
    rw [Finset.mem_biUnion]
    refine ⟨worlds.filter (fun u => q.sameAnswer v u), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_image.mpr ⟨v, hv.1, rfl⟩
      · intro u hu
        simp only [Finset.mem_filter] at hu ⊢
        exact ⟨hu.1, q'.trans w' v u hv.2 (hrefines v u hu.2)⟩
    · simp only [id]; exact Finset.mem_filter.mpr ⟨hv.1, q.refl v⟩
  · intro hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨cell, hcell, hv_in⟩ := hv
    simp only [id] at hv_in
    exact (Finset.mem_filter.mp hcell).2 hv_in

/-- Fine cells within a coarse cell are pairwise disjoint (inherited from the
fine partition being pairwise disjoint). -/
private lemma fine_cells_in_coarse_pairwiseDisjoint [DecidableEq M]
    (q : QUD M) (worlds : Finset M) (c' : Finset M) :
    (((q.toCellsFinset worlds).filter (· ⊆ c')) : Set (Finset M)).PairwiseDisjoint id := by
  intro a ha b hb hab
  exact toCellsFinset_pairwiseDisjoint q worlds
    (Finset.mem_of_mem_filter a ha) (Finset.mem_of_mem_filter b hb) hab

/-! #### Finset-based partition value -/

open Core.DecisionTheory in
/-- The value of a decision problem under partition Q over a Finset of worlds.

V_Q(D, W) = Σ_{c ∈ cells(Q,W)} max_a [Σ_{w∈c} p(w)·u(w,a)]

Following Merin (1999, p. 264), this uses raw weighted sums directly
rather than factoring through conditional EU. The equivalence
`P(c) · max_a condEU(a,c) = max_a [Σ_{w∈c} p(w)·u(w,a)]` holds when
priors are non-negative. The raw form makes Blackwell's theorem a
direct application of sub-additivity. -/
def partitionValue [DecidableEq M] {A : Type*} (dp : DecisionProblem M A)
    (q : QUD M) (worlds : Finset M) (actions : List A) : ℚ :=
  (q.toCellsFinset worlds).sum (fun cell =>
    actions.foldl (fun best a => max best
      (cell.sum (fun w => dp.prior w * dp.utility w a))) 0)

/-! #### Sub-additivity of max -/

/-- foldl-max with pointwise-equal inner functions gives equal results. -/
private lemma foldl_max_congr {α : Type*} (g₁ g₂ : α → ℚ) (actions : List α)
    (h : ∀ a, g₁ a = g₂ a) :
    actions.foldl (fun best a => max best (g₁ a)) 0 =
    actions.foldl (fun best a => max best (g₂ a)) 0 :=
  congrArg (fun g => List.foldl (fun best a => max best (g a)) (0 : ℚ) actions) (funext h)

/-- Sub-additivity of foldl-max over Finset.sum:
max_a (S.sum (fun c => f c a)) ≤ S.sum (fun c => max_a (f c a)) -/
private lemma foldl_max_finset_sum_le {α β : Type*} [DecidableEq β]
    (f : β → α → ℚ) (S : Finset β) (actions : List α) :
    actions.foldl (fun best a => max best (S.sum (fun c => f c a))) 0 ≤
    S.sum (fun c => actions.foldl (fun best a => max best (f c a)) 0) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : ∀ (l : List α), l.foldl (fun best (_ : α) => max best (0 : ℚ)) 0 = 0 := by
      intro l; induction l with
      | nil => rfl
      | cons _ _ ih => simp only [List.foldl_cons, max_self]; exact ih
    linarith [this actions]
  | @insert b T hb ih =>
    simp only [Finset.sum_insert hb]
    calc actions.foldl (fun best a => max best (f b a + T.sum (fun c => f c a))) 0
        ≤ actions.foldl (fun best a => max best (f b a)) 0 +
          actions.foldl (fun best a => max best (T.sum (fun c => f c a))) 0 :=
            foldl_max_add_le (fun a => f b a) (fun a => T.sum (fun c => f c a)) actions
      _ ≤ actions.foldl (fun best a => max best (f b a)) 0 +
          T.sum (fun c => actions.foldl (fun best a => max best (f c a)) 0) := by linarith [ih]

/-! #### Blackwell refinement theorem -/

set_option maxHeartbeats 800000 in
/-- Per-cell step: a coarse cell's raw value ≤ sum of its fine cells' raw values.
Extracted as standalone lemma to keep elaboration context simple. -/
private lemma coarse_cell_le_fine_sum [DecidableEq M] {A : Type*}
    (dp : Core.DecisionTheory.DecisionProblem M A)
    (q : QUD M) (worlds : Finset M) (actions : List A)
    (c' : Finset M) (hdecomp : c' = ((q.toCellsFinset worlds).filter (· ⊆ c')).biUnion id)
    (hdisj : ((q.toCellsFinset worlds).filter (· ⊆ c') : Set (Finset M)).PairwiseDisjoint id) :
    actions.foldl (fun best a => max best
      (c'.sum (fun w => dp.prior w * dp.utility w a))) 0 ≤
    ((q.toCellsFinset worlds).filter (· ⊆ c')).sum (fun cell =>
      actions.foldl (fun best a => max best
        (cell.sum (fun w => dp.prior w * dp.utility w a))) 0) := by
  set S := (q.toCellsFinset worlds).filter (· ⊆ c') with hS
  -- Decompose c'.sum (p·u) into Σ_{c⊆c'} c.sum (p·u)
  have hds : ∀ a, c'.sum (fun w => dp.prior w * dp.utility w a) =
      S.sum (fun c => c.sum (fun w => dp.prior w * dp.utility w a)) := by
    intro a; rw [hdecomp]
    have h := Finset.sum_biUnion
      (f := fun (w : M) => dp.prior w * dp.utility w a) hdisj
    simp only [id] at h; exact h
  -- foldl-max with equal inner ≤ sub-additive decomposition
  have h1 := foldl_max_congr _ _ actions hds
  have h2 := foldl_max_finset_sum_le
    (fun c a => c.sum (fun w => dp.prior w * dp.utility w a)) S actions
  linarith

open Core.DecisionTheory in
/-- Blackwell's theorem for partitions: finer partitions are always at least
as valuable as coarser ones, for any decision problem.

V_Q(D) ≥ V_{Q'}(D) for all decision problems D, whenever Q ⊑ Q'.

**Proof** (Merin 1999, p. 264): Working directly with raw weighted sums
`Σ_{w∈c} p(w)·u(w,a)`:

1. Each coarse cell's sum decomposes into fine cells (`Finset.sum_biUnion`)
2. Sub-additivity of max: `max_a(Σᵢ fᵢ(a)) ≤ Σᵢ max_a(fᵢ(a))`
3. Regrouping: fine cells grouped by coarse cell = all fine cells -/
theorem blackwell_refinement_value [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (q q' : QUD M)
    (worlds : Finset M) (actions : List A)
    (hrefines : q ⊑ q')
    (_hprior : ∀ w, dp.prior w ≥ 0) :
    partitionValue dp q worlds actions ≥ partitionValue dp q' worlds actions := by
  -- Define per-cell value to ensure consistent terms
  let V : Finset M → ℚ := fun cell =>
    actions.foldl (fun best a => max best
      (cell.sum (fun w => dp.prior w * dp.utility w a))) 0
  -- partitionValue = (cells).sum V by definition
  change (q.toCellsFinset worlds).sum V ≥ (q'.toCellsFinset worlds).sum V
  -- Step 1: Each coarse cell's value ≤ sum of its fine cells' values
  have hstep : (q'.toCellsFinset worlds).sum V ≤
    (q'.toCellsFinset worlds).sum (fun c' =>
      ((q.toCellsFinset worlds).filter (· ⊆ c')).sum V) :=
    Finset.sum_le_sum (fun c' hc' =>
      coarse_cell_le_fine_sum dp q worlds actions c'
        (coarse_eq_biUnion_fine q q' worlds hrefines c' hc')
        (fine_cells_in_coarse_pairwiseDisjoint q worlds c'))
  -- Step 2: Regroup — Σ_{c'} Σ_{c⊆c'} V(c) = Σ_c V(c)
  have hregroup : (q'.toCellsFinset worlds).sum (fun c' =>
      ((q.toCellsFinset worlds).filter (· ⊆ c')).sum V) =
    (q.toCellsFinset worlds).sum V := by
    rw [← Finset.sum_biUnion (f := V)]
    · congr 1
      ext c; simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun ⟨_, _, hc, _⟩ => hc, fun hc =>
        let ⟨c', hc', hsub⟩ := fine_cell_sub_coarse_finset q q' worlds hrefines c hc
        ⟨c', hc', hc, hsub⟩⟩
    · -- Fiber sets are pairwise disjoint (a fine cell can't be in two coarse groups)
      intro c'₁ hc'₁ c'₂ hc'₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro c hc₁ hc₂
      simp only [Finset.mem_filter] at hc₁ hc₂
      have ⟨v, hv⟩ : c.Nonempty := by
        simp only [toCellsFinset, Finset.mem_image] at hc₁
        obtain ⟨w, hw, rfl⟩ := hc₁.1
        exact ⟨w, Finset.mem_filter.mpr ⟨hw, q.refl w⟩⟩
      exfalso; apply hne; by_contra hne'
      exact Finset.disjoint_left.mp
        (toCellsFinset_pairwiseDisjoint q' worlds hc'₁ hc'₂ hne')
        (hc₁.2 hv) (hc₂.2 hv)
  linarith [hregroup]

/-! #### Blackwell characterization -/

set_option maxHeartbeats 1600000 in
open Core.DecisionTheory in
/-- Helper: when q merges w,v but q' separates them, a witness DP achieves
strictly higher value under q' than q.

The DP has uniform prior (1/2 each) with utility rewarding correct identification.
Under q (merged cell {w,v}): best raw sum = max(1/2, 1/2) = 1/2.
Under q' (separate cells {w}, {v}): each cell's best raw sum = 1/2, total = 1. -/
private theorem witness_dp_beats_merged [DecidableEq M]
    (q q' : QUD M) (w v : M)
    (hwv_q : q.sameAnswer w v = true)
    (hwv_q'f : q'.sameAnswer w v = false)
    (hvw_q'f : q'.sameAnswer v w = false) :
    ¬ (partitionValue
        { utility := fun m a =>
            if a then (if q'.sameAnswer w m then 1 else 0)
            else (if q'.sameAnswer v m then 1 else 0)
          prior := fun _ => (1 : ℚ) / 2 }
        q {w, v} [true, false] ≥
       partitionValue
        { utility := fun m a =>
            if a then (if q'.sameAnswer w m then 1 else 0)
            else (if q'.sameAnswer v m then 1 else 0)
          prior := fun _ => (1 : ℚ) / 2 }
        q' {w, v} [true, false]) := by
  have hwv : w ≠ v := by intro h; rw [h] at hwv_q'f; exact absurd (q'.refl v) (by simp [hwv_q'f])
  have hvw_q : q.sameAnswer v w = true := by rw [q.symm]; exact hwv_q
  -- The proof proceeds by unfolding to concrete rational arithmetic.
  -- Under q: one merged cell {w,v}, best raw sum = max(1/2, 1/2) = 1/2
  -- Under q': two cells {w},{v}, total = 1/2 + 1/2 = 1
  -- So ¬(1/2 ≥ 1).
  -- Step 1: Compute q-cells — both w,v map to {w,v}, so image = {{w,v}}
  have hcells_q : q.toCellsFinset {w, v} = {{w, v}} := by
    simp only [toCellsFinset, Finset.image_insert, Finset.image_singleton,
               Finset.filter_insert, Finset.filter_singleton,
               q.refl, hwv_q, hvw_q, ite_true,
               Finset.insert_eq_of_mem (Finset.mem_singleton.mpr rfl)]
  -- Step 2: Compute q'-cells — w maps to {w}, v maps to {v}
  have hsingleton_ne : ({w} : Finset M) ≠ {v} := by
    intro h; have := Finset.mem_singleton.mp (h ▸ Finset.mem_singleton.mpr rfl : w ∈ ({v} : Finset M))
    exact hwv this
  have hcells_q' : q'.toCellsFinset {w, v} = {{w}, {v}} := by
    have hie : insert w (∅ : Finset M) = {w} := by ext x; simp
    simp only [toCellsFinset, Finset.image_insert, Finset.image_singleton,
               Finset.filter_insert, Finset.filter_singleton,
               q'.refl, hwv_q'f, hvw_q'f, ite_true, ite_false, Bool.false_eq_true, hie]
  have hnotmem : ({w} : Finset M) ∉ ({{v}} : Finset (Finset M)) :=
    fun h => hsingleton_ne (Finset.mem_singleton.mp h)
  -- Step 3: Compute the partition values
  simp only [partitionValue, hcells_q, hcells_q', Finset.sum_singleton,
             Finset.sum_insert hnotmem, Finset.sum_pair hwv,
             q'.refl, hwv_q'f, hvw_q'f, ite_true]
  norm_num

set_option maxHeartbeats 1600000 in
open Core.DecisionTheory in
/-- Blackwell ordering characterizes refinement: Q refines Q' if and only if
Q is at least as valuable as Q' for every decision problem.

This is the converse of `blackwell_refinement_value`: if Q is always at
least as valuable, then Q must refine Q'. Together they establish that
partition refinement IS Blackwell ordering.

**Proof** (contrapositive): Suppose `q` does not refine `q'`, i.e.,
∃ w v with `q.sameAnswer w v = true` but `q'.sameAnswer w v = false`.
Construct a DP over `worlds = {w, v}` with two actions where distinguishing
w from v matters. Then q' achieves value 1 while q achieves 1/2. -/
theorem blackwell_characterizes_refinement [DecidableEq M]
    (q q' : QUD M)
    (h : ∀ (worlds : Finset M) (A : Type) (dp : DecisionProblem M A) (actions : List A),
      (∀ w, dp.prior w ≥ 0) →
      partitionValue dp q worlds actions ≥ partitionValue dp q' worlds actions) :
    q ⊑ q' := by
  intro w v hwv_q
  by_contra hwv_q'
  have hwv_q'f : q'.sameAnswer w v = false := by
    cases h' : q'.sameAnswer w v with
    | false => rfl
    | true => exact absurd h' hwv_q'
  have hvw_q'f : q'.sameAnswer v w = false := by
    rw [q'.symm]; exact hwv_q'f
  exact witness_dp_beats_merged q q' w v hwv_q hwv_q'f hvw_q'f
    (h {w, v} Bool
      { utility := fun m a =>
          if a then (if q'.sameAnswer w m then 1 else 0)
          else (if q'.sameAnswer v m then 1 else 0)
        prior := fun _ => (1 : ℚ) / 2 }
      [true, false]
      (by intro _; norm_num))

/-! #### Question Utility Bridge

Connect list-based `questionUtility` (from `Core.DecisionTheory`) to
Finset-based `partitionValue`. The algebraic identity:

  questionUtility dp actions (q.toCells worlds)
    = partitionValue dp q Finset.univ actions
    - dpValue dp actions * (Finset.univ : Finset M).sum dp.prior

under non-negative priors. Since `dpValue * totalPrior` is
partition-independent, the Blackwell ordering on `partitionValue`
transfers directly to `questionUtility`. -/

section QuestionUtilityBridge

variable {M : Type*}

/-! ##### Arithmetic helpers -/

/-- Scaling foldl-max by a non-negative constant. -/
private lemma mul_foldl_max_eq {α : Type*} (c : ℚ) (hc : 0 ≤ c)
    (f : α → ℚ) (xs : List α) (init : ℚ) :
    c * xs.foldl (fun best a => max best (f a)) init =
    xs.foldl (fun best a => max best (c * f a)) (c * init) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (max init (f x)), mul_max_of_nonneg init (f x) hc]

/-- foldl of addition can be shifted: init + Σ = foldl from init. -/
private lemma foldl_add_shift {α : Type*} (f : α → ℚ) (init : ℚ) (xs : List α) :
    xs.foldl (fun acc x => acc + f x) init = init + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (init + f x), ih (0 + f x)]
    ring

/-- foldl of addition on a NoDup list = Finset.sum on its toFinset. -/
private lemma foldl_add_eq_toFinset_sum [DecidableEq M]
    (xs : List M) (f : M → ℚ) (hnd : xs.Nodup) :
    xs.foldl (fun acc x => acc + f x) 0 = xs.toFinset.sum f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := (List.nodup_cons.mp hnd).1
    have hxs := (List.nodup_cons.mp hnd).2
    simp only [List.foldl_cons, List.toFinset_cons, zero_add]
    rw [foldl_add_shift f (f x) xs, ih hxs,
        Finset.sum_insert (mt List.mem_toFinset.mp hx)]

/-! ##### Cell correspondence -/

/-- Map a representative to its equivalence class as a Finset. -/
private def cellOfRep [Fintype M] [DecidableEq M] (q : QUD M) (rep : M) : Finset M :=
  Finset.univ.filter (fun w => q.sameAnswer rep w)

/-- cellOfRep maps representatives into toCellsFinset. -/
private lemma cellOfRep_mem_toCellsFinset [Fintype M] [DecidableEq M]
    (q : QUD M) (rep : M) :
    cellOfRep q rep ∈ q.toCellsFinset Finset.univ := by
  simp only [cellOfRep, toCellsFinset]
  exact Finset.mem_image.mpr ⟨rep, Finset.mem_univ _, rfl⟩

/-- cellOfRep is injective on pairwise-inequivalent representatives. -/
private lemma cellOfRep_injOn [Fintype M] [DecidableEq M]
    (q : QUD M) (reps : List M)
    (hpw : ∀ r1 ∈ reps, ∀ r2 ∈ reps, q.sameAnswer r1 r2 = true → r1 = r2) :
    (reps.toFinset : Set M).InjOn (cellOfRep q) := by
  intro r1 hr1 r2 hr2 heq
  have hr1' := List.mem_toFinset.mp hr1
  have hr2' := List.mem_toFinset.mp hr2
  simp only [cellOfRep] at heq
  have : q.sameAnswer r1 r2 = true := by
    have h := Finset.ext_iff.mp heq r2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h.mpr (q.refl r2)
  exact hpw r1 hr1' r2 hr2' this

/-- cellOfRep on representatives surjects onto toCellsFinset. -/
private lemma cellOfRep_surjOn [Fintype M] [DecidableEq M]
    (q : QUD M) (elements : List M) (hcov : elements = Finset.univ.val.toList) :
    Set.SurjOn (cellOfRep q)
      ((elements.foldl (stepFn q) []).toFinset : Set M)
      (q.toCellsFinset Finset.univ : Set (Finset M)) := by
  intro cell hcell
  rw [Finset.mem_coe] at hcell
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hcell
  have hw : w ∈ elements := by
    rw [hcov]; exact Multiset.mem_toList.mpr (Finset.mem_univ w)
  obtain ⟨rep, hrep, hsa⟩ := repFold_covers q elements [] w hw
  refine ⟨rep, List.mem_toFinset.mpr hrep, ?_⟩
  simp only [cellOfRep]
  ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact q.trans w rep u (by rw [q.symm]; exact hsa) h
  · intro h; exact q.trans rep w u hsa h

/-! ##### Per-cell equivalence -/

open Core.DecisionTheory in
/-- P(c) × valueAfterLearning(c) = the per-cell term in `partitionValue`. -/
private theorem cellProb_mul_valueAfterLearning [DecidableEq M] {A : Type*} [DecidableEq A]
    (dp : DecisionProblem M A) (cell : Finset M) (actions : List A)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    cellProbability dp cell * valueAfterLearning dp actions cell =
    actions.foldl (fun best a => max best
      (cell.sum (fun w => dp.prior w * dp.utility w a))) 0 := by
  unfold cellProbability valueAfterLearning
  rw [mul_foldl_max_eq (cell.sum dp.prior)
    (Finset.sum_nonneg (fun w _ => hprior w))
    (fun a => conditionalEU dp cell a) actions 0, mul_zero]
  have heq : ∀ a, cell.sum dp.prior * conditionalEU dp cell a =
      cell.sum (fun w => dp.prior w * dp.utility w a) :=
    fun a => cellProb_mul_conditionalEU dp cell a hprior
  simp_rw [heq]

/-! ##### Question utility as Finset sum

The key conversion: `questionUtility` over `toCells` equals a `Finset.sum`
over `toCellsFinset`. This bridges the List-based question semantics API
to the Finset-based partition machinery. -/

open Core.DecisionTheory in
/-- `questionUtility` over `toCells` equals the corresponding `Finset.sum`
over `toCellsFinset`.

The proof uses the `cellOfRep` bijection between representatives
(computed by `toCells`) and cells in `toCellsFinset`:
1. Unfold `toCells` as `reps.map (fun rep => fun w => sameAnswer rep w)`
2. Use `List.foldl_map` to pull the map into the accumulator
3. Convert `NoDup`-list foldl to `Finset.sum` on `reps.toFinset`
4. Reindex via `Finset.sum_nbij` using the `cellOfRep` bijection -/
private theorem questionUtility_eq_finsetSum [Fintype M] [DecidableEq M]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem M A) (q : QUD M) (actions : List A) :
    questionUtility dp actions (q.toCells (Finset.univ.val.toList)) =
    (q.toCellsFinset (Finset.univ : Finset M)).sum (fun cell =>
      cellProbability dp cell * utilityValue dp actions cell) := by
  -- Abbreviations
  set elements := (Finset.univ : Finset M).val.toList with helements
  set reps := elements.foldl (stepFn q) [] with hreps_def
  set g : Finset M → ℚ := fun cell =>
    cellProbability dp cell * utilityValue dp actions cell with hg_def

  -- Step 1: unfold questionUtility and toCells
  unfold questionUtility
  show (reps.map (fun rep => fun w => q.sameAnswer rep w)).foldl
    (fun acc cell =>
      let cellSet := Finset.univ.filter (fun w => cell w = true)
      acc + cellProbability dp cellSet * utilityValue dp actions cellSet) 0 =
    (q.toCellsFinset Finset.univ).sum g

  -- Step 2: use List.foldl_map to pull the map into the accumulator
  rw [List.foldl_map]
  -- Goal: reps.foldl (fun acc rep => ... (fun w => q.sameAnswer rep w) ...) 0 = ...

  -- Step 3: simplify — for Bool b, (b = true) is the same as the Bool coercion
  -- so Finset.univ.filter (fun w => q.sameAnswer rep w = true) = cellOfRep q rep
  have hcell_eq : ∀ rep : M,
      (fun cell =>
        let cellSet := Finset.univ.filter (fun w => cell w = true)
        cellProbability dp cellSet * utilityValue dp actions cellSet)
        (fun w => q.sameAnswer rep w) = g (cellOfRep q rep) := by
    intro rep; simp only [cellOfRep]; rfl
  simp_rw [hcell_eq]

  -- Step 4: convert NoDup-list foldl to Finset.sum
  have hnd : reps.Nodup :=
    repFold_nodup q elements [] List.nodup_nil
      (fun _ h => nomatch h)
  rw [foldl_add_eq_toFinset_sum reps (fun rep => g (cellOfRep q rep)) hnd]

  -- Step 5: reindex via cellOfRep bijection
  have hpw : ∀ r1 ∈ reps, ∀ r2 ∈ reps, q.sameAnswer r1 r2 = true → r1 = r2 :=
    repFold_pairwiseInequiv q elements []
      (fun _ h => nomatch h)
  exact Finset.sum_nbij (cellOfRep q)
    (fun rep _ => cellOfRep_mem_toCellsFinset q rep)
    (cellOfRep_injOn q reps hpw)
    (cellOfRep_surjOn q elements helements)
    (fun _ _ => rfl)

/-! ##### Cells partition Finset.univ -/

/-- The sum of cell probabilities equals total prior (cells partition the universe). -/
private theorem toCells_totalProb [Fintype M] [DecidableEq M] {A : Type*}
    (dp : Core.DecisionTheory.DecisionProblem M A) (q : QUD M) :
    (q.toCellsFinset (Finset.univ : Finset M)).sum
      (fun cell => Core.DecisionTheory.cellProbability dp cell) =
    (Finset.univ : Finset M).sum dp.prior := by
  simp only [Core.DecisionTheory.cellProbability]
  conv_rhs => rw [← toCellsFinset_covers q (Finset.univ : Finset M)]
  exact (Finset.sum_biUnion (f := dp.prior)
    (toCellsFinset_pairwiseDisjoint q (Finset.univ : Finset M))).symm

/-! ##### Main bridge theorem -/

open Core.DecisionTheory in
/-- Blackwell ordering on `questionUtility` for QUD-derived questions.

Refinement implies higher question utility (with non-negative priors).
This is the key bridge theorem: it connects the proved
`blackwell_refinement_value` (for `partitionValue`) to the list-based
`questionUtility` used in question semantics.

**Proof**: `questionUtility = partitionValue - dpValue × totalPrior`.
Since `dpValue` and `totalPrior` are partition-independent, the ordering
on `partitionValue` (from `blackwell_refinement_value`) transfers. -/
theorem questionUtility_refinement_ge [Fintype M] [DecidableEq M]
    {A : Type*} [DecidableEq A]
    (dp : DecisionProblem M A) (q q' : QUD M) (actions : List A)
    (hRefines : q ⊑ q') (hprior : ∀ w, dp.prior w ≥ 0) :
    questionUtility dp actions (q.toCells (Finset.univ.val.toList)) ≥
    questionUtility dp actions (q'.toCells (Finset.univ.val.toList)) := by
  -- Convert both sides from foldl to Finset.sum
  rw [questionUtility_eq_finsetSum dp q actions,
      questionUtility_eq_finsetSum dp q' actions]
  -- Expand utilityValue = valueAfterLearning - dpValue
  simp only [utilityValue]
  -- P(c) * (val(c) - dpValue) = P(c)*val(c) - P(c)*dpValue
  simp_rw [mul_sub]
  -- Σ (P(c)*val(c) - P(c)*dpValue) = Σ P(c)*val(c) - Σ P(c)*dpValue
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  -- Factor dpValue out of the second sum: Σ P(c)*dpValue = dpValue * Σ P(c)
  simp_rw [mul_comm (cellProbability dp _) (dpValue dp actions),
           ← Finset.mul_sum]
  -- Now both sides: Σ P(c)*val(c) - dpValue * totalPrior
  -- totalPrior is the same for q and q' (cells partition the universe)
  rw [toCells_totalProb dp q, toCells_totalProb dp q']
  -- Remains: Σ_q P(c)*val(c) ≥ Σ_q' P(c)*val(c)
  linarith [show (q.toCellsFinset (Finset.univ : Finset M)).sum
      (fun cell => cellProbability dp cell * valueAfterLearning dp actions cell) ≥
    (q'.toCellsFinset (Finset.univ : Finset M)).sum
      (fun cell => cellProbability dp cell * valueAfterLearning dp actions cell) from by
    -- Use cellProb_mul_valueAfterLearning to convert to partitionValue
    simp_rw [cellProb_mul_valueAfterLearning dp _ actions hprior]
    exact blackwell_refinement_value dp q q' Finset.univ actions hRefines hprior]

/-! ##### Partition value restricted to prior support

When priors are zero outside a subset S, the partition value over the full
universe equals the partition value over S. This bridges from `questionUtility`
(which operates over `Finset.univ`) to `partitionValue` over arbitrary
world sets (needed by `blackwell_characterizes_refinement`). -/

open Core.DecisionTheory in
/-- Per-cell value depends only on worlds with nonzero prior.

If priors are zero outside S, the raw weighted sum over `cell` equals
the raw weighted sum over `cell ∩ S`. -/
private lemma cell_value_restrict_support [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (cell S : Finset M) (a : A)
    (hsupp : ∀ w, w ∉ S → dp.prior w = 0) :
    cell.sum (fun w => dp.prior w * dp.utility w a) =
    (cell ∩ S).sum (fun w => dp.prior w * dp.utility w a) := by
  have hsplit : cell.sum (fun w => dp.prior w * dp.utility w a) =
      (cell \ S).sum (fun w => dp.prior w * dp.utility w a) +
      (cell ∩ S).sum (fun w => dp.prior w * dp.utility w a) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter cell S),
        Finset.sdiff_union_inter]
  rw [hsplit]
  suffices h : (cell \ S).sum (fun w => dp.prior w * dp.utility w a) = 0 by linarith
  apply Finset.sum_eq_zero; intro w hw
  simp only [Finset.mem_sdiff] at hw
  rw [hsupp w hw.2, zero_mul]

open Core.DecisionTheory in
/-- Partition value restricted to prior support.

When priors are zero outside S, `partitionValue` over `Finset.univ` equals
`partitionValue` over S. Cells not intersecting S contribute zero (all priors
are 0). Cells intersecting S have the same per-cell value as the S-restricted
cells. The bijection between nonempty-in-S cells and `toCellsFinset S`
reindexes the sum. -/
theorem partitionValue_restrict_support [Fintype M] [DecidableEq M] {A : Type*}
    (dp : DecisionProblem M A) (q : QUD M) (S : Finset M) (actions : List A)
    (hsupp : ∀ w, w ∉ S → dp.prior w = 0) :
    partitionValue dp q Finset.univ actions = partitionValue dp q S actions := by
  -- Per-cell value function
  set V : Finset M → ℚ := fun cell =>
    actions.foldl (fun best a => max best
      (cell.sum (fun w => dp.prior w * dp.utility w a))) 0
  change (q.toCellsFinset Finset.univ).sum V = (q.toCellsFinset S).sum V
  -- Step 1: For each cell c of Finset.univ, V(c) = V(c ∩ S)
  have hV_restrict : ∀ c ∈ q.toCellsFinset Finset.univ, V c = V (c ∩ S) := by
    intro c _; simp only [V]
    congr 1; ext _ a_act
    exact cell_value_restrict_support dp c S a_act hsupp
  -- Step 2: Split Finset.univ cells into those intersecting S and those not
  have hsplit : (q.toCellsFinset Finset.univ).sum V =
      ((q.toCellsFinset Finset.univ).filter (fun c => (c ∩ S).Nonempty)).sum V +
      ((q.toCellsFinset Finset.univ).filter (fun c => ¬(c ∩ S).Nonempty)).sum V := by
    rw [← Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  -- Empty cells contribute 0
  have hempty : ((q.toCellsFinset Finset.univ).filter (fun c => ¬(c ∩ S).Nonempty)).sum V = 0 := by
    apply Finset.sum_eq_zero; intro c hc
    simp only [Finset.mem_filter, Finset.not_nonempty_iff_eq_empty] at hc
    have hV0 : V c = V (c ∩ S) := hV_restrict c hc.1
    show V c = 0
    rw [hV0, hc.2]; simp only [V, Finset.sum_empty]
    clear hV_restrict hsplit hV0 hc
    induction actions with
    | nil => rfl
    | cons _ _ ih => simp only [List.foldl_cons, max_self]; exact ih
  rw [hempty, add_zero]
  -- Now show the nonempty-intersection cells biject with toCellsFinset S
  -- with matching values V(c) = V(c ∩ S) = V(d)
  -- Map: c ↦ c ∩ S
  apply Finset.sum_nbij (fun c => c ∩ S)
  · -- Maps into toCellsFinset S
    intro c hc
    simp only [Finset.mem_filter] at hc
    obtain ⟨hcm, hne⟩ := hc
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hcm
    simp only [toCellsFinset]
    obtain ⟨v, hv⟩ := hne
    have hvS : v ∈ S := (Finset.mem_inter.mp hv).2
    have hwv : q.sameAnswer w v = true :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hv).1).2
    exact Finset.mem_image.mpr ⟨v, hvS, by
      ext u; constructor
      · intro hu
        have ⟨hfu, hsu⟩ := Finset.mem_inter.mp hu
        have hwu := (Finset.mem_filter.mp hfu).2
        exact Finset.mem_filter.mpr ⟨hsu, q.trans v w u (by rw [q.symm]; exact hwv) hwu⟩
      · intro hu
        have hmf := Finset.mem_filter.mp hu
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.trans w v u hwv hmf.1⟩, hmf.2⟩⟩
  · -- Injective
    intro c1 hc1 c2 hc2 heq
    obtain ⟨hc1m, hne1⟩ := Finset.mem_filter.mp hc1
    obtain ⟨hc2m, _⟩ := Finset.mem_filter.mp hc2
    obtain ⟨w1, _, rfl⟩ := Finset.mem_image.mp hc1m
    obtain ⟨w2, _, rfl⟩ := Finset.mem_image.mp hc2m
    obtain ⟨v, hv⟩ := hne1
    -- v ∈ c1 ∩ S, so v ∈ c2 ∩ S by heq (beta-reduce for ▸)
    have heq' : (Finset.univ.filter (fun u => q.sameAnswer w1 u)) ∩ S =
        (Finset.univ.filter (fun u => q.sameAnswer w2 u)) ∩ S := heq
    have hv2 : v ∈ (Finset.univ.filter (fun u => q.sameAnswer w2 u)) ∩ S := heq' ▸ hv
    have h1v := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).1).2
    have h2v := (Finset.mem_filter.mp (Finset.mem_inter.mp hv2).1).2
    have h12 : q.sameAnswer w1 w2 = true :=
      q.trans w1 v w2 h1v (by rw [q.symm]; exact h2v)
    ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => q.trans w2 w1 u (by rw [q.symm]; exact h12) h,
           fun h => q.trans w1 w2 u h12 h⟩
  · -- Surjective
    intro d hd
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hd
    refine ⟨Finset.univ.filter (fun v => q.sameAnswer w v), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩,
         ⟨w, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.refl w⟩, hw⟩⟩⟩
    · ext u; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  · -- Values match: V(c) = V(c ∩ S)
    intro c hc; simp only [Finset.mem_filter] at hc
    exact hV_restrict c hc.1

end QuestionUtilityBridge

end QUD
