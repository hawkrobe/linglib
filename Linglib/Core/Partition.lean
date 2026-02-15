import Linglib.Core.QUD
import Linglib.Core.DecisionTheory
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

/-! ### EU Compositionality under Coarsening (Merin 1999, Central Theorem) -/

open Core.DecisionTheory in
/-- Expected utility computed via a partition: weight each cell's conditional EU
by the cell's probability.

EU_Q(a) = Σ_{c ∈ cells(Q)} P(c) · EU(a | c)

This is the partition-relative expected utility that Merin (1999) shows is
compositional under coarsening. -/
def partitionEU {A : Type*} (dp : DecisionProblem M A) (q : QUD M)
    (worlds : List M) (a : A) : ℚ :=
  let cells := q.toCells worlds
  cells.foldl (fun acc cell =>
    let cellWorlds := worlds.filter cell
    let cellProb := cellWorlds.foldl (fun s w => s + dp.prior w) 0
    let cellEU := conditionalEU dp cellWorlds a cell
    acc + cellProb * cellEU
  ) 0

/-! #### Arithmetic helpers for EU compositionality -/

private theorem foldl_add_shift' {α : Type*} (f : α → ℚ) (l : List α) (init : ℚ) :
    l.foldl (fun acc w => acc + f w) init = init + l.foldl (fun acc w => acc + f w) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (init + f x), ih (0 + f x)]; ring

private theorem foldl_add_eq_sum_map' {α : Type*} (f : α → ℚ) (l : List α) :
    l.foldl (fun acc w => acc + f w) 0 = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_shift' f xs (0 + f x)]; simp only [zero_add]; rw [ih]

private theorem mul_foldl_sum' {α : Type*} (c : ℚ) (f : α → ℚ) (l : List α) :
    c * l.foldl (fun acc w => acc + f w) 0 =
    l.foldl (fun acc w => acc + c * f w) 0 := by
  rw [foldl_add_eq_sum_map' f, foldl_add_eq_sum_map' (fun w => c * f w)]
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; rw [mul_add, ih]

private theorem sum_nonneg_of_nonneg_priors {α : Type*}
    (f : α → ℚ) (l : List α) (hf : ∀ w, f w ≥ 0) :
    l.foldl (fun s w => s + f w) 0 ≥ 0 := by
  rw [foldl_add_eq_sum_map']
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; linarith [hf x]

private theorem all_zero_of_nonneg_sum_zero {α : Type*}
    (f : α → ℚ) (l : List α) (hf : ∀ w, f w ≥ 0)
    (hsum : l.foldl (fun s w => s + f w) 0 = 0) :
    ∀ w ∈ l, f w = 0 := by
  induction l with
  | nil => intro w hw; exact absurd hw List.not_mem_nil
  | cons x xs ih =>
    intro w hw
    simp only [List.foldl_cons] at hsum
    rw [foldl_add_shift' _ xs (0 + f x)] at hsum; simp only [zero_add] at hsum
    have hx_nn := hf x
    have hxs_nn := sum_nonneg_of_nonneg_priors f xs hf
    have hx0 : f x = 0 := by linarith
    have hxs0 : xs.foldl (fun s w => s + f w) 0 = 0 := by linarith
    rcases List.mem_cons.mp hw with rfl | hmem
    · exact hx0
    · exact ih hxs0 w hmem

private theorem weighted_sum_zero_of_weights_zero {α : Type*}
    (f g : α → ℚ) (l : List α) (hzero : ∀ w ∈ l, f w = 0) :
    l.foldl (fun acc w => acc + f w * g w) 0 = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [foldl_add_shift' _ xs (0 + f x * g x)]; simp only [zero_add]
    rw [hzero x (List.Mem.head xs)]; simp only [zero_mul, zero_add]
    exact ih (fun w hw => hzero w (.tail x hw))

/-! #### Cell probability cancellation -/

open Core.DecisionTheory in
private theorem cellProb_mul_conditionalEU {A : Type*}
    (dp : DecisionProblem M A) (cellWorlds : List M) (a : A) (cell : M → Bool)
    (hfilt : cellWorlds.filter cell = cellWorlds)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    cellWorlds.foldl (fun s w => s + dp.prior w) 0 *
      conditionalEU dp cellWorlds a cell =
    cellWorlds.foldl (fun acc w => acc + dp.prior w * dp.utility w a) 0 := by
  by_cases htot : cellWorlds.foldl (fun s w => s + dp.prior w) 0 = 0
  · -- cellProb = 0: both sides are 0
    rw [htot, zero_mul]
    have hzero := all_zero_of_nonneg_sum_zero dp.prior cellWorlds hprior htot
    exact (weighted_sum_zero_of_weights_zero dp.prior (dp.utility · a)
      cellWorlds hzero).symm
  · -- cellProb ≠ 0: cancel
    simp only [conditionalEU, hfilt]
    set cp := cellWorlds.foldl (fun s w => s + dp.prior w) 0
    have hbeq : (cp == 0) = false := by
      simp only [BEq.beq]; exact decide_eq_false htot
    rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mul_foldl_sum' cp (fun w => dp.prior w / cp * dp.utility w a)]
    congr 1; ext w; field_simp

/-! #### Partition sum decomposition -/

-- Whether w is covered by any representative in the list
private def coveredByReps (q : QUD M) (reps : List M) : M → Bool :=
  fun w => reps.any (fun r => q.sameAnswer r w)

-- Disjoint filter sum: when p, q are disjoint on l,
-- (l.filter p).sum + (l.filter q).sum = (l.filter (p || q)).sum
private theorem disjoint_filter_foldl_add (f : M → ℚ) (p q : M → Bool) (l : List M)
    (h_disj : ∀ w ∈ l, ¬(p w = true ∧ q w = true)) :
    (l.filter p).foldl (fun s w => s + f w) 0 +
    (l.filter q).foldl (fun s w => s + f w) 0 =
    (l.filter (fun w => p w || q w)).foldl (fun s w => s + f w) 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun w hw => h_disj w (.tail x hw))
    simp only [List.filter_cons]
    have hx_disj := h_disj x (.head xs)
    cases hp : p x <;> cases hq : q x
    · -- p x = false, q x = false
      simp only [Bool.false_or, ite_false]; exact ih'
    · -- p x = false, q x = true: x goes to q-filter and (p||q)-filter
      simp only [ite_false, ite_true, Bool.false_or, Bool.false_eq_true,
                 ↓reduceIte, List.foldl_cons]
      rw [foldl_add_shift' _ (xs.filter q) (0 + f x),
          foldl_add_shift' _ (xs.filter (fun w => p w || q w)) (0 + f x)]
      simp only [zero_add]
      linarith [ih']
    · -- p x = true, q x = false: x goes to p-filter and (p||q)-filter
      simp only [ite_true, ite_false, Bool.true_or, Bool.false_eq_true,
                 ↓reduceIte, List.foldl_cons]
      rw [foldl_add_shift' _ (xs.filter p) (0 + f x),
          foldl_add_shift' _ (xs.filter (fun w => p w || q w)) (0 + f x)]
      simp only [zero_add]
      linarith [ih']
    · -- p x = true, q x = true: contradicts disjointness
      exact absurd ⟨hp, hq⟩ hx_disj

-- Invariant: sum over reps = sum over covered worlds
private theorem rep_sum_inv (f : M → ℚ) (q : QUD M) (worlds : List M) (reps : List M)
    (hnodup : reps.Nodup)
    (hpw : ∀ r1 ∈ reps, ∀ r2 ∈ reps, q.sameAnswer r1 r2 = true → r1 = r2) :
    reps.foldl (fun acc rep =>
      acc + (worlds.filter (fun w => q.sameAnswer rep w)).foldl
        (fun s w => s + f w) 0) 0 =
    (worlds.filter (coveredByReps q reps)).foldl (fun s w => s + f w) 0 := by
  induction reps with
  | nil =>
    -- No reps: LHS = 0, RHS = filter by (fun _ => false) = [] → 0
    simp only [List.foldl_nil]
    suffices worlds.filter (coveredByReps q []) = [] by rw [this]; rfl
    exact List.filter_eq_nil_iff.mpr (fun _ _ => by simp [coveredByReps, List.any_nil])
  | cons r rs ih =>
    simp only [List.foldl_cons]
    rw [foldl_add_shift' (fun rep =>
      (worlds.filter (fun w => q.sameAnswer rep w)).foldl (fun s w => s + f w) 0)
      rs _]
    simp only [zero_add]
    -- IH: rs sum = covered-by-rs sum
    have hnodup_rs : rs.Nodup := (List.nodup_cons.mp hnodup).2
    have hr_notin : r ∉ rs := (List.nodup_cons.mp hnodup).1
    have hpw_rs : ∀ r1 ∈ rs, ∀ r2 ∈ rs, q.sameAnswer r1 r2 = true → r1 = r2 :=
      fun r1 h1 r2 h2 => hpw r1 (.tail r h1) r2 (.tail r h2)
    rw [ih hnodup_rs hpw_rs]
    -- Goal: filter-by-r sum + filter-by-coveredByReps-rs sum = filter-by-coveredByReps-(r::rs) sum
    -- coveredByReps q (r :: rs) w = q.sameAnswer r w || coveredByReps q rs w
    have hcov_cons : ∀ w, coveredByReps q (r :: rs) w =
        (q.sameAnswer r w || coveredByReps q rs w) := by
      intro w; simp [coveredByReps, List.any_cons]
    conv_rhs => rw [show worlds.filter (coveredByReps q (r :: rs)) =
      worlds.filter (fun w => q.sameAnswer r w || coveredByReps q rs w)
      from List.filter_congr (fun w _ => hcov_cons w)]
    -- Apply disjoint_filter_foldl_add
    exact disjoint_filter_foldl_add f (fun w => q.sameAnswer r w)
      (coveredByReps q rs) worlds (fun w _ ⟨hr_w, hcov_w⟩ => by
        -- r covers w, and some r' ∈ rs covers w → r = r' → r ∈ rs → contradiction
        obtain ⟨r', hr'_mem, hr'_eq⟩ := List.any_eq_true.mp hcov_w
        have : q.sameAnswer r r' = true :=
          q.trans r w r' hr_w (by rw [q.symm]; exact hr'_eq)
        have : r = r' := hpw r (.head rs) r' (.tail r hr'_mem) this
        exact hr_notin (this ▸ hr'_mem))

-- Filter by a predicate that holds everywhere = identity
private theorem filter_eq_self_of_forall {α : Type*} (p : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, h x (.head xs), ite_true]
    exact congrArg (x :: ·) (ih (fun y hy => h y (.tail x hy)))

-- Main decomposition: sum over toCells = flat sum over worlds
private theorem toCells_sum_decomp (f : M → ℚ) (q : QUD M) (worlds : List M) :
    (q.toCells worlds).foldl (fun acc cell =>
      acc + (worlds.filter cell).foldl (fun s w => s + f w) 0) 0 =
    worlds.foldl (fun s w => s + f w) 0 := by
  -- toCells = reps.map (fun rep => fun w => q.sameAnswer rep w)
  unfold toCells
  set reps := worlds.foldl (stepFn q) []
  -- Convert foldl over map to foldl over reps
  rw [show (reps.map (fun rep w => q.sameAnswer rep w)).foldl
      (fun acc cell => acc + (worlds.filter cell).foldl (fun s w => s + f w) 0) 0 =
    reps.foldl (fun acc rep =>
      acc + (worlds.filter (fun w => q.sameAnswer rep w)).foldl
        (fun s w => s + f w) 0) 0
    from by rw [List.foldl_map]]
  -- Apply rep_sum_inv
  have hempty : ∀ r1 ∈ ([] : List M), ∀ r2 ∈ ([] : List M),
      q.sameAnswer r1 r2 = true → r1 = r2 :=
    fun _ h1 => absurd h1 List.not_mem_nil
  have hnodup : reps.Nodup := repFold_nodup q worlds [] List.nodup_nil hempty
  have hpw : ∀ r1 ∈ reps, ∀ r2 ∈ reps,
      q.sameAnswer r1 r2 = true → r1 = r2 :=
    repFold_pairwiseInequiv q worlds [] hempty
  rw [rep_sum_inv f q worlds reps hnodup hpw]
  -- Now: (worlds.filter (coveredByReps q reps)).foldl ... = worlds.foldl ...
  -- By exhaustivity, every w ∈ worlds is covered
  exact congrArg (fun l => l.foldl (fun s w => s + f w) 0)
    (filter_eq_self_of_forall (coveredByReps q reps) worlds (fun w hw => by
      obtain ⟨r, hr_mem, hr_eq⟩ := repFold_covers q worlds [] w hw
      exact List.any_eq_true.mpr ⟨r, hr_mem, hr_eq⟩))

/-! #### Filter idempotence for cells -/

private theorem filter_filter_self {α : Type*} (p : α → Bool) (l : List α) :
    (l.filter p).filter p = l.filter p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x
    · exact ih
    · simp only [List.filter_cons, hp, ite_true]; exact congrArg (x :: ·) ih

open Core.DecisionTheory in
/-- Law of total expectation for partition-relative EU (Merin 1999).

The unconditional expected utility equals the partition-relative EU for
any partition, because partitions are exhaustive and mutually exclusive.

**Proof sketch**: For each cell c with `cellProb = Σ_{w∈c} prior(w)`:
- If `cellProb ≠ 0`: `cellProb * conditionalEU(c)` =
  `cellProb * Σ_{w∈c} (prior(w)/cellProb) * util(w,a)` =
  `Σ_{w∈c} prior(w) * util(w,a)`.
- If `cellProb = 0`: non-negativity of priors forces each `prior(w) = 0`
  for `w ∈ c`, so `Σ prior(w) * util(w,a) = 0 = cellProb * conditionalEU(c)`.

Then `partitionEU = Σ_c Σ_{w∈c} prior(w)*util(w,a) = Σ_w prior(w)*util(w,a)
= expectedUtility`, using exhaustivity and mutual exclusivity of `toCells`.

**Non-negativity is necessary**: with `prior(w1) = 1, prior(w2) = -1`,
`utility(w1,a) = 1, utility(w2,a) = 0`, and a trivial partition,
`expectedUtility = 1` but `cellProb = 0` forces `partitionEU = 0`. -/
theorem eu_eq_partitionEU {A : Type*} (dp : DecisionProblem M A)
    (worlds : List M) (a : A) (q : QUD M)
    (hprior : ∀ w, dp.prior w ≥ 0) :
    expectedUtility dp worlds a = partitionEU dp q worlds a := by
  unfold expectedUtility partitionEU
  set cells := q.toCells worlds
  -- Step 1: Replace cellProb * conditionalEU with raw weighted sums in the foldl
  suffices h : cells.foldl (fun acc cell =>
      let cellWorlds := worlds.filter cell
      let cellProb := cellWorlds.foldl (fun s w => s + dp.prior w) 0
      let cellEU := conditionalEU dp cellWorlds a cell
      acc + cellProb * cellEU) 0 =
    cells.foldl (fun acc cell =>
      acc + (worlds.filter cell).foldl
        (fun s w => s + dp.prior w * dp.utility w a) 0) 0 by
    rw [h]; exact (toCells_sum_decomp (fun w => dp.prior w * dp.utility w a) q worlds).symm
  -- Step 2: The two foldls agree because each cell step produces the same value
  have hcell_eq : ∀ (cell : M → Bool),
      (worlds.filter cell).foldl (fun s w => s + dp.prior w) 0 *
        conditionalEU dp (worlds.filter cell) a cell =
      (worlds.filter cell).foldl (fun s w => s + dp.prior w * dp.utility w a) 0 :=
    fun cell => cellProb_mul_conditionalEU dp (worlds.filter cell) a cell
      (filter_filter_self cell worlds) hprior
  -- Prove foldl equality by induction on cells, generalizing the accumulator
  suffices ∀ init : ℚ,
      cells.foldl (fun acc cell =>
        let cellWorlds := worlds.filter cell
        let cellProb := cellWorlds.foldl (fun s w => s + dp.prior w) 0
        let cellEU := conditionalEU dp cellWorlds a cell
        acc + cellProb * cellEU) init =
      cells.foldl (fun acc cell =>
        acc + (worlds.filter cell).foldl
          (fun s w => s + dp.prior w * dp.utility w a) 0) init from this 0
  intro init; induction cells generalizing init with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]; rw [hcell_eq c]; exact ih _

open Core.DecisionTheory in
/-- Partition-relative EU is partition-independent (given non-negative priors).

Any two partitions give the same partition-relative EU, because both
equal the unconditional EU (`eu_eq_partitionEU`). The coarsening
hypothesis `_hcoarse` is logically vacuous — included only for API
compatibility with callers that think of this as "coarsening preserves EU." -/
theorem coarsening_preserves_eu {A : Type*}
    (dp : DecisionProblem M A) (q q' : QUD M)
    (worlds : List M) (a : A)
    (_hcoarse : q.coarsens q')
    (hprior : ∀ w, dp.prior w ≥ 0) :
    partitionEU dp q worlds a = partitionEU dp q' worlds a :=
  (eu_eq_partitionEU dp worlds a q hprior).symm.trans
    (eu_eq_partitionEU dp worlds a q' hprior)

/-! ### Blackwell Ordering (Blackwell 1953) -/

open Core.DecisionTheory in
/-- The value of a decision problem under partition Q: the maximum expected
utility achievable when the decision-maker learns which Q-cell obtains. -/
def partitionValue {A : Type*} (dp : DecisionProblem M A)
    (q : QUD M) (worlds : List M) (actions : List A) : ℚ :=
  let cells := q.toCells worlds
  cells.foldl (fun acc cell =>
    let cellWorlds := worlds.filter cell
    let cellProb := cellWorlds.foldl (fun s w => s + dp.prior w) 0
    let bestEU := actions.foldl (fun best a =>
      max best (conditionalEU dp cellWorlds a cell)) 0
    acc + cellProb * bestEU
  ) 0

open Core.DecisionTheory in
/-- Blackwell's theorem for partitions: finer partitions are always at least
as valuable as coarser ones, for any decision problem with non-negative priors.

V_Q(D) ≥ V_{Q'}(D) for all decision problems D, whenever Q ⊑ Q'.

**Proof sketch** (Jensen's inequality for partitions): Each coarse cell c'
is a union of fine cells c₁,...,cₖ. The fine partition chooses the best
action within each cᵢ: `Σᵢ P(cᵢ) · max_a EU(a|cᵢ)`. The coarse partition
chooses one action for all of c': `P(c') · max_a EU(a|c')`. Since
`max_a EU(a|c') = max_a Σᵢ (P(cᵢ)/P(c')) · EU(a|cᵢ) ≤ Σᵢ (P(cᵢ)/P(c')) · max_a EU(a|cᵢ)`,
multiplying by `P(c')` gives the result.

Non-negativity is needed because negative `P(cᵢ)` would flip the inequality. -/
theorem blackwell_refinement_value {A : Type*}
    (dp : DecisionProblem M A) (q q' : QUD M)
    (worlds : List M) (actions : List A)
    (hrefines : q ⊑ q')
    (hprior : ∀ w, dp.prior w ≥ 0) :
    partitionValue dp q worlds actions ≥ partitionValue dp q' worlds actions := by
  sorry -- TODO: decompose coarse cells into fine cells, apply Jensen

set_option maxHeartbeats 1600000 in
open Core.DecisionTheory in
/-- Helper: when q merges w,v but q' separates them, a witness DP achieves
strictly higher value under q' than q.

The DP uses uniform prior (1/2 each) with utility that rewards matching
action to world: `utility(m, true) = 1` if m is in w's cell, 0 otherwise;
`utility(m, false) = 1` if m is in v's cell, 0 otherwise.

Under q (merged): best action gets EU = 1/2, so `partitionValue q = 1/2`.
Under q' (separated): each cell's best action gets EU = 1, so
`partitionValue q' = 1/2 · 1 + 1/2 · 1 = 1`. -/
private theorem witness_dp_beats_merged (q q' : QUD M) (w v : M)
    (hwv_q : q.sameAnswer w v = true)
    (hwv_q'f : q'.sameAnswer w v = false)
    (hvw_q'f : q'.sameAnswer v w = false) :
    ¬ (partitionValue
        { utility := fun m a =>
            if a then (if q'.sameAnswer w m then 1 else 0)
            else (if q'.sameAnswer v m then 1 else 0)
          prior := fun _ => (1 : ℚ) / 2 }
        q [w, v] [true, false] ≥
       partitionValue
        { utility := fun m a =>
            if a then (if q'.sameAnswer w m then 1 else 0)
            else (if q'.sameAnswer v m then 1 else 0)
          prior := fun _ => (1 : ℚ) / 2 }
        q' [w, v] [true, false]) := by
  simp only [partitionValue, toCells, conditionalEU,
             List.foldl_cons, List.foldl_nil,
             List.any_nil, List.any_cons, Bool.or_false, Bool.false_eq_true,
             List.map_cons, List.map_nil,
             List.filter_cons, List.filter_nil,
             q.refl, q'.refl, hwv_q, hwv_q'f, hvw_q'f,
             ite_true, ite_false, Bool.false_eq_true]
  native_decide

set_option maxHeartbeats 1600000 in
open Core.DecisionTheory in
/-- Blackwell ordering characterizes refinement: Q refines Q' if and only if
Q is at least as valuable as Q' for every decision problem.

This is the converse of `blackwell_refinement_value`: if Q is always at
least as valuable, then Q must refine Q'. Together they establish that
partition refinement IS Blackwell ordering.

**Proof** (contrapositive): Suppose `q` does not refine `q'`, i.e.,
∃ w v with `q.sameAnswer w v = true` but `q'.sameAnswer w v = false`.
Construct a DP over `worlds = [w, v]` with two actions where distinguishing
w from v matters: `utility(w, a₁) = 1, utility(w, a₂) = 0, utility(v, a₁) = 0,
utility(v, a₂) = 1`, uniform prior `1/2`. Then q' can condition on {w} vs {v}
and achieve value 1, while q cannot distinguish them and achieves value 1/2.
So q' beats q on this DP, contradicting the hypothesis.

**Note**: The hypothesis quantifies over *all* world lists (not a fixed one),
which is necessary since the witness uses `worlds = [w, v]` for the specific
w, v witnessing non-refinement. -/
theorem blackwell_characterizes_refinement
    (q q' : QUD M)
    (h : ∀ (worlds : List M) (A : Type) (dp : DecisionProblem M A) (actions : List A),
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
    (h [w, v] Bool
      { utility := fun m a =>
          if a then (if q'.sameAnswer w m then 1 else 0)
          else (if q'.sameAnswer v m then 1 else 0)
        prior := fun _ => (1 : ℚ) / 2 }
      [true, false]
      (by intro _; show (0 : ℚ) ≤ 1 / 2; native_decide))

end QUD
