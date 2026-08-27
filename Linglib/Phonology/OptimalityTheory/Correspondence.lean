import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Data.Fintype.Card
import Linglib.Phonology.Constraints.Defs

/-!
# Correspondence Theory

A correspondence between two strings ([mccarthy-prince-1995] (10)) is a relation ℛ
between their positions, and a faithfulness constraint is a condition on ℛ: MAX reads
its domain, DEP its range, IDENT the segments at corresponding positions.
`Correspondence Role α` carries one string per role (`form`) and the relation
`edge r₁ r₂` for every ordered pair of roles, so the input–output, base–reduplicant
and output–output ([benua-1997]) relations of one candidate are cells of a single
diagram. The relation is directed, as ℛ is; "correspondents of one another" is the
derived property `IsSymmetric`.

The constraints of Appendix A are families `Correspondence Role α → Role → Role → ℕ`
counting offending elements; a named constraint is a partial application (MAX-IO is
`(·.maxViol .input .output)`), and each cardinal family vanishes iff the relation has
the matching order-theoretic property (`maxViol_eq_zero_iff`, …). Positions are
`Fin`-indexed, so every pair of `edge` is in range by type. The position-relation
encoding follows [payne-vu-heinz-2017] and [potts-pullum-2002] (base–reduplicant
relations: [dolatian-heinz-2020]).

## Main definitions

* `Correspondence` — role-indexed strings with a directed relation between the
  positions of each ordered pair of roles.
* `Correspondence.maxViol`, `depViol`, `identViol`, `identViolFeature`, `contigIViol`,
  `contigOViol`, `anchorLViol`, `anchorRViol`, `linearityViol`, `uniformityViol`,
  `integrityViol` — the constraint families of Appendix A; `maxViolOn`, `depViolOn` are
  their segment-class restrictions (MAX-V, DEP-C, …).
* `Correspondence.ofPairs`, `diagram`, `parallel`, `identity`, `reduplication` —
  constructors: from index pairs, the diagonal on a role predicate, and the binary
  and input–base–reduplicant diagonal diagrams.
* `Correspondence.IsSymmetric`, `IsFaithful` — symmetry of the relation; freedom from
  the five order-relevant violations on an edge.
* `Correspondence.IsFaithfulness`, `IsMarkedness` — the structural
  faithfulness/markedness split for constraints over correspondences.

## Main results

* `Correspondence.isFaithful_iff_exists_orderIso` — an edge is faithful iff it is the
  graph of an order isomorphism between the two position orders.
* `Correspondence.diagram_isSymmetric` — a diagonal diagram over a symmetric role
  predicate is symmetric.
-/

namespace OptimalityTheory

open Constraints

/-- A correspondence diagram: a string per role and, for each ordered pair of roles,
a directed relation between their positions. -/
structure Correspondence (Role : Type*) (α : Type*) where
  form : Role → List α
  edge : (r₁ r₂ : Role) → Finset (Fin (form r₁).length × Fin (form r₂).length)

namespace Correspondence

variable {Role : Type*} {α : Type*}

/-- Roles of a binary correspondence (`parallel`, `identity`). -/
inductive Side where
  | lhs
  | rhs
  deriving DecidableEq, Repr

/-- Roles of the basic model of reduplication: input, base, reduplicant. -/
inductive ReduplicationRole where
  | input
  | base
  | reduplicant
  deriving DecidableEq, Repr

/-- Correspondence is symmetric when each relation is the converse of the reverse
one. -/
def IsSymmetric (c : Correspondence Role α) : Prop :=
  ∀ r₁ r₂, c.edge r₂ r₁ = (c.edge r₁ r₂).image Prod.swap

/-! ### Constraint families -/

/-- MAX (A.1): the positions of `form r₁` without a correspondent in `form r₂`. -/
def maxViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  (Finset.univ \ (c.edge r₁ r₂).image Prod.fst).card

/-- DEP (A.2): the positions of `form r₂` without a correspondent in `form r₁`. -/
def depViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  (Finset.univ \ (c.edge r₁ r₂).image Prod.snd).card

/-- MAX (A.1) restricted to the positions of `form r₁` whose segment satisfies `P` — the
segment-class instances MAX-V, MAX-C. -/
def maxViolOn (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((Finset.univ.filter fun i : Fin (c.form r₁).length => P (c.form r₁)[i]) \
    (c.edge r₁ r₂).image Prod.fst).card

/-- DEP (A.2) restricted to the positions of `form r₂` whose segment satisfies `P` — the
segment-class instances DEP-V, DEP-C. -/
def depViolOn (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((Finset.univ.filter fun j : Fin (c.form r₂).length => P (c.form r₂)[j]) \
    (c.edge r₁ r₂).image Prod.snd).card

/-- IDENT (A.3) on whole segments: corresponding pairs whose segments differ. -/
def identViol [DecidableEq α] (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p => (c.form r₁)[p.1] ≠ (c.form r₂)[p.2]).card

/-- IDENT(F) (A.3) for the feature `proj`: corresponding pairs differing under
`proj`. -/
def identViolFeature {F : Type*} [DecidableEq F] (proj : α → F)
    (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p => proj (c.form r₁)[p.1] ≠ proj (c.form r₂)[p.2]).card

/-- MAX of a privative property along a segmental correspondence: corresponding pairs
whose first member has `P` and whose second lacks it — the autosegment is lost. -/
def maxViolFeature (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((c.edge r₁ r₂).filter fun p => P (c.form r₁)[p.1] ∧ ¬ P (c.form r₂)[p.2]).card

/-- DEP of a privative property along a segmental correspondence: corresponding pairs whose
second member has `P` and whose first lacks it — the autosegment is inserted. -/
def depViolFeature (P : α → Prop) [DecidablePred P] (c : Correspondence Role α) (r₁ r₂ : Role) :
    ℕ :=
  ((c.edge r₁ r₂).filter fun p => ¬ P (c.form r₁)[p.1] ∧ P (c.form r₂)[p.2]).card

/-- `maxViolFeature` is positive exactly when some correspondent loses `P`. -/
theorem maxViolFeature_pos_iff (P : α → Prop) [DecidablePred P] (c : Correspondence Role α)
    (r₁ r₂ : Role) :
    0 < maxViolFeature P c r₁ r₂ ↔
      ∃ p ∈ c.edge r₁ r₂, P (c.form r₁)[p.1] ∧ ¬ P (c.form r₂)[p.2] := by
  simp [maxViolFeature, Finset.card_pos, Finset.filter_nonempty_iff]

/-- I-CONTIG, "No Skipping" (A.4a): whether the domain of the relation is a contiguous
substring of `form r₁`. -/
def contigIViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if ((((c.edge r₁ r₂).image Prod.fst).image Fin.val).sort (· ≤ ·)).IsChain
      (fun a b => b = a + 1) then 0 else 1

/-- O-CONTIG, "No Intrusion" (A.4b): whether the range of the relation is a contiguous
substring of `form r₂`. -/
def contigOViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if ((((c.edge r₁ r₂).image Prod.snd).image Fin.val).sort (· ≤ ·)).IsChain
      (fun a b => b = a + 1) then 0 else 1

/-- L-ANCHOR (A.5): whether the leftmost positions correspond; vacuous when either
string is empty. -/
def anchorLViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if h : 0 < (c.form r₁).length ∧ 0 < (c.form r₂).length then
    if (⟨0, h.1⟩, ⟨0, h.2⟩) ∈ c.edge r₁ r₂ then 0 else 1
  else 0

/-- R-ANCHOR (A.5): whether the rightmost positions correspond; vacuous when either
string is empty. -/
def anchorRViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  if h : 0 < (c.form r₁).length ∧ 0 < (c.form r₂).length then
    if (⟨(c.form r₁).length - 1, Nat.pred_lt_self h.1⟩,
        ⟨(c.form r₂).length - 1, Nat.pred_lt_self h.2⟩) ∈ c.edge r₁ r₂ then 0 else 1
  else 0

/-- LINEARITY, "No Metathesis" (A.6): the pairs of correspondences `(i₁, j₁)`,
`(i₂, j₂)` with `i₁ < i₂` but `j₂ < j₁`. -/
def linearityViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂ ×ˢ c.edge r₁ r₂).filter fun pq => pq.1.1 < pq.2.1 ∧ pq.2.2 < pq.1.2).card

/-- UNIFORMITY, "No Coalescence" (A.7): the positions of `form r₂` with more than one
correspondent in `form r₁`. -/
def uniformityViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ : Finset (Fin (c.form r₂).length)).filter fun j =>
    1 < ((c.edge r₁ r₂).filter fun p => p.2 = j).card).card

/-- INTEGRITY, "No Breaking" (A.8): the positions of `form r₁` with more than one
correspondent in `form r₂`. -/
def integrityViol (c : Correspondence Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ : Finset (Fin (c.form r₁).length)).filter fun i =>
    1 < ((c.edge r₁ r₂).filter fun p => p.1 = i).card).card

/-! ### Vanishing characterizations

Each cardinal constraint vanishes iff the relation has the corresponding order-theoretic
property: left-total, right-total, functional, injective, order-preserving. -/

variable (c : Correspondence Role α) (r₁ r₂ : Role)

theorem maxViol_eq_zero_iff :
    c.maxViol r₁ r₂ = 0 ↔ Finset.univ ⊆ (c.edge r₁ r₂).image Prod.fst := by
  simp only [maxViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

theorem depViol_eq_zero_iff :
    c.depViol r₁ r₂ = 0 ↔ Finset.univ ⊆ (c.edge r₁ r₂).image Prod.snd := by
  simp only [depViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

theorem maxViolOn_true : maxViolOn (fun _ => True) c r₁ r₂ = c.maxViol r₁ r₂ := by
  simp [maxViolOn, maxViol]

theorem depViolOn_true : depViolOn (fun _ => True) c r₁ r₂ = c.depViol r₁ r₂ := by
  simp [depViolOn, depViol]

theorem integrityViol_eq_zero_iff :
    c.integrityViol r₁ r₂ = 0 ↔ ∀ i, ((c.edge r₁ r₂).filter fun p => p.1 = i).card ≤ 1 := by
  simp [integrityViol, Finset.filter_eq_empty_iff]

theorem uniformityViol_eq_zero_iff :
    c.uniformityViol r₁ r₂ = 0 ↔ ∀ j, ((c.edge r₁ r₂).filter fun p => p.2 = j).card ≤ 1 := by
  simp [uniformityViol, Finset.filter_eq_empty_iff]

theorem linearityViol_eq_zero_iff :
    c.linearityViol r₁ r₂ = 0 ↔
      ∀ p ∈ c.edge r₁ r₂, ∀ q ∈ c.edge r₁ r₂, p.1 < q.1 → ¬ q.2 < p.2 := by
  rw [linearityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact ⟨fun h p hp q hq hpq hqp => h (Finset.mk_mem_product hp hq) ⟨hpq, hqp⟩,
    fun h pq hpq hinv => h _ (Finset.mem_product.1 hpq).1 _ (Finset.mem_product.1 hpq).2
      hinv.1 hinv.2⟩

/-! ### Constructors -/

/-- The index pairs `(0, 0), …, (k - 1, k - 1)` of a parallel correspondence. -/
def diagonalPairs (k : ℕ) : List (ℕ × ℕ) := (List.range k).map fun i => (i, i)

/-- The relation on positions given by index pairs; pairs out of range are dropped. -/
def edgeOfPairs (m n : ℕ) (l : List (ℕ × ℕ)) : Finset (Fin m × Fin n) :=
  (l.filterMap fun p =>
    if h : p.1 < m ∧ p.2 < n then some (⟨p.1, h.1⟩, ⟨p.2, h.2⟩) else none).toFinset

@[simp] theorem mem_edgeOfPairs {m n : ℕ} {l : List (ℕ × ℕ)} {p : Fin m × Fin n} :
    p ∈ edgeOfPairs m n l ↔ ((p.1 : ℕ), (p.2 : ℕ)) ∈ l := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
  simp [edgeOfPairs, ha, hb]

/-- A correspondence from index pairs: `edge r₁ r₂` reads `pairs r₁ r₂` into the two
position types. -/
def ofPairs (form : Role → List α) (pairs : Role → Role → List (ℕ × ℕ)) :
    Correspondence Role α where
  form := form
  edge r₁ r₂ := edgeOfPairs _ _ (pairs r₁ r₂)

@[simp] theorem ofPairs_form (form : Role → List α) (pairs : Role → Role → List (ℕ × ℕ))
    (r : Role) : (ofPairs form pairs).form r = form r := rfl

@[simp] theorem ofPairs_edge (form : Role → List α) (pairs : Role → Role → List (ℕ × ℕ)) :
    (ofPairs form pairs).edge r₁ r₂ = edgeOfPairs _ _ (pairs r₁ r₂) := rfl

/-- The diagonal `(0, 0), (1, 1), …` of `Fin m × Fin n`, one pair per index of the
shorter string. -/
def diagonal (m n : ℕ) : Finset (Fin m × Fin n) :=
  (Finset.univ : Finset (Fin (min m n))).image
    fun i => (i.castLE (min_le_left _ _), i.castLE (min_le_right _ _))

@[simp] theorem mem_diagonal {m n : ℕ} (a : Fin m) (b : Fin n) :
    (a, b) ∈ diagonal m n ↔ (a : ℕ) = (b : ℕ) := by
  simp only [diagonal, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, Fin.ext_iff,
    Fin.val_castLE]
  exact ⟨fun ⟨_, h₁, h₂⟩ => h₁.symm.trans h₂,
    fun h => ⟨⟨a, by have := a.2; have := b.2; omega⟩, rfl, h⟩⟩

theorem card_diagonal (m n : ℕ) : (diagonal m n).card = min m n := by
  rw [diagonal, Finset.card_image_of_injective _ fun _ _ h => Fin.ext (congrArg (·.1.1) h),
    Finset.card_univ, Fintype.card_fin]

theorem image_swap_diagonal (m n : ℕ) : (diagonal m n).image Prod.swap = diagonal n m := by
  ext ⟨a, b⟩
  simp only [Finset.mem_image, mem_diagonal, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  exact ⟨fun ⟨_, _, h, rfl, rfl⟩ => h.symm, fun h => ⟨b, a, h.symm, rfl, rfl⟩⟩

/-- The diagonal correspondence on every pair of roles satisfying `hasEdge`, empty
elsewhere. -/
def diagram (form : Role → List α) (hasEdge : Role → Role → Prop) [DecidableRel hasEdge] :
    Correspondence Role α where
  form := form
  edge r₁ r₂ := if hasEdge r₁ r₂ then diagonal (form r₁).length (form r₂).length else ∅

section diagram

variable (form : Role → List α) (hasEdge : Role → Role → Prop) [DecidableRel hasEdge]

@[simp] theorem diagram_form (r : Role) : (diagram form hasEdge).form r = form r := rfl

theorem diagram_edge : (diagram form hasEdge).edge r₁ r₂ =
    if hasEdge r₁ r₂ then diagonal (form r₁).length (form r₂).length else ∅ := rfl

theorem diagram_edge_pos {r₁ r₂ : Role} (h : hasEdge r₁ r₂) :
    (diagram form hasEdge).edge r₁ r₂ = diagonal (form r₁).length (form r₂).length :=
  if_pos h

theorem diagram_edge_neg {r₁ r₂ : Role} (h : ¬ hasEdge r₁ r₂) :
    (diagram form hasEdge).edge r₁ r₂ = ∅ :=
  if_neg h

theorem diagram_isSymmetric (hsymm : ∀ {r₁ r₂}, hasEdge r₁ r₂ → hasEdge r₂ r₁) :
    IsSymmetric (diagram form hasEdge) := by
  intro r₁ r₂
  by_cases h : hasEdge r₁ r₂
  · rw [diagram_edge_pos _ _ (hsymm h), diagram_edge_pos _ _ h]
    exact (image_swap_diagonal _ _).symm
  · rw [diagram_edge_neg _ _ (mt hsymm h), diagram_edge_neg _ _ h, Finset.image_empty]

end diagram

/-- The diagonal correspondence between two strings, truncated to the shorter. -/
def parallel (s₁ s₂ : List α) : Correspondence Side α :=
  diagram (fun | .lhs => s₁ | .rhs => s₂) (· ≠ ·)

/-- The fully faithful candidate: the diagonal correspondence of a string with itself. -/
def identity (s : List α) : Correspondence Side α := parallel s s

/-- The input–base–reduplicant diagram with diagonal correspondence between each pair of
distinct roles. -/
def reduplication (input base reduplicant : List α) : Correspondence ReduplicationRole α :=
  diagram (fun | .input => input | .base => base | .reduplicant => reduplicant) (· ≠ ·)

theorem parallel_isSymmetric (s₁ s₂ : List α) : IsSymmetric (parallel s₁ s₂) :=
  diagram_isSymmetric _ _ Ne.symm

theorem reduplication_isSymmetric (input base reduplicant : List α) :
    IsSymmetric (reduplication input base reduplicant) :=
  diagram_isSymmetric _ _ Ne.symm

@[simp] theorem parallel_form_lhs (s₁ s₂ : List α) : (parallel s₁ s₂).form .lhs = s₁ := rfl

@[simp] theorem parallel_form_rhs (s₁ s₂ : List α) : (parallel s₁ s₂).form .rhs = s₂ := rfl

@[simp] theorem parallel_edge_diag (s₁ s₂ : List α) (r : Side) :
    (parallel s₁ s₂).edge r r = ∅ :=
  diagram_edge_neg _ _ (by cases r <;> decide)

@[simp] theorem parallel_edge_lhs_rhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).edge .lhs .rhs = diagonal s₁.length s₂.length :=
  diagram_edge_pos _ _ (by decide)

@[simp] theorem parallel_edge_rhs_lhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).edge .rhs .lhs = diagonal s₂.length s₁.length := by
  rw [parallel_isSymmetric s₁ s₂ .lhs .rhs, parallel_edge_lhs_rhs]
  exact image_swap_diagonal _ _

@[simp] theorem reduplication_form_input (input base reduplicant : List α) :
    (reduplication input base reduplicant).form .input = input := rfl

@[simp] theorem reduplication_form_base (input base reduplicant : List α) :
    (reduplication input base reduplicant).form .base = base := rfl

@[simp] theorem reduplication_form_reduplicant (input base reduplicant : List α) :
    (reduplication input base reduplicant).form .reduplicant = reduplicant := rfl

/-! ### Faithfulness on the diagonal

MAX, DEP and IDENT vanish on a diagonal edge between equal strings — the fully faithful
candidate, and total reduplication read on its base–reduplicant edge. -/

theorem maxViol_eq_zero_of_diagonal (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.maxViol r₁ r₂ = 0 := by
  have hlen : (c.form r₁).length = (c.form r₂).length := congrArg List.length hform
  rw [maxViol_eq_zero_iff, hedge]
  intro i _
  exact Finset.mem_image.2 ⟨(i, ⟨i, hlen ▸ i.2⟩), (mem_diagonal _ _).2 rfl, rfl⟩

theorem depViol_eq_zero_of_diagonal (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.depViol r₁ r₂ = 0 := by
  have hlen : (c.form r₁).length = (c.form r₂).length := congrArg List.length hform
  rw [depViol_eq_zero_iff, hedge]
  intro j _
  exact Finset.mem_image.2 ⟨(⟨j, hlen.symm ▸ j.2⟩, j), (mem_diagonal _ _).2 rfl, rfl⟩

theorem identViolFeature_eq_zero_of_diagonal {F : Type*} [DecidableEq F] (proj : α → F)
    (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.identViolFeature proj r₁ r₂ = 0 := by
  simp only [identViolFeature, hedge, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not]
  rintro ⟨i, j⟩ hij
  have hij : (i : ℕ) = j := (mem_diagonal i j).1 hij
  have h : (c.form r₁)[(i : ℕ)]? = (c.form r₂)[(j : ℕ)]? := by rw [hij, hform]
  rw [List.getElem?_eq_getElem i.2, List.getElem?_eq_getElem j.2, Option.some_inj] at h
  exact congrArg proj h

theorem identViol_eq_zero_of_diagonal [DecidableEq α] (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagonal (c.form r₁).length (c.form r₂).length) :
    c.identViol r₁ r₂ = 0 :=
  identViolFeature_eq_zero_of_diagonal c r₁ r₂ id hform hedge

@[simp] theorem maxViol_identity (s : List α) : (identity s).maxViol .lhs .rhs = 0 :=
  maxViol_eq_zero_of_diagonal _ _ _ rfl (parallel_edge_lhs_rhs s s)

@[simp] theorem depViol_identity (s : List α) : (identity s).depViol .lhs .rhs = 0 :=
  depViol_eq_zero_of_diagonal _ _ _ rfl (parallel_edge_lhs_rhs s s)

@[simp] theorem identViol_identity [DecidableEq α] (s : List α) :
    (identity s).identViol .lhs .rhs = 0 :=
  identViol_eq_zero_of_diagonal _ _ _ rfl (parallel_edge_lhs_rhs s s)

@[simp] theorem identViolFeature_identity {F : Type*} [DecidableEq F] (proj : α → F)
    (s : List α) : (identity s).identViolFeature proj .lhs .rhs = 0 :=
  identViolFeature_eq_zero_of_diagonal _ _ _ proj rfl (parallel_edge_lhs_rhs s s)

/-! ### Faithfulness as order isomorphism -/

/-- An edge is faithful when it has no MAX, DEP, INTEGRITY, UNIFORMITY or LINEARITY
violation — exactly the hypotheses under which it is the graph of an order
isomorphism. -/
structure IsFaithful : Prop where
  max : c.maxViol r₁ r₂ = 0
  dep : c.depViol r₁ r₂ = 0
  integrity : c.integrityViol r₁ r₂ = 0
  uniformity : c.uniformityViol r₁ r₂ = 0
  linearity : c.linearityViol r₁ r₂ = 0

/-- Without MAX or INTEGRITY violations the edge is the graph of a function. -/
theorem exists_fun_mem_edge_iff (hmax : c.maxViol r₁ r₂ = 0)
    (hint : c.integrityViol r₁ r₂ = 0) :
    ∃ f : Fin (c.form r₁).length → Fin (c.form r₂).length,
      ∀ i j, (i, j) ∈ c.edge r₁ r₂ ↔ f i = j := by
  have hexU : ∀ i, ∃! j, (i, j) ∈ c.edge r₁ r₂ := fun i => by
    obtain ⟨⟨a, b⟩, hp, rfl⟩ :=
      Finset.mem_image.1 ((maxViol_eq_zero_iff c r₁ r₂).1 hmax (Finset.mem_univ i))
    have hone := Finset.card_le_one.1 ((integrityViol_eq_zero_iff c r₁ r₂).1 hint a)
    exact ⟨b, hp, fun j hj => congrArg Prod.snd
      (hone _ (Finset.mem_filter.2 ⟨hj, rfl⟩) _ (Finset.mem_filter.2 ⟨hp, rfl⟩))⟩
  choose f hf huniq using hexU
  exact ⟨f, fun i j => ⟨fun h => (huniq i j h).symm, fun h => h ▸ hf i⟩⟩

theorem isFaithful_iff_exists_orderIso :
    c.IsFaithful r₁ r₂ ↔
      ∃ e : Fin (c.form r₁).length ≃o Fin (c.form r₂).length,
        ∀ i j, (i, j) ∈ c.edge r₁ r₂ ↔ e i = j := by
  constructor
  · rintro ⟨hmax, hdep, hint, huni, hlin⟩
    obtain ⟨f, mem_iff⟩ := exists_fun_mem_edge_iff c r₁ r₂ hmax hint
    have memf : ∀ i, (i, f i) ∈ c.edge r₁ r₂ := fun i => (mem_iff i (f i)).2 rfl
    -- UNIFORMITY rules out collisions and LINEARITY inversions, so `f` is strictly monotone.
    have hmono : StrictMono f := by
      intro a b hab
      rcases lt_trichotomy (f a) (f b) with h | h | h
      · exact h
      · have hu := Finset.card_le_one.1 ((uniformityViol_eq_zero_iff c r₁ r₂).1 huni (f b))
        exact absurd (congrArg Prod.fst <| hu _ (Finset.mem_filter.2 ⟨memf a, h⟩)
          _ (Finset.mem_filter.2 ⟨memf b, rfl⟩)) (ne_of_lt hab)
      · exact absurd h ((linearityViol_eq_zero_iff c r₁ r₂).1 hlin _ (memf a) _ (memf b) hab)
    have hsurj : Function.Surjective f := fun j => by
      obtain ⟨p, hp, hp2⟩ := Finset.mem_image.1
        ((depViol_eq_zero_iff c r₁ r₂).1 hdep (Finset.mem_univ j))
      exact ⟨p.1, (mem_iff p.1 j).1 (by simpa [← hp2] using hp)⟩
    exact ⟨StrictMono.orderIsoOfSurjective f hmono hsurj,
      fun i j => by rw [mem_iff, StrictMono.coe_orderIsoOfSurjective]⟩
  · rintro ⟨e, he⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (maxViol_eq_zero_iff c r₁ r₂).2 fun i _ =>
        Finset.mem_image.2 ⟨(i, e i), (he i (e i)).2 rfl, rfl⟩
    · exact (depViol_eq_zero_iff c r₁ r₂).2 fun j _ =>
        Finset.mem_image.2 ⟨(e.symm j, j), (he _ j).2 (e.apply_symm_apply j), rfl⟩
    · refine (integrityViol_eq_zero_iff c r₁ r₂).2 fun i =>
        Finset.card_le_one.2 fun p hp q hq => ?_
      rw [Finset.mem_filter] at hp hq
      exact Prod.ext (hp.2.trans hq.2.symm) <| calc
        p.2 = e p.1 := ((he p.1 p.2).1 hp.1).symm
        _   = e q.1 := by rw [hp.2.trans hq.2.symm]
        _   = q.2   := (he q.1 q.2).1 hq.1
    · refine (uniformityViol_eq_zero_iff c r₁ r₂).2 fun j =>
        Finset.card_le_one.2 fun p hp q hq => ?_
      rw [Finset.mem_filter] at hp hq
      refine Prod.ext (e.injective ?_) (hp.2.trans hq.2.symm)
      calc e p.1 = p.2 := (he p.1 p.2).1 hp.1
        _ = q.2   := hp.2.trans hq.2.symm
        _ = e q.1 := ((he q.1 q.2).1 hq.1).symm
    · refine (linearityViol_eq_zero_iff c r₁ r₂).2 fun p hp q hq hpq => ?_
      rw [← (he p.1 p.2).1 hp, ← (he q.1 q.2).1 hq]
      exact not_lt.2 (e.lt_iff_lt.2 hpq).le

/-- A faithful edge joins strings of equal length. -/
theorem length_eq_of_isFaithful (h : c.IsFaithful r₁ r₂) :
    (c.form r₁).length = (c.form r₂).length := by
  obtain ⟨e, _⟩ := (isFaithful_iff_exists_orderIso c r₁ r₂).1 h
  simpa using Fintype.card_congr e.toEquiv

/-! ### Faithfulness and markedness constraints

A constraint over correspondences is faithfulness when the fully faithful candidate
satisfies it, and markedness when it reads only the output string. The split is
structural, and non-vacuous: \*STRUC is markedness and fires on `identity s`. -/

/-- A constraint over binary correspondences is **faithfulness** when the fully faithful
candidate `identity s` satisfies it. -/
def IsFaithfulness (k : Constraint (Correspondence Side α)) : Prop :=
  ∀ s : List α, k (identity s) = 0

/-- A constraint is **markedness** for the role `out` when it depends only on
`form out`. -/
def IsMarkedness (out : Role) (k : Constraint (Correspondence Role α)) : Prop :=
  ∀ c₁ c₂ : Correspondence Role α, c₁.form out = c₂.form out → k c₁ = k c₂

theorem isFaithfulness_maxViol : IsFaithfulness (α := α) (maxViol · .lhs .rhs) :=
  maxViol_identity

theorem isFaithfulness_depViol : IsFaithfulness (α := α) (depViol · .lhs .rhs) :=
  depViol_identity

theorem isFaithfulness_identViol [DecidableEq α] :
    IsFaithfulness (α := α) (identViol · .lhs .rhs) :=
  identViol_identity

theorem exists_isMarkedness_not_isFaithfulness [Inhabited α] :
    ∃ k : Constraint (Correspondence Side α), IsMarkedness .rhs k ∧ ¬ IsFaithfulness k :=
  ⟨fun c => (c.form .rhs).length, fun _ _ h => by simp [h],
    fun h => by simpa [identity] using h [default]⟩

end Correspondence

end OptimalityTheory
