import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Data.Fintype.Card
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Basic
import Linglib.Phonology.OptimalityTheory.Constraints

/-!
# Correspondence Theory
[mccarthy-prince-1995] [benua-1997]

Correspondence diagrams and their faithfulness constraints. A `Corr Role α`
gives each role a string (`form`) and each ordered role pair a correspondence
relation `edge` between positions. Each faithfulness constraint is a map
`Corr Role α → Role → Role → ℕ`.

Following [mccarthy-prince-1995] (Def. 10), `edge r₁ r₂` is the directed
relation ℛ ⊆ S₁ × S₂ that every constraint reads (MAX off its Domain, DEP off
its Range, …). Symmetry — "correspondents of one another" — is a *derived*
property (`IsSymmetric`, proved of the constructors), not built into the type,
since M&P's ℛ is a directed subset. The position-relation encoding follows the
model-theoretic treatment of [payne-vu-heinz-2017] and
[potts-pullum-2002] (reduplicative B-R: [dolatian-heinz-2020]).

## Main definitions

* `Corr` — a correspondence diagram (`form` plus the directed relation `edge`).
* `Corr.maxViol`, `depViol`, `identViol`, `linearityViol`, `contigIViol`,
  `anchorLViol`, `integrityViol`, `uniformityViol` — the faithfulness
  families; named constraints are partial applications (`MAX-IO` is
  `c.maxViol .input .output`).
* `Corr.diagram` — the universal constructor; `parallel`, `identity`,
  `reduplication` are diagonal specializations.
* `Corr.IsSymmetric` — correspondence symmetry, derived for the constructors.
* `Corr.RoleQuiv` — the labeled-quiver structure on `Role`.

## Main results

* `Corr.IsFaithful` — the conjunction of the five order-relevant zeros
  (MAX, DEP, INTEGRITY, UNIFORMITY, LINEARITY).
* `Corr.isFaithful_iff_exists_orderIso` — a correspondence is faithful iff
  its edge is the graph of an order isomorphism between the two position
  orders.
* `Corr.exists_orderIso_of_faithful` — the forward direction (the converse
  of the `identity_*_zero` lemmas).
-/

namespace OptimalityTheory.Correspondence

open Constraints OptimalityTheory
open Finset

/-! ### Binary and ternary roles -/

/-- Roles for a binary correspondence (`Corr.parallel`, `Corr.identity`). -/
inductive Side where
  | lhs
  | rhs
  deriving DecidableEq, Repr

/-- Roles for a reduplicative correspondence: input, base, reduplicant
    ([mccarthy-prince-1995]); used by `Corr.reduplication`. -/
inductive RedupRole where
  | input
  | base
  | reduplicant
  deriving DecidableEq, Repr

/-! ### The correspondence diagram -/

/-- A correspondence diagram: role-indexed `form`s and a directed
    correspondence relation `edge` between positions ([mccarthy-prince-1995]
    Def. 10). The in-range bound is carried by the `Fin`-indexed type of
    `edge` rather than a separate well-formedness field. -/
structure Corr (Role : Type*) (α : Type*) where
  form : Role → List α
  edge : (r₁ r₂ : Role) → Finset (Fin (form r₁).length × Fin (form r₂).length)

namespace Corr

variable {Role : Type*} {α : Type*}

/-- Correspondence is symmetric — "correspondents of one another"
    ([mccarthy-prince-1995] Def. 10): each relation is the converse of
    the reverse one. A derived property (`diagram_isSymmetric`), not a field. -/
def IsSymmetric (c : Corr Role α) : Prop :=
  ∀ r₁ r₂, c.edge r₂ r₁ = (c.edge r₁ r₂).image Prod.swap

/-! ### Constraint families -/

/-- MAX ([mccarthy-prince-1995] A.1): the count of `form r₁` positions with
    no correspondent in `form r₂`. MAX-OO is basemap faithfulness ([benua-1997]). -/
def maxViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  (Finset.univ \ (c.edge r₁ r₂).image Prod.fst).card

/-- DEP ([mccarthy-prince-1995] A.2): the count of `form r₂` positions with
    no correspondent in `form r₁`. DEP-IO prohibits epenthesis. -/
def depViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  (Finset.univ \ (c.edge r₁ r₂).image Prod.snd).card

/-- IDENT ([mccarthy-prince-1995] A.3): corresponding pairs whose segments
    differ. IDENT-OO is OO-faithfulness ([benua-1997], [mccarthy-2005],
    [rolle-2018]). Each coordinate of a correspondence pair is a `Fin`
    in range, so `(form r₁)[p.1]` is the total indexed lookup (no `Option`).
    See `identViolFeature` for the feature-by-feature variant. -/
def identViol [DecidableEq α] (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p =>
    (c.form r₁)[p.1] ≠ (c.form r₂)[p.2]).card

/-- Featural IDENT ([mccarthy-prince-1995] A.3): corresponding pairs
    differing under `proj` ([benua-1997], [rose-walker-2011]). -/
def identViolFeature {F : Type*} [DecidableEq F] (proj : α → F)
    (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p =>
    proj (c.form r₁)[p.1] ≠ proj (c.form r₂)[p.2]).card

/-! ### Contiguity -/

/-- A `ℕ`-list is contiguous iff consecutive elements differ by 1. -/
abbrev IsContiguous (l : List ℕ) : Prop := List.IsChain (fun a b => b = a + 1) l

instance : (l : List ℕ) → Decidable (IsContiguous l) :=
  inferInstanceAs ((l : List ℕ) → Decidable (List.IsChain _ l))

/-- I-CONTIGUITY "No Skipping" ([mccarthy-prince-1995] A.4a): the domain
    of correspondence is contiguous in `form r₁`. The `Fin`-valued domain is
    projected to its `ℕ` values and sorted before the chain check. -/
def contigIViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  let dom := (((c.edge r₁ r₂).image Prod.fst).image Fin.val).sort (· ≤ ·)
  if IsContiguous dom then 0 else 1

/-- O-CONTIGUITY "No Intrusion" ([mccarthy-prince-1995] A.4b): the range
    of correspondence is contiguous in `form r₂`. -/
def contigOViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  let rng := (((c.edge r₁ r₂).image Prod.snd).image Fin.val).sort (· ≤ ·)
  if IsContiguous rng then 0 else 1

/-! ### Anchors -/

/-- L-ANCHOR ([mccarthy-prince-1995] A.5): leftmost positions correspond.
    When either form is empty there is no leftmost position, so the constraint
    is vacuously satisfied; otherwise the `Fin` endpoints are the two `0`s. -/
def anchorLViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  if h : (c.form r₁).length = 0 ∨ (c.form r₂).length = 0 then 0
  else
    have h₁ : 0 < (c.form r₁).length := Nat.pos_of_ne_zero (fun e => h (Or.inl e))
    have h₂ : 0 < (c.form r₂).length := Nat.pos_of_ne_zero (fun e => h (Or.inr e))
    if (⟨0, h₁⟩, ⟨0, h₂⟩) ∈ c.edge r₁ r₂ then 0 else 1

/-- R-ANCHOR ([mccarthy-prince-1995] A.5): rightmost positions correspond.
    The `Fin` endpoints are the two `Fin.last`s when both forms are nonempty. -/
def anchorRViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  if h : (c.form r₁).length = 0 ∨ (c.form r₂).length = 0 then 0
  else
    have h₁ : 0 < (c.form r₁).length := Nat.pos_of_ne_zero (fun e => h (Or.inl e))
    have h₂ : 0 < (c.form r₂).length := Nat.pos_of_ne_zero (fun e => h (Or.inr e))
    if (⟨(c.form r₁).length - 1, Nat.pred_lt_self h₁⟩,
        ⟨(c.form r₂).length - 1, Nat.pred_lt_self h₂⟩) ∈ c.edge r₁ r₂
       then 0 else 1

/-! ### Linearity, uniformity, integrity -/

/-- LINEARITY "No Metathesis" ([mccarthy-prince-1995] A.6): the count of
    inversion pairs `(i₁,j₁), (i₂,j₂) ∈ edge` with `i₁ < i₂` but `j₂ < j₁`
    (coordinates compared via `Fin.lt`). -/
def linearityViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂ ×ˢ c.edge r₁ r₂).filter fun pq => pq.1.1 < pq.2.1 ∧ pq.2.2 < pq.1.2).card

/-- UNIFORMITY "No Coalescence" ([mccarthy-prince-1995] A.7): the count of
    `form r₂` positions with more than one correspondent in `form r₁`. -/
def uniformityViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ : Finset (Fin (c.form r₂).length)).filter fun j =>
    ((c.edge r₁ r₂).filter fun p => p.2 = j).card > 1).card

/-- INTEGRITY "No Breaking" ([mccarthy-prince-1995] A.8): the count of
    `form r₁` positions with more than one correspondent in `form r₂`. -/
def integrityViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.univ : Finset (Fin (c.form r₁).length)).filter fun i =>
    ((c.edge r₁ r₂).filter fun p => p.1 = i).card > 1).card

/-! ### Faithfulness predicate bridges

Each cardinal constraint vanishes iff the correspondence has the corresponding
order-theoretic property (`maxViol = 0` ⟺ left-total, etc.). These are the
named characterizations the order-isomorphism theorem is assembled from. -/

theorem maxViol_eq_zero_iff (c : Corr Role α) (r₁ r₂ : Role) :
    c.maxViol r₁ r₂ = 0 ↔
      (Finset.univ : Finset (Fin (c.form r₁).length)) ⊆ (c.edge r₁ r₂).image Prod.fst := by
  simp only [maxViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

theorem depViol_eq_zero_iff (c : Corr Role α) (r₁ r₂ : Role) :
    c.depViol r₁ r₂ = 0 ↔
      (Finset.univ : Finset (Fin (c.form r₂).length)) ⊆ (c.edge r₁ r₂).image Prod.snd := by
  simp only [depViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

theorem integrityViol_eq_zero_iff (c : Corr Role α) (r₁ r₂ : Role) :
    c.integrityViol r₁ r₂ = 0 ↔
      ∀ i, ((c.edge r₁ r₂).filter fun p => p.1 = i).card ≤ 1 := by
  rw [integrityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i; have := h (Finset.mem_univ i); omega
  · intro h i _; have := h i; omega

theorem uniformityViol_eq_zero_iff (c : Corr Role α) (r₁ r₂ : Role) :
    c.uniformityViol r₁ r₂ = 0 ↔
      ∀ j, ((c.edge r₁ r₂).filter fun p => p.2 = j).card ≤ 1 := by
  rw [uniformityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h j; have := h (Finset.mem_univ j); omega
  · intro h j _; have := h j; omega

theorem linearityViol_eq_zero_iff (c : Corr Role α) (r₁ r₂ : Role) :
    c.linearityViol r₁ r₂ = 0 ↔
      ∀ p ∈ c.edge r₁ r₂, ∀ q ∈ c.edge r₁ r₂, p.1 < q.1 → ¬ q.2 < p.2 := by
  rw [linearityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h p hp q hq hpq hqp
    have hmem : (p, q) ∈ c.edge r₁ r₂ ×ˢ c.edge r₁ r₂ := Finset.mem_product.mpr ⟨hp, hq⟩
    exact h hmem ⟨hpq, hqp⟩
  · intro h pq hpq hinv
    rw [Finset.mem_product] at hpq
    exact h _ hpq.1 _ hpq.2 hinv.1 hinv.2

/-! ### Universal constructors -/

/-- The parallel-pair diagonal in `Fin`-coordinates: `(0,0), (1,1), …` up to
    `min m n`, each index cast up into the two position types via `Fin.castLE`. -/
def diagDiag (m n : ℕ) : Finset (Fin m × Fin n) :=
  (Finset.univ : Finset (Fin (min m n))).image
    (fun i => (i.castLE (min_le_left _ _), i.castLE (min_le_right _ _)))

/-- Membership in the diagonal: `(a, b) ∈ diagDiag m n` iff the two indices
    have equal underlying values. -/
theorem mem_diagDiag {m n : ℕ} (a : Fin m) (b : Fin n) :
    (a, b) ∈ diagDiag m n ↔ (a : ℕ) = (b : ℕ) := by
  simp only [diagDiag, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    rw [Prod.mk.injEq] at hi
    have h1 : (a : ℕ) = (i : ℕ) := congrArg Fin.val hi.1.symm
    have h2 : (b : ℕ) = (i : ℕ) := congrArg Fin.val hi.2.symm
    rw [h1, h2]
  · intro hab
    refine ⟨⟨a.1, by have := a.2; have := b.2; omega⟩, ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨Fin.ext rfl, Fin.ext hab⟩

theorem diagDiag_image_fst {m : ℕ} :
    (diagDiag m m).image Prod.fst = (Finset.univ : Finset (Fin m)) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, iff_true, Prod.exists]
  exact ⟨a, a, (mem_diagDiag a a).mpr rfl, rfl⟩

theorem diagDiag_image_snd {m : ℕ} :
    (diagDiag m m).image Prod.snd = (Finset.univ : Finset (Fin m)) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, iff_true, Prod.exists]
  exact ⟨b, b, (mem_diagDiag b b).mpr rfl, rfl⟩

/-- The diagonal has `min m n` pairs — one per index of the shorter form. -/
theorem diagDiag_card (m n : ℕ) : (diagDiag m n).card = min m n := by
  have hinj : Function.Injective
      (fun i : Fin (min m n) => (i.castLE (min_le_left m n), i.castLE (min_le_right m n))) :=
    fun _ _ hab => Fin.ext (congrArg (Fin.val ∘ Prod.fst) hab)
  rw [diagDiag, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

private theorem image_swap_diagDiag (m n : ℕ) :
    (diagDiag m n).image Prod.swap = diagDiag n m := by
  ext p
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_diagDiag]
    exact ((mem_diagDiag q.1 q.2).mp hq).symm
  · intro hp
    refine ⟨p.swap, ?_, p.swap_swap⟩
    rw [mem_diagDiag]
    exact ((mem_diagDiag p.1 p.2).mp hp).symm

/-- Universal constructor: where `hasEdge` holds, the parallel-pair
    correspondence `(0,0), (1,1), …` truncated to `min` of the two lengths;
    elsewhere none. For non-parallel structure (infixation, re-alignment)
    build `edge` directly (`Transderivational.diagramWithEdge`). -/
def diagram (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] : Corr Role α where
  form := form
  edge r₁ r₂ := if hasEdge r₁ r₂ then diagDiag (form r₁).length (form r₂).length else ∅

@[simp] theorem diagram_form (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] (r : Role) :
    (diagram form hasEdge).form r = form r := rfl

theorem diagram_edge (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] (r₁ r₂ : Role) :
    (diagram form hasEdge).edge r₁ r₂ =
      if hasEdge r₁ r₂ then diagDiag (form r₁).length (form r₂).length else ∅ := rfl

theorem diagram_edge_pos (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] {r₁ r₂ : Role} (h : hasEdge r₁ r₂) :
    (diagram form hasEdge).edge r₁ r₂ = diagDiag (form r₁).length (form r₂).length := by
  rw [diagram_edge, if_pos h]

theorem diagram_edge_neg (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] {r₁ r₂ : Role} (h : ¬ hasEdge r₁ r₂) :
    (diagram form hasEdge).edge r₁ r₂ = ∅ := by
  rw [diagram_edge, if_neg h]
  rfl

/-- A `diagram` over a symmetric predicate is a symmetric correspondence —
    symmetry *derived*, not stipulated. -/
theorem diagram_isSymmetric (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] (hsymm : Symmetric hasEdge) :
    IsSymmetric (diagram form hasEdge) := by
  intro r₁ r₂
  by_cases h : hasEdge r₁ r₂
  · rw [diagram_edge_pos _ _ (hsymm h), diagram_edge_pos _ _ h]
    exact (image_swap_diagDiag _ _).symm
  · rw [diagram_edge_neg _ _ (fun h' => h (hsymm h')), diagram_edge_neg _ _ h,
      Finset.image_empty]

/-- Parallel-pair correspondence between two strings, truncated to the
    shorter (`List.zip` semantics). -/
def parallel (s₁ s₂ : List α) : Corr Side α :=
  diagram (fun | .lhs => s₁ | .rhs => s₂) (· ≠ ·)

/-- The fully-faithful candidate: identity correspondence on one string
    ([mccarthy-prince-1995]). -/
def identity (s : List α) : Corr Side α := parallel s s

/-- 3-role input/base/reduplicant diagram with parallel-pair cross-role
    edges ([mccarthy-prince-1995]). -/
def reduplication (input base reduplicant : List α) : Corr RedupRole α :=
  diagram
    (fun | .input => input | .base => base | .reduplicant => reduplicant)
    (· ≠ ·)

theorem parallel_isSymmetric (s₁ s₂ : List α) : IsSymmetric (parallel s₁ s₂) :=
  diagram_isSymmetric _ _ fun _ _ h => h.symm

theorem reduplication_isSymmetric (input base reduplicant : List α) :
    IsSymmetric (reduplication input base reduplicant) :=
  diagram_isSymmetric _ _ fun _ _ h => h.symm

@[simp] theorem reduplication_form_input (input base reduplicant : List α) :
    (reduplication input base reduplicant).form .input = input := rfl

@[simp] theorem reduplication_form_base (input base reduplicant : List α) :
    (reduplication input base reduplicant).form .base = base := rfl

@[simp] theorem reduplication_form_reduplicant (input base reduplicant : List α) :
    (reduplication input base reduplicant).form .reduplicant = reduplicant := rfl

/-! ### Identity-correspondence zero lemmas -/

@[simp] theorem parallel_form_lhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).form .lhs = s₁ := rfl

@[simp] theorem parallel_form_rhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).form .rhs = s₂ := rfl

@[simp] theorem parallel_edge_diag (s₁ s₂ : List α) (r : Side) :
    (parallel s₁ s₂).edge r r = ∅ := by
  simp only [parallel]; exact diagram_edge_neg _ _ (by cases r <;> decide)

@[simp] theorem parallel_edge_lhs_rhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).edge .lhs .rhs = diagDiag s₁.length s₂.length := by
  simp only [parallel]; exact diagram_edge_pos _ _ (by decide)

@[simp] theorem parallel_edge_rhs_lhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).edge .rhs .lhs = diagDiag s₂.length s₁.length := by
  rw [parallel_isSymmetric s₁ s₂ .lhs .rhs, parallel_edge_lhs_rhs]
  exact image_swap_diagDiag _ _

/-- `MAX` vanishes on a **diagonal** edge between equal forms: if `c.edge r₁ r₂`
    is the parallel-pair diagonal and `c.form r₁ = c.form r₂`, every `r₁`
    position has a correspondent. The role-agnostic core of `identity_max_zero`
    — it also fires for total reduplication (`r₁, r₂` the base/reduplicant roles
    with equal forms). -/
theorem maxViol_eq_zero_of_diag (c : Corr Role α) (r₁ r₂ : Role)
    (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagDiag (c.form r₁).length (c.form r₂).length) :
    c.maxViol r₁ r₂ = 0 := by
  have hlen : (c.form r₁).length = (c.form r₂).length := congrArg List.length hform
  rw [maxViol_eq_zero_iff, hedge]
  intro i _
  rw [Finset.mem_image]
  exact ⟨(i, ⟨(i : ℕ), hlen ▸ i.2⟩), (mem_diagDiag _ _).mpr rfl, rfl⟩

/-- `DEP` vanishes on a diagonal edge between equal forms — the dual of
    `maxViol_eq_zero_of_diag`: every `r₂` position has a correspondent. -/
theorem depViol_eq_zero_of_diag (c : Corr Role α) (r₁ r₂ : Role)
    (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagDiag (c.form r₁).length (c.form r₂).length) :
    c.depViol r₁ r₂ = 0 := by
  have hlen : (c.form r₁).length = (c.form r₂).length := congrArg List.length hform
  rw [depViol_eq_zero_iff, hedge]
  intro j _
  rw [Finset.mem_image]
  exact ⟨(⟨(j : ℕ), hlen.symm ▸ j.2⟩, j), (mem_diagDiag _ _).mpr rfl, rfl⟩

theorem identity_max_zero (s : List α) :
    (identity s).maxViol .lhs .rhs = 0 :=
  maxViol_eq_zero_of_diag (identity s) .lhs .rhs rfl (parallel_edge_lhs_rhs s s)

theorem identity_dep_zero (s : List α) :
    (identity s).depViol .lhs .rhs = 0 :=
  depViol_eq_zero_of_diag (identity s) .lhs .rhs rfl (parallel_edge_lhs_rhs s s)

/-- `IDENT` vanishes on a diagonal edge between **equal forms**: corresponding
    positions hold the same segment. Unlike `MAX`/`DEP`, this needs
    `c.form r₁ = c.form r₂`, not just equal length — an order-isomorphic edge
    between distinct strings can still violate `IDENT`. -/
theorem identViol_eq_zero_of_diag [DecidableEq α] (c : Corr Role α) (r₁ r₂ : Role)
    (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagDiag (c.form r₁).length (c.form r₂).length) :
    c.identViol r₁ r₂ = 0 := by
  simp only [identViol]
  rw [hedge, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  have hpq : (p.1 : ℕ) = (p.2 : ℕ) := (mem_diagDiag p.1 p.2).mp (by simpa using hp)
  simp only [not_not]
  have h? : (c.form r₁)[(p.1 : ℕ)]? = (c.form r₂)[(p.2 : ℕ)]? := by
    rw [hpq]; exact congrArg (·[(p.2 : ℕ)]?) hform
  rwa [List.getElem?_eq_getElem p.1.2, List.getElem?_eq_getElem p.2.2,
       Option.some_inj] at h?

/-- Featural `IDENT` vanishes on a diagonal edge between equal forms — the
    `proj`-relativized form of `identViol_eq_zero_of_diag`. -/
theorem identViolFeature_eq_zero_of_diag {F : Type*} [DecidableEq F] (proj : α → F)
    (c : Corr Role α) (r₁ r₂ : Role)
    (hform : c.form r₁ = c.form r₂)
    (hedge : c.edge r₁ r₂ = diagDiag (c.form r₁).length (c.form r₂).length) :
    c.identViolFeature proj r₁ r₂ = 0 := by
  simp only [identViolFeature]
  rw [hedge, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  have hpq : (p.1 : ℕ) = (p.2 : ℕ) := (mem_diagDiag p.1 p.2).mp (by simpa using hp)
  simp only [not_not]
  have h? : (c.form r₁)[(p.1 : ℕ)]? = (c.form r₂)[(p.2 : ℕ)]? := by
    rw [hpq]; exact congrArg (·[(p.2 : ℕ)]?) hform
  have he : (c.form r₁)[p.1] = (c.form r₂)[p.2] := by
    rwa [List.getElem?_eq_getElem p.1.2, List.getElem?_eq_getElem p.2.2,
         Option.some_inj] at h?
  rw [he]

theorem identity_ident_zero [DecidableEq α] (s : List α) :
    (identity s).identViol .lhs .rhs = 0 :=
  identViol_eq_zero_of_diag (identity s) .lhs .rhs rfl (parallel_edge_lhs_rhs s s)

theorem identity_identFeature_zero {F : Type*} [DecidableEq F] (proj : α → F)
    (s : List α) :
    (identity s).identViolFeature proj .lhs .rhs = 0 :=
  identViolFeature_eq_zero_of_diag proj (identity s) .lhs .rhs rfl
    (parallel_edge_lhs_rhs s s)

/-! ### Faithfulness as order-isomorphism -/

/-- The five order-relevant zeros bundled: a correspondence is **faithful**
    (on the `(r₁, r₂)` edge) when it has no MAX, DEP, INTEGRITY, UNIFORMITY,
    or LINEARITY violation ([mccarthy-prince-1995] (A.1), (A.2), (A.6),
    (A.7), (A.8)). This is exactly the hypothesis set under which the edge is
    the graph of an order isomorphism. -/
structure IsFaithful (c : Corr Role α) (r₁ r₂ : Role) : Prop where
  max : c.maxViol r₁ r₂ = 0
  dep : c.depViol r₁ r₂ = 0
  integrity : c.integrityViol r₁ r₂ = 0
  uniformity : c.uniformityViol r₁ r₂ = 0
  linearity : c.linearityViol r₁ r₂ = 0

/-- MAX + INTEGRITY: the edge is the graph of a function `Fin n → Fin m` — each
    `form r₁` position has exactly one correspondent (MAX: at least one; INTEGRITY:
    at most one). `Fin`-typed storage means `p ∈ edge` already gives `p : Fin n × Fin m`,
    with no in-range packaging. -/
private theorem exists_corrFun (c : Corr Role α) (r₁ r₂ : Role)
    (hmax : c.maxViol r₁ r₂ = 0) (hint : c.integrityViol r₁ r₂ = 0) :
    ∃ f : Fin (c.form r₁).length → Fin (c.form r₂).length,
      ∀ i j, (i, j) ∈ c.edge r₁ r₂ ↔ f i = j := by
  have hexU : ∀ i, ∃! j, (i, j) ∈ c.edge r₁ r₂ := fun i => by
    obtain ⟨⟨a, b⟩, hp, rfl⟩ :=
      Finset.mem_image.mp ((maxViol_eq_zero_iff c r₁ r₂).mp hmax (Finset.mem_univ i))
    have hone := Finset.card_le_one.mp ((integrityViol_eq_zero_iff c r₁ r₂).mp hint a)
    exact ⟨b, hp, fun j hj => congrArg Prod.snd
      (hone _ (Finset.mem_filter.mpr ⟨hj, rfl⟩) _ (Finset.mem_filter.mpr ⟨hp, rfl⟩))⟩
  choose f hf huniq using hexU
  exact ⟨f, fun i j => ⟨fun h => (huniq i j h).symm, fun h => h ▸ hf i⟩⟩

/-- **Faithful ⟺ order-isomorphism.** A correspondence is faithful (no MAX,
    DEP, INTEGRITY, UNIFORMITY, or LINEARITY violation) iff its edge is the
    graph of an order isomorphism between the two position orders. The forward
    direction is the converse of the `identity_*_zero` lemmas, and the formal
    content of M&P's fully-faithful candidate being the identity. -/
theorem isFaithful_iff_exists_orderIso (c : Corr Role α) (r₁ r₂ : Role) :
    c.IsFaithful r₁ r₂ ↔
      ∃ e : Fin (c.form r₁).length ≃o Fin (c.form r₂).length,
        ∀ i j, (i, j) ∈ c.edge r₁ r₂ ↔ e i = j := by
  set E := c.edge r₁ r₂
  constructor
  · rintro ⟨hmax, hdep, hint, huni, hlin⟩
    obtain ⟨f, mem_iff⟩ := exists_corrFun c r₁ r₂ hmax hint
    have memf : ∀ i, (i, f i) ∈ E := fun i => (mem_iff i (f i)).mpr rfl
    -- UNIFORMITY rules out collisions, LINEARITY rules out inversions: `f` is strictly
    -- monotone (whence injective for free).
    have hmono : StrictMono f := by
      intro a b hab
      rcases lt_trichotomy (f a) (f b) with h | h | h
      · exact h
      · have hu := Finset.card_le_one.mp ((uniformityViol_eq_zero_iff c r₁ r₂).mp huni (f b))
        exact absurd (congrArg Prod.fst <| hu _ (Finset.mem_filter.mpr ⟨memf a, h⟩)
          _ (Finset.mem_filter.mpr ⟨memf b, rfl⟩)) (ne_of_lt hab)
      · exact absurd h ((linearityViol_eq_zero_iff c r₁ r₂).mp hlin _ (memf a) _ (memf b) hab)
    -- DEP makes `f` surjective.
    have hsurj : Function.Surjective f := by
      intro j
      obtain ⟨p, hp, hp2⟩ := Finset.mem_image.mp
        ((depViol_eq_zero_iff c r₁ r₂).mp hdep (Finset.mem_univ j))
      exact ⟨p.1, (mem_iff p.1 j).mp (by simpa [← hp2] using hp)⟩
    exact ⟨StrictMono.orderIsoOfSurjective f hmono hsurj,
      fun i j => by rw [mem_iff, StrictMono.coe_orderIsoOfSurjective]⟩
  · -- The edge is the graph `{(i, e i)}`; each zero is a face of `e` being an order iso.
    rintro ⟨e, he⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (maxViol_eq_zero_iff c r₁ r₂).mpr fun i _ =>
        Finset.mem_image.mpr ⟨(i, e i), (he i (e i)).mpr rfl, rfl⟩
    · exact (depViol_eq_zero_iff c r₁ r₂).mpr fun j _ =>
        Finset.mem_image.mpr ⟨(e.symm j, j), (he _ j).mpr (e.apply_symm_apply j), rfl⟩
    · refine (integrityViol_eq_zero_iff c r₁ r₂).mpr fun i =>
        Finset.card_le_one.mpr fun p hp q hq => ?_
      rw [Finset.mem_filter] at hp hq
      exact Prod.ext (hp.2.trans hq.2.symm) <| calc
        p.2 = e p.1 := ((he p.1 p.2).mp hp.1).symm
        _   = e q.1 := by rw [hp.2.trans hq.2.symm]
        _   = q.2   := (he q.1 q.2).mp hq.1
    · refine (uniformityViol_eq_zero_iff c r₁ r₂).mpr fun j =>
        Finset.card_le_one.mpr fun p hp q hq => ?_
      rw [Finset.mem_filter] at hp hq
      refine Prod.ext (e.injective ?_) (hp.2.trans hq.2.symm)
      calc e p.1 = p.2 := (he p.1 p.2).mp hp.1
        _ = q.2   := hp.2.trans hq.2.symm
        _ = e q.1 := ((he q.1 q.2).mp hq.1).symm
    · refine (linearityViol_eq_zero_iff c r₁ r₂).mpr fun p hp q hq hpq => ?_
      rw [← (he p.1 p.2).mp hp, ← (he q.1 q.2).mp hq]
      exact not_lt.mpr (le_of_lt (e.lt_iff_lt.mpr hpq))

/-- **Faithful ⟹ order-isomorphism** (the forward direction of
    `isFaithful_iff_exists_orderIso`). -/
theorem exists_orderIso_of_faithful (c : Corr Role α) (r₁ r₂ : Role)
    (hmax : c.maxViol r₁ r₂ = 0) (hdep : c.depViol r₁ r₂ = 0)
    (hint : c.integrityViol r₁ r₂ = 0) (huni : c.uniformityViol r₁ r₂ = 0)
    (hlin : c.linearityViol r₁ r₂ = 0) :
    ∃ e : Fin (c.form r₁).length ≃o Fin (c.form r₂).length,
      ∀ i j, (i, j) ∈ c.edge r₁ r₂ ↔ e i = j :=
  (isFaithful_iff_exists_orderIso c r₁ r₂).mp ⟨hmax, hdep, hint, huni, hlin⟩

/-- A faithful correspondence forces equal lengths (no deletion, no
    epenthesis). -/
theorem length_eq_of_faithful (c : Corr Role α) (r₁ r₂ : Role)
    (hmax : c.maxViol r₁ r₂ = 0) (hdep : c.depViol r₁ r₂ = 0)
    (hint : c.integrityViol r₁ r₂ = 0) (huni : c.uniformityViol r₁ r₂ = 0)
    (hlin : c.linearityViol r₁ r₂ = 0) :
    (c.form r₁).length = (c.form r₂).length := by
  obtain ⟨e, _⟩ := exists_orderIso_of_faithful c r₁ r₂ hmax hdep hint huni hlin
  simpa using Fintype.card_congr e.toEquiv

/-! ### NamedConstraint bridges -/

/-- Bridge a `Corr`-violation function into a `NamedConstraint` — the single
    plumbing point into `Constraint`'s evaluation machinery. -/
def toConstraint (family : Family) (label : String)
    (eval : Corr Role α → ℕ) : NamedConstraint (Corr Role α) where
  name := label
  family := family
  eval := eval

def toIdentConstraint [DecidableEq α] (r₁ r₂ : Role)
    (label : String) : NamedConstraint (Corr Role α) :=
  toConstraint .faithfulness ("IDENT-" ++ label) (fun c => c.identViol r₁ r₂)

def toIdentFeatureConstraint {F : Type*} [DecidableEq F]
    (proj : α → F) (r₁ r₂ : Role) (label : String) :
    NamedConstraint (Corr Role α) :=
  toConstraint .faithfulness ("IDENT-" ++ label)
    (fun c => c.identViolFeature proj r₁ r₂)

def toMaxConstraint (r₁ r₂ : Role) (label : String) :
    NamedConstraint (Corr Role α) :=
  toConstraint .faithfulness ("MAX-" ++ label) (fun c => c.maxViol r₁ r₂)

def toDepConstraint (r₁ r₂ : Role) (label : String) :
    NamedConstraint (Corr Role α) :=
  toConstraint .faithfulness ("DEP-" ++ label) (fun c => c.depViol r₁ r₂)

/-! ### Faithfulness of the bridges: vanishing on the faithful candidate

The faithfulness `to*Constraint` bridges assign zero violations to the fully
faithful candidate `identity s` — the defining behaviour of a Correspondence-
Theory faithfulness constraint ([mccarthy-prince-1995]). This is the content the
`.faithfulness` tag abbreviates; the tag itself is documentary, so the math
lives in these lemmas. Markedness is non-vacuously different
(`exists_markedness_not_vanishesOnIdentity`). Anti-faithfulness ([alderete-1999])
is out of scope — it demands disparity and is *maximal* on `identity`. -/

@[simp] theorem toMaxConstraint_eval_identity (label : String) (s : List α) :
    (toMaxConstraint Side.lhs Side.rhs label).eval (identity s) = 0 :=
  identity_max_zero s

@[simp] theorem toDepConstraint_eval_identity (label : String) (s : List α) :
    (toDepConstraint Side.lhs Side.rhs label).eval (identity s) = 0 :=
  identity_dep_zero s

@[simp] theorem toIdentConstraint_eval_identity [DecidableEq α]
    (label : String) (s : List α) :
    (toIdentConstraint Side.lhs Side.rhs label).eval (identity s) = 0 :=
  identity_ident_zero s

@[simp] theorem toIdentFeatureConstraint_eval_identity {F : Type*} [DecidableEq F]
    (proj : α → F) (label : String) (s : List α) :
    (toIdentFeatureConstraint proj Side.lhs Side.rhs label).eval (identity s) = 0 :=
  identity_identFeature_zero proj s

/-- A correspondence constraint **vanishes on the faithful candidate** when it
    scores no violations on any fully faithful `identity s` — the behavioural
    invariant the `.faithfulness` tag abbreviates ([mccarthy-prince-1995]). -/
def VanishesOnIdentity (c : NamedConstraint (Corr Side α)) : Prop :=
  ∀ s : List α, c.eval (identity s) = 0

theorem toMaxConstraint_vanishesOnIdentity (label : String) :
    VanishesOnIdentity (α := α) (toMaxConstraint Side.lhs Side.rhs label) :=
  toMaxConstraint_eval_identity label

theorem toDepConstraint_vanishesOnIdentity (label : String) :
    VanishesOnIdentity (α := α) (toDepConstraint Side.lhs Side.rhs label) :=
  toDepConstraint_eval_identity label

theorem toIdentConstraint_vanishesOnIdentity [DecidableEq α] (label : String) :
    VanishesOnIdentity (α := α) (toIdentConstraint Side.lhs Side.rhs label) :=
  toIdentConstraint_eval_identity label

/-- **Markedness need not vanish on the faithful candidate.** A `*Struc`-style
    constraint (one violation per output segment) fires on `identity s`, so the
    split is non-vacuous: `VanishesOnIdentity` characterizes the faithfulness
    constructors, not every constraint. -/
theorem exists_markedness_not_vanishesOnIdentity [Inhabited α] :
    ∃ c : NamedConstraint (Corr Side α),
      c.family = .markedness ∧ ¬ VanishesOnIdentity c :=
  ⟨mkMarkGrad "*Struc" (fun c => (c.form Side.rhs).length), rfl, fun h => by
    have h1 := h [default]
    simp [mkMarkGrad, identity] at h1⟩

end Corr

/-! ### Reduplication constraints

The canonical [mccarthy-prince-1995] reduplicative-faithfulness
constraints as `NamedConstraint (Corr RedupRole α)`; study files import these
names rather than re-rolling `Corr.toMaxConstraint .input .base "IO"`. -/

namespace Reduplication

def maxIO {α : Type*} : NamedConstraint (Corr RedupRole α) :=
  Corr.toMaxConstraint .input .base "IO"

def maxBR {α : Type*} : NamedConstraint (Corr RedupRole α) :=
  Corr.toMaxConstraint .base .reduplicant "BR"

def depIO {α : Type*} : NamedConstraint (Corr RedupRole α) :=
  Corr.toDepConstraint .input .base "IO"

def identBR {α : Type*} [DecidableEq α] : NamedConstraint (Corr RedupRole α) :=
  Corr.toIdentConstraint .base .reduplicant "BR"

def identIO {α : Type*} [DecidableEq α] : NamedConstraint (Corr RedupRole α) :=
  Corr.toIdentConstraint .input .base "IO"

end Reduplication

namespace Corr

/-! ### Quiver structure -/

/-- The labeled-quiver structure on `Role`: morphisms `r₁ ⟶ r₂` are the
    correspondence pairs `(i, j) ∈ c.edge r₁ r₂`. Carried by a value-indexed
    newtype since the instance depends on `c`; path-based (stratal, OT-CC)
    evaluation via `Quiver.Path` is not yet formalised. -/
def RoleQuiv {Role α : Type*} (_ : Corr Role α) : Type _ := Role

instance {Role α : Type*} (c : Corr Role α) : Quiver (RoleQuiv c) where
  Hom r₁ r₂ := { p : Fin (c.form r₁).length × Fin (c.form r₂).length // p ∈ c.edge r₁ r₂ }

end Corr

end OptimalityTheory.Correspondence
