import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Data.Fintype.Card
import Linglib.Core.Constraint.OT.Basic
import Linglib.Phonology.OptimalityTheory.Constraints

/-!
# Correspondence Theory
@cite{mccarthy-prince-1995} @cite{benua-1997}

Correspondence diagrams and their faithfulness constraints. A `Corr Role α`
gives each role a string (`form`) and each ordered role pair a correspondence
relation `edge` between positions. Each faithfulness constraint is a map
`Corr Role α → Role → Role → ℕ`.

Following @cite{mccarthy-prince-1995} (Def. 10), `edge r₁ r₂` is the directed
relation ℛ ⊆ S₁ × S₂ that every constraint reads (MAX off its Domain, DEP off
its Range, …). Symmetry — "correspondents of one another" — is a *derived*
property (`IsSymmetric`, proved of the constructors), not built into the type,
since M&P's ℛ is a directed subset. The position-relation encoding follows the
model-theoretic treatment of @cite{payne-vu-heinz-2017} and
@cite{potts-pullum-2002} (reduplicative B-R: @cite{dolatian-heinz-2020}).

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

* `Corr.exists_orderIso_of_faithful` — a correspondence with no MAX, DEP,
  INTEGRITY, UNIFORMITY, or LINEARITY violation is the graph of an order
  isomorphism (the converse of the `identity_*_zero` lemmas).
-/

namespace Phonology.Correspondence

open Core.Constraint.OT
open Finset

/-! ### Binary and ternary roles -/

/-- Roles for a binary correspondence (`Corr.parallel`, `Corr.identity`). -/
inductive Side where
  | lhs
  | rhs
  deriving DecidableEq, Repr

/-- Roles for a reduplicative correspondence: input, base, reduplicant
    (@cite{mccarthy-prince-1995}); used by `Corr.reduplication`. -/
inductive RedupRole where
  | input
  | base
  | reduplicant
  deriving DecidableEq, Repr

/-! ### The correspondence diagram -/

/-- A correspondence diagram: role-indexed `form`s and a directed
    correspondence relation `edge` between positions (@cite{mccarthy-prince-1995}
    Def. 10). `edge_lt_length` bounds each pair to in-range positions. -/
structure Corr (Role : Type*) (α : Type*) where
  form : Role → List α
  edge : Role → Role → Finset (ℕ × ℕ)
  edge_lt_length : ∀ r₁ r₂, ∀ p ∈ edge r₁ r₂,
    p.1 < (form r₁).length ∧ p.2 < (form r₂).length

namespace Corr

variable {Role : Type*} {α : Type*}

/-- Correspondence is symmetric — "correspondents of one another"
    (@cite{mccarthy-prince-1995} Def. 10): each relation is the converse of
    the reverse one. A derived property (`diagram_isSymmetric`), not a field. -/
def IsSymmetric (c : Corr Role α) : Prop :=
  ∀ r₁ r₂, c.edge r₂ r₁ = (c.edge r₁ r₂).image Prod.swap

/-! ### Constraint families -/

/-- MAX (@cite{mccarthy-prince-1995} A.1): the count of `form r₁` positions with
    no correspondent in `form r₂`. MAX-OO is basemap faithfulness (@cite{benua-1997}). -/
def maxViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.range (c.form r₁).length) \ (c.edge r₁ r₂).image Prod.fst).card

/-- DEP (@cite{mccarthy-prince-1995} A.2): the count of `form r₂` positions with
    no correspondent in `form r₁`. DEP-IO prohibits epenthesis. -/
def depViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.range (c.form r₂).length) \ (c.edge r₁ r₂).image Prod.snd).card

/-- IDENT (@cite{mccarthy-prince-1995} A.3): corresponding pairs whose segments
    differ. IDENT-OO is OO-faithfulness (@cite{benua-1997}, @cite{mccarthy-2005},
    @cite{rolle-2018}). See `identViolFeature` for the feature-by-feature
    variant. -/
def identViol [DecidableEq α] (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p =>
    (c.form r₁)[p.1]? ≠ (c.form r₂)[p.2]?).card

/-- Featural IDENT (@cite{mccarthy-prince-1995} A.3): corresponding pairs
    differing under `proj` (@cite{benua-1997}, @cite{rose-walker-2011}). -/
def identViolFeature {F : Type*} [DecidableEq F] (proj : α → F)
    (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p =>
    (c.form r₁)[p.1]?.map proj ≠ (c.form r₂)[p.2]?.map proj).card

/-! ### Contiguity -/

/-- A `ℕ`-list is contiguous iff consecutive elements differ by 1. -/
abbrev IsContiguous (l : List ℕ) : Prop := List.IsChain (fun a b => b = a + 1) l

instance : (l : List ℕ) → Decidable (IsContiguous l) :=
  inferInstanceAs ((l : List ℕ) → Decidable (List.IsChain _ l))

/-- I-CONTIGUITY "No Skipping" (@cite{mccarthy-prince-1995} A.4a): the domain
    of correspondence is contiguous in `form r₁`. -/
def contigIViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  let dom := ((c.edge r₁ r₂).image Prod.fst).sort (· ≤ ·)
  if IsContiguous dom then 0 else 1

/-- O-CONTIGUITY "No Intrusion" (@cite{mccarthy-prince-1995} A.4b): the range
    of correspondence is contiguous in `form r₂`. -/
def contigOViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  let rng := ((c.edge r₁ r₂).image Prod.snd).sort (· ≤ ·)
  if IsContiguous rng then 0 else 1

/-! ### Anchors -/

/-- L-ANCHOR (@cite{mccarthy-prince-1995} A.5): leftmost positions correspond. -/
def anchorLViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  if (c.form r₁).length = 0 ∨ (c.form r₂).length = 0 then 0
  else if (0, 0) ∈ c.edge r₁ r₂ then 0 else 1

/-- R-ANCHOR (@cite{mccarthy-prince-1995} A.5): rightmost positions correspond. -/
def anchorRViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  if (c.form r₁).length = 0 ∨ (c.form r₂).length = 0 then 0
  else if ((c.form r₁).length - 1, (c.form r₂).length - 1) ∈ c.edge r₁ r₂
       then 0 else 1

/-! ### Linearity, uniformity, integrity -/

/-- LINEARITY "No Metathesis" (@cite{mccarthy-prince-1995} A.6): the count of
    inversion pairs `(i₁,j₁), (i₂,j₂) ∈ edge` with `i₁ < i₂` but `j₂ < j₁`. -/
def linearityViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂ ×ˢ c.edge r₁ r₂).filter fun pq => pq.1.1 < pq.2.1 ∧ pq.2.2 < pq.1.2).card

/-- UNIFORMITY "No Coalescence" (@cite{mccarthy-prince-1995} A.7): the count of
    `form r₂` positions with more than one correspondent in `form r₁`. -/
def uniformityViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.range (c.form r₂).length).filter fun j =>
    ((c.edge r₁ r₂).filter fun p => p.2 = j).card > 1).card

/-- INTEGRITY "No Breaking" (@cite{mccarthy-prince-1995} A.8): the count of
    `form r₁` positions with more than one correspondent in `form r₂`. -/
def integrityViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.range (c.form r₁).length).filter fun i =>
    ((c.edge r₁ r₂).filter fun p => p.1 = i).card > 1).card

/-! ### Faithfulness predicate bridges

Each cardinal constraint vanishes iff the correspondence has the corresponding
order-theoretic property (`maxViol = 0` ⟺ left-total, etc.). These are the
named characterizations the order-isomorphism theorem is assembled from. -/

theorem maxViol_eq_zero_iff (c : Corr Role α) (r₁ r₂ : Role) :
    c.maxViol r₁ r₂ = 0 ↔
      Finset.range (c.form r₁).length ⊆ (c.edge r₁ r₂).image Prod.fst := by
  simp only [maxViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

theorem depViol_eq_zero_iff (c : Corr Role α) (r₁ r₂ : Role) :
    c.depViol r₁ r₂ = 0 ↔
      Finset.range (c.form r₂).length ⊆ (c.edge r₁ r₂).image Prod.snd := by
  simp only [depViol, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

theorem integrityViol_eq_zero_iff (c : Corr Role α) (r₁ r₂ : Role) :
    c.integrityViol r₁ r₂ = 0 ↔
      ∀ i, i < (c.form r₁).length → ((c.edge r₁ r₂).filter fun p => p.1 = i).card ≤ 1 := by
  rw [integrityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i hi; have := h (Finset.mem_range.mpr hi); omega
  · intro h i hi; have := h i (Finset.mem_range.mp hi); omega

theorem uniformityViol_eq_zero_iff (c : Corr Role α) (r₁ r₂ : Role) :
    c.uniformityViol r₁ r₂ = 0 ↔
      ∀ j, j < (c.form r₂).length → ((c.edge r₁ r₂).filter fun p => p.2 = j).card ≤ 1 := by
  rw [uniformityViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h j hj; have := h (Finset.mem_range.mpr hj); omega
  · intro h j hj; have := h j (Finset.mem_range.mp hj); omega

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

private theorem range_image_wf (n m₁ m₂ : ℕ) (h₁ : n ≤ m₁) (h₂ : n ≤ m₂) :
    ∀ p ∈ (Finset.range n).image (fun i => (i, i)),
      p.1 < m₁ ∧ p.2 < m₂ := by
  intro p hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨i, hi, rfl⟩ := hmem
  exact ⟨lt_of_lt_of_le hi h₁, lt_of_lt_of_le hi h₂⟩

private theorem image_swap_diag (n : ℕ) :
    ((Finset.range n).image (fun i => (i, i))).image Prod.swap =
      (Finset.range n).image (fun i => (i, i)) := by
  rw [Finset.image_image]; rfl

/-- Universal constructor: where `hasEdge` holds, the parallel-pair
    correspondence `(0,0), (1,1), …` truncated to `min` of the two lengths;
    elsewhere none. For non-parallel structure (infixation, re-alignment)
    build `edge` directly (`Transderivational.diagramWithEdge`). -/
def diagram (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] : Corr Role α where
  form := form
  edge r₁ r₂ := if hasEdge r₁ r₂ then
    (Finset.range (min (form r₁).length (form r₂).length)).image fun i => (i, i)
  else ∅
  edge_lt_length := by
    intro r₁ r₂ p hmem
    by_cases h : hasEdge r₁ r₂
    · rw [if_pos h] at hmem
      exact range_image_wf _ _ _ (min_le_left _ _) (min_le_right _ _) p hmem
    · rw [if_neg h] at hmem
      simp at hmem

@[simp] theorem diagram_form (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] (r : Role) :
    (diagram form hasEdge).form r = form r := rfl

theorem diagram_edge (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] (r₁ r₂ : Role) :
    (diagram form hasEdge).edge r₁ r₂ =
      if hasEdge r₁ r₂ then
        (Finset.range (min (form r₁).length (form r₂).length)).image (fun i => (i, i))
      else ∅ := rfl

theorem diagram_edge_pos (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] {r₁ r₂ : Role} (h : hasEdge r₁ r₂) :
    (diagram form hasEdge).edge r₁ r₂ =
      (Finset.range (min (form r₁).length (form r₂).length)).image (fun i => (i, i)) := by
  rw [diagram_edge, if_pos h]

theorem diagram_edge_neg (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] {r₁ r₂ : Role} (h : ¬ hasEdge r₁ r₂) :
    (diagram form hasEdge).edge r₁ r₂ = ∅ := by
  rw [diagram_edge, if_neg h]

/-- A `diagram` over a symmetric predicate is a symmetric correspondence —
    symmetry *derived*, not stipulated. -/
theorem diagram_isSymmetric (form : Role → List α) (hasEdge : Role → Role → Prop)
    [DecidableRel hasEdge] (hsymm : Symmetric hasEdge) :
    IsSymmetric (diagram form hasEdge) := by
  intro r₁ r₂
  by_cases h : hasEdge r₁ r₂
  · rw [diagram_edge_pos _ _ (hsymm h), diagram_edge_pos _ _ h, image_swap_diag,
      Nat.min_comm (form r₂).length (form r₁).length]
  · rw [diagram_edge_neg _ _ (fun h' => h (hsymm h')), diagram_edge_neg _ _ h,
      Finset.image_empty]

/-- Parallel-pair correspondence between two strings, truncated to the
    shorter (`List.zip` semantics). -/
def parallel (s₁ s₂ : List α) : Corr Side α :=
  diagram (fun | .lhs => s₁ | .rhs => s₂) (· ≠ ·)

/-- The fully-faithful candidate: identity correspondence on one string
    (@cite{mccarthy-prince-1995}). -/
def identity (s : List α) : Corr Side α := parallel s s

/-- 3-role input/base/reduplicant diagram with parallel-pair cross-role
    edges (@cite{mccarthy-prince-1995}). -/
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
    (parallel s₁ s₂).edge .lhs .rhs =
      (Finset.range (min s₁.length s₂.length)).image (fun i => (i, i)) := by
  simp only [parallel]; exact diagram_edge_pos _ _ (by decide)

@[simp] theorem parallel_edge_rhs_lhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).edge .rhs .lhs =
      (Finset.range (min s₁.length s₂.length)).image (fun i => (i, i)) := by
  rw [parallel_isSymmetric s₁ s₂ .lhs .rhs, parallel_edge_lhs_rhs, image_swap_diag]

theorem identity_max_zero (s : List α) :
    (identity s).maxViol .lhs .rhs = 0 := by
  simp only [identity, maxViol, parallel_form_lhs, parallel_edge_lhs_rhs,
             Finset.image_image, Function.comp_def, Finset.image_id']
  simp

theorem identity_dep_zero (s : List α) :
    (identity s).depViol .lhs .rhs = 0 := by
  simp only [identity, depViol, parallel_form_rhs, parallel_edge_lhs_rhs,
             Finset.image_image, Function.comp_def, Finset.image_id']
  simp

theorem identity_ident_zero [DecidableEq α] (s : List α) :
    (identity s).identViol .lhs .rhs = 0 := by
  simp only [identity, identViol, parallel_form_lhs, parallel_form_rhs,
             parallel_edge_lhs_rhs]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨i, _, rfl⟩ := hp
  simp

theorem identity_identFeature_zero {F : Type*} [DecidableEq F] (proj : α → F)
    (s : List α) :
    (identity s).identViolFeature proj .lhs .rhs = 0 := by
  simp only [identity, identViolFeature, parallel_form_lhs, parallel_form_rhs,
             parallel_edge_lhs_rhs]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨i, _, rfl⟩ := hp
  simp

/-! ### Faithfulness as order-isomorphism -/

/-- **Faithful ⟹ order-isomorphism.** A correspondence with no MAX, DEP,
    INTEGRITY, UNIFORMITY, or LINEARITY violation is the graph of an order
    isomorphism between the two position orders — the converse of the
    `identity_*_zero` lemmas, and the formal content of M&P's fully-faithful
    candidate being the identity (the simultaneous zero of
    @cite{mccarthy-prince-1995} (A.1), (A.2), (A.6), (A.7), (A.8)). -/
theorem exists_orderIso_of_faithful (c : Corr Role α) (r₁ r₂ : Role)
    (hmax : c.maxViol r₁ r₂ = 0) (hdep : c.depViol r₁ r₂ = 0)
    (hint : c.integrityViol r₁ r₂ = 0) (huni : c.uniformityViol r₁ r₂ = 0)
    (hlin : c.linearityViol r₁ r₂ = 0) :
    ∃ e : Fin (c.form r₁).length ≃o Fin (c.form r₂).length,
      ∀ (i : Fin (c.form r₁).length) (j : Fin (c.form r₂).length),
        ((i : ℕ), (j : ℕ)) ∈ c.edge r₁ r₂ ↔ e i = j := by
  set n := (c.form r₁).length with hn
  set m := (c.form r₂).length with hm
  set E := c.edge r₁ r₂ with hE
  have hwf : ∀ p ∈ E, p.1 < n ∧ p.2 < m := c.edge_lt_length r₁ r₂
  have hsubL : Finset.range n ⊆ E.image Prod.fst := (maxViol_eq_zero_iff c r₁ r₂).mp hmax
  have hsubR : Finset.range m ⊆ E.image Prod.snd := (depViol_eq_zero_iff c r₁ r₂).mp hdep
  have hfunL : ∀ i, i < n → (E.filter (fun p => p.1 = i)).card ≤ 1 :=
    (integrityViol_eq_zero_iff c r₁ r₂).mp hint
  have hfunR : ∀ j, j < m → (E.filter (fun p => p.2 = j)).card ≤ 1 :=
    (uniformityViol_eq_zero_iff c r₁ r₂).mp huni
  have hnoinv : ∀ p ∈ E, ∀ q ∈ E, p.1 < q.1 → ¬ q.2 < p.2 :=
    (linearityViol_eq_zero_iff c r₁ r₂).mp hlin
  -- MAX + INTEGRITY: every left position has a *unique* correspondent.
  have hexU : ∀ i, i < n → ∃! j, ((i, j) ∈ E) := by
    intro i hi
    have hmem : i ∈ E.image Prod.fst := hsubL (Finset.mem_range.mpr hi)
    rw [Finset.mem_image] at hmem
    obtain ⟨p, hp, hp1⟩ := hmem
    have hpE : (i, p.2) ∈ E := by simpa [← hp1] using hp
    refine ⟨p.2, hpE, fun j hj => ?_⟩
    have hcard := hfunL i hi
    rw [Finset.card_le_one] at hcard
    have h1 : (i, p.2) ∈ E.filter (fun q => q.1 = i) := Finset.mem_filter.mpr ⟨hpE, rfl⟩
    have h2 : (i, j) ∈ E.filter (fun q => q.1 = i) := Finset.mem_filter.mpr ⟨hj, rfl⟩
    simpa using hcard _ h2 _ h1
  -- Extract `f : Fin n → Fin m` choosing the unique correspondent, with `mem_iff`.
  have hpick : ∀ i : Fin n, ∃ j : Fin m, ((i : ℕ), (j : ℕ)) ∈ E := fun i =>
    let ⟨j, hj, _⟩ := hexU i i.2; ⟨⟨j, (hwf _ hj).2⟩, hj⟩
  choose f hf using hpick
  have mem_iff : ∀ (i : Fin n) (j : Fin m), ((i : ℕ), (j : ℕ)) ∈ E ↔ f i = j := by
    refine fun i j => ⟨fun hmem => ?_, ?_⟩
    · obtain ⟨j', _, huniq⟩ := hexU i i.2
      exact Fin.ext ((huniq _ (hf i)).trans (huniq _ hmem).symm)
    · rintro rfl; exact hf i
  -- UNIFORMITY: `f` is injective (a single right position has one source).
  have hinj : Function.Injective f := by
    intro a b hab
    have ha : ((a : ℕ), (f a : ℕ)) ∈ E := (mem_iff a (f a)).mpr rfl
    have hb : ((b : ℕ), (f b : ℕ)) ∈ E := (mem_iff b (f b)).mpr rfl
    rw [hab] at ha
    have hcard := hfunR (f b) (f b).2
    rw [Finset.card_le_one] at hcard
    have h1 : ((a : ℕ), (f b : ℕ)) ∈ E.filter (fun p => p.2 = (f b : ℕ)) :=
      Finset.mem_filter.mpr ⟨ha, rfl⟩
    have h2 : ((b : ℕ), (f b : ℕ)) ∈ E.filter (fun p => p.2 = (f b : ℕ)) :=
      Finset.mem_filter.mpr ⟨hb, rfl⟩
    exact Fin.ext (by simpa using congrArg Prod.fst (hcard _ h1 _ h2))
  -- DEP: `f` is surjective (every right position is hit).
  have hsurj : Function.Surjective f := by
    intro j
    have hmem : (j : ℕ) ∈ E.image Prod.snd := hsubR (Finset.mem_range.mpr j.2)
    rw [Finset.mem_image] at hmem
    obtain ⟨p, hp, hp2⟩ := hmem
    exact ⟨⟨p.1, (hwf _ hp).1⟩, (mem_iff ⟨p.1, (hwf _ hp).1⟩ j).mp (by simpa [← hp2] using hp)⟩
  -- LINEARITY = 0: no inversions, so `f` is strictly monotone.
  have hmono : StrictMono f := by
    intro a b hab
    have ha : ((a : ℕ), (f a : ℕ)) ∈ E := (mem_iff a (f a)).mpr rfl
    have hb : ((b : ℕ), (f b : ℕ)) ∈ E := (mem_iff b (f b)).mpr rfl
    rcases lt_or_gt_of_ne (fun h => (ne_of_lt hab) (hinj h)) with h | h
    · exact h
    · exact absurd h (hnoinv _ ha _ hb hab)
  refine ⟨StrictMono.orderIsoOfSurjective f hmono hsurj, fun i j => ?_⟩
  rw [mem_iff, StrictMono.coe_orderIsoOfSurjective]

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
    plumbing point into `Core.Constraint.OT`'s evaluation machinery. -/
def toConstraint (family : ConstraintFamily) (label : String)
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

end Corr

/-! ### Reduplication constraints

The canonical @cite{mccarthy-prince-1995} reduplicative-faithfulness
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
  Hom r₁ r₂ := { p : ℕ × ℕ // p ∈ c.edge r₁ r₂ }

end Corr

end Phonology.Correspondence
