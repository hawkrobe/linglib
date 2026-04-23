import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Quiver.Basic
import Linglib.Core.Constraint.OT.Basic
import Linglib.Theories.Phonology.OptimalityTheory.Constraints

/-!
# Correspondence Theory
@cite{mccarthy-prince-1995} @cite{benua-1997}

Correspondence Theory (@cite{mccarthy-prince-1995}) replaces the PARSE/FILL
approach to faithfulness (@cite{prince-smolensky-1993}) with a relation
ℛ between strings. Faithfulness constraints are structural properties of
ℛ — completeness (MAX, DEP), featural identity (IDENT), order preservation
(LINEARITY), contiguity (CONTIGUITY), edge alignment (ANCHOR).

@cite{benua-1997} extends correspondence from binary input-output and
base-reduplicant relations to a *family* of relations indexed by
morphological/derivational role: I-O, B-R, I-R, O-O — and, in subsequent
work, sympathy candidates, basemap projections (@cite{rolle-2018}),
paradigm members (@cite{mccarthy-2005}), candidate-chain steps. The
unifying object is a **labeled diagram of strings**: a finite indexed
family of forms together with binary correspondence relations between
them.

## The unifying type: `Corr Role α`

A `Corr Role α` is a `Role`-indexed family of strings of `α` together with
a `Role × Role`-indexed family of correspondence relations (sets of
position-pairs). Each constraint family is a function
`Corr Role α → Role → Role → ℕ`: `MAX-IO` is `c.maxViol .input .output`;
`IDENT-OO` is `c.identViol .o₁ .o₂`. The "same constraint schema generates
distinct constraints for each domain" claim of @cite{mccarthy-prince-1995}
becomes literally true at the type level — there is one
`Corr.identViol`; named instances are partial applications.

## Edges as `Finset`

Correspondence relations are *sets* of position pairs (@cite{mccarthy-prince-1995}
Definition 10), not ordered sequences — so `edge` returns `Finset (ℕ × ℕ)`
rather than `List (ℕ × ℕ)`. INTEGRITY (one-to-many) and UNIFORMITY
(many-to-one) violations are then `Finset.card` of suitable filters,
without indexing artifacts and with no double-counting.

## The binary case: `Side`

For two-form correspondences (M&P 1995 binary I-O, B-R, etc.), the role
type is `Side` (`.lhs | .rhs`). Constructors `Corr.parallel s₁ s₂` and
`Corr.identity s` produce `Corr Side α`. This is the substrate used by
`BasemapCorrespondence` (matrix vs. basemap tier) and
`Process.Harmony.OT` (input vs. output harmony tier). Multi-role
theories supply their own `Role` enums — see `TCT.lean`,
`Transderivational.lean`, `BasemapCorrespondence.lean`.

## Out of scope

- *Composition* of correspondences. @cite{mccarthy-prince-1995} explicitly
  has no through-correspondence; correspondence is a labeled quiver, not
  a category — there is no composition law to formalize here.
- *Path-based evaluation* (stratal cycles, candidate chains). When needed,
  derive via `Mathlib.Combinatorics.Quiver.Path` over the role quiver
  — see `StratalOT.lean` and `TCT.lean`.
-/

namespace Phonology.Correspondence

open Core.Constraint.OT
open Finset

-- ============================================================================
-- § 1: The Binary Role
-- ============================================================================

/-- The two roles for a binary correspondence diagram. The substrate role
    type for `Corr.parallel` and `Corr.identity` — the latter being the
    @cite{mccarthy-prince-1995} input-output binary case. Multi-role
    theories supply their own role enums. -/
inductive Side where
  | lhs
  | rhs
  deriving DecidableEq, Repr

/-- Display label for a `Side` (used in constraint names). -/
def Side.label : Side → String
  | .lhs => "L"
  | .rhs => "R"

-- ============================================================================
-- § 2: The Correspondence Diagram
-- ============================================================================

/-- A **correspondence diagram**: a `Role`-indexed family of strings of `α`
    together with a `Role × Role`-indexed family of binary correspondence
    relations. The unifying object behind I-O / B-R / I-R / O-O / OP / LC /
    Stratal / Antifaith / MxBM-C correspondence theories.

    @cite{mccarthy-prince-1995} Definition 10 (binary case): "Given two
    strings S₁, S₂, correspondence is a relation ℛ from the elements of S₁
    to those of S₂." Generalized to multiple typed forms following
    @cite{benua-1997}.

    `edge r₁ r₂` is the set of position pairs `(i, j)` such that position
    `i` of `form r₁` corresponds to position `j` of `form r₂`. The relation
    need not be a function: one-to-many (INTEGRITY) and many-to-one
    (UNIFORMITY) are permitted and counted by their constraint families.

    The `wf` field guarantees position validity: any `(i, j) ∈ edge r₁ r₂`
    satisfies `i < (form r₁).length` and `j < (form r₂).length`. -/
structure Corr (Role : Type*) (α : Type*) where
  form : Role → List α
  edge : Role → Role → Finset (ℕ × ℕ)
  wf : ∀ r₁ r₂, ∀ p ∈ edge r₁ r₂,
        p.1 < (form r₁).length ∧ p.2 < (form r₂).length

namespace Corr

variable {Role : Type*} {α : Type*}

-- ============================================================================
-- § 3: Constraint Families
-- ============================================================================

/-- **(A.1) MAX** — every element of `form r₁` has a correspondent in `form r₂`.

    Counts positions of `form r₁` with no correspondent in `form r₂` under
    `edge r₁ r₂`. MAX-IO prohibits deletion; MAX-BR demands total
    reduplication; MAX-OO is the basemap-faithfulness constraint of
    @cite{benua-1997}. -/
def maxViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.range (c.form r₁).length) \ (c.edge r₁ r₂).image Prod.fst).card

/-- **(A.2) DEP** — every element of `form r₂` has a correspondent in `form r₁`.

    Counts positions of `form r₂` with no correspondent in `form r₁` under
    `edge r₁ r₂`. DEP-IO prohibits epenthesis; DEP-BR prohibits fixed
    default segmentism. -/
def depViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.range (c.form r₂).length) \ (c.edge r₁ r₂).image Prod.snd).card

/-- **(A.3) IDENT** — corresponding elements are featurally identical.

    Counts pairs `(i, j) ∈ edge r₁ r₂` where `(form r₁)[i] ≠ (form r₂)[j]`.
    IDENT-IO penalises featural unfaithfulness; IDENT-OO is the basemap
    and paradigm-uniformity constraint of @cite{benua-1997},
    @cite{mccarthy-2005}, and the basemap-faithfulness layer of
    @cite{rolle-2018}.

    For a featural variant comparing forms feature-by-feature (rather than
    by full segment identity), see `identViolFeature`. -/
def identViol [DecidableEq α] (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p =>
    (c.form r₁)[p.1]? ≠ (c.form r₂)[p.2]?).card

/-- **(A.3*) IDENT-[F]** — featural variant of IDENT. Counts pairs
    `(i, j) ∈ edge r₁ r₂` where projecting both elements through
    `proj : α → F` yields different values. Used by Benua-style featural
    OO-IDENT (@cite{benua-1997} Ch 4 Tiberian Hebrew: `IDENT-[continuant]`)
    and by harmony systems (@cite{rose-walker-2011}: `IDENT-[F]` for the
    harmony feature). -/
def identViolFeature {F : Type*} [DecidableEq F] (proj : α → F)
    (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((c.edge r₁ r₂).filter fun p =>
    (c.form r₁)[p.1]?.map proj ≠ (c.form r₂)[p.2]?.map proj).card

-- ============================================================================
-- § 4: Contiguity (via mathlib `List.Chain'`)
-- ============================================================================

/-- A list of natural numbers is contiguous (no gaps) iff its consecutive
    elements differ by 1. Defined as `List.Chain' (fun a b => b = a + 1)`
    — mathlib's standard "consecutive" predicate. -/
abbrev IsContiguous (l : List ℕ) : Prop := List.Chain' (fun a b => b = a + 1) l

instance : (l : List ℕ) → Decidable (IsContiguous l)
  | [] => .isTrue List.Chain'.nil
  | [_] => .isTrue (List.chain'_singleton _)
  | a :: b :: rest =>
    if h₁ : b = a + 1 then
      match instDecidableIsContiguous (b :: rest) with
      | .isTrue h₂ => .isTrue (List.Chain'.cons h₁ h₂)
      | .isFalse h₂ => .isFalse fun h => h₂ h.tail
    else .isFalse fun h => h₁ (List.chain'_cons.mp h).1

/-- **(A.4a) I-CONTIGUITY** — "No Skipping." Domain(ℛ) is a contiguous
    substring of `form r₁`. Violated by internal deletion. -/
def contigIViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  let dom := ((c.edge r₁ r₂).image Prod.fst).sort (· ≤ ·)
  if IsContiguous dom then 0 else 1

/-- **(A.4b) O-CONTIGUITY** — "No Intrusion." Range(ℛ) is a contiguous
    substring of `form r₂`. Violated by internal epenthesis. -/
def contigOViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  let rng := ((c.edge r₁ r₂).image Prod.snd).sort (· ≤ ·)
  if IsContiguous rng then 0 else 1

-- ============================================================================
-- § 5: Anchors
-- ============================================================================

/-- **(A.5a) L-ANCHOR** — leftmost positions correspond. Binary 0/1.
    In prefixing reduplication, L-ANCHOR-BR ≫ R-ANCHOR-BR. -/
def anchorLViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  if (c.form r₁).length = 0 ∨ (c.form r₂).length = 0 then 0
  else if (0, 0) ∈ c.edge r₁ r₂ then 0 else 1

/-- **(A.5b) R-ANCHOR** — rightmost positions correspond. -/
def anchorRViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  if (c.form r₁).length = 0 ∨ (c.form r₂).length = 0 then 0
  else if ((c.form r₁).length - 1, (c.form r₂).length - 1) ∈ c.edge r₁ r₂
       then 0 else 1

-- ============================================================================
-- § 6: LINEARITY, UNIFORMITY, INTEGRITY
-- ============================================================================

/-- **(A.6) LINEARITY** — "No Metathesis." Counts inversion pairs
    `(i₁, j₁), (i₂, j₂) ∈ edge` with `i₁ < i₂` but `j₂ < j₁`. -/
def linearityViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ∑ p ∈ c.edge r₁ r₂,
    ((c.edge r₁ r₂).filter fun q => p.1 < q.1 ∧ q.2 < p.2).card

/-- **(A.7) UNIFORMITY** — "No Coalescence." Counts positions of `form r₂`
    with multiple correspondents in `form r₁`. -/
def uniformityViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.range (c.form r₂).length).filter fun j =>
    ((c.edge r₁ r₂).filter fun p => p.2 = j).card > 1).card

/-- **(A.8) INTEGRITY** — "No Breaking." Counts positions of `form r₁`
    with multiple correspondents in `form r₂`. -/
def integrityViol (c : Corr Role α) (r₁ r₂ : Role) : ℕ :=
  ((Finset.range (c.form r₁).length).filter fun i =>
    ((c.edge r₁ r₂).filter fun p => p.1 = i).card > 1).card

-- ============================================================================
-- § 7: Universal Constructors (binary case via `Side`)
-- ============================================================================

/-- The parallel-pair correspondence between two strings. Forms `.lhs ↦ s₁`,
    `.rhs ↦ s₂`; for cross-side edges, position `i` of one is paired with
    position `i` of the other, ranging up to the shorter length. The
    substrate for Hamming-distance-style faithfulness on tier-projected
    forms — used by `BasemapCorrespondence` (matrix vs. basemap tonal
    tier) and `Process.Harmony.OT` (input vs. output harmony tier).

    On unequal-length inputs, the truncation matches `List.zip` semantics:
    only positions `< min s₁.length s₂.length` are paired. For equal-length
    inputs, every position participates. -/
def parallel (s₁ s₂ : List α) : Corr Side α where
  form
    | .lhs => s₁
    | .rhs => s₂
  edge r₁ r₂ :=
    if r₁ = r₂ then ∅
    else (Finset.range (min s₁.length s₂.length)).image fun i => (i, i)
  wf := by
    intro r₁ r₂ p hmem
    by_cases hreq : r₁ = r₂
    · simp [hreq] at hmem
    · simp only [if_neg hreq, Finset.mem_image, Finset.mem_range] at hmem
      obtain ⟨i, hi, hp⟩ := hmem
      cases hp
      cases r₁ <;> cases r₂ <;> simp_all

/-- The identity correspondence on a single string. The fully-faithful
    candidate of @cite{mccarthy-prince-1995}: input = output, every
    position paired with itself. -/
def identity (s : List α) : Corr Side α := parallel s s

-- ============================================================================
-- § 8: Identity Zero Theorems
-- ============================================================================

@[simp] theorem parallel_form_lhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).form .lhs = s₁ := rfl

@[simp] theorem parallel_form_rhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).form .rhs = s₂ := rfl

@[simp] theorem parallel_edge_diag (s₁ s₂ : List α) (r : Side) :
    (parallel s₁ s₂).edge r r = ∅ := by
  simp [parallel]

@[simp] theorem parallel_edge_lhs_rhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).edge .lhs .rhs =
      (Finset.range (min s₁.length s₂.length)).image (fun i => (i, i)) := by
  simp [parallel]

@[simp] theorem parallel_edge_rhs_lhs (s₁ s₂ : List α) :
    (parallel s₁ s₂).edge .rhs .lhs =
      (Finset.range (min s₁.length s₂.length)).image (fun i => (i, i)) := by
  simp [parallel]

/-- Identity correspondence has zero MAX violations. -/
theorem identity_max_zero (s : List α) :
    (identity s).maxViol .lhs .rhs = 0 := by
  simp only [identity, maxViol, parallel_form_lhs, parallel_edge_lhs_rhs,
             Finset.image_image, Function.comp_def, Finset.image_id']
  simp

/-- Identity correspondence has zero DEP violations. -/
theorem identity_dep_zero (s : List α) :
    (identity s).depViol .lhs .rhs = 0 := by
  simp only [identity, depViol, parallel_form_rhs, parallel_edge_lhs_rhs,
             Finset.image_image, Function.comp_def, Finset.image_id']
  simp

/-- Identity correspondence has zero IDENT violations. -/
theorem identity_ident_zero [DecidableEq α] (s : List α) :
    (identity s).identViol .lhs .rhs = 0 := by
  simp only [identity, identViol, parallel_form_lhs, parallel_form_rhs,
             parallel_edge_lhs_rhs]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨i, _, rfl⟩ := hp
  simp

/-- Identity correspondence has zero featural-IDENT violations (for any
    feature projection). -/
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

-- ============================================================================
-- § 9: Length Bounds
-- ============================================================================

theorem maxViol_le_length (c : Corr Role α) (r₁ r₂ : Role) :
    c.maxViol r₁ r₂ ≤ (c.form r₁).length := by
  simp only [maxViol]
  exact (Finset.card_le_card (Finset.sdiff_subset)).trans
        (Finset.card_range _).le

theorem depViol_le_length (c : Corr Role α) (r₁ r₂ : Role) :
    c.depViol r₁ r₂ ≤ (c.form r₂).length := by
  simp only [depViol]
  exact (Finset.card_le_card (Finset.sdiff_subset)).trans
        (Finset.card_range _).le

theorem uniformityViol_le_length (c : Corr Role α) (r₁ r₂ : Role) :
    c.uniformityViol r₁ r₂ ≤ (c.form r₂).length := by
  simp only [uniformityViol]
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

theorem integrityViol_le_length (c : Corr Role α) (r₁ r₂ : Role) :
    c.integrityViol r₁ r₂ ≤ (c.form r₁).length := by
  simp only [integrityViol]
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

-- ============================================================================
-- § 10: NamedConstraint Bridges
-- ============================================================================

/-- Build a `NamedConstraint` from a `Corr`-violation function. The single
    point of plumbing into `Core.Constraint.OT`'s evaluation machinery —
    every named correspondence constraint factors through this. -/
def toConstraint {Role α : Type} (family : ConstraintFamily) (label : String)
    (eval : Corr Role α → ℕ) : NamedConstraint (Corr Role α) where
  name := label
  family := family
  eval := eval

/-- IDENT as a `NamedConstraint`. Specializes `toConstraint` to identViol. -/
def toIdentConstraint {Role α : Type} [DecidableEq α] (r₁ r₂ : Role)
    (label : String) : NamedConstraint (Corr Role α) :=
  toConstraint .faithfulness ("IDENT-" ++ label) (fun c => c.identViol r₁ r₂)

/-- IDENT-[F] as a `NamedConstraint`. Featural variant of `toIdentConstraint`. -/
def toIdentFeatureConstraint {Role α : Type} {F : Type} [DecidableEq F]
    (proj : α → F) (r₁ r₂ : Role) (label : String) :
    NamedConstraint (Corr Role α) :=
  toConstraint .faithfulness ("IDENT-" ++ label)
    (fun c => c.identViolFeature proj r₁ r₂)

/-- MAX as a `NamedConstraint`. -/
def toMaxConstraint {Role α : Type} (r₁ r₂ : Role) (label : String) :
    NamedConstraint (Corr Role α) :=
  toConstraint .faithfulness ("MAX-" ++ label) (fun c => c.maxViol r₁ r₂)

/-- DEP as a `NamedConstraint`. -/
def toDepConstraint {Role α : Type} (r₁ r₂ : Role) (label : String) :
    NamedConstraint (Corr Role α) :=
  toConstraint .faithfulness ("DEP-" ++ label) (fun c => c.depViol r₁ r₂)

-- ============================================================================
-- § 11: Quiver Structure
-- ============================================================================

/-- A correspondence diagram `c : Corr Role α` carries a labeled-quiver
    structure on `Role`: the morphisms from `r₁` to `r₂` are the
    correspondence pairs `(i, j) ∈ c.edge r₁ r₂`. The `Quiver` instance
    cannot live on `Role` itself (it would need to depend on the value
    `c`); instead we wrap `Role` in a definitional newtype `RoleQuiv c`
    and put the `Quiver` instance there.

    Use case: stratal/OT-CC chained evaluation, where derivations are
    paths in the role-quiver. `Quiver.Path` and the rest of mathlib's
    `Combinatorics.Quiver` API then become available. -/
def RoleQuiv {Role α : Type*} (_ : Corr Role α) : Type _ := Role

instance {Role α : Type*} (c : Corr Role α) : Quiver (RoleQuiv c) where
  Hom r₁ r₂ := { p : ℕ × ℕ // p ∈ c.edge r₁ r₂ }

end Corr

end Phonology.Correspondence
