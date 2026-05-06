import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Theories.Syntax.Minimalist.HeadFunction

/-!
# Minimalist Labeling (@cite{marcolli-chomsky-berwick-2025} §1.15)

The MCB §1.15 Labeling Algorithm: assign categorial labels to non-leaf
vertices of a `SyntacticObject` via an externally-supplied
`HeadFunction`. There is no canonical "the" label of an SO — labeling
is parametric over the head function chosen by the analyst.

This file is the **single source of truth** for Minimalist labeling.
The pre-MCB selection-driven algorithm (`getCategory`, `label`,
`labelCat`, `selects`, `sameLabel`, `projectsIn`, `isMaximalIn`,
`isHeadIn`, `isPhraseIn`, etc.) was deleted at 0.230.X — it predated
both linglib's MCB substrate and the @cite{marcolli-chomsky-berwick-2025}
formalisation, and bridged-via-`HeadFunction.selectionBased`
preservation was rejected as perpetuating the legacy mindset (selection
determines projection) that MCB explicitly relaxes.

## Public API

- `labelVertex h T v` — MCB Definition 1.15.2: the categorial label at
  vertex `v` of `T` under head function `h`. Returns `none` for leaves
  (which carry their `LIToken`'s `outerCat` directly) and when `T ∉
  Dom(h)`.
- `labelRoot h T = labelVertex h T T` — root-label special case.
- `isLabelable h T v` — Prop: `labelVertex h T v` is `some _`.
- `sameLabelAt h T x y` — `x` and `y` carry the same label in `T` under `h`.
- `isHeadOf h T x` — `x` is a leaf token equal to `h.head T` (so `x` is
  the projecting head of `T`).
- `projectsAt h T x` — `x ⊆ T`, `x` is non-leaf, and `labelVertex h T x
  = labelRoot h T` (so `x` carries the same label as the root).

## Choice of head function

For consumers without natural derivational context, the standard
choices are `HeadFunction.leftSpine` (left-headed; canonical for
English-like analyses) or `HeadFunction.rightSpine` (right-headed).
For Studies with a `Derivation`, the per-paper head function lives
on the derivation (see `Selection.lean`'s `Derivation.headLI?`).

The MCB framework treats these as equally valid; the choice is per-
analysis, not a property of the language faculty.
-/

namespace Minimalist.Labeling

open Minimalist (HeadFunction Cat SyntacticObject LIToken)

-- ============================================================================
-- § 1: MCB §1.15.2 Labeling Algorithm
-- ============================================================================

/-- The categorial label at vertex `v` of `T` under head function `h`,
    when `T ∈ Dom(h)`. Returns `none` for leaf vertices (which carry
    their own `LIToken`'s category directly, not a "label" in the
    head-function sense) and when `T ∉ Dom(h)`.

    Implements @cite{marcolli-chomsky-berwick-2025} §1.15.2 case 1
    (default): `h_T(v).outerCat` for non-leaf `v` in `T ∈ Dom(h)`. -/
def labelVertex (h : HeadFunction) (T v : SyntacticObject) : Option Cat :=
  if h.Dom T then
    match v with
    | .leaf _ => none
    | .node _ _ => some (h.headAt v).item.outerCat
  else
    -- TODO: shared-feature fallback (Def 1.15.2 case 4): if T = .node a b
    -- and h.headAt a, h.headAt b share a feature, label root by that
    -- feature. Requires feature-bundle-intersection from CategorialFeatures.
    none

/-- The label at the root of `T` (a frequent special case). -/
def labelRoot (h : HeadFunction) (T : SyntacticObject) : Option Cat :=
  labelVertex h T T

/-- For `T ∈ Dom(h)` with `T = .node a b`, the root label is the
    outer category of `h(T)`. -/
@[simp] theorem labelRoot_node_in_dom (h : HeadFunction) (a b : SyntacticObject)
    (hT : h.Dom (.node a b)) :
    labelRoot h (.node a b) = some ((h.head (.node a b)).item.outerCat) := by
  show labelVertex h (.node a b) (.node a b) = _
  unfold labelVertex HeadFunction.head
  rw [if_pos hT]

/-- Leaves never get a "label" from the algorithm — they carry their
    own `LIToken`'s category. -/
@[simp] theorem labelVertex_leaf (h : HeadFunction) (T : SyntacticObject)
    (tok : LIToken) :
    labelVertex h T (.leaf tok) = none := by
  unfold labelVertex
  split <;> rfl

/-- When `T ∉ Dom(h)`, the algorithm's default case fails (returns
    `none`); the shared-feature fallback (case 4) is not yet
    implemented. -/
theorem labelVertex_not_in_dom (h : HeadFunction) (T v : SyntacticObject)
    (hT : ¬ h.Dom T) :
    labelVertex h T v = none := by
  unfold labelVertex
  rw [if_neg hT]

/-- A vertex is **labelable** by the algorithm iff `labelVertex` returns
    `some _`. Non-labelable vertices correspond to objects filtered
    out by the Externalization quotient map `Π_L` per
    @cite{marcolli-chomsky-berwick-2025} §1.15. -/
def isLabelable (h : HeadFunction) (T v : SyntacticObject) : Prop :=
  (labelVertex h T v).isSome

instance (h : HeadFunction) (T v : SyntacticObject) :
    Decidable (isLabelable h T v) := by
  unfold isLabelable; infer_instance

/-- For `T ∈ Dom(h)`, every internal vertex is labelable (default case applies). -/
theorem internal_vertex_labelable_in_dom
    (h : HeadFunction) (T : SyntacticObject) (a b : SyntacticObject)
    (hT : h.Dom T) :
    isLabelable h T (.node a b) := by
  unfold isLabelable labelVertex
  rw [if_pos hT]
  exact rfl

-- ============================================================================
-- § 2: Relational predicates (parametric over the head function)
-- ============================================================================

/-- Two vertices `x`, `y` of `T` carry the same label under `h`. -/
def sameLabelAt (h : HeadFunction) (T x y : SyntacticObject) : Prop :=
  labelVertex h T x = labelVertex h T y ∧ (labelVertex h T x).isSome

instance (h : HeadFunction) (T x y : SyntacticObject) :
    Decidable (sameLabelAt h T x y) := by
  unfold sameLabelAt; infer_instance

/-- `x` is the projecting head of `T` under `h`: `x` is a leaf whose
    token equals `h.head T`. Decidable on `LIToken.DecidableEq`. -/
def isHeadOf (h : HeadFunction) (T x : SyntacticObject) : Prop :=
  match x with
  | .leaf tok => h.head T = tok
  | .node _ _ => False

instance (h : HeadFunction) (T x : SyntacticObject) :
    Decidable (isHeadOf h T x) := by
  unfold isHeadOf
  cases x <;> infer_instance

/-- `x` projects at vertex `x` of `T` under `h`: `x` is a non-leaf
    contained in `T` whose label equals `T`'s root label. This is the
    MCB analogue of "x is on the projection path of the root head". -/
def projectsAt (h : HeadFunction) (T x : SyntacticObject) : Prop :=
  containsOrEq T x ∧ labelVertex h T x = labelRoot h T ∧ (labelRoot h T).isSome

instance (h : HeadFunction) (T x : SyntacticObject) :
    Decidable (projectsAt h T x) := by
  unfold projectsAt; infer_instance

/-- `x` is **+max(imal)** in `T` under `h`: `x ⊆ T` and `x` does not
    project at any strict ancestor in `T`. The classic MCB-style
    notion of a maximal projection (@cite{marcolli-chomsky-berwick-2025}
    Lemma 1.14.1's terminus of a γ_ℓ projection path).

    Bounded over `T.subtrees` so the predicate is decidable. -/
def isMaximalAt (h : HeadFunction) (T x : SyntacticObject) : Prop :=
  containsOrEq T x ∧
    ∀ z ∈ T.subtrees, contains z x → ¬ sameLabelAt h T x z ∨ z = x

instance (h : HeadFunction) (T x : SyntacticObject) :
    Decidable (isMaximalAt h T x) := by
  unfold isMaximalAt; infer_instance

/-- `x` is **+min(imal)** in `T` under `h`: `x` is a leaf in `T`. (MCB
    treats heads as leaves; `+min` adds the membership requirement.) -/
def isMinimalAt (T x : SyntacticObject) : Prop :=
  isTermOf x T ∧ x.isLeaf

instance (T x : SyntacticObject) : Decidable (isMinimalAt T x) := by
  unfold isMinimalAt; infer_instance

/-- A **head** in `T`: `+min` and `−max` (it projects). MCB §1.15
    classification carried over. -/
def isHeadIn (h : HeadFunction) (T x : SyntacticObject) : Prop :=
  isMinimalAt T x ∧ ¬ isMaximalAt h T x

instance (h : HeadFunction) (T x : SyntacticObject) :
    Decidable (isHeadIn h T x) := by
  unfold isHeadIn; infer_instance

/-- A **phrase** in `T`: `+max`. MCB §1.15 classification carried over. -/
def isPhraseIn (h : HeadFunction) (T x : SyntacticObject) : Prop :=
  isMaximalAt h T x

instance (h : HeadFunction) (T x : SyntacticObject) :
    Decidable (isPhraseIn h T x) := by
  unfold isPhraseIn; infer_instance

end Minimalist.Labeling
