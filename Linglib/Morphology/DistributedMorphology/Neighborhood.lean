import Mathlib.Data.List.Basic

/-!
# Neighborhoods

The local environment a postsyntactic rule inspects: a focus terminal with
the terminals to either side, nearest first. Vocabulary Items and
Impoverishment rules are stated over the same neighborhoods — an item's
site is itself a neighborhood of feature lists, and it applies
where every feature it mentions, at the focus or on a neighbor, is present
(`Neighborhood.positioned`, `⊆`).

## Main definitions

* `Neighborhood` — focus, left context, right context.
* `Neighborhood.positioned` — the features of a neighborhood of feature
  lists, each tagged with its `Position`.
* `⊆` on `Neighborhood (List F)` — inclusion of positioned features.

## Implementation notes

A bare bundle coerces to the context-free neighborhood and `∅` is the
empty site, so a context-free Vocabulary Item is written
`⟨[f₁, f₂], e⟩` and the Elsewhere item `⟨∅, e⟩`. Positions count outward
from the focus: `left` toward the root, `right` toward the clause.
-/

namespace DistributedMorphology

variable {Bundle F : Type*}

/-- The local context a postsyntactic rule may inspect: the `focus` terminal
and the terminals to either side, nearest first. A condition that only
inspects `focus` is paradigmatic; one that reads `leftCtx` or `rightCtx` is
syntagmatic. -/
structure Neighborhood (Bundle : Type*) where
  focus    : Bundle
  leftCtx  : List Bundle := []
  rightCtx : List Bundle := []
  deriving Repr, DecidableEq

namespace Neighborhood

/-- A bundle, viewed as a context-free neighborhood. -/
def ofBundle (fb : Bundle) : Neighborhood Bundle := { focus := fb }

instance : Coe Bundle (Neighborhood Bundle) := ⟨ofBundle⟩

instance [EmptyCollection Bundle] : EmptyCollection (Neighborhood Bundle) := ⟨{ focus := ∅ }⟩

@[simp] theorem focus_ofBundle (fb : Bundle) : (ofBundle fb).focus = fb := rfl

@[simp] theorem leftCtx_ofBundle (fb : Bundle) : (ofBundle fb).leftCtx = [] := rfl

@[simp] theorem rightCtx_ofBundle (fb : Bundle) : (ofBundle fb).rightCtx = [] := rfl

/-! ### Positioned features -/

/-- A position in a neighborhood: the focus, or the `i`-th terminal to a
side, nearest first. -/
inductive Position where
  | focus
  | left (i : ℕ)
  | right (i : ℕ)
  deriving DecidableEq, Repr

/-- The features of a neighborhood of feature lists, each tagged with the
position it sits at. -/
def positioned (n : Neighborhood (List F)) : List (Position × F) :=
  n.focus.map (Position.focus, ·) ++
    n.leftCtx.zipIdx.flatMap (fun p => p.1.map (Position.left p.2, ·)) ++
    n.rightCtx.zipIdx.flatMap (fun p => p.1.map (Position.right p.2, ·))

/-- A site is included in a neighborhood when every positioned feature it
mentions is present; a terminal it does not mention is unconstrained — the
Subset Principle over neighborhoods. -/
instance : HasSubset (Neighborhood (List F)) := ⟨fun s n => s.positioned ⊆ n.positioned⟩

theorem subset_def {s n : Neighborhood (List F)} : s ⊆ n ↔ s.positioned ⊆ n.positioned :=
  Iff.rfl

instance [DecidableEq F] :
    DecidableRel (· ⊆ · : Neighborhood (List F) → Neighborhood (List F) → Prop) :=
  fun s n => inferInstanceAs (Decidable (s.positioned ⊆ n.positioned))

theorem Subset.refl (n : Neighborhood (List F)) : n ⊆ n := List.Subset.refl _

theorem Subset.trans {a b c : Neighborhood (List F)} (h₁ : a ⊆ b) (h₂ : b ⊆ c) : a ⊆ c :=
  List.Subset.trans h₁ h₂

instance : Std.Refl (· ⊆ · : Neighborhood (List F) → Neighborhood (List F) → Prop) := ⟨Subset.refl⟩

instance : Trans (· ⊆ · : Neighborhood (List F) → Neighborhood (List F) → Prop) (· ⊆ ·) (· ⊆ ·) :=
  ⟨Subset.trans⟩

@[simp] theorem positioned_ofBundle (fs : List F) :
    (ofBundle fs : Neighborhood (List F)).positioned = fs.map (Position.focus, ·) := by
  simp [positioned, ofBundle]

@[simp] theorem positioned_empty : (∅ : Neighborhood (List F)).positioned = [] := rfl

/-- Context-free sites compare by feature inclusion. -/
theorem ofBundle_subset_ofBundle {s t : List F} :
    (ofBundle s : Neighborhood (List F)) ⊆ ofBundle t ↔ s ⊆ t := by
  rw [subset_def, positioned_ofBundle, positioned_ofBundle]
  exact List.map_subset_iff _ fun _ _ h => (Prod.mk.inj h).2

end Neighborhood

end DistributedMorphology
