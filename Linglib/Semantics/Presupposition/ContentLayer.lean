import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Basic
import Linglib.Semantics.Presupposition.Basic

/-!
# Content layers

This file defines the three layers of a semantic contribution — presupposition, at-issue
content, and implicature — the propositions carrying content at each layer, and the layers
of such a proposition that a correction makes offensive, which a denial targets. The layers
are [van-der-sandt-maier-2003]'s labels `pr`, `fr`, and `imp` of Layered DRT; `PartialProp`
is the two-layer case, and `BiLayered` collapses the two backgrounded layers into one
not-at-issue layer for analyses that only separate proffered from backgrounded content
([anderbois-brasoveanu-henderson-2015]).

## Main definitions

* `ContentLayer` — the three layers.
* `LayeredProp` — content at each layer, with `get`, `toPartialProp`, `ofPartialProp`, and
  `toBiLayered`.
* `LayeredProp.IsOffensive`, `LayeredProp.offensiveLayers` — the layers inconsistent with a
  correction.
* `BiLayered` — at-issue and not-at-issue content, with `ofProp`.

## References

* [van-der-sandt-maier-2003]
* [tonhauser-beaver-roberts-simons-2013]
* [anderbois-brasoveanu-henderson-2015]
-/

namespace Presupposition

/-- The layer of a semantic contribution: a backgrounded precondition, the proffered
content, or an enrichment beyond the truth conditions. -/
inductive ContentLayer
  | presupposition
  | atIssue
  | implicature
  deriving DecidableEq, Fintype, Repr

/-- Content at each of the three layers; the implicature layer is trivial by default. -/
@[ext]
structure LayeredProp (W : Type*) where
  presupposition : W → Prop
  atIssue : W → Prop
  implicature : W → Prop := fun _ => True

/-- At-issue and not-at-issue content; the not-at-issue layer is trivial by default. -/
@[ext]
structure BiLayered (W : Type*) where
  atIssue : W → Prop
  notAtIssue : W → Prop := fun _ => True

namespace BiLayered

variable {W : Type*}

/-- A proposition with no not-at-issue content. -/
def ofProp (p : W → Prop) : BiLayered W := { atIssue := p }

@[simp] theorem ofProp_atIssue (p : W → Prop) : (ofProp p).atIssue = p := rfl

@[simp] theorem ofProp_notAtIssue (p : W → Prop) : (ofProp p).notAtIssue = fun _ => True := rfl

end BiLayered

namespace LayeredProp

variable {W : Type*} (φ : LayeredProp W)

/-- The content at a layer. -/
def get : ContentLayer → W → Prop
  | .presupposition => φ.presupposition
  | .atIssue => φ.atIssue
  | .implicature => φ.implicature

instance [DecidablePred φ.presupposition] [DecidablePred φ.atIssue]
    [DecidablePred φ.implicature] (l : ContentLayer) : DecidablePred (φ.get l) := by
  cases l <;> simp only [get] <;> infer_instance

/-- The two-layer proposition, discarding the implicature. -/
def toPartialProp : PartialProp W := ⟨φ.presupposition, φ.atIssue⟩

/-- A two-layer proposition, with no implicature. -/
def ofPartialProp (p : PartialProp W) : LayeredProp W := ⟨p.presup, p.assertion, fun _ => True⟩

@[simp] theorem toPartialProp_ofPartialProp (p : PartialProp W) :
    (ofPartialProp p).toPartialProp = p := rfl

/-- The backgrounded layers collapsed into the not-at-issue layer. -/
def toBiLayered : BiLayered W := ⟨φ.atIssue, fun w => φ.presupposition w ∧ φ.implicature w⟩

/-- Layer `l` is offensive against the correction `K` when no `K`-world satisfies its
content — the layers a denial with correction `K` targets. -/
def IsOffensive (l : ContentLayer) (K : Set W) : Prop := ∀ w ∈ K, ¬ φ.get l w

theorem isOffensive_iff_disjoint (l : ContentLayer) (K : Set W) :
    φ.IsOffensive l K ↔ Disjoint {w | φ.get l w} K := by
  simp [IsOffensive, Set.disjoint_right]

instance [Fintype W] (l : ContentLayer) (K : Set W) [DecidablePred (· ∈ K)]
    [DecidablePred (φ.get l)] : Decidable (φ.IsOffensive l K) :=
  inferInstanceAs (Decidable (∀ w, w ∈ K → ¬ φ.get l w))

/-- The layers offensive against the correction `K`. -/
def offensiveLayers (K : Set W) [∀ l, Decidable (φ.IsOffensive l K)] : Finset ContentLayer :=
  Finset.univ.filter (φ.IsOffensive · K)

end LayeredProp

end Presupposition
