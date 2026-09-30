module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Basic
public import Linglib.Semantics.Presupposition.Basic

/-!
# Content layers

This file defines the three layers of a semantic contribution — presupposition, at-issue
content, and implicature — the propositions carrying content at each layer, and the layers
of such a proposition that a correction makes offensive, which a denial targets. The layers
are [van-der-sandt-maier-2003]'s labels `pr`, `fr`, and `imp` of Layered DRT; `PartialProp`
is the two-layer case.

## Main definitions

* `ContentLayer` — the three layers.
* `LayeredProp` — content at each layer, with `get`, `toPartialProp`, and `ofPartialProp`.
* `LayeredProp.IsOffensive`, `LayeredProp.offensiveLayers` — the layers inconsistent with a
  correction.

## References

* [van-der-sandt-maier-2003]
* [tonhauser-beaver-roberts-simons-2013]
-/

@[expose] public section

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
