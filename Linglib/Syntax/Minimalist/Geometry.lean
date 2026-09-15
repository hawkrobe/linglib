import Mathlib.Data.Finset.Basic

/-!
# Feature geometries

This file defines a feature geometry, a finite set of privative features together with the
entailment closure of each feature, the features that bearing it entails, itself included
([harley-ritter-2002]). Closures are reflexive and closed under entailment, so entailment is a
preorder on the features and a feature's closure is [deal-2025a]'s geometric closure, the
features a probe copies when it interacts with that feature. A geometry satisfies mismatch
resolution when every two of its features entail a common feature, the premise of coordination
resolution without default insertion ([adamson-anagnostopoulou-2025]).

## Main definitions

* `Minimalist.Geometry`: a finite set of features with the entailment closure of each.
* `Minimalist.Geometry.Entails`: the entailment preorder, `a` entailing `b` when `b` lies in
  the closure of `a`.
* `Minimalist.Geometry.MismatchResolution`: every two features of the geometry entail a common
  feature.

## References

* [harley-ritter-2002]
* [adamson-anagnostopoulou-2025]
* [deal-2025a]
-/

namespace Minimalist

/-- A feature geometry is a finite set of features with the entailment closure of each, the
features that bearing it entails, itself included and closed under entailment. -/
structure Geometry (F : Type*) where
  /-- The features of the geometry. -/
  nodes : Finset F
  /-- The closure of a feature under entailment. -/
  above : F → Finset F
  /-- A feature entails itself. -/
  self_mem_above : ∀ a, a ∈ above a
  /-- What an entailed feature entails, the entailing feature entails. -/
  above_subset_above : ∀ a b, b ∈ above a → above b ⊆ above a

namespace Geometry

variable {F : Type*} (G : Geometry F)

/-- `a` entails `b` when `b` lies in the closure of `a`. -/
def Entails (a b : F) : Prop := b ∈ G.above a

instance [DecidableEq F] (a b : F) : Decidable (G.Entails a b) :=
  inferInstanceAs (Decidable (b ∈ G.above a))

theorem Entails.refl (a : F) : G.Entails a a := G.self_mem_above a

theorem Entails.trans {a b c : F} (hab : G.Entails a b) (hbc : G.Entails b c) : G.Entails a c :=
  G.above_subset_above a b hab hbc

/-- Entailment is inclusion of closures. -/
theorem entails_iff_subset {a b : F} : G.Entails a b ↔ G.above b ⊆ G.above a :=
  ⟨G.above_subset_above a b, fun h => h (G.self_mem_above b)⟩

/-- Every two features of the geometry entail a common feature. -/
def MismatchResolution [DecidableEq F] : Prop :=
  ∀ a ∈ G.nodes, ∀ b ∈ G.nodes, (G.above a ∩ G.above b).Nonempty

instance [DecidableEq F] : Decidable G.MismatchResolution := by
  unfold MismatchResolution; infer_instance

end Geometry

end Minimalist
