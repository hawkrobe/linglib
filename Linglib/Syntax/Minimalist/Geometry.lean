import Mathlib.Data.Finset.Basic

/-!
# Feature geometries

This file defines a feature geometry, a finite set of privative features together with, for
each feature, the features that bearing it entails, itself included, the features that dominate
it in the geometry of [harley-ritter-2002]. Entailment is reflexive and transitive, so it is a
preorder on the features. Its converse, the features a given feature dominates, is
[deal-2025a]'s geometric closure, the features a probe copies when it interacts with that
feature. A geometry satisfies mismatch resolution when every two of its features entail a
common feature, the premise of coordination resolution without default insertion
([adamson-anagnostopoulou-2025]).

## Main definitions

* `Minimalist.Geometry`: a finite set of features with, for each, its entailments.
* `Minimalist.Geometry.MismatchResolution`: every two features of the geometry entail a common
  feature.

## References

* [harley-ritter-2002]
* [adamson-anagnostopoulou-2025]
* [deal-2025a]
-/

namespace Minimalist

/-- A feature geometry is a finite set of features with, for each feature, the features that
bearing it entails, itself included, so that entailment is reflexive and transitive. -/
structure Geometry (F : Type*) where
  /-- The features of the geometry. -/
  nodes : Finset F
  /-- The entailments of a feature, itself included. -/
  entailments : F → Finset F
  /-- A feature is among its own entailments. -/
  mem_entailments_self : ∀ a, a ∈ entailments a
  /-- The entailments of an entailment are entailments. -/
  entailments_subset_of_mem : ∀ a b, b ∈ entailments a → entailments b ⊆ entailments a

namespace Geometry

variable {F : Type*} (G : Geometry F)

/-- A feature is among another's entailments iff its entailments are among the other's. -/
theorem mem_entailments_iff_subset {a b : F} :
    b ∈ G.entailments a ↔ G.entailments b ⊆ G.entailments a :=
  ⟨G.entailments_subset_of_mem a b, fun h => h (G.mem_entailments_self b)⟩

/-- Every two features of the geometry entail a common feature. -/
def MismatchResolution [DecidableEq F] : Prop :=
  ∀ a ∈ G.nodes, ∀ b ∈ G.nodes, (G.entailments a ∩ G.entailments b).Nonempty

instance [DecidableEq F] : Decidable G.MismatchResolution := by
  unfold MismatchResolution; infer_instance

end Geometry

end Minimalist
