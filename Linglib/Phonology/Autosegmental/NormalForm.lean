/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Data.Fintype.Sort
import Linglib.Phonology.Autosegmental.MixedGraph

/-!
# Normal forms of autosegmental representations

Every finite representation is isomorphic to its **normal form**: the same
representation reindexed onto the canonical vertex type `(i : ι) × Fin nᵢ`,
each tier fiber enumerated in ascending precedence order
(`IsTierOrdered.isStrictTotalOrder` → `linearOrderOfSTO` → `monoEquivOfFin`).
The normal form is a `Representation` — not a separate carrier — and
`normalizeIso` is definitional: `normalize` pulls the graph back along the
enumeration equivalence.

Strictness lives where Mac Lane coherence puts it: on the skeleton. The monoid
of isomorphism classes `Skeleton (Representation t)` carries concatenation with
associativity on the nose (`CategoryTheory.Monoidal.Skeleton`), and
`toSkeleton_normalize` says `normalize` chooses representatives.

## Main definitions

* `Representation.fiber`, `Representation.vertexEquiv`: the tier fibers of a
  finite representation and the canonical enumeration of its vertex type.
* `Representation.normalize`: the normal form, a `Representation` on the
  canonical vertex type.

## Main results

* `Representation.normalizeIso`: `X.normalize ≅ X`.
* `Representation.arcs_normalize`: on normal forms the arcs are the ascending
  position order — the classification content, [jardine-heinz-2015]'s tiered
  presentation recovered as a theorem.
* `Representation.toSkeleton_normalize`: normal forms represent their
  isomorphism class in the skeleton monoid.
-/

namespace Autosegmental

open CategoryTheory

variable {ι : Type*} {τ : ι → Type*}

section NormalForm
open scoped Classical

/-- Fiber of the tier coloring at `i`: vertices of `X.obj` labelled to tier `i`.
    Under `IsTierOrdered` its arcs form a strict total order, and under
    `Finite X.obj.V` it is finite — the two ingredients `monoEquivOfFin`
    needs to enumerate the fiber as `Fin _`. -/
def Representation.fiber (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι)) (i : ι) :
    Type _ := {v : X.obj.V // (X.obj.label v).1 = i}

variable {X : Representation (Sigma.fst : ((i : ι) × τ i) → ι)}

/-- The `τ i` component of a fiber element, extracted from the labeling by
    transporting along the fiber's tier-membership witness. -/
def Representation.fiberLabel {i : ι} (v : X.fiber i) : τ i :=
  v.property ▸ (X.obj.label v.val).2

instance Representation.fiber.instFinite [Finite X.obj.V] (i : ι) : Finite (X.fiber i) :=
  Subtype.finite

/-- The arcs restricted to a tier fiber form a strict total order — the classed
    form of Axioms 1–2 applied to the tier coloring `Sigma.fst`. -/
instance Representation.fiber.instIsStrictTotalOrder (i : ι) :
    IsStrictTotalOrder (X.fiber i) (fun a b => X.obj.graph.arcs.Adj a.val b.val) :=
  X.property.1.isStrictTotalOrder i

/-- Classical linear order on the fiber, from `IsStrictTotalOrder` via
    `linearOrderOfSTO`. -/
noncomputable instance Representation.fiber.instLinearOrder (i : ι) :
    LinearOrder (X.fiber i) := by
  classical
  exact linearOrderOfSTO (fun a b : X.fiber i => X.obj.graph.arcs.Adj a.val b.val)

/-- The number of tier-`i` vertices. -/
noncomputable def Representation.tierLen (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι))
    [Finite X.obj.V] (i : ι) : ℕ :=
  letI := Fintype.ofFinite (X.fiber i)
  Fintype.card (X.fiber i)

/-- The canonical enumeration of a finite representation's vertex type: tier
    fibers in ascending precedence order, assembled over the tier index. -/
noncomputable def Representation.vertexEquiv [Finite X.obj.V] :
    ((i : ι) × Fin (X.tierLen i)) ≃ X.obj.V :=
  letI : ∀ i : ι, Fintype (X.fiber i) := fun _ => Fintype.ofFinite _
  (Equiv.sigmaCongrRight
    (fun i : ι => (monoEquivOfFin (X.fiber i) rfl).toEquiv)).trans
    (Equiv.sigmaFiberEquiv (fun v : X.obj.V => (X.obj.label v).1))

/-- The tier-`i` label word: the fiber's labels read off in ascending precedence
    order — the tier content the normal form canonicalizes. -/
noncomputable def Representation.tierWord [Finite X.obj.V] (i : ι) : List (τ i) :=
  letI := Fintype.ofFinite (X.fiber i)
  List.ofFn fun p : Fin (X.tierLen i) => X.fiberLabel (monoEquivOfFin (X.fiber i) rfl p)

/-- The normal form: `X` reindexed onto the canonical vertex type by pulling
    edges, arcs, and labels back along `vertexEquiv`. A `Representation` — the
    normal form is not a separate kind of object. -/
noncomputable def Representation.normalize
    (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι)) [Finite X.obj.V] :
    Representation (Sigma.fst : ((i : ι) × τ i) → ι) where
  obj :=
    { V := (i : ι) × Fin (X.tierLen i)
      graph :=
        { edges := X.obj.graph.edges.comap X.vertexEquiv
          arcs := ⟨fun v w => X.obj.graph.arcs.Adj (X.vertexEquiv v) (X.vertexEquiv w)⟩ }
      label := fun v => X.obj.label (X.vertexEquiv v) }
  property :=
    ⟨⟨fun _ _ h => X.property.1.tier_eq h,
      fun _ _ hne htier => X.property.1.total (fun hv => hne (X.vertexEquiv.injective hv)) htier,
      fun _ h => X.property.1.irrefl _ h,
      fun _ _ _ huv hvw => X.property.1.trans huv hvw⟩,
     fun _ _ hadj harc => X.property.2 hadj harc⟩

/-- The normal form is isomorphic to the original — definitionally, since
    `normalize` is a pullback along `vertexEquiv`. -/
noncomputable def Representation.normalizeIso [Finite X.obj.V] : X.normalize ≅ X :=
  Representation.mkIso
    { toEquiv := X.vertexEquiv
      edges_iff := fun _ _ => Iff.rfl
      arcs_iff := fun _ _ => Iff.rfl
      label_comp := fun _ => rfl }

/-- Normal forms represent their isomorphism class: `normalize` is a section of
    the quotient onto the skeleton, where the monoid of iso classes carries
    strictly associative concatenation (`CategoryTheory.Monoidal.Skeleton`). -/
theorem Representation.toSkeleton_normalize [Finite X.obj.V] :
    toSkeleton (X.normalize) = toSkeleton X :=
  Quotient.sound ⟨X.normalizeIso⟩

end NormalForm

end Autosegmental
