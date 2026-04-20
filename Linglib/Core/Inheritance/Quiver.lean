import Linglib.Core.Inheritance.Basic
import Mathlib.Combinatorics.Quiver.Path

/-!
# Inheritance Quiver — labeled-multigraph view of a network

@cite{hudson-2010}'s WG networks are labeled directed multigraphs:
multiple parallel edges between the same two nodes are allowed (e.g. a
node may have both an `isA` link and a property link to another), and
each edge carries a `LinkKind` plus an optional label of type `R`. This
is exactly mathlib's `Quiver V` (where `Hom a b : Type` rather than
`Prop` so parallel edges remain distinguishable).

The instance is placed on a wrapper type `Vertex net` rather than directly
on `α`, because a single node type may appear in multiple unrelated
networks. The wrapper is the idiomatic mathlib pattern (cf. `OrderDual`,
`Multiplicative`); see `Core.Inheritance.Order` for the parallel
`Preorder` instance on `IsAOrder net`.

## What the Quiver layer buys

- `Quiver.Path` for composable sequences of links — the natural type for
  derivation chains in default inheritance and Best Fit.
- Quiver homomorphisms `Vertex net₁ ⥤q Vertex net₂` for structure-preserving
  network maps (the categorical "morphism between WG networks").
- The "one network" thesis (kinship and syntax in the same category)
  becomes: both `Vertex englishAuxNet` and `Vertex kinshipNet` are objects
  of the category of quivers, and a Hudson-style cross-domain analogy is
  a quiver homomorphism between them.

The path-versus-`IsA` bridge (`Path → IsA` for paths consisting only of
isA links, and the converse) is left as future work; the current file
sets up the categorical scaffolding so consumers can begin using
`⟶`/`Path.cons`/`Hom.toPath` directly.
-/

set_option autoImplicit false

namespace Core.Inheritance

variable {α R : Type} [DecidableEq α] [DecidableEq R]

/-- A node type viewed as the vertex set of a particular network's quiver.
Definitionally equal to `α`, but carries the `Quiver` instance. -/
def Vertex (_ : Network α R) : Type := α

namespace Vertex

/-- The `Quiver` instance: a hom from `a` to `b` is a link in the network
whose source and target match. Parallel links (different kinds, different
labels, same endpoints) are distinct hom elements — `Quiver.Hom` is a
`Type`, not a `Prop`. -/
instance quiver (net : Network α R) : Quiver (Vertex net) where
  Hom a b := { l : Link α R // l ∈ net.links ∧ l.source = a ∧ l.target = b }

/-- The underlying subtype of a quiver hom. -/
abbrev Hom (net : Network α R) (a b : α) : Type :=
  { l : Link α R // l ∈ net.links ∧ l.source = a ∧ l.target = b }

/-- An isA link packaged as a `Vertex.Hom`. Use `Quiver.Hom.toPath` to lift
to a length-1 `Quiver.Path`. -/
def isAHom (net : Network α R) {a b : α}
    (h : ⟨LinkKind.isA, a, b, none⟩ ∈ net.links) :
    Hom net a b :=
  ⟨⟨.isA, a, b, none⟩, h, rfl, rfl⟩

end Vertex

end Core.Inheritance
