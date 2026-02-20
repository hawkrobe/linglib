import Mathlib.CategoryTheory.Category.Basic
import Linglib.Core.Partition

/-!
# Category of QUD Partitions

Category of QUD (Question Under Discussion) partitions over a fixed type `M`,
with refinement witnesses as morphisms.

This is a **thin** category (at most one morphism between any two objects):
refinement is a preorder on partitions, and all refinement proofs between the
same QUDs are equal by proof irrelevance.

`QUD.refines_refl` and `QUD.refines_trans` from `Partition.lean` provide the
categorical identity and composition.
-/

namespace Core.Categorical

/-- Bundled QUD: an object in the partition category for a fixed meaning type. -/
structure BundledQUD (M : Type*) where
  /-- The underlying QUD partition. -/
  qud : QUD M

/-- Hom type for the QUD category: a refinement witness lifted to `Type`.

    `QUD.refines` is `Prop`-valued; `PLift` promotes it to `Type 0` so it
    can serve as a `CategoryTheory.Category` hom type. The category is thin
    (at most one morphism between any two objects). -/
def QUDHom {M : Type*} (q q' : BundledQUD M) : Type :=
  PLift (QUD.refines q.qud q'.qud)

/-- QUDHom is proof-irrelevant: at most one morphism between any two objects. -/
instance {M : Type*} {q q' : BundledQUD M} : Subsingleton (QUDHom q q') :=
  ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩

instance (M : Type*) : CategoryTheory.Category (BundledQUD M) where
  Hom := QUDHom
  id q := ⟨QUD.refines_refl q.qud⟩
  comp f g := ⟨QUD.refines_trans f.down g.down⟩

/-- The trivial partition is terminal: every QUD refines it. -/
def QUDHom.toTrivial {M : Type*} (q : BundledQUD M) :
    QUDHom q ⟨QUD.trivial⟩ :=
  ⟨QUD.all_refine_trivial q.qud⟩

/-- Compose of two QUDs refines the left factor. -/
def QUDHom.composeLeft {M : Type*} (q₁ q₂ : BundledQUD M) :
    QUDHom ⟨q₁.qud * q₂.qud⟩ q₁ :=
  ⟨QUD.compose_refines_left q₁.qud q₂.qud⟩

end Core.Categorical
