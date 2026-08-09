import Mathlib.ModelTheory.Bundled
import Mathlib.Order.Hom.Lattice

/-!
# Lindström generalized quantifiers

`[UPSTREAM]` candidate. A (Lindström 1966; Mostowski 1957 for type `⟨1⟩`) generalized
quantifier over a language `L` is an **isomorphism-invariant class of `L`-structures**:
the field `holds`, a `Set (Bundled L.Structure)` closed under `L`-isomorphism. The
iso-invariance (Mostowski's QUANT / permutation invariance, in its general
type-`⟨1ⁿ⟩` form) is *part of the type*, not a side condition checked on a denotation.

This is the same shape as mathlib's `FirstOrder.Language.age` (an iso-invariant
`Set (Bundled L.Structure)`; cf. `age.is_equiv_invariant`) — a thin layer over
`Bundled`/`≃[L]`, not a new framework. The first-order *definability* of such a class
is decided by the Ehrenfeucht–Fraïssé apparatus in this directory
(`not_foDefinable_of_nEquiv`); its per-model *realization* (a determiner denotation)
and the linguistic generalized-quantifier API live downstream in `Semantics.Quantification`.

## Main definitions

* `FirstOrder.Language.LindstromQuantifier` — an iso-invariant class of `L`-structures.
* `BooleanAlgebra (LindstromQuantifier L)` — the Boolean algebra of generalized quantifiers
  (`Qᶜ` outer negation, `Q ⊓ R`/`Q ⊔ R` conjunction/disjunction, `⊤`/`⊥` the trivial quantifiers),
  obtained by pulling the powerset algebra back along the injective `holds`; `holdsHom` bundles that
  embedding as a `BoundedLatticeHom`.
-/

universe u v w

namespace FirstOrder.Language

open CategoryTheory
open scoped FirstOrder

/-- A (Lindström) generalized quantifier over `L`: an isomorphism-invariant class of
`L`-structures. The defining closure under `L`-isomorphism is built into the type. -/
@[ext]
structure LindstromQuantifier (L : Language.{u, v}) where
  /-- The class of structures the quantifier holds of. -/
  holds : Set (Bundled.{w} L.Structure)
  /-- The class is closed under `L`-isomorphism (Mostowski QUANT, general form). -/
  iso_inv : ∀ {M N : Bundled.{w} L.Structure}, Nonempty (M ≃[L] N) → (M ∈ holds ↔ N ∈ holds)

namespace LindstromQuantifier

variable {L : Language.{u, v}}

/-! ### Boolean-algebra structure

The iso-invariant classes are a sub-Boolean-algebra of `Set (Bundled L.Structure)` — closed under
complement, finite meet/join, `⊤` (all structures) and `⊥` (none), because `L`-isomorphism is an
equivalence. `holds` is the injective embedding, so the algebra is pulled back along it: `Qᶜ` is
outer negation (`every ↦ not-every`), `Q ⊓ R`/`Q ⊔ R` are conjunction/disjunction. -/

instance : LE (LindstromQuantifier.{u, v, w} L) := ⟨fun Q R => Q.holds ≤ R.holds⟩
instance : LT (LindstromQuantifier.{u, v, w} L) := ⟨fun Q R => Q.holds < R.holds⟩
instance : Max (LindstromQuantifier.{u, v, w} L) :=
  ⟨fun Q R => ⟨Q.holds ∪ R.holds, fun h => or_congr (Q.iso_inv h) (R.iso_inv h)⟩⟩
instance : Min (LindstromQuantifier.{u, v, w} L) :=
  ⟨fun Q R => ⟨Q.holds ∩ R.holds, fun h => and_congr (Q.iso_inv h) (R.iso_inv h)⟩⟩
instance : Top (LindstromQuantifier.{u, v, w} L) := ⟨⟨Set.univ, fun _ => Iff.rfl⟩⟩
instance : Bot (LindstromQuantifier.{u, v, w} L) := ⟨⟨∅, fun _ => Iff.rfl⟩⟩
instance : Compl (LindstromQuantifier.{u, v, w} L) :=
  ⟨fun Q => ⟨Q.holdsᶜ, fun h => not_congr (Q.iso_inv h)⟩⟩
instance : SDiff (LindstromQuantifier.{u, v, w} L) :=
  ⟨fun Q R => ⟨Q.holds \ R.holds,
    fun h => by simp only [Set.mem_sdiff]; exact and_congr (Q.iso_inv h) (not_congr (R.iso_inv h))⟩⟩
instance : HImp (LindstromQuantifier.{u, v, w} L) :=
  ⟨fun Q R => ⟨Q.holds ⇨ R.holds,
    fun h => by simp only [himp_eq]; exact or_congr (R.iso_inv h) (not_congr (Q.iso_inv h))⟩⟩

theorem holds_injective : Function.Injective (holds : LindstromQuantifier.{u, v, w} L → _) :=
  fun _ _ h => LindstromQuantifier.ext h

/-- The Boolean algebra of generalized quantifiers over `L`, pulled back along the injective `holds`
embedding into the powerset algebra `Set (Bundled L.Structure)`. -/
instance : BooleanAlgebra (LindstromQuantifier.{u, v, w} L) :=
  Function.Injective.booleanAlgebra holds holds_injective
    (fun {_ _} => Iff.rfl) (fun {_ _} => Iff.rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem holds_sup (Q R : LindstromQuantifier.{u, v, w} L) :
    (Q ⊔ R).holds = Q.holds ∪ R.holds := rfl
@[simp] theorem holds_inf (Q R : LindstromQuantifier.{u, v, w} L) :
    (Q ⊓ R).holds = Q.holds ∩ R.holds := rfl
@[simp] theorem holds_compl (Q : LindstromQuantifier.{u, v, w} L) : Qᶜ.holds = Q.holdsᶜ := rfl
@[simp] theorem holds_top : (⊤ : LindstromQuantifier.{u, v, w} L).holds = Set.univ := rfl
@[simp] theorem holds_bot : (⊥ : LindstromQuantifier.{u, v, w} L).holds = ∅ := rfl

/-- `holds` bundled: the embedding of the generalized-quantifier Boolean algebra into the powerset
algebra `Set (Bundled L.Structure)` is a `BoundedLatticeHom` (it also preserves `ᶜ`, see
`holds_compl`) — the Lindström analogue of `Core.Order.holdsHom`. -/
def holdsHom :
    BoundedLatticeHom (LindstromQuantifier.{u, v, w} L) (Set (Bundled.{w} L.Structure)) where
  toFun := holds
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

end LindstromQuantifier

end FirstOrder.Language
