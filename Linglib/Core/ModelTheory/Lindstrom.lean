module

public import Mathlib.ModelTheory.Bundled
public import Mathlib.Order.Hom.Lattice

/-!
# Lindström generalized quantifiers

`[UPSTREAM]` candidate. A generalized quantifier over a language `L`, in Lindström's sense, is a
class of `L`-structures closed under isomorphism, so the invariance Mostowski imposed on
quantifiers is part of the type rather than a side condition on a denotation. These classes form
a Boolean subalgebra of the powerset of `Bundled L.Structure`. Each sentence defines one, its
class of models, and the Ehrenfeucht–Fraïssé results in this directory decide which classes arise
this way, the classes Lindström writes `EC`.

## Main definitions

* `FirstOrder.Language.LindstromQuantifier`: an isomorphism-invariant class of `L`-structures.
* `FirstOrder.Language.LindstromQuantifier.ofSentence`: the class of models of a sentence.
* `FirstOrder.Language.LindstromQuantifier.holdsHom`: the embedding into the powerset algebra.

## Implementation notes

Lindström restricts quantifiers to classes of relational structures; here `L` may have function
symbols, which costs nothing since isomorphism invariance is the only condition.

## References

* [lindstrom-1966]
* [mostowski-1957]
-/

@[expose] public section

universe u v w

namespace FirstOrder.Language

open CategoryTheory
open scoped FirstOrder

/-- A Lindström quantifier over `L` is a class of `L`-structures closed under `L`-isomorphism. -/
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

/-- `holdsHom` is the embedding of the quantifiers into the powerset algebra
`Set (Bundled L.Structure)` as a bounded lattice homomorphism; it also preserves complements
(`holds_compl`). -/
def holdsHom :
    BoundedLatticeHom (LindstromQuantifier.{u, v, w} L) (Set (Bundled.{w} L.Structure)) where
  toFun := holds
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

/-- The quantifier defined by a sentence holds of exactly the models of the sentence. -/
def ofSentence (φ : L.Sentence) : LindstromQuantifier.{u, v, w} L where
  holds := {M | M ⊨ φ}
  iso_inv := fun ⟨e⟩ => StrongHomClass.realize_sentence e φ

@[simp] theorem mem_holds_ofSentence {φ : L.Sentence} {M : Bundled.{w} L.Structure} :
    M ∈ (ofSentence φ).holds ↔ M ⊨ φ := Iff.rfl

end LindstromQuantifier

end FirstOrder.Language
