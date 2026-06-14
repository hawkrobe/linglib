import Mathlib.ModelTheory.Bundled

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
* `compl`/`inf`/`sup` — the Boolean algebra of generalized quantifiers (closed under
  complement, intersection, union, since iso-invariance is preserved).
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

/-- Outer negation `¬Q`: the structures *not* in `Q`. (`every ↦ not-every`.) -/
def compl (Q : LindstromQuantifier.{u, v, w} L) : LindstromQuantifier.{u, v, w} L where
  holds := Q.holdsᶜ
  iso_inv h := not_congr (Q.iso_inv h)

/-- Meet `Q ⊓ R`: structures in both classes (conjunction of quantifiers). -/
def inf (Q R : LindstromQuantifier.{u, v, w} L) : LindstromQuantifier.{u, v, w} L where
  holds := Q.holds ∩ R.holds
  iso_inv h := and_congr (Q.iso_inv h) (R.iso_inv h)

/-- Join `Q ⊔ R`: structures in either class (disjunction of quantifiers). -/
def sup (Q R : LindstromQuantifier.{u, v, w} L) : LindstromQuantifier.{u, v, w} L where
  holds := Q.holds ∪ R.holds
  iso_inv h := or_congr (Q.iso_inv h) (R.iso_inv h)

@[simp] theorem compl_holds (Q : LindstromQuantifier.{u, v, w} L) : Q.compl.holds = Q.holdsᶜ := rfl
@[simp] theorem inf_holds (Q R : LindstromQuantifier.{u, v, w} L) :
    (Q.inf R).holds = Q.holds ∩ R.holds := rfl
@[simp] theorem sup_holds (Q R : LindstromQuantifier.{u, v, w} L) :
    (Q.sup R).holds = Q.holds ∪ R.holds := rfl

@[simp] theorem compl_compl (Q : LindstromQuantifier.{u, v, w} L) : Q.compl.compl = Q := by
  ext : 1; simp

end LindstromQuantifier

end FirstOrder.Language
