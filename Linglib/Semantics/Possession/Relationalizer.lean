module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Relational nouns and the relationalizer

A relational noun denotes a family `R : ι → α` of properties indexed by possessors, `R x` being
the property of standing in the noun's relation to `x`, and a sortal noun denotes one property
`P : α`. The properties form a lattice, such as `κ → Prop` or the situation-indexed
`κ → σ → Prop`, and the type-shifters between the two kinds of noun are its operations. Barker's
relationalizer `π` opens a possessor slot on a sortal noun by meeting it with a free relation.
The possessor slot of a relational noun is closed by the supremum `⨆ x, R x`, the property of
standing in the relation to something: this is Barker's detransitivizer `Ex`, Adamson's
alienator, Partee and Borschev's first projection, and the range operator of Hanink and
Koontz-Garboden.

## Main definitions

* `Possession.π`: the relationalizer, `π P R x = P ⊓ R x`.
* `Possession.dom`: the possessors of a `P`, `dom P R x ↔ ∃ y, P y ∧ R x y`.

## Main statements

* `Possession.π_iSup_self`: a relational noun whose possessor slot is closed and then reopened
  by its own relation is the noun itself, so the lexical reading of a possessive is one
  resolution of the free relation.
* `Possession.iSup_π`: closing the possessor slot of a relationalized noun keeps the sortal noun.

## References

* [barker-2011]
* [adamson-2024]
* [partee-borschev-2003]
* [hanink-koontz-garboden-2025]
* [peters-westerstahl-2006]
-/

@[expose] public section

namespace Possession

variable {ι κ α : Type*}

/-! ### The relationalizer -/

/-- The relationalizer opens a possessor slot on a sortal noun `P` through a relation `R`, so
that `π P R x` is the property of being a `P` that stands in `R` to `x`. -/
def π [Min α] (P : α) (R : ι → α) : ι → α := fun x ↦ P ⊓ R x

theorem π_apply [Min α] (P : α) (R : ι → α) (x : ι) : π P R x = P ⊓ R x := rfl

@[simp] theorem π_top [SemilatticeInf α] [OrderTop α] (R : ι → α) : π ⊤ R = R :=
  funext fun _ ↦ top_inf_eq _

/-- Closing the possessor slot of a relationalized noun keeps the sortal noun and closes the
relation. -/
theorem iSup_π [Order.Frame α] (P : α) (R : ι → α) : ⨆ x, π P R x = P ⊓ ⨆ x, R x :=
  (inf_iSup_eq P R).symm

/-- A relational noun whose possessor slot is closed and then reopened by its own relation is the
noun itself. -/
@[simp] theorem π_iSup_self [CompleteLattice α] (R : ι → α) : π (⨆ x, R x) R = R :=
  funext fun x ↦ inf_eq_right.2 (le_iSup R x)

/-! ### Possessors -/

/-- The possessors of a `P` are the individuals that stand in `R` to something satisfying `P`. -/
def dom (P : κ → Prop) (R : ι → κ → Prop) (x : ι) : Prop := ∃ y, P y ∧ R x y

instance [Fintype κ] {P : κ → Prop} {R : ι → κ → Prop} [DecidablePred P]
    [∀ x, DecidablePred (R x)] : DecidablePred (dom P R) :=
  fun x ↦ inferInstanceAs (Decidable (∃ y, P y ∧ R x y))

/-- The possessors of something in a relation's range, when possessing is the relation itself,
are the individuals that bear the relation to something. -/
theorem dom_iSup_self (R : ι → κ → Prop) (x : ι) : dom (⨆ x, R x) R x ↔ ∃ y, R x y :=
  iff_of_eq (congrArg (fun S : ι → κ → Prop ↦ ∃ y, S x y) (π_iSup_self R))

end Possession
