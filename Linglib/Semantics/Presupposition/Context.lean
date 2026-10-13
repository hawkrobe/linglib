module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Core.Relation.SetRel
public import Linglib.Discourse.CommonGround

/-!
# Presuppositions in context

A context set admits a sentence with a presupposition when it entails the presupposition, in the
tradition of Stalnaker, Karttunen and Heim. An embedded clause is checked in its local context,
the image of the context under the relation that takes each world to the worlds at which the
clause is evaluated. The local context entails a proposition iff the context entails its core
along the relation, so a sentence inherits the core of an embedded clause's presupposition
(`PartialProp.admits_image_iff`), which entails that presupposition when the relation is
reflexive (`SetRel.core_subset_self`).

Karttunen's table of local contexts gives the relations of the connectives. A first argument and
the argument of negation are evaluated along the identity. In the second argument of a
conjunction or a conditional a world sees itself where the first argument holds, and in a second
disjunct where it fails (`Connective.rel`). The complement of an attitude verb is evaluated along
the subject's doxastic accessibility, so its local context is the beliefs attributed to the
subject in the context, and the report presupposes that the subject believes what the complement
presupposes. Theories of projection agree on the table and differ in why it holds. They part at
disjunction, where the table is asymmetric and symmetric filtering is
`PartialProp.orKPSymmetric`.

## Main declarations

* `PartialProp.Admits`: the context entails the presupposition.
* `PartialProp.admits_image_iff`: a local context admits a sentence iff the context entails the
  core of its presupposition.
* `Connective.localContext`, `Connective.rel`: the local context of the second argument of a
  connective, and the relation whose image it is (`Connective.localContext_eq_image`).
* `PartialProp.admits_andFilter`, `PartialProp.admits_impFilter`, `PartialProp.admits_orFilter`:
  the filtering connectives are admittance in the local contexts.

## References

* [stalnaker-1974]
* [heim-1983]
* [heim-1992]
* [karttunen-1973]
* [karttunen-1974-presupposition]
* [peters-1979]
* [schlenker-2009]
-/

@[expose] public section

namespace Presupposition

variable {W : Type*}

/-- The context `c` admits `p` when it entails `p`'s presupposition; where it does not, the
presupposition projects. -/
abbrev PartialProp.Admits (p : PartialProp W) (c : Set W) : Prop := c ⊆ p.presup

/-- The local context along `R` admits `p` iff the context entails the core of `p`'s
presupposition along `R`. -/
theorem PartialProp.admits_image_iff {p : PartialProp W} {R : SetRel W W} {C : Set W} :
    p.Admits (R.image C) ↔ C ⊆ R.core p.presup :=
  SetRel.image_subset_iff

/-- The binary connectives of [karttunen-1974-presupposition]'s table of local contexts. -/
inductive Connective
  | conj
  | cond
  | disj
  deriving DecidableEq, Fintype

/-- The local context of a connective's second argument in the context `C`, where `A` is the
first argument's content. It is `C` updated with `A` for a conjunction or a conditional, and with
the negation of `A` for a disjunction. -/
def Connective.localContext (C A : Set W) : Connective → Set W
  | conj => C ∩ A
  | cond => C ∩ A
  | disj => C ∩ Aᶜ

/-- The relation along which the second argument of a connective is evaluated, where `A` is the
first argument's content. A world sees itself when it is in the local context of the trivial
context, so where `A` holds for a conjunction or a conditional and where it fails for a
disjunction. -/
def Connective.rel (A : Set W) (c : Connective) : SetRel W W := .ofSet (c.localContext Set.univ A)

/-- The local context of a connective's second argument is the image of the context under the
connective's relation. -/
theorem Connective.localContext_eq_image (c : Connective) (C A : Set W) :
    c.localContext C A = (c.rel A).image C := by
  cases c <;> simp [Connective.localContext, Connective.rel]

namespace PartialProp

open Connective

variable {C : Set W} {p q : PartialProp W}

/-- A context admits Karttunen's filtering conjunction when it admits the first conjunct and the
second conjunct's local context admits the second. -/
theorem admits_andFilter :
    (p.andFilter q).Admits C ↔ p.Admits C ∧ q.Admits (conj.localContext C p.assertion) :=
  ⟨fun h ↦ ⟨fun _ hw ↦ (h hw).1, fun _ hw ↦ (h hw.1).2 hw.2⟩,
    fun h _ hw ↦ ⟨h.1 hw, fun ha ↦ h.2 ⟨hw, ha⟩⟩⟩

/-- A context admits Karttunen's filtering conditional when it admits the antecedent and the
consequent's local context admits the consequent. -/
theorem admits_impFilter :
    (p.impFilter q).Admits C ↔ p.Admits C ∧ q.Admits (cond.localContext C p.assertion) :=
  admits_andFilter

/-- A context admits Karttunen's filtering disjunction when it admits the first disjunct and the
second disjunct's local context admits the second. -/
theorem admits_orFilter :
    (p.orFilter q).Admits C ↔ p.Admits C ∧ q.Admits (disj.localContext C p.assertion) :=
  ⟨fun h ↦ ⟨fun _ hw ↦ (h hw).1, fun _ hw ↦ (h hw.1).2 hw.2⟩,
    fun h _ hw ↦ ⟨h.1 hw, fun ha ↦ h.2 ⟨hw, ha⟩⟩⟩

end PartialProp

end Presupposition
