module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Discourse.CommonGround

/-!
# Presuppositions in context

A context set (`Set W`) admits a sentence with a presupposition (`PartialProp W`) when it
entails the presupposition, [heim-1983]'s "c admits φ" and [karttunen-1974-presupposition]'s
"c satisfies the presuppositions of φ", in the tradition of [stalnaker-1974]; otherwise the
presupposition projects. An embedded presupposition is checked in its local context:
[karttunen-1974-presupposition] gives the second argument of a conjunction or a conditional the
context updated with the first argument's content, the second disjunct the context updated with
its negation, and the first argument, or the argument of negation, the context itself.
`Connective.localContext` is that table. Theories of projection agree on it and differ in why it
holds, so each proves it of its own mechanism: Karttunen's filtering connectives are admittance
in it (`PartialProp.admits_andFilter` and its siblings), Heim's context change potentials
evaluate their second argument in it (`Semantics/Dynamic/Partial.lean`), and [schlenker-2009]
derives it from transparency. The theories part at disjunction, where the table is asymmetric
and symmetric filtering is `PartialProp.orKPSymmetric`.

## Main declarations

* `PartialProp.Admits` — the context entails the presupposition.
* `Connective`, `Connective.localContext` — the local context of a connective's second argument.
* `PartialProp.admits_andFilter`, `PartialProp.admits_impFilter`,
  `PartialProp.admits_orFilter` — the filtering connectives are admittance in the local
  contexts.

## References

* [stalnaker-1974]
* [heim-1983]
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

/-- The binary connectives of [karttunen-1974-presupposition]'s table of local contexts. -/
inductive Connective
  | conj
  | cond
  | disj
  deriving DecidableEq, Fintype

/-- The local context of a connective's second argument in the context `C`, where `A` is the
first argument's content: `C` updated with `A` for a conjunction or a conditional, and with its
negation for a disjunction. -/
def Connective.localContext (C A : Set W) : Connective → Set W
  | conj => C ∩ A
  | cond => C ∩ A
  | disj => C ∩ Aᶜ

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
