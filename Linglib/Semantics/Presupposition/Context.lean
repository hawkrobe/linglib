module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Discourse.CommonGround

/-!
# Presuppositions in context

A presupposition (`PartialProp W`) is satisfied in a context set (`Set W`) when the context
entails it, in the tradition of [stalnaker-1974] and [heim-1983], and projects otherwise. Where
it is satisfied is its local context: [karttunen-1974-presupposition] gives the second argument
of a conjunction or a conditional the context updated with the first argument's content, the
second disjunct the context updated with its negation, and the first argument, or the argument
of negation, the context itself. `Connective.localContext` is that table. Theories of projection
agree on it and differ in why it holds, so each proves it of its own mechanism: Karttunen's
filtering connectives are satisfaction in it (`presupSatisfied_andFilter` and its siblings),
Heim's context change potentials evaluate their second argument in it
(`Semantics/Dynamic/Partial.lean`), and [schlenker-2009] derives it from transparency. The
theories part at disjunction, where the table is asymmetric and symmetric filtering is
`PartialProp.orKPSymmetric`.

## Main declarations

* `presupSatisfied`, `presupProjects` — the context entails the presupposition, or does not.
* `Connective`, `Connective.localContext` — the local context of a connective's second argument.
* `presupSatisfied_andFilter`, `presupSatisfied_impFilter`, `presupSatisfied_orFilter` — the
  filtering connectives are satisfaction in the local contexts.

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

namespace Context

/-- A presupposition is satisfied in the context `c` when the context entails it. -/
abbrev presupSatisfied (c : Set W) (p : PartialProp W) : Prop := c ⊆ p.presup

/-- A presupposition projects from the context `c` when the context does not entail it. -/
abbrev presupProjects (c : Set W) (p : PartialProp W) : Prop :=
  ¬ presupSatisfied c p

end Context

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

namespace Context

open Connective

variable {C : Set W} {p q : PartialProp W}

/-- Karttunen's filtering conjunction is satisfied in a context when the first conjunct is and
the second is satisfied in its local context. -/
theorem presupSatisfied_andFilter :
    presupSatisfied C (p.andFilter q) ↔
      presupSatisfied C p ∧ presupSatisfied (conj.localContext C p.assertion) q :=
  ⟨fun h ↦ ⟨fun _ hw ↦ (h hw).1, fun _ hw ↦ (h hw.1).2 hw.2⟩,
    fun h _ hw ↦ ⟨h.1 hw, fun ha ↦ h.2 ⟨hw, ha⟩⟩⟩

/-- Karttunen's filtering conditional is satisfied in a context when the antecedent is and the
consequent is satisfied in its local context. -/
theorem presupSatisfied_impFilter :
    presupSatisfied C (p.impFilter q) ↔
      presupSatisfied C p ∧ presupSatisfied (cond.localContext C p.assertion) q :=
  presupSatisfied_andFilter

/-- Karttunen's filtering disjunction is satisfied in a context when the first disjunct is and
the second is satisfied in its local context. -/
theorem presupSatisfied_orFilter :
    presupSatisfied C (p.orFilter q) ↔
      presupSatisfied C p ∧ presupSatisfied (disj.localContext C p.assertion) q :=
  ⟨fun h ↦ ⟨fun _ hw ↦ (h hw).1, fun _ hw ↦ (h hw.1).2 hw.2⟩,
    fun h _ hw ↦ ⟨h.1 hw, fun ha ↦ h.2 ⟨hw, ha⟩⟩⟩

end Context

end Presupposition
