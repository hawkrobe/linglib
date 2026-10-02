module

public import Linglib.Syntax.Category.Verb.Defs

/-!
# Factivity and trigger status of a verb entry

A verb entry is factive when it carries one of Karttunen's factivity classes; veridicality is an
entailment and does not make it factive. A verb presupposes its complement by factivity or as a
change of state. Its trigger type follows from its event structure, after Roberts and Simons: it
is a soft trigger when it presupposes its complement or, after Solstad and Bott, when it is an
occasion verb, and an implicative trigger when it carries an implication signature.

## References

* [karttunen-1971]
* [karttunen-1971b]
* [roberts-simons-2024]
* [solstad-bott-2024]
-/

@[expose] public section

namespace Verb

variable {v : Verb}

/-- The verb is factive when it carries a [karttunen-1971b] factivity class. -/
def IsFactive (v : Verb) : Prop := v.factivity ≠ none

instance : DecidablePred IsFactive := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The verb presupposes its complement, by factivity or as a change of state. -/
def PresupposesComplement (v : Verb) : Prop := v.IsFactive ∨ v.phasal ≠ none

instance : DecidablePred PresupposesComplement := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The kind of presupposition trigger the verb is, from its event structure. The soft/hard
distinction is not operationalized, so `.soft` stands for both the complement presupposition
and the occasion presupposition. -/
def triggerType? (v : Verb) : Option Presupposition.TriggerType :=
  if v.PresupposesComplement then some .soft
  else if v.implicative ≠ none then some .implicative
  else if v.senseTag = .occasion then some .soft
  else none

/-- The verb is a presupposition trigger. -/
def IsTrigger (v : Verb) : Prop := v.triggerType? ≠ none

instance : DecidablePred IsTrigger := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

@[simp] theorem isFactive_iff : v.IsFactive ↔ v.factivity ≠ none := Iff.rfl

theorem isFactive_iff_exists : v.IsFactive ↔ ∃ c, v.factivity = some c :=
  Option.ne_none_iff_exists'

@[simp] theorem not_isFactive_iff : ¬ v.IsFactive ↔ v.factivity = none := not_not

theorem IsFactive.presupposesComplement (h : v.IsFactive) : v.PresupposesComplement := Or.inl h

theorem presupposesComplement_of_phasal (h : v.phasal ≠ none) : v.PresupposesComplement :=
  Or.inr h

theorem triggerType_of_presupposesComplement (h : v.PresupposesComplement) :
    v.triggerType? = some .soft := by simp [triggerType?, h]

theorem triggerType_eq_none_iff :
    v.triggerType? = none ↔
      ¬ v.PresupposesComplement ∧ v.implicative = none ∧ v.senseTag ≠ .occasion := by
  unfold triggerType?; split_ifs <;> simp_all

@[simp] theorem isTrigger_iff :
    v.IsTrigger ↔ v.PresupposesComplement ∨ v.implicative ≠ none ∨ v.senseTag = .occasion := by
  simp only [IsTrigger, ne_eq, triggerType_eq_none_iff]; tauto

theorem IsFactive.isTrigger (h : v.IsFactive) : v.IsTrigger :=
  isTrigger_iff.2 (.inl (.inl h))

end Verb
