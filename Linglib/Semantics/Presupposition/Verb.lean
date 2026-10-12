module

public import Linglib.Syntax.Category.Verb.Defs

/-!
# Presupposition triggers among verbs

A verb is factive when its entry records one of Karttunen's factivity classes; veridicality is an
entailment and does not make a verb factive. A verb triggers a presupposition when it is factive,
presupposing its complement; phasal, presupposing the prior state (`Aspect.Phasal.denote`);
implicative, presupposing that what it asserts is a condition for its complement
(`Implicative.sentence`); or an occasion verb, presupposing an eventuality that gave its agent
reason to act. Roberts and Simons explain the first two as preconditions of the event the verb
describes, and Solstad and Bott identify the last.

## References

* [karttunen-1971]
* [karttunen-1971b]
* [roberts-simons-2024]
* [solstad-bott-2024]
-/

@[expose] public section

namespace Verb

/-- The verb is factive when it carries a [karttunen-1971b] factivity class. -/
def IsFactive (v : Verb) : Prop := v.factivity ≠ none

instance : DecidablePred IsFactive := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The verb triggers a presupposition when it is factive, phasal, implicative or an occasion
verb. -/
def IsTrigger (v : Verb) : Prop :=
  v.IsFactive ∨ v.phasal ≠ none ∨ v.implicative ≠ ⊥ ∨ v.senseTag = .occasion

instance : DecidablePred IsTrigger := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

end Verb
