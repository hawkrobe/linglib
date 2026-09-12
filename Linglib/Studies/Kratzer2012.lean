import Mathlib.Data.Fintype.Prod
import Linglib.Semantics.Modality.Kratzer.Operators

/-!
# Kratzer (2012): Modals and Conditionals

This file formalizes the distinction the book's second chapter draws, in its typology of
conversational backgrounds, between realistic backgrounds representing evidence of things and
informational backgrounds representing the propositional content of a source of information.
A rumor that Roger was elected chief can feed either. As evidence of things it determines the
worlds that contain a counterpart of the rumor, produced the same way; whether Roger's
counterpart was elected there depends on how reliable the source is, so *given the rumor,
Roger must have been elected chief* is false when the rumor rests on shaky evidence and true
only when the source is reliable. As a source of information it determines the worlds
compatible with what it says, so the German reportative *sollen* in *dem Gerücht nach soll
Roger zum Häuptling gewählt worden sein* is true whatever the rumor's provenance, even a lie.
The informational background is therefore not realistic: the actual world need not be among
the worlds the rumor describes.

## Implementation notes

The worlds record whether Roger was elected and whether the rumor exists, so every claim is
decided over `Bool × Bool`. The evidence-of-things background at a world lists the status of
the rumor there; the informational background lists the rumor's content. Reliability is stated
generally, as a proposition of the background entailing the content wherever the rumor
exists, rather than as an extra coordinate. Counterparts are identified with the rumor's
status, since the model has no other individuals.

## References

* [kratzer-2012]
* [kratzer-1981] — the original typology of conversational backgrounds
* [rullmann-matthewson-davis-2008] — the St'át'imcets reportative the chapter contrasts with
  German *sollen*
-/

namespace Kratzer2012

open Modality.Kratzer

/-- A world: was Roger elected chief, and does the rumor that he was exist? -/
abbrev World := Bool × Bool

/-- Roger was elected chief. -/
def chief : World → Prop := (·.1 = true)

/-- The rumor exists. -/
def rumor : World → Prop := (·.2 = true)

/-- The rumor as evidence of things: the background at `w` records the rumor's status in
`w`, so the accessible worlds are those with a counterpart of the actual rumor, or with
none if there is none. -/
def evidence : ModalBase World := λ w => [λ v => v.2 = w.2]

/-- The rumor as a source of information: the background lists its content. -/
def content : ModalBase World := Function.const World [chief]

/-- Decide a claim about the backgrounds over the four worlds. -/
scoped macro "decide_worlds" : tactic =>
  `(tactic| ((try simp only [simpleNecessity, simplePossibility, ModalLogic.box,
      ModalLogic.diamond, kratzerR, isRealistic, evidence, content, chief, rumor,
      Function.const_apply, List.forall_mem_cons, List.mem_nil_iff, false_implies,
      implies_true, and_true]) <;> decide))

/-- The evidence-of-things background is realistic: every world has the rumor's status it
has. -/
theorem evidence_realistic : isRealistic evidence := by decide_worlds

/-- The informational background is not realistic: at a world where the rumor is a lie,
the world itself is not among those compatible with the rumor's content. -/
theorem content_not_realistic : ¬ isRealistic content := by decide_worlds

/-- (8b): the reportative reading holds at every world, a lie included, because it reports
the rumor's content. -/
theorem sollen_holds (w : World) : simpleNecessity content chief w := by
  decide_worlds

/-- (8a) on shaky evidence: where the rumor exists, the worlds with a counterpart of it
include one where Roger was not elected, so Roger need not have been elected chief. -/
theorem not_must_chief (w : World) : ¬ simpleNecessity evidence chief w := by
  revert w; decide_worlds

/-- Yet the rumor leaves Roger's election possible wherever it exists. -/
theorem can_chief (w : World) (h : rumor w) : simplePossibility evidence chief w := by
  revert h w; decide_worlds

/-- (8a) from a reliable source: if the background also records that the rumor is reliable,
a proposition entailing its content wherever the rumor exists, then Roger must have been
elected chief. Stated for any worlds and backgrounds. -/
theorem must_of_reliable {W : Type*} (rumor chief reliable : W → Prop) (f : ModalBase W)
    (hf : ∀ w, rumor w → rumor ∈ f w ∧ reliable ∈ f w)
    (hrel : ∀ v, reliable v → rumor v → chief v) (w : W) (hw : rumor w) :
    simpleNecessity f chief w := λ v hv =>
  hrel v (hv reliable (hf w hw).2) (hv rumor (hf w hw).1)

end Kratzer2012
