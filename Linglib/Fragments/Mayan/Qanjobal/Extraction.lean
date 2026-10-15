module

public import Linglib.Syntax.Reflex
public import Linglib.Syntax.Voice.Basic
public import Linglib.Syntax.Person.Basic
public import Linglib.Fragments.Mayan.Extraction

/-!
# Q'anjob'al Agent Focus and extraction marking

Q'anjob'al (Q'anjob'alan Mayan) extracts an intransitive subject or a transitive object
freely, but a transitive subject only through the Agent Focus form of the verb, which adds the
suffix *-on* to the stem, drops Set A, and takes the intransitive status suffix *-i* in place
of the transitive *-V'*; either status suffix surfaces only when the verb is phrase-final.
Agent Focus is confined to third-person agents, and a first- or second-person agent focuses
with the regular transitive verb. The same form, under no restriction on person, is the verb
of every non-finite embedded transitive clause, the construction Kaufman named the Crazy
Antipassive and which is found in the Q'anjob'alan branch alone.

## Main declarations

* `Qanjobal.StatusSuffix`: the intransitive and transitive status suffixes, each a morph.
* `Qanjobal.agentFocus`, `Qanjobal.voice`: the Agent Focus voice, and the voice of each
  `Mayan.VerbForm`.
* `Qanjobal.StatusSuffix.ofVerbForm`, `Qanjobal.suffixes`: the status suffix and the suffixes of
  each form.
* `Qanjobal.verbForm`: the form of a transitive verb by the finiteness of its clause, the
  argument extracted from it and the person of its agent.
* `Qanjobal.Extraction.realize`: the reflexes extraction from each argument role licenses
  with an agent of each person, the Agent Focus form where it replaces the transitive.

## Main results

* `Qanjobal.StatusSuffix.ofVerbForm_eq_itv_iff`: the intransitive status suffix goes with the
  absence of Set A.
* `Qanjobal.verbForm_eq_agentFocus_iff`: Agent Focus is the form of every non-finite
  transitive and of a finite one whose third-person subject is extracted.
* `Qanjobal.Extraction.mem_realize_iff`: the Agent Focus reflex appears exactly under the
  extraction of a third-person transitive subject.

## References

* [coon-mateo-pedro-preminger-2014]
-/

@[expose] public section

namespace Qanjobal

/-- A verb stem ends in a status suffix, intransitive or transitive, which surfaces only
phrase-finally. -/
inductive StatusSuffix where
  | itv
  | tv
  deriving DecidableEq, Repr

/-- The intransitive status suffix is *-i* and the transitive one *-V'*. -/
def StatusSuffix.morph : StatusSuffix → Morphology.Morph
  | .itv => .suff "i"
  | .tv => .suff "V'"

/-- Agent Focus keeps both core terms, as the active does, and is coded by *-on*. -/
def agentFocus : Voice := Voice.agentVoice.marked [.suff "on"]

/-- The voice of each form, the uncoded active for the regular transitive and Agent Focus for
the Agent Focus form. -/
def voice : Mayan.VerbForm → Voice
  | .transitive => Voice.active
  | .agentFocus => agentFocus

/-- The regular transitive takes the transitive status suffix and the Agent Focus form the
intransitive one. -/
def StatusSuffix.ofVerbForm : Mayan.VerbForm → StatusSuffix
  | .transitive => .tv
  | .agentFocus => .itv

/-- A form takes the intransitive status suffix exactly when it lacks Set A. -/
theorem StatusSuffix.ofVerbForm_eq_itv_iff (f : Mayan.VerbForm) :
    ofVerbForm f = .itv ↔ ¬ f.HasSetA := by
  decide +revert

/-- The suffixes of a form, the marker of its voice before its status suffix. -/
def suffixes (f : Mayan.VerbForm) : List Morphology.Morph :=
  (voice f).marker ++ [(StatusSuffix.ofVerbForm f).morph]

/-- A transitive verb takes the Agent Focus form in a non-finite clause and in a finite clause
whose third-person subject is extracted, and the regular transitive form otherwise. -/
def verbForm (finite : Bool) (extracted : Option ArgumentRole) (agent : Person) :
    Mayan.VerbForm :=
  if finite = false ∨ (extracted = some .A ∧ ¬ agent.IsSAP) then .agentFocus else .transitive

theorem verbForm_eq_agentFocus_iff (finite : Bool) (extracted : Option ArgumentRole)
    (agent : Person) :
    verbForm finite extracted agent = .agentFocus ↔
      finite = false ∨ (extracted = some .A ∧ ¬ agent.IsSAP) := by
  unfold verbForm
  split_ifs with h <;> simp [h]

/-- A non-finite transitive takes the Agent Focus form whoever its agent is. -/
theorem verbForm_false (extracted : Option ArgumentRole) (agent : Person) :
    verbForm false extracted agent = .agentFocus := rfl

/-- A speech-act-participant agent never takes the Agent Focus form in a finite clause. -/
theorem verbForm_true_of_isSAP {agent : Person} (h : agent.IsSAP)
    (extracted : Option ArgumentRole) : verbForm true extracted agent = .transitive := by
  simp [verbForm, h]

namespace Extraction

/-- Extraction is marked when it changes the form of a finite verb, by the suffixes of the
form it selects; with an agent of the given person, only a third-person transitive subject
switches the verb to Agent Focus. -/
def realize (agent : Person) (r : ArgumentRole) : Finset (Reflex Mayan.Host) :=
  if verbForm true (some r) agent = verbForm true none agent then ∅
  else {.morpheme .verb (suffixes (verbForm true (some r) agent))}

/-- The Agent Focus reflex appears exactly under the extraction of a third-person transitive
subject. -/
theorem mem_realize_iff (agent : Person) (r : ArgumentRole) :
    Reflex.morpheme .verb (suffixes .agentFocus) ∈ realize agent r ↔
      r = .A ∧ ¬ agent.IsSAP := by
  decide +revert

/-- Extraction by a speech-act-participant agent is unmarked. -/
theorem realize_of_isSAP {agent : Person} (h : agent.IsSAP) (r : ArgumentRole) :
    realize agent r = ∅ := by
  simp [realize, verbForm_true_of_isSAP h]

end Extraction

end Qanjobal
