import Linglib.Semantics.Modality.Narrog

/-!
# Narrog (2010): (Inter)subjectification in the Domain of Modality and Mood

This file formalizes the directionality claim of [narrog-2010] and its account of the
cross-linguistic rarity of strong obligation. The eight most common changes of modal
meaning in the sample of [bybee-perkins-pagliuca-1994], from future to imperative, from
root possibility to permission, from obligation to certainty, and the rest, are placed on
the two-dimensional semantic map of `Semantics/Modality/Narrog`, and every one of them
increases or preserves speaker orientation whatever its volitivity (`directionality`,
`directionality_via_subjectivity`); the deontic-to-epistemic shift is one instance among
several, and the most frequent changes run from non-volitive to volitive meanings
(`nonvolitive_to_volitive_attested`). Strong obligation is performative, volitive, and
speaker-oriented, so it is face-threatening, whereas weak obligation is descriptive and is
not (`toNarrogPosition`, `face_threat_from_performativity`); the chapter's survey of two
hundred languages finds markers of strong obligation in a minority of them, no more
numerous than markers of weak obligation, and its Japanese corpus data find the
strong-necessity construction never used with a second-person subject.

## Implementation notes

The changes are checked against the same table as reprinted in [narrog-2012]; the survey
counts and the person-frequency table are reported in prose rather than typed into this
file.

## References

* [narrog-2010]
* [narrog-2012]
* [bybee-perkins-pagliuca-1994]
-/

namespace Narrog2010

open Modality.Narrog

/-- An attested cross-linguistic change of modal meaning, as a pair of regions of the
semantic map. -/
structure Change where
  label : String
  source : NarrogRegion
  target : NarrogRegion

/-- The eight most common changes of modal meaning in the sample of
[bybee-perkins-pagliuca-1994]. -/
def commonChanges : List Change :=
  [ ⟨"future/prediction → imperative",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.volitive, .mood⟩⟩
  , ⟨"root possibility → permission",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.volitive, .speakerOriented⟩⟩
  , ⟨"root/epistemic possibility → admonitive",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.volitive, .mood⟩⟩
  , ⟨"obligation → imperative",
     ⟨.volitive, .speakerOriented⟩, ⟨.volitive, .mood⟩⟩
  , ⟨"ability/root possibility → epistemic possibility",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.nonVolitive, .speakerOriented⟩⟩
  , ⟨"strong obligation → certainty",
     ⟨.volitive, .speakerOriented⟩, ⟨.nonVolitive, .speakerOriented⟩⟩
  , ⟨"weak obligation → probability",
     ⟨.volitive, .speakerOriented⟩, ⟨.nonVolitive, .speakerOriented⟩⟩
  , ⟨"prediction/future → probability",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.nonVolitive, .speakerOriented⟩⟩
  ]

/-- Every attested change increases or preserves speaker orientation. -/
theorem directionality :
    ∀ c ∈ commonChanges, c.source.orientation ≤ c.target.orientation := by
  decide

/-- Through the bridge from speaker orientation to subjectivity, every attested change
increases or preserves subjectivity as well. -/
theorem directionality_via_subjectivity :
    ∀ c ∈ commonChanges,
      c.source.orientation.toSubjectivityLevel ≤ c.target.orientation.toSubjectivityLevel := by
  decide

/-- Volitivity is orthogonal to the direction of change: changes cross the volitivity
boundary in both directions, and the deontic-to-epistemic shift is the volitive-to-
non-volitive case at constant orientation. -/
theorem nonvolitive_to_volitive_attested :
    (∃ c ∈ commonChanges, c.source.volitivity = .nonVolitive ∧ c.target.volitivity = .volitive) ∧
      ∃ c ∈ commonChanges, c.source.volitivity = .volitive ∧ c.target.volitivity = .nonVolitive ∧
        c.source.orientation = c.target.orientation := by
  decide

/-- How a language grammaticalizes deontic necessity: a *must*-type marker, a *should*-type
marker, a marker unspecified for strength, or one the description leaves indeterminable. -/
inductive DeonticNecessityType where
  | strong
  | weak
  | neutral
  | indeterminate
  deriving DecidableEq

/-- The position of each type in the three-dimensional space: strong obligation is
performative, the speaker creating the obligation by uttering it, and weak obligation is
descriptive, reporting an existing norm. -/
def toNarrogPosition : DeonticNecessityType → NarrogPosition
  | .strong => strongObligation
  | .weak => weakObligation
  | .neutral => weakObligation
  | .indeterminate => dynamicAbility

/-- Strong obligation is face-threatening and weak obligation is not, and the two differ only
in performativity, which is why languages tend not to grammaticalize strong obligation, or
do so only indirectly. -/
theorem face_threat_from_performativity :
    (toNarrogPosition .strong).isFaceThreatening = true ∧
      (toNarrogPosition .weak).isFaceThreatening = false ∧
      (toNarrogPosition .strong).performativity ≠ (toNarrogPosition .weak).performativity ∧
      (toNarrogPosition .strong).toRegion = (toNarrogPosition .weak).toRegion := by
  decide

end Narrog2010
