import Linglib.Semantics.Modality.Narrog

/-!
# Narrog (2010): (Inter)subjectification in the Domain of Modality and Mood

This file formalizes the directionality claim of [narrog-2010] and its account of the
cross-linguistic rarity of strong obligation. Modal meanings are placed on the two-dimensional
map of `Semantics/Modality/Narrog`, volitivity against speaker orientation, and the claim of
§3.1 is that semantic change never decreases speaker orientation, whatever it does to
volitivity (`Directional`). The eight most frequent changes of modal meaning in the sample of
[bybee-perkins-pagliuca-1994], the chapter's Table 2, all satisfy it (`commonChanges`,
`directionality`), and so preserve or raise subjectivity through the bridge to the cline of
Traugott (`directionality_via_subjectivity`); the three most frequent run from non-volitive
to volitive meanings, future and possibility markers becoming imperatives, permissions, and
admonitives (§3.2, `most_frequent_to_volitive`), so the deontic-to-epistemic shift is one
change among several rather than the representative one, and volitivity is crossed in both
directions (`volitivity_both_directions`). A change from probability to an event-oriented
obligation is what the chapter names as a counterexample and finds undocumented; the claim
excludes it (`probability_to_obligation_excluded`). Strong obligation is a minority category,
Table 4 finding must-type markers in sixty of two hundred languages against sixty-two
should-type ones, and the explanation of §4.2 is that a must-type marker, unlike a
should-type one, is performative, so that a strong obligation imposed on the hearer is
face-threatening and is avoided where the speaker lacks authority
(`must_should_differ_in_performativity`); the Japanese strong-necessity construction
accordingly occurs with no second-person subject at all in the corpus counts of Table 5.

## Implementation notes

The map's three levels of speaker orientation put deontic and epistemic meanings on one
level, so the deontic-to-epistemic changes of Table 2 preserve the level, where the chapter
counts them as increases on a finer scale. The must-type and should-type positions are the
substrate's `strongObligation` and `weakObligation`, which originate with this chapter. The
counts of Tables 3 to 7 and the Lakota future used as a second-person obligation (§3.2) are
described in prose.

## References

* [narrog-2010]
* [narrog-2012]
* [bybee-perkins-pagliuca-1994]
-/

namespace Narrog2010

open Modality.Narrog

/-- The directionality claim of §3.1: a change from one region of the map to another never
decreases speaker orientation, whatever it does to volitivity. -/
def Directional (source target : NarrogRegion) : Prop :=
  source.orientation ≤ target.orientation

instance (s t : NarrogRegion) : Decidable (Directional s t) := inferInstanceAs (Decidable (_ ≤ _))

/-- An attested change of modal meaning: its source and target regions, and the number of
grams of the sample of [bybee-perkins-pagliuca-1994] showing it. -/
structure Change where
  label : String
  source : NarrogRegion
  target : NarrogRegion
  grams : ℕ

/-- The change satisfies the directionality claim. -/
def Change.Directional (c : Change) : Prop := Narrog2010.Directional c.source c.target

/-- The change crosses from non-volitive to volitive meaning. -/
def Change.ToVolitive (c : Change) : Prop :=
  c.source.volitivity = .nonVolitive ∧ c.target.volitivity = .volitive

instance : DecidablePred Change.Directional :=
  λ c => inferInstanceAs (Decidable (c.source.orientation ≤ c.target.orientation))
instance : DecidablePred Change.ToVolitive := λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Table 2: the eight most frequent changes of modal meaning in the sample of
[bybee-perkins-pagliuca-1994], with their gram counts. Future, prediction, and possibility
markers are event-oriented modality, obligation, permission, and epistemic assessment
speaker-oriented, and the imperative and admonitive mood. -/
def commonChanges : List Change :=
  [ ⟨"future/prediction → imperative",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.volitive, .mood⟩, 13⟩
  , ⟨"root possibility → permission",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.volitive, .speakerOriented⟩, 9⟩
  , ⟨"root/epistemic possibility → admonitive",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.volitive, .mood⟩, 5⟩
  , ⟨"obligation → imperative",
     ⟨.volitive, .speakerOriented⟩, ⟨.volitive, .mood⟩, 4⟩
  , ⟨"ability/root possibility → epistemic possibility",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.nonVolitive, .speakerOriented⟩, 4⟩
  , ⟨"strong obligation → certainty",
     ⟨.volitive, .speakerOriented⟩, ⟨.nonVolitive, .speakerOriented⟩, 3⟩
  , ⟨"weak obligation → probability",
     ⟨.volitive, .speakerOriented⟩, ⟨.nonVolitive, .speakerOriented⟩, 2⟩
  , ⟨"prediction/future → probability",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.nonVolitive, .speakerOriented⟩, 2⟩
  ]

/-- Every attested change increases or preserves speaker orientation. -/
theorem directionality : ∀ c ∈ commonChanges, c.Directional := by decide

/-- Through the bridge to the subjectivity cline, every attested change increases or preserves
subjectivity as well. -/
theorem directionality_via_subjectivity :
    ∀ c ∈ commonChanges,
      c.source.orientation.toSubjectivityLevel ≤ c.target.orientation.toSubjectivityLevel :=
  λ c hc => speakerOrientation_toSubjectivity_monotone _ _ (directionality c hc)

/-- Table 2 lists the changes by frequency, and the three most frequent cross from non-volitive
to volitive meaning (§3.2), the direction a deontic-to-epistemic theory would call
counter-directional. -/
theorem most_frequent_to_volitive :
    (commonChanges.map Change.grams).Pairwise (· ≥ ·) ∧
      ∀ c ∈ commonChanges.take 3, c.ToVolitive := by
  decide

/-- Volitivity is orthogonal to the direction of change: the attested changes cross it in both
directions, the deontic-to-epistemic shift being the volitive-to-non-volitive case. -/
theorem volitivity_both_directions :
    (∃ c ∈ commonChanges, c.ToVolitive) ∧
      ∃ c ∈ commonChanges,
        c.source.volitivity = .volitive ∧ c.target.volitivity = .nonVolitive := by
  decide

/-- The chapter's own example of what a counterexample would be, a change from probability to
an event-oriented obligation, is excluded by the claim; no such change is documented. -/
theorem probability_to_obligation_excluded :
    ¬ Directional ⟨.nonVolitive, .speakerOriented⟩ ⟨.volitive, .eventOriented⟩ := by
  decide

/-! ### Strong obligation (§4) -/

/-- Must-type and should-type obligation occupy one region of the map and differ in
performativity alone, and the performative one is face-threatening: the chapter's reason why
strong obligation is grammaticalized in a minority of languages and, in Japanese, kept away
from second-person subjects, while imperatives, always performative and used under full
authority, are near-universal. -/
theorem must_should_differ_in_performativity :
    strongObligation.toRegion = weakObligation.toRegion ∧
      strongObligation.isFaceThreatening = true ∧ weakObligation.isFaceThreatening = false ∧
      imperative.isFaceThreatening = true :=
  ⟨strong_weak_differ_only_in_performativity, strong_obligation_face_threatening,
   weak_obligation_not_face_threatening, imperative_face_threatening⟩

end Narrog2010
