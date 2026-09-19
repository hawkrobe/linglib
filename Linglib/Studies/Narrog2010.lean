import Linglib.Semantics.Modality.Narrog

/-!
# Narrog (2010): (Inter)subjectification in the Domain of Modality and Mood

This file formalizes the directionality claim of [narrog-2010] and the use the chapter makes of
the eight most frequent changes of modal meaning in the sample of
[bybee-perkins-pagliuca-1994]. Uses of modal markers are placed on the semantic map of
`Semantics/Modality/Narrog`, and the claim is that a change never decreases orientation towards
the speaker and the speech situation, whatever it does to volitivity. The meaning labels of the
tabulated changes fix the volitivity of source and target and tell modality proper from mood
(`Meaning.volitivity`, `Meaning.IsMood`). On that basis the changes pair the two values of
volitivity in every way (`volitivity_independent`), each change from non-volitive to volitive
meaning is more frequent than each deontic-to-epistemic one (`toNonVolitive_lt_toVolitive`), so
the deontic-to-epistemic shift is one change among several and not the representative one, and
no change leads out of mood (`source_not_isMood`). The changes into mood, future and possibility
markers becoming imperatives and admonitives and obligation markers becoming imperatives,
conform to the claim wherever the source use lay (`Meaning.Admits.le_of_isMood`). A change from
probability to an event-oriented obligation is what the chapter names as a counterexample and
finds undocumented, and the claim excludes it (`not_le_eventOriented`).

The chapter's second half asks why strong obligation is rarely grammaticalized: must-type
markers were found in sixty of two hundred languages, and the Japanese strong-necessity
construction occurs with no second-person subject in the corpus counts the chapter cites.
Imperatives are in principle always performative and used under full authority, while obligation
markers either report obligations or impose them without such authority, which is
face-threatening, so that direct reference to obligation is habitually avoided in many cultures
and obligation markers are less often available as sources of epistemic ones. That argument and
its counts are not formalized.

## Implementation notes

The chapter argues that the five tabulated changes within modality proper also increase speaker
orientation, the deontic-to-epistemic ones included, but it assigns no positions to their
meanings, and orientation is a property of a use and not of a meaning label. `Meaning.Admits`
therefore constrains the orientation of the mood meanings alone.

## References

* [narrog-2010]
* [bybee-perkins-pagliuca-1994]
-/

namespace Narrog2010

open Modality.Narrog

/-- The meanings between which the tabulated changes run, at the granularity of the chapter's
table. -/
inductive Meaning where
  /-- Future or prediction. -/
  | future
  /-- Ability or root possibility. -/
  | ability
  | rootPossibility
  /-- Root or epistemic possibility. -/
  | possibility
  | permission
  | obligation
  | strongObligation
  | weakObligation
  | epistemicPossibility
  | probability
  | certainty
  | imperative
  | admonitive
  deriving DecidableEq, Repr

namespace Meaning

/-- Obligation, permission, and the directive moods involve an element of will; future,
possibility, ability, and the epistemic meanings do not. -/
def volitivity : Meaning → Volitivity
  | permission | obligation | strongObligation | weakObligation | imperative | admonitive =>
    .volitive
  | future | ability | rootPossibility | possibility | epistemicPossibility | probability
  | certainty => .nonVolitive

/-- The imperative and the admonitive mark speech acts and belong to mood; the other meanings
belong to modality proper. -/
def IsMood : Meaning → Prop
  | imperative | admonitive => True
  | _ => False

instance : DecidablePred IsMood := fun m ↦ by cases m <;> unfold IsMood <;> infer_instance

/-- A region is a possible position of a use of the meaning when it has the meaning's
volitivity and, for a mood, lies at the speech act-oriented end of the map. -/
def Admits (m : Meaning) (r : Region) : Prop :=
  r.volitivity = m.volitivity ∧ (m.IsMood → r.orientation = ⊤)

/-- A change into mood conforms to the directionality claim wherever the source use lay. -/
theorem Admits.le_of_isMood {m : Meaning} {t : Region} (ht : m.Admits t) (hm : m.IsMood)
    (s : Region) : s ≤ t :=
  Region.le_of_orientation_eq_top (ht.2 hm) s

/-- A change out of mood into a lower region does not conform. -/
theorem Admits.not_le_of_isMood {m : Meaning} {s t : Region} (hs : m.Admits s) (hm : m.IsMood)
    (ht : t.orientation < ⊤) : ¬ s ≤ t :=
  Region.not_le_of_orientation_eq_top (hs.2 hm) ht

end Meaning

/-- A change of modal meaning, with the number of grams of the sample of
[bybee-perkins-pagliuca-1994] that show it, one gram per language. -/
structure Change where
  source : Meaning
  target : Meaning
  grams : ℕ

/-- The change crosses from non-volitive to volitive meaning. -/
def Change.ToVolitive (c : Change) : Prop :=
  c.source.volitivity = .nonVolitive ∧ c.target.volitivity = .volitive

/-- The change crosses from volitive to non-volitive meaning, as the deontic-to-epistemic
changes do. -/
def Change.ToNonVolitive (c : Change) : Prop :=
  c.source.volitivity = .volitive ∧ c.target.volitivity = .nonVolitive

instance : DecidablePred Change.ToVolitive := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred Change.ToNonVolitive := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The eight most frequent changes of modal meaning in the sample of
[bybee-perkins-pagliuca-1994], as the chapter tabulates them. -/
def commonChanges : List Change :=
  [⟨.future, .imperative, 13⟩, ⟨.rootPossibility, .permission, 9⟩,
   ⟨.possibility, .admonitive, 5⟩, ⟨.obligation, .imperative, 4⟩,
   ⟨.ability, .epistemicPossibility, 4⟩, ⟨.strongObligation, .certainty, 3⟩,
   ⟨.weakObligation, .probability, 2⟩, ⟨.future, .probability, 2⟩]

/-- Change is attested within the volitive meanings, within the non-volitive ones, and across
volitivity in both directions, so volitivity does not constrain the direction of change. -/
theorem volitivity_independent (v v' : Volitivity) :
    ∃ c ∈ commonChanges, c.source.volitivity = v ∧ c.target.volitivity = v' := by
  cases v <;> cases v' <;> decide

/-- Every change from non-volitive to volitive meaning is more frequent than every change from
volitive to non-volitive meaning, the direction a deontic-to-epistemic theory takes as
representative. -/
theorem toNonVolitive_lt_toVolitive :
    ∀ c ∈ commonChanges, ∀ d ∈ commonChanges,
      c.ToVolitive → d.ToNonVolitive → d.grams < c.grams := by
  decide

/-- No tabulated change leads out of mood, the one configuration that the meaning labels alone
would show to run against the claim. -/
theorem source_not_isMood : ∀ c ∈ commonChanges, ¬ c.source.IsMood := by decide

/-- Future, possibility, and obligation markers all feed mood, from both sides of the volitivity
dimension. -/
theorem isMood_of_both_volitivities (v : Volitivity) :
    ∃ c ∈ commonChanges, c.source.volitivity = v ∧ c.target.IsMood := by
  cases v <;> decide

/-- The chapter's own example of what a counterexample would be, a change from probability to an
event-oriented obligation: no change into an event-oriented region conforms when the source use
lies above the event-oriented pole, as a speaker's assessment of probability does. -/
theorem not_le_eventOriented {s : Region} (hs : ⊥ < s.orientation) (v : Volitivity) :
    ¬ s ≤ ⟨v, ⊥⟩ :=
  Region.not_le_of_orientation_eq_bot hs rfl

end Narrog2010
