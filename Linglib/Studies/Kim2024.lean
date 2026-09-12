import Linglib.Semantics.Causation.Psych
import Linglib.Semantics.Causation.PsychLink
import Linglib.Studies.Pesetsky1995
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Kim (2024): On the Argument Structure of Object Experiencer Verbs

This file formalizes the Uniform Projection Hypothesis of [kim-2024] for the object-experiencer
psych verbs, [belletti-rizzi-1988]'s Class II: every such verb projects a Cause and an
Experiencer, and the eventive–stative split among them comes from the causal source, a
mind-external percept (*frighten*) against a mind-internal representation (*concern*). From the
source follow the intensionality of the subject position, the temporal relation of cause and
state (precedence with a transition, or an overlap that maintains the state), and the subtype of
the stimulus in [pesetsky-1995]'s terms: an external percept is a Target, an internal
representation the Subject Matter, and since Subject Matter maps to the onset of the causal chain,
which an overt Cause also occupies, the T/SM restriction follows from the Onset Condition. The
English fragment's psych verbs carry their causal source, and their opacity, temporal profile and
stimulus subtype are derived from it (`classII_consistent_all`, `internal_implies_opaque`,
`transition_iff_external`, `internal_derives_sm`), with the two readings of *worry* differing
only in the source (`worry_uniform_projection`).

The comparison with [pesetsky-1995]: both accounts predict that a Cause and a Subject Matter
cannot co-occur, Pesetsky by the Head Movement Constraint on the nonaffixal *about*, Kim by the
Onset Condition, but they diverge on a Cause with a Target, which Pesetsky's nonaffixal *at*
blocks just the same while the Onset Condition allows it (`accounts_diverge_on_cause_target`).

## Implementation notes

Causal source, the Onset Condition and the stimulus subtype are the substrate's
`Causation.Psych`, the temporal profiles `Causation.PsychLink`; the fragment stores each verb's
`causalSource` and `opaqueContext`, and consistency is the derived opacity agreeing with the
stored one.

## References

* [kim-2024]
* [belletti-rizzi-1988]
* [pesetsky-1995]
-/

namespace Kim2024

open Causation.Psych Causation.PsychLink English.Predicates.Verbal Pesetsky1995.PsychVerbs
  Minimalist

/-! ### Class II verbs and their causal source -/

/-- A Class II entry is consistent with the hypothesis when the opacity of its subject position
is what its causal source predicts. -/
def classII_consistent (v : VerbEntry) : Prop :=
  v.causalSource.map subjectIntensional = some v.opaqueContext

/-- A Class I entry has no causal source: the distinction is Class-II-specific. -/
def classI_consistent (v : VerbEntry) : Prop := v.causalSource = none

instance (v : VerbEntry) : Decidable (classII_consistent v) :=
  inferInstanceAs (Decidable (_ = _))

instance (v : VerbEntry) : Decidable (classI_consistent v) :=
  inferInstanceAs (Decidable (_ = _))

/-- The fragment's Class II verbs: the eventive ones with an external source, the stative ones
with an internal source, and *worry* on both readings. -/
def classII : List VerbEntry :=
  [frighten, amuse, fascinate, irritate, annoy, bore, charm, impress, surprise, scare, delight,
   embarrass, upset_psych, disgust, shock, confuse, disappoint, worry_eventive,
   concern, interest, worry_stative, please_psych, trouble, puzzle]

/-- The fragment's Class I verbs. -/
def classI : List VerbEntry := [enjoy, like, love, hate, fear_np, dread_np]

theorem classII_consistent_all : ∀ v ∈ classII, classII_consistent v := by decide

theorem classI_consistent_all : ∀ v ∈ classI, classI_consistent v := by decide

/-- Opacity follows from an internal source: the subject's referent is a representation of the
experiencer's, so co-referential terms need not substitute. -/
theorem internal_implies_opaque {v : VerbEntry} (h : classII_consistent v)
    (hs : v.causalSource = some .internal) : v.opaqueContext = true := by
  simpa [classII_consistent, hs, subjectIntensional] using h.symm

/-- Transparency follows from an external source. -/
theorem external_implies_transparent {v : VerbEntry} (h : classII_consistent v)
    (hs : v.causalSource = some .external) : v.opaqueContext = false := by
  simpa [classII_consistent, hs, subjectIntensional] using h.symm

/-- Uniform projection within one verb: the eventive and stative readings of *worry* share
their arguments and differ only in causal source. -/
theorem worry_uniform_projection :
    worry_eventive.causalSource ≠ worry_stative.causalSource := by
  decide

/-! ### Temporal profile and stimulus subtype -/

/-- The causal link involves a transition of the experiencer's state exactly when the source is
external: a percept precedes the state it brings about, a representation overlaps the state it
maintains. -/
theorem transition_iff_external {T : Type*} [LinearOrder T] (cs : CausalSource) :
    (CausalSource.toLink T cs).involvesTransition = true ↔ cs = .external := by
  cases cs <;> simp [CausalSource.toLink, eventiveLink, maintenanceLink]

/-- A verb's stimulus subtype is derived from its causal source. -/
def derivedStimulusType (v : VerbEntry) : Option StimulusType :=
  v.causalSource.map CausalSource.toStimulusType

/-- An external source makes the stimulus a Target, which does not compete with an overt
Cause. -/
theorem external_derives_target {v : VerbEntry} (hs : v.causalSource = some .external) :
    derivedStimulusType v = some .target ∧ StimulusType.target.conflictsWithCause = false :=
  ⟨by simp [derivedStimulusType, hs, CausalSource.toStimulusType], rfl⟩

/-- An internal source makes the stimulus the Subject Matter, which maps to the onset of the
causal chain and so conflicts with an overt Cause: the T/SM restriction from the Onset
Condition. -/
theorem internal_derives_sm {v : VerbEntry} (hs : v.causalSource = some .internal) :
    derivedStimulusType v = some .subjectMatter ∧
      StimulusType.subjectMatter.conflictsWithCause = true ∧ onsetCondition .onset = true :=
  ⟨by simp [derivedStimulusType, hs, CausalSource.toStimulusType], rfl, rfl⟩

/-! ### The comparison with Pesetsky (1995) -/

/-- Pesetsky's prediction is symmetric: *at* and *about* are both nonaffixal and so both block
the incorporation of CAUS. -/
theorem pesetsky_symmetric_blocking : headAt.affixal = false ∧ headAbout.affixal = false :=
  ⟨rfl, rfl⟩

/-- Both accounts predict a Cause with a Subject Matter ill-formed, and the data agree. -/
theorem both_accounts_predict_cause_sm_illformed :
    StimulusType.subjectMatter.conflictsWithCause = true ∧ headAbout.affixal = false ∧
      (tsmData.filter λ d => d.causePresent && d.smPresent).all (!·.wellFormed) = true :=
  ⟨rfl, rfl, by decide⟩

/-- The accounts diverge on a Cause with a Target: Pesetsky's nonaffixal *at* blocks it like
*about*, while a Target maps to the terminus and the Onset Condition allows it. -/
theorem accounts_diverge_on_cause_target :
    headAt.affixal = false ∧ StimulusType.target.conflictsWithCause = false :=
  ⟨rfl, rfl⟩

end Kim2024
