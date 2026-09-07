import Linglib.Semantics.Tense.Reichenbach
import Linglib.Semantics.Evidential.Source
import Linglib.Features.Mirativity
import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Mood.Defs

/-!
# Tense and evidence

Cumming's frame for a tense-evidential paradigm has three times, of speech, of the
acquisition of the speaker's evidence, and of the topic event; here it is the library's
Reichenbach frame with an acquisition time added. A cell of a paradigm constrains two
relations: the evidential perspective, between the event and the acquisition of the
evidence, and the utterance perspective, between the event and the speech time, each a cell
of the tense partition. Nonfuture tenses require evidence downstream of the event, while
future forms leave the evidential perspective free or require prospective evidence, and
where an evidential fixes the relation of the acquisition to speech, the utterance
perspective is the composition of the two cells. The constraints are read temporally, as in
Cumming's tables; his own constraint is causal, and the temporal reading of Lee's and Koev's
accounts is one he, Cariani and Huijsmans criticize. The constraint is not part of what is
asserted: the library renders it as a presupposition, so that a cell's meaning presupposes
its evidential perspective and asserts the bare content.

## Main definitions

* `EvidentialFrame` — the Reichenbach frame with an acquisition time, with the predicates
  `Downstream` and `Acquired`.
* `EPCondition`, `UPCondition` — the attested constraint shapes on the two perspectives,
  each a cell of the tense partition read as a predicate on frames by `toConstraint`.
* `TAMEEntry` — a paradigm cell: a label with its two constraints and optional mood and
  mirativity, and its `meaning` as a presuppositional proposition.
* `TAMEEntry.up_toConstraint_of_comp` — the utterance perspective derived by composition.
* `EPCondition.downstream_of_isNonfuture` — nonfuture cells require downstream evidence.

## References

* [S. Cumming, *Tense and evidence* (2026)][cumming-2026]
* [F. Cariani, *Future-past asymmetries, evidential grounding, and projection*
  (2022)][cariani-2022]
* [M. Huijsmans, *Timing of evidence and epistemic modal claims* (2025)][huijsmans-2025]
* [H. Reichenbach, *Elements of symbolic logic* (1947)][reichenbach-1947]
-/

namespace Tense.Evidential

open Tense
open _root_.Evidential
open Features.Mirativity
open Presupposition

variable {T : Type*}

/-! ### Frames -/

/-- Reichenbach's frame with the time at which the speaker acquires the evidence grounding
the assertion. -/
structure EvidentialFrame (T : Type*) extends ReichenbachFrame T where
  /-- The time at which the speaker acquires the evidence for the assertion. -/
  acquisitionTime : T

namespace EvidentialFrame

/-- Evidence downstream of the event, read temporally as in Cumming's tables: the event
precedes or coincides with the acquisition of the evidence. -/
def Downstream [LE T] (f : EvidentialFrame T) : Prop := f.eventTime ≤ f.acquisitionTime

/-- The evidence is acquired by the time of speech. -/
def Acquired [LE T] (f : EvidentialFrame T) : Prop := f.acquisitionTime ≤ f.speechTime

instance [LE T] [DecidableLE T] (f : EvidentialFrame T) : Decidable f.Downstream :=
  inferInstanceAs (Decidable (f.eventTime ≤ f.acquisitionTime))

instance [LE T] [DecidableLE T] (f : EvidentialFrame T) : Decidable f.Acquired :=
  inferInstanceAs (Decidable (f.acquisitionTime ≤ f.speechTime))

/-- Downstream evidence acquired by the time of speech is evidence for a nonfuture event. -/
theorem eventTime_le_speechTime [Preorder T] {f : EvidentialFrame T} (hd : f.Downstream)
    (hA : f.Acquired) : f.eventTime ≤ f.speechTime :=
  le_trans hd hA

end EvidentialFrame

/-! ### Evidential perspective -/

/-- The attested constraints on the evidential perspective, the relation of the event to the
acquisition of the evidence, across English, Korean and Bulgarian. -/
inductive EPCondition where
  /-- The event precedes or coincides with the acquisition: English past and progressive,
  Bulgarian nonfuture. -/
  | downstream
  /-- The event precedes the acquisition: Korean *-te* and *-ney* with the past. -/
  | strictDownstream
  /-- The event coincides with the acquisition: Korean *-te* and *-ney* with the present. -/
  | contemporaneous
  /-- The acquisition precedes the event: the Korean and Bulgarian future evidentials and
  the English *will have* and *will now*. -/
  | prospective
  /-- No constraint: the English future. -/
  | unconstrained
  deriving DecidableEq, Repr

/-- The cell of the tense partition an evidential-perspective constraint selects, on the
pair of event and acquisition times. -/
def EPCondition.toRelation : EPCondition → Finset Ordering
  | .downstream       => futureᶜ
  | .strictDownstream => past
  | .contemporaneous  => present
  | .prospective      => future
  | .unconstrained    => ⊤

/-- The evidential-perspective constraint as a predicate on frames. -/
def EPCondition.toConstraint [LinearOrder T] (e : EPCondition) (f : EvidentialFrame T) : Prop :=
  compare f.eventTime f.acquisitionTime ∈ e.toRelation

instance [LinearOrder T] (e : EPCondition) (f : EvidentialFrame T) :
    Decidable (e.toConstraint f) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- The evidential perspective a constraint shape projects to, if any. -/
def EPCondition.toEvidentialPerspective : EPCondition → Option EvidentialPerspective
  | .downstream => some .retrospective
  | .strictDownstream => some .retrospective
  | .contemporaneous => some .contemporaneous
  | .prospective => some .prospective
  | .unconstrained => none

instance : HasEvidentialPerspective EPCondition where
  toEvidentialPerspective := EPCondition.toEvidentialPerspective

/-- A nonfuture constraint shape requires downstream evidence. -/
theorem EPCondition.downstream_of_isNonfuture [LinearOrder T] {ep : EPCondition}
    {f : EvidentialFrame T} (h : Evidential.IsNonfuture ep) (hf : ep.toConstraint f) :
    f.Downstream := by
  cases ep <;> simp only [toConstraint, toRelation, Finset.mem_compl, compare_mem_past,
    compare_mem_present, compare_mem_future, not_lt] at hf
  exacts [hf, hf.le, hf.le, absurd h (by decide), absurd h (by decide)]

/-! ### Utterance perspective -/

/-- The attested constraints on the utterance perspective, the relation of the event to the
speech time. -/
inductive UPCondition where
  /-- The event precedes speech. -/
  | past
  /-- The event coincides with speech. -/
  | present
  /-- Speech precedes the event. -/
  | future
  /-- The event precedes or coincides with speech: Bulgarian nonfuture. -/
  | nonfuture
  /-- No constraint. -/
  | unconstrained
  deriving DecidableEq, Repr

/-- The cell of the tense partition an utterance-perspective constraint selects, on the pair
of event and speech times. -/
def UPCondition.toRelation : UPCondition → Finset Ordering
  | .past          => Tense.past
  | .present       => Tense.present
  | .future        => Tense.future
  | .nonfuture     => Tense.futureᶜ
  | .unconstrained => ⊤

/-- The utterance-perspective constraint as a predicate on frames. -/
def UPCondition.toConstraint [LinearOrder T] (u : UPCondition) (f : EvidentialFrame T) : Prop :=
  compare f.eventTime f.speechTime ∈ u.toRelation

instance [LinearOrder T] (u : UPCondition) (f : EvidentialFrame T) :
    Decidable (u.toConstraint f) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-! ### Paradigm cells -/

/-- A cell of a tense-aspect-mood-evidentiality paradigm: its label, its constraints on the
two perspectives, and optional mood and mirativity. -/
structure TAMEEntry where
  /-- The morphological label of the cell. -/
  label : String
  /-- The constraint on the evidential perspective. -/
  ep : EPCondition
  /-- The constraint on the utterance perspective. -/
  up : UPCondition
  /-- The grammatical mood, if specified. -/
  mood : Option Mood.Grammatical := none
  /-- The mirativity value, if specified. -/
  mirative : Option MirativityValue := none

instance : HasEvidentialPerspective TAMEEntry where
  toEvidentialPerspective p := toEvidentialPerspective p.ep

namespace TAMEEntry

variable [LinearOrder T]

/-- Where the cell's utterance-perspective cell is the composition of its
evidential-perspective cell with a cell relating acquisition to speech, the utterance
perspective follows from the evidential perspective and that relation. -/
theorem up_toConstraint_of_comp {p : TAMEEntry} {R : Finset Ordering}
    (h : p.up.toRelation = comp p.ep.toRelation R) {f : EvidentialFrame T}
    (hE : p.ep.toConstraint f) (hR : compare f.acquisitionTime f.speechTime ∈ R) :
    p.up.toConstraint f := by
  unfold UPCondition.toConstraint
  rw [h]
  exact compare_mem_comp hE hR

/-- The meaning of a cell at a frame, with the evidential-perspective constraint rendered as
a presupposition and the content asserted; the utterance perspective is left to the tense. -/
@[simps] def meaning {W : Type*} (p : TAMEEntry) (f : EvidentialFrame T) (φ : W → Prop) :
    PartialProp W where
  presup _ := p.ep.toConstraint f
  assertion := φ

end TAMEEntry

end Tense.Evidential
