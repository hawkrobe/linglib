import Linglib.Semantics.Reference.Rigidity
import Linglib.Semantics.Modality.ModalTypes
import Linglib.Semantics.Presupposition.Basic
import Linglib.Pragmatics.Expressives.Basic
import Linglib.Data.Examples.Kubota2026

/-!
# Kubota (2026): Outlook Management

This file formalizes [kubota-2026]'s account of the Japanese *outlook markers*, adverbs and
focus particles such as *dōse* 'anyway', *nanka* 'anything like', *semete* 'at least',
*mushiro* 'rather', and *koso* 'precisely', whose secondary meaning is two-layered: a
presupposition that the prior discourse has made a counterstance salient, and an
expressive-like stance that situates the prejacent relative to that counterstance. `Outlook`
carries the three components, with the stance layer indexed by an outlook in the sense of
[coppock-2018]. Its presuppositional and expressive projections are its `PartialProp` and
`TwoDimProp` images, so that denial reaches the prejacent alone ((40)–(41)), and the shifted
readings under attitude verbs ((42)) are exactly the non-rigidity of the stance layer
(`isRigid_iff`), which a pure expressive in the sense of [potts-2007b] lacks
(`ofTwoDimProp_isRigid`).

The chapter's judgment data are the rows of `Data/Examples/Kubota2026.json`, and its
generalizations are stated over them. An outlook-marked utterance is felicitous iff the prior
move raises a counterstance, an evaluative assertion or a polar question about the prejacent's
issue rather than a general wh-question (`counterstance_requirement`, (37)–(39)). The contrary
marker *mushiro* and the confirmatory *yahari* are licensed by opposite expectations and neither
stance can be cancelled (`mushiro_yahari_expectation`, (11)–(12)). *Nanka* combines with every
modal flavor but is pejorative only under priority modality (`nanka_pejorative_iff_priority`,
(45)), while *semete* combines only with priority modals (`semete_selects_priority`, (46)),
priority modality being the deontic and bouletic flavors of [portner-2009].

## Implementation notes

The chapter is descriptive and defers its formal analysis to [kubota-ido-2025], where both
layers derive from a counterstance-marker discourse function over a [farkas-bruce-2010]
Table; `Outlook` records the chapter-level picture with the two layers as fields. Perspective
shift is modelled as outlook-relativity of the stance layer, following the chapter's remark
that outlook markers fail [potts-2007b]'s independence and nondisplaceability and instead
behave like locally accommodated presuppositions ([heim-1992]). Judgments the chapter marks
?? are recorded as `questionable`. The substrate's `circumstantial` flavor stands in for the
chapter's ability modals.

## TODO

* Deriving the two layers from a Table update, as [kubota-ido-2025] does, is not attempted.

## References

* [kubota-2026]
* [kubota-ido-2025]
* [coppock-2018]
* [potts-2007b]
* [heim-1992]
* [portner-2009]
* [farkas-bruce-2010]
-/

namespace Kubota2026

open Data.Examples (LinguisticExample)
open Modality (ModalFlavor)
open Pragmatics.Expressives (TwoDimProp)
open Presupposition (PartialProp)

/-! ### The two-layered meaning (§3) -/

/-- The meaning of an outlook-marked clause: the at-issue prejacent, the presupposed salient
counterstance, and the stance layer, evaluated relative to an outlook. -/
structure Outlook (W O : Type*) where
  /-- The at-issue content. -/
  prejacent : W → Prop
  /-- The presupposition that a counterstance is salient ((37)–(39)). -/
  counterstance : W → Prop
  /-- The evaluative stance, relative to an outlook. -/
  evaluation : O → W → Prop

namespace Outlook

variable {W O : Type*}

/-- The presuppositional projection: the counterstance is presupposed, the prejacent asserted. -/
@[simps] def toPartialProp (m : Outlook W O) : PartialProp W := ⟨m.counterstance, m.prejacent⟩

/-- The expressive projection at an outlook: the prejacent with the stance as its use-conditional
dimension. -/
@[simps] def toTwoDimProp (m : Outlook W O) (o : O) : TwoDimProp W :=
  ⟨m.prejacent, m.evaluation o⟩

/-- Negation, and so denial, leaves the counterstance presupposition in place ((40)–(41)). -/
theorem presup_neg_toPartialProp (m : Outlook W O) :
    m.toPartialProp.neg.presup = m.counterstance := rfl

/-- Negation leaves the stance layer in place at every outlook ((40)–(41)). -/
theorem ci_neg_toTwoDimProp (m : Outlook W O) (o : O) :
    (m.toTwoDimProp o).neg.ci = m.evaluation o := rfl

/-- A meaning is rigid when its stance layer does not depend on the outlook. -/
def IsRigid (m : Outlook W O) : Prop := Reference.IsRigid m.evaluation

/-- Perspective shift is non-rigidity: the expressive projection varies with the outlook iff
the stance layer does ((42)). -/
theorem isRigid_iff (m : Outlook W O) :
    m.IsRigid ↔ ∀ o o', m.toTwoDimProp o = m.toTwoDimProp o' := by
  simp only [IsRigid, Reference.IsRigid, toTwoDimProp, TwoDimProp.mk.injEq, true_and]

/-- A pure expressive as an outlook-marked meaning: its conventional implicature is the same at
every outlook, and it presupposes nothing. -/
def ofTwoDimProp (t : TwoDimProp W) : Outlook W O :=
  ⟨t.atIssue, λ _ => True, λ _ => t.ci⟩

/-- Pure expressives are rigid, so they do not shift under embedding ([potts-2007b]'s
nondisplaceability). -/
theorem ofTwoDimProp_isRigid (t : TwoDimProp W) : (ofTwoDimProp (O := O) t).IsRigid :=
  Reference.isRigid_const t.ci

end Outlook

/-! ### The counterstance requirement ((37)–(39)) -/

/-- The prior discourse move an outlook-marked utterance responds to. -/
inductive PriorMove where
  /-- An assertion evaluating the prejacent's topic ((37)). -/
  | evaluativeAssertion
  /-- A polar question about the prejacent's issue ((39), Q1). -/
  | polarQuestion
  /-- A general wh-question that leaves the prejacent's issue unraised ((38), (39) Q2). -/
  | whQuestion
  deriving DecidableEq

/-- A prior move raises a counterstance when it puts the prejacent's issue at issue: an
evaluative assertion or a polar question does, a general wh-question does not. -/
def PriorMove.RaisesCounterstance (m : PriorMove) : Prop := m ≠ .whQuestion

instance : DecidablePred PriorMove.RaisesCounterstance :=
  λ m => inferInstanceAs (Decidable (m ≠ .whQuestion))

/-- The row's prior move. -/
def priorMove? (row : LinguisticExample) : Option PriorMove :=
  match row.feature? "priorMove" with
  | some "evaluativeAssertion" => some .evaluativeAssertion
  | some "polarQuestion" => some .polarQuestion
  | some "whQuestion" => some .whQuestion
  | _ => none

/-- The prediction for a row: felicitous iff its prior move raises a counterstance. -/
def PredictsFelicitous (row : LinguisticExample) : Prop :=
  match priorMove? row with
  | some m => m.RaisesCounterstance
  | none => False

instance (row : LinguisticExample) : Decidable (PredictsFelicitous row) := by
  unfold PredictsFelicitous
  split <;> infer_instance

/-- An outlook-marked utterance is felicitous iff the prior move raises a counterstance. -/
theorem counterstance_requirement :
    ∀ row ∈ Examples.all, row.feature? "phenomenon" = some "counterstance" →
      (row.judgment = .acceptable ↔ PredictsFelicitous row) := by
  decide

/-! ### Non-cancelability ((10)–(12)) -/

/-- Under a context marked as unexpected the contrary marker *mushiro* is licensed and the
confirmatory *yahari* is not, and conversely under a context marked as expected: the stance is
conventional and cannot be cancelled. -/
theorem mushiro_yahari_expectation :
    ∀ row ∈ Examples.all, row.feature? "phenomenon" = some "noncancelability" →
      row.feature? "contextExpectation" ≠ none →
      (row.feature? "marker" = some "mushiro" ↔
        row.feature? "contextExpectation" = some "unexpected") := by
  decide

/-! ### Modal interactions ((45)–(46)) -/

/-- Priority modality after [portner-2009]: the deontic and bouletic flavors, as against
epistemic and ability modality. -/
def IsPriority : ModalFlavor → Prop
  | .deontic | .bouletic => True
  | .epistemic | .circumstantial => False

instance : DecidablePred IsPriority := λ f => by
  cases f <;> unfold IsPriority <;> infer_instance

/-- The row's modal flavor. -/
def flavor? (row : LinguisticExample) : Option ModalFlavor :=
  match row.feature? "modalFlavor" with
  | some "epistemic" => some .epistemic
  | some "deontic" => some .deontic
  | some "bouletic" => some .bouletic
  | some "circumstantial" => some .circumstantial
  | _ => none

/-- The row's modal is a priority modal. -/
def PriorityRow (row : LinguisticExample) : Prop :=
  match flavor? row with
  | some f => IsPriority f
  | none => False

instance (row : LinguisticExample) : Decidable (PriorityRow row) := by
  unfold PriorityRow
  split <;> infer_instance

/-- *Nanka* combines with modals of every flavor ((45)). -/
theorem nanka_unrestricted :
    ∀ row ∈ Examples.all, row.feature? "marker" = some "nanka" →
      row.feature? "phenomenon" = some "modalInteraction" → row.judgment = .acceptable := by
  decide

/-- The negative implication of *nanka* is pejorative under priority modals and comparatively
neutral under epistemic and ability modals ((45)). -/
theorem nanka_pejorative_iff_priority :
    ∀ row ∈ Examples.all, row.feature? "marker" = some "nanka" →
      row.feature? "phenomenon" = some "modalInteraction" →
      (row.feature? "evaluation" = some "pejorative" ↔ PriorityRow row) := by
  decide

/-- *Semete* combines with priority modals and not with epistemic or ability modals ((46)). -/
theorem semete_selects_priority :
    ∀ row ∈ Examples.all, row.feature? "marker" = some "semete" →
      row.feature? "phenomenon" = some "modalInteraction" →
      (row.judgment = .acceptable ↔ PriorityRow row) := by
  decide

end Kubota2026
