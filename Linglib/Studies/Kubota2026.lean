import Linglib.Semantics.Intensional.Rigidity
import Linglib.Studies.HarrisPotts2009
import Linglib.Semantics.Modality.ModalTypes
import Linglib.Fragments.Japanese.Particles
import Linglib.Data.Examples.Kubota2026

/-!
# Kubota 2026: outlook management
[kubota-2026] [kubota-ido-2025] [coppock-2018] [farkas-bruce-2010] [potts-2007]

[kubota-2026]'s analysis of Japanese *outlook markers* (*nanka*, *dōse*, *semete*, *koso*,
*mushiro*, …): discourse-sensitive adverbs and focus particles with a two-layered secondary
meaning — a presuppositional counterstance requirement plus an expressive-like evaluative
stance ([kubota-2026] §3). The term *outlook* is [coppock-2018]'s, whose outlooks replace
worlds as circumstances of evaluation for **at-issue** discretionary content; the term
*counterstance* originates with [kennedy-willer-2016]; the two-layered object is the
chapter's, and rendering its stance layer as a [potts-2005]-style CI tier is this
formalisation's bridge onto `TwoDimProp`. The chapter itself classifies that layer as
CI-*like* while arguing it fails [potts-2007]'s independence and nondisplaceability: under
attitudes it shifts to the holder like a locally accommodated presupposition ([heim-1992]),
not by semantic binding of an index. The secondary-meaning diagnostics ([potts-2007] (27))
follow the projection typology of [tonhauser-beaver-roberts-simons-2013].

The handbook chapter is descriptive and defers the formal analysis to its companion
[kubota-ido-2025], where the two layers are *derived* from a counterstance-marker discourse
function over a [farkas-bruce-2010] Table rather than stipulated; the two-field denotation
here is the chapter-level picture, and deriving it from a Table update is the natural
follow-up. `saltDenotation` is a minimal `Outlook` with `prejacent`/`counterstance` stubbed,
and counterstance salience is read off the discourse-context features of the data rows. The
rival framing is [gutzmann-2015]'s use-conditional treatment of counterstance particles
(e.g. German *doch*), where the second layer is use-conditional rather than presuppositional.

The lexical inventory is theory-neutral and lives in `Fragments/Japanese/Particles.lean`
(`Japanese.OutlookMarkers`); the judgment data ((10), (37)-(46)) in
`Data/Examples/Kubota2026.json`. This file carries the paper's apparatus: the stance
classification, the modal selectional restrictions, and the dual-layer denotation.

## Main definitions

* `Outlook` — the two-layered denotation: prejacent, counterstance presupposition, and an
  outlook-indexed stance layer (an `Intension` into CI content).
* `StanceType` — the four evaluative stances ([kubota-2026] (1)-(2)).
* `Marker` — the per-particle classification (form + stance + modal compatibility).
* `saltDenotation` — the `Outlook` denotation of a *nanka*/*dōse*-marked clause ((42)).

## Main results

* `saltDenotation_not_rigid` — perspective shift, **derived**: the stance layer tracks the
  outlook (`Intension.IsRigid` fails), so it shifts to the attitude holder under embedding
  ((42)), unlike a pure expressive (`Outlook.ofTwoDimProp`, rigid by construction).
* `ciItem_resolve_eq_toTwoDimProp`, `ciItem_shifts_iff_not_rigid` — the outlook index
  generalizes [harris-potts-2009]'s orientation variable: a `CIItem` embeds as an `Outlook`
  with trivial counterstance, and the two shift diagnostics coincide.
* `outlookMarker_shifts_unlike_expressive`, `outlookMarker_patterns_with_hardPresup` — the
  diagnostic profile places outlook markers between pure expressives and presupposition
  triggers ([potts-2007] (27)): they perspective-shift unlike expressives, yet pattern with
  (anaphoric) presuppositions on displaceability and discourse-antecedent need.
* `semete_rejects_epistemic`, `nanka_accepts_all_modals`, `semete_only_documented_restriction`
  — the modal selectional facts ([kubota-2026] (45)-(46)).
* `felicitous_iff_counterstance_salient` — over the (37)-(39) rows, an outlook-marked
  utterance is felicitous iff the discourse context makes a counterstance salient.
* `modal_row_acceptable_iff_compat` — over the (45)-(46) rows, acceptability is exactly
  membership of the row's modal flavor in the marker's `modalCompat`.

## References

[kubota-2026] [kubota-ido-2025] [coppock-2018] [kennedy-willer-2016] [farkas-bruce-2010]
[potts-2005] [potts-2007] [harris-potts-2009] [tonhauser-beaver-roberts-simons-2013]
[heim-1992] [gutzmann-2015]
-/

namespace Kubota2026

open Pragmatics.Expressives (TwoDimProp SecondaryMeaningProperties expressiveProperties)
open Intensional (Intension)
open Semantics.Modality (ModalFlavor)
open Japanese.OutlookMarkers (OutlookMarkerForm)
open Data.Examples (LinguisticExample)
open Semantics.Presupposition (PartialProp)

/-! ### Stance classification -/

/-- The evaluative stance an outlook marker expresses ([kubota-2026] (1)-(2)): how the
speaker situates the prejacent relative to a salient counterstance. -/
inductive StanceType where
  /-- Low evaluation ([kubota-2026]'s term): the prejacent is undesirable or implausible
      (*nanka* 'anything like', *dōse* 'anyway'). -/
  | negative
  /-- Minimum standard: the least one could settle for (*semete*/*kurai* 'at least'). -/
  | minimum
  /-- Contrary to expectation (*mushiro*/*kaette* 'rather', *yoppodo* 'much more'). -/
  | contrary
  /-- Emphatic confirmation (*masani*/*koso* 'precisely'). -/
  | emphasis
  deriving DecidableEq, Repr, Inhabited

/-! ### Modal selectional restrictions

[kubota-2026] (45)-(46): outlook markers select for modal flavors. Stored as a
`List ModalFlavor` used as a set — a `List` kernel-reduces under `decide` (the proofs below
and the `Examples.all` row theorems rely on this), whereas `Finset` membership does not. -/

/-- The modal flavors a marker is compatible with (a `List` used as a set). -/
abbrev ModalCompatibility := List ModalFlavor

/-! ### Per-particle classification -/

/-- A per-particle classification: the Fragment form plus [kubota-2026]'s stance and modal
selectional restriction. -/
structure Marker where
  /-- The theory-neutral lexical form, from `Fragments/Japanese/Particles.lean`. -/
  form : OutlookMarkerForm
  /-- The evaluative stance. [kubota-2026] gives the four `StanceType`s ((1)-(2)) but no
  per-particle table, so the assignment is the formaliser's gloss-based reading. -/
  stance : StanceType
  /-- The modal flavors the marker tolerates. Only *nanka* (all) and *semete*
  (`[.deontic, .bouletic]`) are documented by [kubota-2026]; see `Marker.semete`. -/
  modalCompat : ModalCompatibility
  deriving Repr

namespace Marker

/-! The stance assignments are the formaliser's gloss-based reading of [kubota-2026]'s four
categories ((1)-(2)); the chapter tabulates none. `modalCompat` is `ModalFlavor.all` for
every marker except the two [kubota-2026] documents — *nanka* (all flavors, (45)) and
*semete* (`[.deontic, .bouletic]`, (46)) — so `.all` elsewhere is an untested default, not
an attested claim of unrestricted selection. -/

/-- *dōse* 'anyway' — pessimistic outlook ([kubota-2026] (3a)). -/
def dōse : Marker := ⟨Japanese.OutlookMarkers.dōse, .negative, ModalFlavor.all⟩
def shosen : Marker := ⟨Japanese.OutlookMarkers.shosen, .negative, ModalFlavor.all⟩
/-- *yahari* 'after all/as expected' — emphatic confirmation of an expectation; [kubota-2026]
    (11)-(12) contrast *yahari* 'as expected' against *mushiro* 'rather' (contrary), which
    supports the `.emphasis` reading. -/
def yahari : Marker := ⟨Japanese.OutlookMarkers.yahari, .emphasis, ModalFlavor.all⟩
/-- *kekkyoku* 'after all/in the end' — conclusive/resignative. [kubota-2026] gives no
    per-word stance table (the (1)-(2) groupings are by gloss and source, not stance — note
    *yahari*, in the same (1a) group, is emphasis), so this assignment is tentative. -/
def kekkyoku : Marker := ⟨Japanese.OutlookMarkers.kekkyoku, .emphasis, ModalFlavor.all⟩
def masani : Marker := ⟨Japanese.OutlookMarkers.masani, .emphasis, ModalFlavor.all⟩
def mushiro : Marker := ⟨Japanese.OutlookMarkers.mushiro, .contrary, ModalFlavor.all⟩
def kaette : Marker := ⟨Japanese.OutlookMarkers.kaette, .contrary, ModalFlavor.all⟩
def yoppodo : Marker := ⟨Japanese.OutlookMarkers.yoppodo, .contrary, ModalFlavor.all⟩
/-- *semete* 'at least' selects deontic/desiderative ordering sources, not epistemic/ability
    ([kubota-2026] (46)). -/
def semete : Marker := ⟨Japanese.OutlookMarkers.semete, .minimum, [.deontic, .bouletic]⟩
/-- *mashite* 'let alone, much less' — an a-fortiori scalar marker, arguably the scalar
    opposite of *semete*; the `.minimum` grouping is the weakest stance assignment here. -/
def mashite : Marker := ⟨Japanese.OutlookMarkers.mashite, .minimum, ModalFlavor.all⟩
/-- *nanka* — the prototypical outlook marker; compatible with all flavors, evaluative force
    varying by flavor ([kubota-2026] (45)). -/
def nanka : Marker := ⟨Japanese.OutlookMarkers.nanka, .negative, ModalFlavor.all⟩
def kurai : Marker := ⟨Japanese.OutlookMarkers.kurai, .minimum, ModalFlavor.all⟩
def koso : Marker := ⟨Japanese.OutlookMarkers.koso, .emphasis, ModalFlavor.all⟩

/-- The classified Japanese outlook markers. -/
def all : List Marker :=
  [dōse, shosen, yahari, kekkyoku, masani, mushiro, kaette, yoppodo, semete, mashite,
   nanka, kurai, koso]

/-! #### Modal selection ([kubota-2026] (45)-(46)) -/

/-- *semete* rejects epistemic modals ([kubota-2026] (46a)). -/
theorem semete_rejects_epistemic : ModalFlavor.epistemic ∉ semete.modalCompat := by decide

/-- *semete* accepts deontic modals ([kubota-2026] (46d)). -/
theorem semete_accepts_deontic : ModalFlavor.deontic ∈ semete.modalCompat := by decide

/-- *nanka* accepts every modal flavor (the evaluative force varies; [kubota-2026] (45)). -/
theorem nanka_accepts_all_modals (f : ModalFlavor) : f ∈ nanka.modalCompat := by
  cases f <;> decide

/-- *semete* is the only marker whose modal restriction [kubota-2026] documents (via (46));
the other markers carry the `.all` default, so this is a fact about the classification as
recorded here, **not** a claim that *semete* is uniquely restricted in Japanese —
[kubota-2026] notes that outlook markers *often* differ in modal compatibility and gives
*semete* only as an example. -/
theorem semete_only_documented_restriction :
    (all.filter (fun m => decide (ModalFlavor.epistemic ∉ m.modalCompat))).map (·.form.romaji)
      = ["semete"] := by decide

end Marker

/-! ### The paper's rows ([kubota-2026] (10), (37)-(46))

The judgment data live in `Data/Examples/Kubota2026.json`. The adapters read a row's
`paperFeatures` back into the theory's vocabulary; the theorems restate the paper's
generalizations as facts about the rows. -/

/-- The row's marker, as classified in `Marker.all` (by romaji form). -/
def markerOf (row : LinguisticExample) : Option Marker :=
  (row.feature? "marker").bind fun r => Marker.all.find? (·.form.romaji == r)

/-- The row's modal flavor, from the `modalFlavor` feature. -/
def flavorOf (row : LinguisticExample) : Option ModalFlavor :=
  match row.feature? "modalFlavor" with
  | some "epistemic"      => some .epistemic
  | some "deontic"        => some .deontic
  | some "bouletic"       => some .bouletic
  | some "circumstantial" => some .circumstantial
  | _                     => none

/-- **Counterstance requirement** ([kubota-2026] (37)-(39)): an outlook-marked utterance
is felicitous iff the discourse context makes a counterstance salient — (37)/(39)-Q1
follow an evaluative assertion or question, (38)/(39)-Q2 a neutral question. -/
theorem felicitous_iff_counterstance_salient :
    ∀ row ∈ Examples.all, row.feature? "phenomenon" = some "counterstance" →
      (row.judgment = .acceptable ↔ row.feature? "counterstanceSalient" = some "true") := by
  decide

/-- The theory's prediction for a marker–modal row: the row's flavor lies in the
marker's selectional restriction. -/
def predictedCompat (row : LinguisticExample) : Option Bool := do
  pure (decide ((← flavorOf row) ∈ (← markerOf row).modalCompat))

/-- **Modal selection over the rows** ([kubota-2026] (45)-(46)): a marker–modal row is
acceptable iff the marker's `modalCompat` contains the row's flavor — the selectional
restrictions in `Marker` are exactly the attested judgment pattern. -/
theorem modal_row_acceptable_iff_compat :
    ∀ row ∈ Examples.all, row.feature? "phenomenon" = some "modalInteraction" →
      (row.judgment = .acceptable ↔ predictedCompat row = some true) := by
  decide

/-! ### Outlook denotation

The two-layered denotation of [kubota-2026] §3: an at-issue prejacent, a presupposed salient
counterstance, and a stance layer indexed by an outlook `O`. Perspective shift ((42)) is
*derived*: the stance layer is an `Intension O (W → Prop)`, and shiftability is exactly the
failure of `Intension.IsRigid` — a pure expressive is the constant (rigid) family, so it
cannot shift. -/

/-- An outlook-indexed two-layered meaning ([kubota-2026] §3): at-issue content is shared
across outlooks (only the stance layer shifts), so the prejacent is stored once and the
stance layer is a function of the outlook. -/
structure Outlook (W O : Type*) where
  /-- At-issue content (the *prejacent*), outlook-independent. -/
  prejacent : W → Prop
  /-- Presupposed salient counterstance ([kubota-2026] (37)-(39)). -/
  counterstance : W → Prop
  /-- Evaluative stance layer, relative to an outlook. -/
  evaluation : Intension O (W → Prop)

namespace Outlook

variable {W O : Type*}

/-- Presuppositional projection: the counterstance is the presupposition, the prejacent the
assertion. Outlook-independent. -/
@[simps] def toPartialProp (m : Outlook W O) : PartialProp W := ⟨m.counterstance, m.prejacent⟩

/-- Two-dimensional projection at an outlook `o`: an ordinary `TwoDimProp` recovered by
fixing the perspective. -/
@[simps] def toTwoDimProp (m : Outlook W O) (o : O) : TwoDimProp W := ⟨m.prejacent, m.evaluation o⟩

/-- The counterstance (presupposition) projects through negation — via `PartialProp.neg`. -/
theorem counterstance_projects_through_neg (m : Outlook W O) :
    (PartialProp.neg m.toPartialProp).presup = m.counterstance := rfl

/-- The stance layer projects through negation at a fixed outlook — via `TwoDimProp.neg`. -/
theorem ci_projects_through_neg (m : Outlook W O) (o : O) :
    (TwoDimProp.neg (m.toTwoDimProp o)).ci = m.evaluation o := rfl

/-- An outlook is **rigid** when its stance layer ignores the outlook — `Intension.IsRigid`
applied to `evaluation`. Perspective shift is exactly the failure of this. -/
def IsRigid (m : Outlook W O) : Prop := Intension.IsRigid m.evaluation

/-- A `TwoDimProp` (a pure expressive — a single, speaker-rigid CI) as the constant outlook
family — `Intension.rigid` on the CI tier, with the trivial counterstance. -/
def ofTwoDimProp (t : TwoDimProp W) : Outlook W O where
  prejacent := t.atIssue
  counterstance := fun _ => True
  evaluation := Intension.rigid t.ci

@[simp] theorem ofTwoDimProp_toTwoDimProp (t : TwoDimProp W) (o : O) :
    (ofTwoDimProp t).toTwoDimProp o = t := rfl

/-- Every embedded `TwoDimProp` is rigid by construction (`Intension.rigid_isRigid`) — on
[potts-2005]'s speaker-orientation idealization, a pure expressive does not shift;
[harris-potts-2009] document pragmatic non-speaker orientation even unembedded, so rigidity
models the idealization, not an absolute. -/
theorem ofTwoDimProp_isRigid (t : TwoDimProp W) : (ofTwoDimProp (O := O) t).IsRigid :=
  Intension.rigid_isRigid t.ci

end Outlook

/-! ### Perspective shift, derived -/

/-- [kubota-2026] (42) (`Examples.ex42_perspective_shift`): "My advisor thought I wouldn't
get into SALT (*nanka*/*dōse*)." `O := Bool` (advisor's pessimistic outlook vs. speaker's
confident one); the negative evaluation holds exactly at the pessimistic outlook.

A minimal model: `prejacent`/`counterstance` are stubbed to `fun _ => True`, isolating the
outlook-relative `evaluation` — the only field the perspective-shift result turns on. -/
def saltDenotation : Outlook Unit Bool where
  prejacent := fun _ => True
  counterstance := fun _ => True
  evaluation := fun pessimistic _ => pessimistic = true

/-- **Perspective shift, derived** ([kubota-2026] (42)): the marker's stance layer is not
rigid — it differs across outlooks, so under embedding it shifts to the holder (a
local-accommodation pattern, [heim-1992]). Routed through `Intension.varying_not_rigid`;
this is the structural fact mirrored by the `allowsPerspectiveShift` diagnostic (see
`outlookMarker_shifts_unlike_expressive`). -/
theorem saltDenotation_not_rigid : ¬ saltDenotation.IsRigid :=
  Intension.varying_not_rigid saltDenotation.evaluation true false fun h => by
    simpa [saltDenotation] using congrFun h ()

/-- Contrast: a pure expressive (`Outlook.ofTwoDimProp`) is rigid — it cannot perspective
shift. The difference between this and `saltDenotation_not_rigid` *is* the
`allowsPerspectiveShift` diagnostic. -/
theorem expressive_rigid (t : TwoDimProp Unit) :
    (Outlook.ofTwoDimProp (O := Bool) t).IsRigid :=
  Outlook.ofTwoDimProp_isRigid t

/-! ### Bridge to [harris-potts-2009]'s orientation variable

The outlook index generalizes the orientation variable of [harris-potts-2009]
(`HarrisPotts2009.CIItem`): a `CIItem` is an `Outlook` over `O := Orientation Person` with
trivial counterstance, resolution coincides with the two-dimensional projection, and the two
accounts' shift diagnostics agree — a non-speaker-oriented reading exists exactly when the
embedded outlook is not rigid. -/

/-- A [harris-potts-2009] CI item as an `Outlook` over orientations: same at-issue content
and orientation-indexed CI, trivial counterstance. -/
def _root_.HarrisPotts2009.CIItem.toOutlook {Person W : Type}
    (item : HarrisPotts2009.CIItem Person W) :
    Outlook W (HarrisPotts2009.Orientation Person) :=
  ⟨item.atIssue, fun _ => True, item.ciFor⟩

/-- Orientation resolution is the two-dimensional projection of the embedded outlook. -/
theorem ciItem_resolve_eq_toTwoDimProp {Person W : Type}
    (item : HarrisPotts2009.CIItem Person W) (o : HarrisPotts2009.Orientation Person) :
    item.resolve o = item.toOutlook.toTwoDimProp o := rfl

/-- The two shift diagnostics agree: some pair of orientations resolves to different
two-dimensional meanings iff the embedded outlook is not rigid. -/
theorem ciItem_shifts_iff_not_rigid {Person W : Type}
    (item : HarrisPotts2009.CIItem Person W) :
    (∃ o₁ o₂, item.resolve o₁ ≠ item.resolve o₂) ↔ ¬ item.toOutlook.IsRigid := by
  simp [HarrisPotts2009.CIItem.resolve, HarrisPotts2009.CIItem.toOutlook, Outlook.IsRigid,
    Intensional.Intension.IsRigid, TwoDimProp.mk.injEq, not_forall]

/-- The counterstance projects through negation (via `PartialProp.neg`), and the CI tier
projects at each outlook (via `TwoDimProp.neg`) — the dual presupposition/CI projection. -/
theorem saltDenotation_projects (o : Bool) :
    (PartialProp.neg saltDenotation.toPartialProp).presup = saltDenotation.counterstance ∧
    (TwoDimProp.neg (saltDenotation.toTwoDimProp o)).ci = saltDenotation.evaluation o :=
  ⟨Outlook.counterstance_projects_through_neg _, Outlook.ci_projects_through_neg _ _⟩

/-! ### Diagnostic fingerprint ([potts-2007] (27))

The [potts-2007] six-diagnostic fingerprint (`SecondaryMeaningProperties`), extended by the
two contrasts [kubota-2026] §3 turns on. Both extensions reify the chapter's prose
observations, not entries in [potts-2007]'s table; the `allowsPerspectiveShift` field is the
editorial counterpart of the structural `saltDenotation_not_rigid` above. -/

/-- [kubota-2026]'s diagnostic profile: [potts-2007]'s six diagnostics plus the two contrasts
distinguishing outlook markers from pure expressives and pure presupposition triggers. -/
structure OutlookDiagnostics extends SecondaryMeaningProperties where
  /-- Readily receives a shifted (attitude-holder) reading under embedding ([kubota-2026]
  (42)) — a local-accommodation pattern ([heim-1992]). `false` records "not readily", not
  "never": [harris-potts-2009] document pragmatic non-speaker orientation even for
  unembedded expressives. -/
  allowsPerspectiveShift : Bool
  /-- Requires a salient issue/counterstance in prior discourse ([kubota-2026] (37)-(39)). -/
  requiresDiscourseAntecedent : Bool
  deriving Repr, DecidableEq

/-- Diagnostic profile of outlook markers ([kubota-2026] §3): shares descriptive ineffability
and immediacy with expressives, but lacks independence and nondisplaceability and allows
perspective shift (the structural counterpart is `saltDenotation_not_rigid`). -/
def outlookMarkerProfile : OutlookDiagnostics where
  independent := false
  nondisplaceable := false
  perspectiveDependent := true
  descriptivelyIneffable := true
  immediate := true
  repeatable := false
  allowsPerspectiveShift := true
  requiresDiscourseAntecedent := true

/-- A pure expressive's profile: the six [potts-2007] diagnostics from the substrate's
`expressiveProperties`, not readily shifted under embedding and needing no discourse
antecedent ([kubota-2026]'s contrast class). -/
def expressiveDiagnostics : OutlookDiagnostics :=
  { toSecondaryMeaningProperties := expressiveProperties
  , allowsPerspectiveShift := false
  , requiresDiscourseAntecedent := false }

/-- Diagnostic profile of an anaphoric/additive presupposition trigger (*mata* 'again'), for
contrast ([kubota-2026]'s comparison class). It shares `allowsPerspectiveShift` with outlook
markers — but for a different reason: an ordinary presupposition shifts by local satisfaction
in the attitude holder's alternatives ([heim-1992]), not by stance-layer non-rigidity. -/
def hardPresupProfile : OutlookDiagnostics where
  independent := false
  nondisplaceable := false
  perspectiveDependent := false
  descriptivelyIneffable := false
  immediate := false
  repeatable := false
  allowsPerspectiveShift := true
  requiresDiscourseAntecedent := true

/-- Outlook markers perspective-shift, pure expressives do not — the diagnostic that the
`saltDenotation_not_rigid` vs `expressive_rigid` contrast realizes ([kubota-2026];
[potts-2007]). -/
theorem outlookMarker_shifts_unlike_expressive :
    outlookMarkerProfile.allowsPerspectiveShift
      ≠ expressiveDiagnostics.allowsPerspectiveShift := by decide

/-- Outlook markers pattern *with* (anaphoric) presupposition triggers on displaceability and
discourse-antecedent need ([kubota-2026]): the two added diagnostics do not separate them. -/
theorem outlookMarker_patterns_with_hardPresup :
    outlookMarkerProfile.allowsPerspectiveShift = hardPresupProfile.allowsPerspectiveShift ∧
    outlookMarkerProfile.requiresDiscourseAntecedent
      = hardPresupProfile.requiresDiscourseAntecedent := by decide

/-- What *does* separate outlook markers from presupposition triggers: descriptive
ineffability (the expressive-like diagnostic; [kubota-2026], [potts-2007]). -/
theorem outlookMarker_ineffable_unlike_hardPresup :
    outlookMarkerProfile.descriptivelyIneffable ≠ hardPresupProfile.descriptivelyIneffable := by
  decide

end Kubota2026
