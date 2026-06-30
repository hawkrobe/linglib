import Linglib.Pragmatics.Expressives.Outlook
import Linglib.Semantics.Modality.ModalTypes
import Linglib.Fragments.Japanese.Particles
import Linglib.Data.Examples.Kubota2026

/-!
# Kubota 2026: outlook management
[kubota-2026] [kubota-ido-2025] [coppock-2018] [farkas-bruce-2010] [potts-2007]

[kubota-2026]'s analysis of Japanese *outlook markers* (*nanka*, *dōse*, *semete*, *koso*,
*mushiro*, …): discourse-sensitive adverbs and focus particles with a two-layered secondary
meaning — a presuppositional counterstance requirement plus an expressive-like evaluative
stance — built on [coppock-2018]'s outlook-based semantics. An outlook marker denotes an
`Outlook`: an outlook-indexed two-dimensional meaning carrying a counterstance presupposition
and an outlook-relative evaluation. The perspective index is the orientation variable of
[harris-potts-2009]; the secondary-meaning diagnostics ([potts-2007] (27)) follow the
projection typology of [tonhauser-beaver-roberts-simons-2013].

The handbook chapter [kubota-2026] is descriptive and defers the formal analysis to its
companion [kubota-ido-2025]; the apparatus formalised here (the `Outlook` denotation, the
perspective-shift result) is theirs. The discourse dynamics they invoke — the
[farkas-bruce-2010] Table model and a [heim-1992] local-satisfaction account of perspective
shift — are *not* modelled here: `saltDenotation` is a minimal `Outlook` with
`prejacent`/`counterstance` stubbed, and counterstance salience is read off the
discourse-context features of the data rows, not derived from a Table update. Deriving
felicity from the denotation against a real Table state is the natural follow-up. The rival
framing is [gutzmann-2015]'s use-conditional treatment of counterstance particles (e.g.
German *doch*), where the second layer is use-conditional rather than presuppositional.

The lexical inventory is theory-neutral and lives in `Fragments/Japanese/Particles.lean`
(`Japanese.OutlookMarkers`); the judgment data ((10), (37)-(46)) in
`Data/Examples/Kubota2026.json`. This file carries the paper's apparatus: the stance
classification, the modal selectional restrictions, and the dual-layer denotation.

## Main definitions

* `StanceType` — the four evaluative stances ([kubota-2026] (1)-(2)).
* `Marker` — the per-particle classification (form + stance + modal compatibility).
* `saltDenotation` — the `Outlook` denotation of a *nanka*/*dōse*-marked clause ((42)).

## Main results

* `saltDenotation_not_rigid` — perspective shift, **derived**: the CI tracks the outlook, so
  unlike a pure expressive (`Outlook.ofTwoDimProp`, which is `IsRigid`) it shifts to the
  attitude holder under embedding ((42)).
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

[kubota-2026] [kubota-ido-2025] [coppock-2018] [farkas-bruce-2010] [potts-2007]
[harris-potts-2009] [tonhauser-beaver-roberts-simons-2013] [heim-1992] [gutzmann-2015]
-/

namespace Kubota2026

open Pragmatics.Expressives (Outlook TwoDimProp SecondaryMeaningProperties expressiveProperties)
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

/-- Value of a `paperFeatures` key, if present. -/
private def featureOf (row : LinguisticExample) (key : String) : Option String :=
  (row.paperFeatures.find? (·.1 == key)).map (·.2)

/-- The row's marker, as classified in `Marker.all` (by romaji form). -/
def markerOf (row : LinguisticExample) : Option Marker :=
  (featureOf row "marker").bind fun r => Marker.all.find? (·.form.romaji == r)

/-- The row's modal flavor, from the `modalFlavor` feature. -/
def flavorOf (row : LinguisticExample) : Option ModalFlavor :=
  match featureOf row "modalFlavor" with
  | some "epistemic"      => some .epistemic
  | some "deontic"        => some .deontic
  | some "bouletic"       => some .bouletic
  | some "circumstantial" => some .circumstantial
  | _                     => none

/-- **Counterstance requirement** ([kubota-2026] (37)-(39)): an outlook-marked utterance
is felicitous iff the discourse context makes a counterstance salient — (37)/(39)-Q1
follow an evaluative assertion or question, (38)/(39)-Q2 a neutral question. -/
theorem felicitous_iff_counterstance_salient :
    ∀ row ∈ Examples.all, featureOf row "phenomenon" = some "counterstance" →
      (row.judgment = .acceptable ↔ featureOf row "counterstanceSalient" = some "true") := by
  decide

/-- The theory's prediction for a marker–modal row: the row's flavor lies in the
marker's selectional restriction. -/
def predictedCompat (row : LinguisticExample) : Option Bool := do
  pure (decide ((← flavorOf row) ∈ (← markerOf row).modalCompat))

/-- **Modal selection over the rows** ([kubota-2026] (45)-(46)): a marker–modal row is
acceptable iff the marker's `modalCompat` contains the row's flavor — the selectional
restrictions in `Marker` are exactly the attested judgment pattern. -/
theorem modal_row_acceptable_iff_compat :
    ∀ row ∈ Examples.all, featureOf row "phenomenon" = some "modalInteraction" →
      (row.judgment = .acceptable ↔ predictedCompat row = some true) := by
  decide

/-! ### Outlook denotation and perspective shift

An outlook marker denotes an `Outlook` ([coppock-2018]): a counterstance presupposition plus
an outlook-relative evaluation. Perspective shift ([kubota-2026] (42)) is then *derived* — the
CI tracks the outlook, so under an attitude verb (which supplies the holder's outlook) it
shifts to the holder, unlike a pure expressive. -/

/-- [kubota-2026] (42) (`Examples.ex42_perspective_shift`): "My advisor thought I wouldn't
get into SALT (*nanka*/*dōse*)." `O := Bool` (advisor's pessimistic outlook vs. speaker's
confident one); the negative evaluation holds exactly at the pessimistic outlook.

A minimal model: `prejacent`/`counterstance` are stubbed to `fun _ => True`, isolating the
outlook-relative `evaluation` — the only field the perspective-shift result turns on. -/
def saltDenotation : Outlook Unit Bool where
  prejacent := fun _ => True
  counterstance := fun _ => True
  evaluation := fun pessimistic _ => pessimistic = true

/-- **Perspective shift, derived** ([kubota-2026] (42)): the marker's CI is not rigid — it
differs across outlooks, so an attitude verb shifts it to the holder. Routed through the
substrate's `Outlook.not_isRigid_of_evaluation_ne`; this is the structural fact mirrored by
the `allowsPerspectiveShift` diagnostic (see `outlookMarker_shifts_unlike_expressive`). -/
theorem saltDenotation_not_rigid : ¬ saltDenotation.IsRigid :=
  Outlook.not_isRigid_of_evaluation_ne (o₁ := true) (o₂ := false) fun h => by
    simpa [saltDenotation] using congrFun h ()

/-- Contrast: a pure expressive (`Outlook.ofTwoDimProp`) is rigid — it cannot perspective
shift. The difference between this and `saltDenotation_not_rigid` *is* the
`allowsPerspectiveShift` diagnostic. -/
theorem expressive_rigid (t : TwoDimProp Unit) :
    (Outlook.ofTwoDimProp (O := Bool) t).IsRigid :=
  Outlook.ofTwoDimProp_isRigid t

/-- The counterstance projects through negation (via `PartialProp.neg`), and the CI tier
projects at each outlook (via `TwoDimProp.neg`) — the dual presupposition/CI projection. -/
theorem saltDenotation_projects (o : Bool) :
    (PartialProp.neg saltDenotation.toPartialProp).presup = saltDenotation.counterstance ∧
    (TwoDimProp.neg (saltDenotation.toTwoDimProp o)).ci = saltDenotation.evaluation o :=
  ⟨Outlook.counterstance_projects_through_neg _, Outlook.ci_projects_through_neg _ _⟩

/-! ### Diagnostic fingerprint ([potts-2007] (27))

The theory-neutral diagnostic profile [kubota-2026] argues outlook markers exhibit. The
`allowsPerspectiveShift` field is the editorial counterpart of the structural
`saltDenotation_not_rigid` above; the discrimination theorems below pin which diagnostics
separate the profile from a pure expressive and from a presupposition trigger. -/

/-- Diagnostic profile of outlook markers ([kubota-2026] §3): shares descriptive ineffability
and immediacy with expressives, but lacks independence and nondisplaceability and allows
perspective shift (the structural counterpart is `saltDenotation_not_rigid`). -/
def outlookMarkerProfile : SecondaryMeaningProperties where
  independent := false
  nondisplaceable := false
  perspectiveDependent := true
  descriptivelyIneffable := true
  immediate := true
  repeatable := false
  allowsPerspectiveShift := true
  requiresDiscourseAntecedent := true

/-- Diagnostic profile of an anaphoric/additive presupposition trigger (*mata* 'again'), for
contrast ([kubota-2026]'s comparison class). It shares `allowsPerspectiveShift` with outlook
markers — but for a different reason: an ordinary presupposition shifts by local satisfaction
in the attitude holder's alternatives ([heim-1992]), not by CI non-rigidity. -/
def hardPresupProfile : SecondaryMeaningProperties where
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
      ≠ expressiveProperties.allowsPerspectiveShift := by decide

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
