import Linglib.Pragmatics.Expressives.Outlook
import Linglib.Semantics.Modality.ModalTypes
import Linglib.Fragments.Japanese.Particles

/-!
# Kubota 2026: outlook management
[kubota-2026] [coppock-2018] [farkas-bruce-2010] [potts-2007]

[kubota-2026]'s analysis of Japanese *outlook markers* (*nanka*, *dōse*, *semete*, *koso*,
*mushiro*, …): discourse-sensitive adverbs and focus particles with two-layered secondary
meaning — a presuppositional counterstance requirement and an expressive-like evaluative
stance. The dual nature is meant to fall out of the single counterstance-marking function,
formalised via [coppock-2018]'s outlook-based semantics and the [farkas-bruce-2010] Table
model; an outlook marker denotes an `Outlook` (an outlook-indexed two-dimensional meaning).

The lexical inventory is theory-neutral and lives in `Fragments/Japanese/Particles.lean`
(`Japanese.OutlookMarkers`); this file carries the paper's apparatus: the stance
classification, the modal selectional restrictions, and the dual-layer denotation.

## Main definitions

* `StanceType` — the four evaluative stances ([kubota-2026] (1)-(2)).
* `Marker` — the per-particle classification (form + stance + modal compatibility).
* `saltDenotation` — the `Outlook` denotation of a *nanka*/*dōse*-marked clause ((42)).

## Main results

* `saltDenotation_not_rigid` — perspective shift, **derived**: the CI tracks the outlook, so
  unlike a pure expressive (`Outlook.ofTwoDimProp`, which is `IsRigid`) it shifts to the
  attitude holder under embedding ((42)).
* `semete_rejects_epistemic`, `nanka_accepts_all_modals`, `semete_unique_modal_restriction`
  — the modal selectional facts ((45)-(46)).

## References

[kubota-2026] [coppock-2018] [farkas-bruce-2010] [potts-2007]
-/

namespace Kubota2026

open Pragmatics.Expressives (Outlook TwoDimProp SecondaryMeaningProperties)
open Semantics.Modality (ModalFlavor)
open Japanese.OutlookMarkers (OutlookMarkerForm)

/-! ### Stance classification -/

/-- The evaluative stance an outlook marker expresses ([kubota-2026] (1)-(2)): how the
speaker situates the prejacent relative to a salient counterstance. -/
inductive StanceType where
  /-- Negative/pessimistic: the prejacent is undesirable or implausible
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

[kubota-2026] (45)-(46): outlook markers select for modal flavors (`List ModalFlavor`, used
as a set; see `Pragmatics.Expressives.Outlook` for the `List`-vs-`Finset` rationale). -/

/-- The modal flavors a marker is compatible with. -/
abbrev ModalCompatibility := List ModalFlavor

/-! ### Per-particle classification -/

/-- A per-particle classification: the Fragment form plus [kubota-2026]'s stance and modal
selectional restriction. -/
structure Marker where
  form : OutlookMarkerForm
  stance : StanceType
  modalCompat : ModalCompatibility
  deriving Repr

namespace Marker

/-- *dōse* 'anyway' — pessimistic outlook ([kubota-2026] (3a)). -/
def dōse : Marker := ⟨Japanese.OutlookMarkers.dōse, .negative, ModalFlavor.all⟩
def shosen : Marker := ⟨Japanese.OutlookMarkers.shosen, .negative, ModalFlavor.all⟩
def yahari : Marker := ⟨Japanese.OutlookMarkers.yahari, .emphasis, ModalFlavor.all⟩
def kekkyoku : Marker := ⟨Japanese.OutlookMarkers.kekkyoku, .emphasis, ModalFlavor.all⟩
def masani : Marker := ⟨Japanese.OutlookMarkers.masani, .emphasis, ModalFlavor.all⟩
def mushiro : Marker := ⟨Japanese.OutlookMarkers.mushiro, .contrary, ModalFlavor.all⟩
def kaette : Marker := ⟨Japanese.OutlookMarkers.kaette, .contrary, ModalFlavor.all⟩
def yoppodo : Marker := ⟨Japanese.OutlookMarkers.yoppodo, .contrary, ModalFlavor.all⟩
/-- *semete* 'at least' selects deontic/desiderative ordering sources, not epistemic/ability
    ([kubota-2026] (46)). -/
def semete : Marker := ⟨Japanese.OutlookMarkers.semete, .minimum, [.deontic, .bouletic]⟩
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

/-! #### Per-particle stance ([kubota-2026] (1)-(2)) -/

theorem dōse_is_negative : dōse.stance = .negative := rfl
theorem shosen_is_negative : shosen.stance = .negative := rfl
theorem yahari_is_emphasis : yahari.stance = .emphasis := rfl
theorem kekkyoku_is_emphasis : kekkyoku.stance = .emphasis := rfl
theorem masani_is_emphasis : masani.stance = .emphasis := rfl
theorem mushiro_is_contrary : mushiro.stance = .contrary := rfl
theorem kaette_is_contrary : kaette.stance = .contrary := rfl
theorem yoppodo_is_contrary : yoppodo.stance = .contrary := rfl
theorem semete_is_minimum : semete.stance = .minimum := rfl
theorem mashite_is_minimum : mashite.stance = .minimum := rfl
theorem nanka_is_negative : nanka.stance = .negative := rfl
theorem kurai_is_minimum : kurai.stance = .minimum := rfl
theorem koso_is_emphasis : koso.stance = .emphasis := rfl

/-! #### Modal selection ([kubota-2026] (45)-(46)) -/

/-- *semete* rejects epistemic modals ([kubota-2026] (46a)). -/
theorem semete_rejects_epistemic : ModalFlavor.epistemic ∉ semete.modalCompat := by decide

/-- *semete* accepts deontic modals ([kubota-2026] (46d)). -/
theorem semete_accepts_deontic : ModalFlavor.deontic ∈ semete.modalCompat := by decide

/-- *nanka* accepts every modal flavor (the evaluative force varies; [kubota-2026] (45)). -/
theorem nanka_accepts_all_modals (f : ModalFlavor) : f ∈ nanka.modalCompat := by
  cases f <;> decide

/-- *semete* is the only marker that rejects the epistemic flavor ([kubota-2026] (46)). -/
theorem semete_unique_modal_restriction :
    (all.filter (fun m => decide (ModalFlavor.epistemic ∉ m.modalCompat))).map (·.form.romaji)
      = ["semete"] := by decide

end Marker

/-! ### Outlook denotation and perspective shift

An outlook marker denotes an `Outlook` ([coppock-2018]): a counterstance presupposition plus
an outlook-relative evaluation. Perspective shift ([kubota-2026] (42)) is then *derived* — the
CI tracks the outlook, so under an attitude verb (which supplies the holder's outlook) it
shifts to the holder, unlike a pure expressive. -/

/-- [kubota-2026] (42): "My advisor thought I wouldn't get into SALT (*nanka*/*dōse*)."
`O := Bool` (advisor's pessimistic outlook vs. speaker's confident one); the negative
evaluation holds exactly at the pessimistic outlook. -/
def saltDenotation : Outlook Unit Bool where
  prejacent := fun _ => True
  counterstance := fun _ => True
  evaluation := fun pessimistic _ => pessimistic = true

/-- **Perspective shift, derived** ([kubota-2026] (42)): the marker's CI is not rigid — it
differs across outlooks, so an attitude verb shifts it to the holder. This is the structural
fact behind `outlookMarkerProfile.allowsPerspectiveShift = true`. -/
theorem saltDenotation_not_rigid : ¬ saltDenotation.IsRigid := by
  intro h
  have h1 : saltDenotation.evaluation true () := rfl
  exact Bool.noConfusion ((h true false) ▸ h1)

/-- Contrast: a pure expressive (`Outlook.ofTwoDimProp`) is rigid — it cannot perspective
shift. The difference between this and `saltDenotation_not_rigid` *is* the
`allowsPerspectiveShift` diagnostic. -/
theorem expressive_rigid (t : TwoDimProp Unit) :
    (Outlook.ofTwoDimProp (O := Bool) t).IsRigid :=
  Outlook.ofTwoDimProp_isRigid t

/-- The counterstance projects through negation (via `PrProp.neg`), and the CI tier projects
at each outlook (via `TwoDimProp.neg`) — the dual presupposition/CI projection. -/
theorem saltDenotation_projects (o : Bool) :
    (Semantics.Presupposition.PrProp.neg saltDenotation.toPrProp).presup = saltDenotation.counterstance ∧
    (TwoDimProp.neg (saltDenotation.toTwoDimProp o)).ci = saltDenotation.evaluation o :=
  ⟨Outlook.counterstance_projects_through_neg _, Outlook.ci_projects_through_neg _ _⟩

/-! ### Diagnostic fingerprint ([potts-2007] (27))

The theory-neutral diagnostic profile [kubota-2026] argues outlook markers exhibit. The
perspective fields (`allowsPerspectiveShift`, `nondisplaceable`) are backed by the structural
facts above; the lexical-conceptual fields (ineffability, immediacy) are irreducible. -/

/-- Diagnostic profile of outlook markers ([kubota-2026] §3): shares descriptive ineffability
and immediacy with expressives, but lacks independence and nondisplaceability and allows
perspective shift (the latter derived in `saltDenotation_not_rigid`). -/
def outlookMarkerProfile : SecondaryMeaningProperties where
  independent := false
  nondisplaceable := false
  perspectiveDependent := true
  descriptivelyIneffable := true
  immediate := true
  repeatable := false
  allowsPerspectiveShift := true
  requiresDiscourseAntecedent := true

/-- Diagnostic profile of hard presupposition triggers (*mata* 'again'), for contrast. -/
def hardPresupProfile : SecondaryMeaningProperties where
  independent := false
  nondisplaceable := false
  perspectiveDependent := false
  descriptivelyIneffable := false
  immediate := false
  repeatable := false
  allowsPerspectiveShift := true
  requiresDiscourseAntecedent := true

end Kubota2026
