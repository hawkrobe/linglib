import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Theories.Semantics.Modality.Assert
import Linglib.Theories.Syntax.Minimalism.SpeechActs
import Linglib.Fragments.French.Modals

/-!
# @cite{ruytenbeek-etal-2017}: Indirect Request Processing, Sentence Types
  and Illocutionary Forces

Journal of Pragmatics 119 (2017) 46–62.

Two French eye-tracking experiments testing the **literalist** view that
sentence types encode illocutionary force at the semantic level. Both
studies support **non-literalist** theories: directive force arises from
shared semantic features between imperatives and modal constructions, not
from sentence type per se.

## Two mechanisms for directive force

The paper invokes two routes by which a non-imperative sentence type can
carry directive force:

1. **Shared deontic semantics** (@cite{kaufmann-2012}): a construction
   whose modal flavor matches the imperative's deontic semantics receives
   directive force directly. *Vous devez VP* (Study 2) and *Vous pouvez VP*
   (granting permission, p.58 Discussion) instantiate this route.
2. **Convention of means / preparatory-condition questioning**
   (@cite{clark-1979}): a construction that questions the addressee's
   ability to perform an action receives directive force pragmatically.
   *Pouvez-vous VP?* and *Est-il possible de VP?* (Study 1) instantiate
   this route.

This file formalizes both as decidable predicates on `SentType`, and
defines a joint `SentType.isDirective` diagnostic. The paper's empirical
findings are encoded as predictions of these mechanisms (not as
restatements of raw RT/proportion data — those live in docstrings with
paper page references).

## Cross-paper bridges

- `Theories/Semantics/Modality/Assert.lean`: the imperative's
  `primaryFlavor = .deontic` is the layered foundation;
  `SentType.modalFlavor` for the imperative branch derives from it
  (not restipulated).
- `Phenomena/Directives/Studies/Roberts2023.lean`: a chronologically
  later sibling that contradicts mechanism 1 for the imperative
  prejacent's modal flavor; the cross-paper wedge lives in Roberts2023.

## A note on empirical numbers

The original version of this file hard-coded RT means, fixation
durations, and move-response proportions read off Figs 3/5/6/8. Per the
2026-04-24 audit, these were either reconstructions of percentages
reported in the paper text (frantext counts), upper-bound stipulations
(must.moveProp = 99/120 from "n=21 t/f" plus 18 unallocated errors), or
eyeball reads of bar charts that are demonstrably off (Fig.3's *can* move
≈ 45/123, not the original file's 98/123). The paper's actual claims are
β estimates with confidence intervals (Study 1 p.53, Study 2 p.57) and
significance tests (e.g. z = −3.29, p = 0.0028 for can vs possible
move responses, p.57). This file now records the directional ordering
predictions and lets the statistics live in docstrings — Lean is not the
right place for hand-transcribed regression coefficients.
-/

namespace RuytenbeekEtAl2017

open Core.Modality (ModalFlavor ModalForce)
open Core.Discourse (PreparatoryCondition)
open Semantics.Modality.Assert (primaryFlavor SpeechActType)
open Minimalism.SpeechActs (SAPMood)

/-! ## §1. Sentence types and modal projections -/

/-- The eight sentence types appearing across Studies 1 and 2.

    Study 1 uses `imperative`, `canYouInterrog`, `possibleInterrog`, and
    `ctrlInterrog`. Study 2 uses `imperative`, `mustDeclarative`,
    `canDeclarative`, `possibleDecl`, and `plainDeclarative` (the control
    declarative). The paper also includes 3 *control imperatives* in
    Study 2 alongside the 3 *You must* sentences (p.56) — these collapse
    to `imperative` here since they are imperatives without a polar
    response option. -/
inductive SentType where
  /-- *Mettez le cercle rouge…* — Study 1 + 2 imperative. -/
  | imperative
  /-- *Pouvez-vous VP?* — Study 1 conventionalised IR. -/
  | canYouInterrog
  /-- *Est-il possible de VP?* — Study 1 non-conventionalised IR. -/
  | possibleInterrog
  /-- *Le cercle rouge est-il…?* — Study 1 control interrogative. -/
  | ctrlInterrog
  /-- *Vous devez VP* — Study 2 deontic-necessity declarative. -/
  | mustDeclarative
  /-- *Vous pouvez VP* — Study 2 modal declarative. The paper's
      Discussion (p.58) attributes the construction's directive
      readings to the **permission** sense of *pouvoir* — i.e. deontic
      possibility rather than circumstantial ability. -/
  | canDeclarative
  /-- *Il est possible de VP* — Study 2 existential-possibility
      declarative. -/
  | possibleDecl
  /-- *Le cercle rouge est…* — Study 2 control declarative. -/
  | plainDeclarative
  deriving DecidableEq, Repr

/-- Morphosyntactic mood of each sentence type. -/
def SentType.mood : SentType → SAPMood
  | .imperative       => .imperative
  | .canYouInterrog   => .interrogative
  | .possibleInterrog => .interrogative
  | .ctrlInterrog     => .interrogative
  | .mustDeclarative  => .declarative
  | .canDeclarative   => .declarative
  | .possibleDecl     => .declarative
  | .plainDeclarative => .declarative

/-- Contextually salient modal flavor for each sentence type.

    The imperative branch is **derived** from
    `Semantics.Modality.Assert.primaryFlavor` rather than restipulated
    (layered grounding — see `imperative_modalFlavor_eq_assert` below).

    The `canDeclarative` flavor is `.deontic`, not `.circumstantial`,
    per the paper's Discussion (p.58):
    > "One of the most salient reading of the French *pouvoir* (can) is
    > that of a permission. … granting permission may sometimes be
    > interpreted as a reason to act."

    Permission is deontic possibility, and the paper's Fig.6 *can* >
    *possible* asymmetry in directive interpretation (z = −3.29,
    p = 0.0028, p.57) follows from mechanism 1 firing on `canDeclarative`
    but not on `possibleDecl`. The `canYouInterrog` branch keeps
    `.circumstantial` per p.50 Materials: "in a context where the only
    plausible interpretation of *pouvez* and *possible* is that of an
    ability modal."

    The `.deontic` / `.circumstantial` / `.possibility` choices sit in
    the `Option ModalFlavor` namespace because `ctrlInterrog` and
    `plainDeclarative` carry no modal. -/
def SentType.modalFlavor : SentType → Option ModalFlavor
  | .imperative       => some (primaryFlavor .imperative)
  | .canYouInterrog   => some .circumstantial
  | .possibleInterrog => some .circumstantial
  | .ctrlInterrog     => none
  | .mustDeclarative  => some .deontic
  | .canDeclarative   => some .deontic
  | .possibleDecl     => some .circumstantial
  | .plainDeclarative => none

/-- Modal force (necessity / possibility) for each sentence type. -/
def SentType.modalForce : SentType → Option ModalForce
  | .imperative       => some .necessity
  | .canYouInterrog   => some .possibility
  | .possibleInterrog => some .possibility
  | .ctrlInterrog     => none
  | .mustDeclarative  => some .necessity
  | .canDeclarative   => some .possibility
  | .possibleDecl     => some .possibility
  | .plainDeclarative => none

/-- The imperative's flavor is the same one Hacquard's SAP architecture
    assigns to imperative speech acts — derived, not coincidentally
    equal. Layered Grounding for the headline @cite{kaufmann-2012}
    commitment. -/
theorem imperative_modalFlavor_eq_assert :
    SentType.modalFlavor .imperative = some (primaryFlavor .imperative) := rfl

/-! ## §2. Mechanism 1 — shared deontic semantics (@cite{kaufmann-2012})

A construction is mechanism-1-compatible with directive force when its
modal flavor matches the imperative's. The check is a single equality on
`ModalFlavor`. Mechanism 1 does not distinguish necessity from
possibility — that ranking is a quantitative finding the paper reports
(must >> can in directive rate, p.57) which mechanism 1 alone
underdetermines. -/

/-- Mechanism 1 directive licensing: the construction's modal flavor
    matches the imperative's. -/
def directiveCompatible (flavor : ModalFlavor) : Prop :=
  flavor = primaryFlavor .imperative

instance : DecidablePred directiveCompatible := fun _ => decEq _ _

/-- A sentence type is mechanism-1-compatible iff it has a modal flavor
    matching the imperative's. -/
def SentType.directiveCompatibleMech1 (s : SentType) : Prop :=
  match s.modalFlavor with
  | some f => directiveCompatible f
  | none   => False

instance : DecidablePred SentType.directiveCompatibleMech1 := fun s => by
  unfold SentType.directiveCompatibleMech1
  cases s.modalFlavor with
  | none   => exact .isFalse not_false
  | some f => exact inferInstance

/-! ## §3. Mechanism 2 — preparatory-condition questioning (@cite{clark-1979})

The non-conventionalised IR *Est-il possible de VP?* and the
conventionalised *Pouvez-vous VP?* both target the addressee's ability
to perform the requested action. Per @cite{clark-1979}, asking about a
preparatory condition for a request licenses the directive interpretation
without sharing the imperative's modal semantics. The substrate
`Core.Discourse.PreparatoryCondition` (Searle's hierarchy: ability /
knowledge / memory / perception / permission / willingness) is the
target type; the projection `SentType.queriedPrep` mirrors
`Phenomena/Politeness/Studies/FrancikClark1985.lean`'s
`RequestForm.queriedCondition`. -/

/-- The preparatory condition queried by each sentence type, when one is
    queried. The two interrogative IRs both query `.ability`. -/
def SentType.queriedPrep : SentType → Option PreparatoryCondition
  | .canYouInterrog   => some .ability
  | .possibleInterrog => some .ability
  | _                 => none

/-- Mechanism 2 directive licensing: the construction queries an
    addressee preparatory condition. -/
def SentType.directiveCompatibleMech2 (s : SentType) : Prop :=
  s.queriedPrep.isSome

instance : DecidablePred SentType.directiveCompatibleMech2 := fun _ =>
  inferInstanceAs (Decidable (Option.isSome _))

/-! ## §4. Joint diagnostic and direct directive force

The paper's non-literalist model: a sentence type is directive-compatible
iff EITHER mechanism fires. The imperative itself is direct (no
indirection); the seven non-imperative types route through one of the two
mechanisms (or neither, in which case the construction is non-directive). -/

/-- Joint diagnostic: directive force is licensed by mechanism 1 OR
    mechanism 2 (or by being an imperative outright). -/
def SentType.isDirective (s : SentType) : Prop :=
  s = .imperative ∨ s.directiveCompatibleMech1 ∨ s.directiveCompatibleMech2

instance : DecidablePred SentType.isDirective := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-! ## §5. Predictions

The paper's central qualitative finding is that the SIX directive
sentence types (`imperative`, `canYouInterrog`, `possibleInterrog`,
`mustDeclarative`, `canDeclarative`, `possibleDecl` excluded) all
receive substantial directive interpretations, while the two non-modal
controls do not. The joint mechanism predicts exactly this partition. -/

section Predictions

/-- The imperative is directive (mechanism 1 via `primaryFlavor`). -/
theorem imperative_isDirective :
    SentType.isDirective .imperative := by decide

/-- *Vous devez VP* is directive via mechanism 1 (deontic necessity
    matches the imperative's flavor). -/
theorem mustDeclarative_isDirective :
    SentType.isDirective .mustDeclarative := by decide

/-- *Vous pouvez VP* is directive via mechanism 1 (deontic possibility =
    permission, p.58 Discussion). The paper's Fig.6 *can* > *possible*
    move-response asymmetry (z = −3.29, p = 0.0028) follows from the
    fact that mechanism 1 fires on `canDeclarative` but not on
    `possibleDecl`. -/
theorem canDeclarative_isDirective :
    SentType.isDirective .canDeclarative := by decide

/-- *Pouvez-vous VP?* is directive via mechanism 2 (queries the
    addressee's ability, the canonical preparatory condition for
    requests). -/
theorem canYouInterrog_isDirective :
    SentType.isDirective .canYouInterrog := by decide

/-- *Est-il possible de VP?* is directive via mechanism 2. The paper's
    Study 1 finding that this non-conventionalised IR is processed as
    fast as the conventionalised *Pouvez-vous VP?* (p.53, "all p's >
    0.99 in post hoc comparisons" for move-response RTs) follows from
    both querying the same preparatory condition. -/
theorem possibleInterrog_isDirective :
    SentType.isDirective .possibleInterrog := by decide

/-- The control interrogative *Le cercle rouge est-il…?* is not
    directive: no modal flavor, no preparatory-condition target. -/
theorem ctrlInterrog_not_isDirective :
    ¬ SentType.isDirective .ctrlInterrog := by decide

/-- *Il est possible de VP* (declarative) is not mechanism-1-compatible
    (circumstantial flavor) and not mechanism-2-compatible (no queried
    condition; the form is not interrogative). The paper's Fig.6 shows
    it has the lowest move-response rate of the four Study 2 modal
    conditions — consistent with no mechanism firing. -/
theorem possibleDecl_not_isDirective :
    ¬ SentType.isDirective .possibleDecl := by decide

/-- The control declarative *Le cercle rouge est…* is not directive. -/
theorem plainDeclarative_not_isDirective :
    ¬ SentType.isDirective .plainDeclarative := by decide

/-- The paper's headline qualitative finding: the joint
    mechanism-1-or-mechanism-2 diagnostic correctly partitions the eight
    sentence types into directive (the five modal sentences plus the
    imperative) and non-directive (the two controls plus
    `possibleDecl`). -/
theorem joint_diagnostic_partitions_sentence_types :
    SentType.isDirective .imperative ∧
    SentType.isDirective .mustDeclarative ∧
    SentType.isDirective .canDeclarative ∧
    SentType.isDirective .canYouInterrog ∧
    SentType.isDirective .possibleInterrog ∧
    ¬ SentType.isDirective .possibleDecl ∧
    ¬ SentType.isDirective .ctrlInterrog ∧
    ¬ SentType.isDirective .plainDeclarative := by decide

end Predictions

/-! ## §6. Force–type mismatch (the headline anti-literalist claim)

The paper's core theoretical claim is that sentence type does NOT encode
illocutionary force: a declarative sentence type can carry directive
force (via mechanism 1 for *Vous devez VP*), and an interrogative
sentence type can carry directive force (via mechanism 2 for *Pouvez-vous
VP?*). Both mismatches are derivable from the joint diagnostic plus the
default-mood projection. -/

section ForceTypeMismatch

/-- Default illocutionary force for a declarative is not directive. -/
theorem declarative_default_not_imperative :
    (SAPMood.toClauseType .declarative).force ≠ .imperative := by decide

/-- Force–type mismatch for *Vous devez VP*: declarative sentence type
    + directive force (via mechanism 1). -/
theorem mustDeclarative_force_mismatch :
    SentType.mood .mustDeclarative = .declarative ∧
    SentType.isDirective .mustDeclarative := by decide

/-- Force–type mismatch for *Vous pouvez VP*: same shape via the
    permission reading. -/
theorem canDeclarative_force_mismatch :
    SentType.mood .canDeclarative = .declarative ∧
    SentType.isDirective .canDeclarative := by decide

/-- Force–type mismatch for *Pouvez-vous VP?*: interrogative sentence
    type + directive force (via mechanism 2). -/
theorem canYouInterrog_force_mismatch :
    SentType.mood .canYouInterrog = .interrogative ∧
    SentType.isDirective .canYouInterrog := by decide

/-- Force–type mismatch for *Est-il possible de VP?*. -/
theorem possibleInterrog_force_mismatch :
    SentType.mood .possibleInterrog = .interrogative ∧
    SentType.isDirective .possibleInterrog := by decide

end ForceTypeMismatch

/-! ## §7. Bridge to French Fragment

The `SentType.modalFlavor` and `SentType.modalForce` projections are
consistent with the lexical entries in `Fragments/French/Modals.lean`:
each sentence type's flavor and force appear in the corresponding modal
verb's `forceFlavors` list. This is a derive-don't-duplicate consistency
check — changing a Fragment entry's flavor inventory will break these
theorems. -/

section FrenchFragmentBridge

open Fragments.French.Modals (devoir pouvoir ilEstPossible)

/-- *Vous devez VP* = deontic necessity: shared with *devoir*'s
    forceFlavor inventory. -/
theorem mustDeclarative_forceFlavor_in_devoir :
    (⟨.necessity, .deontic⟩ : Core.Modality.ForceFlavor) ∈ devoir.forceFlavors := by decide

/-- *Vous pouvez VP* = deontic possibility (permission): shared with
    *pouvoir*'s forceFlavor inventory. -/
theorem canDeclarative_forceFlavor_in_pouvoir :
    (⟨.possibility, .deontic⟩ : Core.Modality.ForceFlavor) ∈ pouvoir.forceFlavors := by decide

/-- *Il est possible de VP* = circumstantial possibility: shared with
    the impersonal construction's flavor inventory. -/
theorem possibleDecl_circumstantial_in_ilEstPossible :
    .circumstantial ∈ ilEstPossible.flavors := by decide

end FrenchFragmentBridge

end RuytenbeekEtAl2017
