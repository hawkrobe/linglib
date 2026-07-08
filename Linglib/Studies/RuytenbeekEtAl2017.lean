import Linglib.Discourse.SpeechAct
import Linglib.Semantics.Mood.SpeechEvent
import Linglib.Fragments.Romance.French.Modals

/-!
# [ruytenbeek-etal-2017]: Indirect Request Processing, Sentence Types
  and Illocutionary Forces

Journal of Pragmatics 119 (2017) 46–62.

Two French eye-tracking experiments testing the **literalist** view that
sentence types encode illocutionary force at the semantic level. Both
studies support **non-literalist** theories: directive force in
non-imperative constructions arises from semantic features they share
with imperatives, not from sentence type per se.

## Three mechanisms for non-imperative directive force

The paper invokes three (overlapping) routes by which a non-imperative
construction can carry directive force:

1. **Shared deontic semantics** ([kaufmann-2012]; paper §3.4
   Discussion). A construction whose modal flavor matches the
   imperative's deontic semantics is directive-compatible. *Vous devez VP*
   and the permission reading of *Vous pouvez VP* (paper §3.4)
   instantiate this route. Formalised as `SentType.deonticMatch`.
2. **Preparatory-condition questioning** ([clark-1979]; paper §1
   Introduction). An interrogative that questions an addressee
   preparatory condition (canonically `.ability`) is directive-compatible.
   *Pouvez-vous VP?* and *Est-il possible de VP?* instantiate this route.
   Formalised as `SentType.prepConditionQueried`; the deeper
   characterisation `interrogative + circumstantial-modal` is proved
   equivalent in `prepConditionQueried_iff_interrog_circumstantial`.
3. **Force-dynamic enablement** ([johnson-1987], [sweetser-1990],
   [talmy-2000]; paper §4 General Discussion, p. 61). The four
   constructions that semantically encode the addressee's *enablement*
   to perform the action — both interrogative IRs *and* both
   ability/possibility declaratives — pattern together. Formalised as
   `SentType.enablementEncoded`, derived directly from
   `modalForce = some .possibility` in this paper's domain. This is the
   broader generalisation that distinguishes the corrected
   formalisation from earlier versions that categorically denied
   directive force to *Il est possible de VP*.

The three mechanisms overlap. *Vous pouvez VP* fires (1) and (3); the
two interrogative IRs fire (2) and (3); *Il est possible de VP* fires
(3) only. The joint `SentType.isDirective` diagnostic licenses
directive force when any mechanism fires (or when the construction is
itself an imperative).

## A note on empirical numbers

Hand-transcribed RT means, fixation durations, and move-response
proportions read off Figs. 3/5/6/8 in the original version of this
file were either reconstructions of percentages reported in the paper
text, upper-bound stipulations, or eyeball reads of bar charts that
are demonstrably off (per the 2026-04-24 audit and 2026-05-13 PDF
re-audit). The paper's actual claims are β estimates with confidence
intervals (Study 1 §2.3, Study 2 §3.3) and significance tests. This
file records the directional ordering predictions and lets statistics
live in docstrings — Lean is not the right place for hand-transcribed
regression coefficients.

## Cross-paper bridges

- `Semantics/Mood/SpeechEvent.lean`: the imperative's
  `primaryFlavor = .deontic` is the layered foundation;
  `SentType.modalFlavor` for the imperative branch derives from it.
- `Studies/Roberts2023.lean`: a chronologically
  later sibling that contradicts the imperative's deontic-flavor
  assignment; the cross-paper wedge lives in Roberts2023.
- `Studies/FrancikClark1985.lean`: another
  consumer of `PreparatoryCondition`. Both that file's
  `RequestForm.queriedCondition` and this file's `SentType.queriedPrep`
  are `Option PreparatoryCondition`-valued projections sharing the
  Searle/Francik substrate.

## Mood substrate choice

This file uses `Mood.Illocutionary` rather than the
Minimalist-derived `SAPMood`. The two are isomorphic on the
declarative/interrogative/imperative cases used here, and
`Illocutionary` is the canonical substrate (`SAPMood` adds
syntax-derivation machinery the paper does not invoke). This also
keeps the file independent of the Minimalist substrate.
-/

namespace RuytenbeekEtAl2017

open Semantics.Modality (ModalFlavor ModalForce)
open Mood (Illocutionary)
open Mood.Illocutionary (primaryFlavor)

/-! ### Sentence types and modal projections -/

/-- The eight sentence types appearing across Studies 1 and 2.

    Study 1 §2.1 (p. 51) uses `imperative`, `canYouInterrog`,
    `possibleInterrog`, and `ctrlInterrog` (24 trials = 4 × 6).
    Study 2 §3.1 (p. 56) uses `imperative` (3 *You must* + 3 control
    imperatives), `mustDeclarative`, `canDeclarative`, `possibleDecl`,
    and `plainDeclarative` (24 trials). The 3 control imperatives in
    Study 2 collapse to `imperative` here since they are imperatives
    without a polar response option. -/
inductive SentType where
  /-- *Mettez le cercle rouge…* — Study 1 + Study 2 imperative. -/
  | imperative
  /-- *Pouvez-vous VP?* — Study 1 conventionalised IR. -/
  | canYouInterrog
  /-- *Est-il possible de VP?* — Study 1 non-conventionalised IR. -/
  | possibleInterrog
  /-- *Le cercle rouge est-il…?* — Study 1 control interrogative. -/
  | ctrlInterrog
  /-- *Vous devez VP* — Study 2 deontic-necessity declarative. -/
  | mustDeclarative
  /-- *Vous pouvez VP* — Study 2 modal declarative. The paper's §3.4
      Discussion attributes the directive readings to the **permission**
      sense of *pouvoir* (deontic possibility, not circumstantial
      ability); the paper's §4 General Discussion offers the broader
      force-dynamic enablement analysis (mechanism 3) as the unified
      pattern. -/
  | canDeclarative
  /-- *Il est possible de VP* — Study 2 existential-possibility
      declarative. Per paper §2.1 the modal base is unrestricted (in
      the sense of [kratzer-1991]); we choose `.circumstantial`
      as the canonical flavor since *Pouvez-vous VP?* (semantically
      close per p. 50) is restricted to the ability reading in the
      experimental contexts. -/
  | possibleDecl
  /-- *Le cercle rouge est…* — Study 2 control declarative. -/
  | plainDeclarative
  deriving DecidableEq, Repr

/-- Morphosyntactic mood of each sentence type. -/
def SentType.mood : SentType → Illocutionary
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
    `Mood.Illocutionary.primaryFlavor` rather than restipulated
    (layered grounding — see `imperative_modalFlavor_eq_assert` below).

    `canDeclarative = .deontic` follows the paper's §3.4 Discussion
    explanation of the *Vous pouvez VP* directive readings via the
    permission sense of *pouvoir*. `canYouInterrog = .circumstantial`
    follows the paper's §2.1 (p. 50) statement that the experimental
    contexts force the ability reading of *pouvez*/*possible*.

    `ctrlInterrog` and `plainDeclarative` carry no modal, hence the
    `Option` codomain. -/
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

/-- The imperative's flavor matches the one Hacquard's SAP architecture
    assigns to imperative speech acts — derived, not coincidentally
    equal. Layered Grounding for the headline [kaufmann-2012]
    commitment. -/
theorem imperative_modalFlavor_eq_assert :
    SentType.modalFlavor .imperative = some (primaryFlavor .imperative) := rfl

/-! ### Mechanism 1 — shared deontic semantics ([kaufmann-2012])

A construction is mechanism-1-compatible with directive force when its
modal flavor matches the imperative's. The check is a single equality
on `ModalFlavor`. Mechanism 1 does not distinguish necessity from
possibility — that ranking is a quantitative finding (paper §3.3:
*You must* yields more directive interpretations than *You can*,
z = -8.11, p < 0.001) which mechanism 1 alone underdetermines. -/

/-- A sentence type is mechanism-1-compatible iff its modal flavor
    matches the imperative's. Encodes [kaufmann-2012]'s
    deontic-modal account of imperatives: any construction with the
    same modal flavor is a candidate directive. -/
def SentType.deonticMatch (s : SentType) : Prop :=
  s.modalFlavor = some (primaryFlavor .imperative)

instance : DecidablePred SentType.deonticMatch := fun _ => decEq _ _

/-! ### Mechanism 2 — preparatory-condition questioning ([clark-1979])

Per [clark-1979], asking about a preparatory condition for a
request licenses the directive interpretation without sharing the
imperative's modal semantics. The substrate
`PreparatoryCondition` (Searle's hierarchy: ability /
knowledge / memory / perception / permission / willingness) is the
target type; the projection `SentType.queriedPrep` mirrors
`Studies/FrancikClark1985.lean`'s
`RequestForm.queriedCondition`. -/

/-- The preparatory condition queried by each sentence type, when one
    is queried. The two interrogative IRs both query `.ability` (per
    paper §2.1 p. 50, the experimental contexts force the ability
    reading). The empty `.queriedPrep` cases are the imperative,
    declaratives, and the control interrogative — none of which raise
    a polar question over an addressee precondition. -/
def SentType.queriedPrep : SentType → Option PreparatoryCondition
  | .canYouInterrog   => some .ability
  | .possibleInterrog => some .ability
  | _                 => none

/-- Mechanism 2 directive licensing: the construction queries an
    addressee preparatory condition. -/
def SentType.prepConditionQueried (s : SentType) : Prop :=
  s.queriedPrep.isSome

instance : DecidablePred SentType.prepConditionQueried := fun _ =>
  inferInstanceAs (Decidable (Option.isSome _))

/-- Deeper characterisation of mechanism 2 in this paper's domain:
    `queriedPrep = some .ability` iff the construction is an
    interrogative with circumstantial modal flavor. This is the
    structural content of [clark-1979]'s "convention of means"
    applied to the paper's specific stimulus set, where circumstantial
    modal force in an interrogative form picks out exactly the
    ability-questioning indirect requests. -/
theorem queriedPrep_eq_ability_iff_interrog_circumstantial (s : SentType) :
    s.queriedPrep = some .ability ↔
      s.mood = .interrogative ∧ s.modalFlavor = some .circumstantial := by
  cases s <;> decide

/-! ### Mechanism 3 — force-dynamic enablement ([johnson-1987],
    [sweetser-1990], [talmy-2000])

Per the paper's §4 General Discussion (p. 61), all four constructions
that semantically encode the addressee's *enablement* to perform the
action — *Pouvez-vous VP?*, *Vous pouvez VP*, *Est-il possible de VP?*,
and *Il est possible de VP* — pattern together as candidate directives.
This is the broader generalisation that mechanism 2 (questioning only)
misses: declarative ability/possibility constructions also encode the
enablement-to-act semantic content, and the paper's data show that
*Il est possible de VP* indeed receives directive interpretations
(though fewer than *Vous pouvez VP*; z = -3.29, p = 0.0028, §3.3).

Force-dynamic enablement in this paper's domain reduces to "the
construction has possibility modal force": the four enablement-encoding
constructions are precisely the four with `modalForce = some
.possibility`. The derivation is captured directly in the definition;
the explicit four-construction list (matching the paper's prose at
p. 61) appears in `mechanism_attribution`. -/

/-- Mechanism 3 directive licensing: the construction encodes a
    force-dynamic enablement pattern, characterised in this paper's
    domain by possibility modal force. The four ability/possibility
    constructions in the paper instantiate this. -/
def SentType.enablementEncoded (s : SentType) : Prop :=
  s.modalForce = some .possibility

instance : DecidablePred SentType.enablementEncoded := fun _ => decEq _ _

/-! ### Joint diagnostic

The paper's non-literalist model: a sentence type is directive-compatible
iff at least one mechanism fires (or the construction is itself an
imperative). The imperative is direct (no indirection); *Vous devez VP*
fires (1); *Vous pouvez VP* fires (1) and (3); the two interrogative
IRs fire (2) and (3); *Il est possible de VP* fires (3) only; the two
controls fire none. -/

/-- Joint diagnostic: directive force is licensed by mechanism 1, 2,
    or 3 (or by being an imperative outright). -/
def SentType.isDirective (s : SentType) : Prop :=
  s = .imperative ∨ s.deonticMatch
                  ∨ s.prepConditionQueried
                  ∨ s.enablementEncoded

instance : DecidablePred SentType.isDirective := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-! ### Predictions

Six of the eight sentence types are directive (imperative + the five
modal sentences); the two non-modal controls are not. The joint
`isDirective` diagnostic produces this partition. The
mechanism-attribution table records *which* mechanism licenses each
directive sentence type — the empirical content of the paper's
non-literalist analysis. -/

/-- The paper's headline qualitative finding (§4 General Discussion):
    the joint diagnostic correctly partitions the eight sentence types
    into directive (imperative + 5 modal sentences) and non-directive
    (2 controls). -/
theorem joint_diagnostic_partitions_sentence_types :
    SentType.isDirective .imperative ∧
    SentType.isDirective .mustDeclarative ∧
    SentType.isDirective .canDeclarative ∧
    SentType.isDirective .canYouInterrog ∧
    SentType.isDirective .possibleInterrog ∧
    SentType.isDirective .possibleDecl ∧
    ¬ SentType.isDirective .ctrlInterrog ∧
    ¬ SentType.isDirective .plainDeclarative := by decide

/-- Mechanism-attribution table: which sentence types each mechanism
    licenses, and which it rejects. Documents the empirical content
    of the three-mechanism analysis: mechanism 1 (deontic match) fires
    on the imperative, *Vous devez VP*, and *Vous pouvez VP*;
    mechanism 2 (preparatory-condition questioning) fires only on the
    two interrogative IRs; mechanism 3 (force-dynamic enablement)
    fires on all four ability/possibility constructions. -/
theorem mechanism_attribution :
    -- Mechanism 1 (deontic match):
    SentType.deonticMatch .imperative ∧
    SentType.deonticMatch .mustDeclarative ∧
    SentType.deonticMatch .canDeclarative ∧
    ¬ SentType.deonticMatch .canYouInterrog ∧
    ¬ SentType.deonticMatch .possibleInterrog ∧
    ¬ SentType.deonticMatch .possibleDecl ∧
    -- Mechanism 2 (preparatory-condition questioning):
    SentType.prepConditionQueried .canYouInterrog ∧
    SentType.prepConditionQueried .possibleInterrog ∧
    ¬ SentType.prepConditionQueried .mustDeclarative ∧
    ¬ SentType.prepConditionQueried .canDeclarative ∧
    ¬ SentType.prepConditionQueried .possibleDecl ∧
    -- Mechanism 3 (force-dynamic enablement):
    SentType.enablementEncoded .canYouInterrog ∧
    SentType.enablementEncoded .possibleInterrog ∧
    SentType.enablementEncoded .canDeclarative ∧
    SentType.enablementEncoded .possibleDecl ∧
    ¬ SentType.enablementEncoded .mustDeclarative := by decide

/-! ### Force–type mismatch (the headline anti-literalist claim)

The paper's core theoretical claim (§4 General Discussion) is that
sentence type does NOT encode illocutionary force: declarative sentence
types can carry directive force (via mechanisms 1/3 for *Vous devez VP*,
*Vous pouvez VP*, and *Il est possible de VP*), and interrogative
sentence types can carry directive force (via mechanisms 2/3 for the
two IRs).

The literalist default is the Searle taxonomy: declarative mood maps
to assertive force, interrogative mood maps to question-class
directives (asking, not commanding). Both defaults are falsified by
the existence of force–type mismatch witnesses below. -/

/-- A sentence-type carries a force–type mismatch when its
    morphosyntactic mood is `m` but it nonetheless licenses directive
    interpretation. The five mismatch cases (`mustDeclarative`,
    `canDeclarative`, `possibleDecl`, `canYouInterrog`,
    `possibleInterrog`) all instantiate this. -/
abbrev SentType.forceTypeMismatch (s : SentType) (m : Illocutionary) : Prop :=
  s.mood = m ∧ s.isDirective

/-- The literalist Searle default for declarative mood is
    `.assertive`, not `.directive`. The paper's data falsify the
    consequence "declarative-mood utterances cannot carry directive
    force" (witnessed by `anti_literalism_for_declaratives`). -/
theorem declarative_default_searleClass :
    Illocutionary.declarative.searleClass = .assertive := rfl

/-- Anti-literalism witness: there is a sentence type whose
    morphosyntactic mood is declarative yet which licenses directive
    interpretation. (`mustDeclarative`, `canDeclarative`, and
    `possibleDecl` all witness this; `mustDeclarative` is the canonical
    paper Study 2 case.) -/
theorem anti_literalism_for_declaratives :
    ∃ s : SentType, s.mood = .declarative ∧ s.isDirective :=
  ⟨.mustDeclarative, by decide, by decide⟩

/-- Anti-literalism witness: there is a sentence type whose
    morphosyntactic mood is interrogative yet which licenses directive
    interpretation. (`canYouInterrog` and `possibleInterrog` both
    witness this; either is the canonical paper Study 1 case.) -/
theorem anti_literalism_for_interrogatives :
    ∃ s : SentType, s.mood = .interrogative ∧ s.isDirective :=
  ⟨.canYouInterrog, by decide, by decide⟩

/-- The five non-imperative sentence types that carry directive
    force — declarative-form mismatches and interrogative-form
    mismatches alike. -/
theorem nonImperative_force_type_mismatches :
    SentType.forceTypeMismatch .mustDeclarative .declarative ∧
    SentType.forceTypeMismatch .canDeclarative .declarative ∧
    SentType.forceTypeMismatch .possibleDecl .declarative ∧
    SentType.forceTypeMismatch .canYouInterrog .interrogative ∧
    SentType.forceTypeMismatch .possibleInterrog .interrogative := by decide

/-! ### Bridge to French Fragment

The `SentType.modalFlavor` and `SentType.modalForce` projections are
consistent with the lexical entries in `Fragments/French/Modals.lean`:
each sentence type's force–flavor pair appears in the corresponding
modal verb's `forceFlavors` list. This is a derive-don't-duplicate
consistency check — changing a Fragment entry's flavor inventory will
break these theorems. -/

section FrenchFragmentBridge

open French.Modals (devoir pouvoir ilEstPossible)
open Semantics.Modality (ForceFlavor)

/-- *Vous devez VP* = deontic necessity, present in *devoir*'s
    force-flavor inventory. -/
theorem mustDeclarative_forceFlavor_in_devoir :
    (⟨.necessity, .deontic⟩ : ForceFlavor) ∈ devoir.forceFlavors := by decide

/-- *Vous pouvez VP* = deontic possibility (permission), present in
    *pouvoir*'s force-flavor inventory. -/
theorem canDeclarative_forceFlavor_in_pouvoir :
    (⟨.possibility, .deontic⟩ : ForceFlavor) ∈ pouvoir.forceFlavors := by decide

/-- *Il est possible de VP* = circumstantial possibility, present in
    the impersonal construction's force-flavor inventory. -/
theorem possibleDecl_forceFlavor_in_ilEstPossible :
    (⟨.possibility, .circumstantial⟩ : ForceFlavor) ∈
      ilEstPossible.forceFlavors := by decide

end FrenchFragmentBridge

end RuytenbeekEtAl2017
