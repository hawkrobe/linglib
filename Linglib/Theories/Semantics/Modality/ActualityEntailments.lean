import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Theories.Semantics.Tense.Aspect.Core

/-!
# Actuality Entailments: Position × Aspect
  @cite{hacquard-2006} @cite{hacquard-2009} @cite{bhatt-1999}

Derives **actuality entailments** from the relative scope of aspect and
modal, building on **event-relative modality** (`EventRelativity.lean`).

## The Puzzle

The same modal verb shows different entailment patterns depending on
interpretation (@cite{bhatt-1999}, @cite{hacquard-2006} Ch.1):

- Root (ability) + PFV: "Jane **a pu** prendre le train" → she took it
- Root (ability) + IMPF: "Jane **pouvait** prendre le train" → maybe not
- Epistemic + PFV: "Jane **a pu** prendre le train" → maybe not

## @cite{hacquard-2006}'s Solution

The relative position of the modal determines which event binder
captures it:

- Root modals (below AspP): `[AspP PRFV [ModP can [VP take train]]]`
  Perfective quantifies over the entire modal+VP event → actualization.

- Epistemic modals (above AspP): `[ModP can [AspP PRFV [VP take train]]]`
  Modal scopes over perfective → perfective applies to VP only in
  accessible worlds → no actualization in the actual world.

## Content Licensing Explains the Asymmetry

WHY are epistemic modals always above aspect? Content licensing
(EventRelativity §8): epistemic modal bases require a contentful event.
VP events lack content. Therefore epistemic modals cannot be bound by
aspect — they must be above AspP. Root modals need only circumstantial
backgrounds (any event type), so they CAN be below AspP.

The actuality entailment asymmetry follows from content licensing +
aspect scope, without stipulation.

The earlier `CausalFrame`-bridge §4 (showing `actualityWithAspect .perfective`
matches `sufficientAt ∧ actualizedAt`) was deleted in Phase D-H along with
the `CausalFrame`/`ComplementEntailing` substrate; the qualitative bridge to
@cite{nadathur-2023}'s causal account now lives at the V2 SEM level in
study files and `Semantics/Causation/`.
-/

namespace Semantics.Modality.ActualityEntailments

open Semantics.Modality.EventRelativity
open Semantics.Tense.Aspect.Core (ViewpointAspectB)


-- ════════════════════════════════════════════════════
-- § 1. Aspect Scope (@cite{hacquard-2006}, Ch.1)
-- ════════════════════════════════════════════════════

/-- The relative scope of aspect and the modal in the clause structure.

Root modals are below AspP: aspect quantifies over the modal event.
Epistemic modals are above AspP: the modal quantifies over aspect.

This structural difference — not lexical semantics — is the sole
source of the actuality entailment asymmetry. -/
inductive AspectModalScope where
  /-- Root: [Asp [Mod [VP]]] — aspect scopes over modal -/
  | aspectOverModal
  /-- Epistemic: [Mod [Asp [VP]]] — modal scopes over aspect -/
  | modalOverAspect
  deriving DecidableEq, Repr

/-- Position determines aspect scope.
belowAsp → aspect over modal (root configuration).
aboveAsp → modal over aspect (epistemic configuration). -/
def toAspectScope : ModalPosition → AspectModalScope
  | .belowAsp => .aspectOverModal
  | .aboveAsp => .modalOverAspect

theorem belowAsp_aspect_over_modal :
    toAspectScope .belowAsp = .aspectOverModal := rfl

theorem aboveAsp_modal_over_aspect :
    toAspectScope .aboveAsp = .modalOverAspect := rfl


-- ════════════════════════════════════════════════════
-- § 2. Actuality Entailment Predictions
-- ════════════════════════════════════════════════════

/-- Whether the theory predicts an actuality entailment for a given
position × aspect combination.

Only root + perfective yields an actuality entailment:

| Position | Aspect | AE? | Why |
|----------|--------|-----|-----|
| root (below Asp) | PFV | ✓ | Asp > Mod: PFV forces completion |
| root (below Asp) | IMPF | ✗ | Asp > Mod: IMPF doesn't force completion |
| epistemic (above Asp) | PFV | ✗ | Mod > Asp: PFV in accessible worlds only |
| epistemic (above Asp) | IMPF | ✗ | Mod > Asp: no completion | -/
def actualityEntailmentPredicted (pos : ModalPosition) (asp : ViewpointAspectB) : Bool :=
  match pos, asp with
  | .belowAsp, .perfective => true
  | _, _ => false

theorem root_perfective_entails :
    actualityEntailmentPredicted .belowAsp .perfective = true := rfl

theorem root_imperfective_no_entailment :
    actualityEntailmentPredicted .belowAsp .imperfective = false := rfl

theorem epistemic_perfective_no_entailment :
    actualityEntailmentPredicted .aboveAsp .perfective = false := rfl

theorem epistemic_imperfective_no_entailment :
    actualityEntailmentPredicted .aboveAsp .imperfective = false := rfl

/-- Only root + perfective yields actuality entailments.
This is a characterization result: AE ↔ (belowAsp ∧ perfective). -/
theorem only_root_perfective :
    ∀ pos asp, actualityEntailmentPredicted pos asp = true →
      pos = .belowAsp ∧ asp = .perfective := by
  intro pos asp h
  cases pos <;> cases asp <;> simp_all [actualityEntailmentPredicted]

/-- The prediction aligns with the aspect scope story: AE holds
exactly when aspect scopes over the modal AND aspect is perfective. -/
theorem ae_iff_aspect_over_modal_pfv (pos : ModalPosition) (asp : ViewpointAspectB) :
    actualityEntailmentPredicted pos asp =
      (toAspectScope pos == .aspectOverModal && asp == .perfective) := by
  cases pos <;> cases asp <;> rfl


-- ════════════════════════════════════════════════════
-- § 3. Same Modal, Different Positions
-- ════════════════════════════════════════════════════

/-- The same lexical modal yields different actuality patterns depending
solely on position. This is Hacquard's core argument against lexical
ambiguity: French *pouvoir*, Greek *boro*, Hindi *saknaa* are single
lexical items whose actuality behavior is structurally determined. -/
theorem same_modal_different_entailments :
    actualityEntailmentPredicted .belowAsp .perfective = true ∧
    actualityEntailmentPredicted .aboveAsp .perfective = false := ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 4. Content Licensing Explains the Asymmetry
-- ════════════════════════════════════════════════════

/-! WHY are epistemic modals always above aspect? Content licensing
(EventRelativity §8) provides the answer:

- Epistemic modal bases require CON(e) — propositional content.
- VP events (running, swimming) lack propositional content.
- Aspect binds modals to VP events.
- Therefore: a modal bound by aspect CANNOT be epistemic.
- Therefore: epistemic modals are necessarily above AspP.
- Therefore: perfective never scopes over epistemic modals.
- Therefore: no actuality entailment for epistemics.

The chain: content licensing → position → scope → (no) AE. -/

/-- The full explanatory chain from content licensing to actuality
entailments, linking EventRelativity §§8–9 to @cite{hacquard-2006} Ch.1. -/
theorem content_licensing_to_actuality :
    -- Step 1: VP events lack content → can't project epistemic
    EventBinder.vpEvent.hasContent = false ∧
    EventBinder.vpEvent.canProjectEpistemic = false ∧
    -- Step 2: Low position → aspect over modal
    toAspectScope .belowAsp = .aspectOverModal ∧
    -- Step 3: Root + PFV → actuality entailment
    actualityEntailmentPredicted .belowAsp .perfective = true ∧
    -- Step 4: High position → modal over aspect → no AE
    toAspectScope .aboveAsp = .modalOverAspect ∧
    actualityEntailmentPredicted .aboveAsp .perfective = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Epistemic modals are necessarily high (above Asp), because
low modals are bound to VP events which lack content. -/
theorem epistemic_necessarily_no_ae :
    -- Low modals can't be epistemic (content licensing)
    ModalPosition.belowAsp.defaultBinder.canProjectEpistemic = false ∧
    -- High modals yield no AE regardless of aspect
    actualityEntailmentPredicted .aboveAsp .perfective = false ∧
    actualityEntailmentPredicted .aboveAsp .imperfective = false :=
  ⟨rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 5. The Full Picture: Three-Way Interaction
-- ════════════════════════════════════════════════════

/-- The actuality entailment pattern results from the interaction of
content licensing, syntactic position, and viewpoint aspect.

This theorem chains together:
- EventRelativity §8 (content licensing determines available flavors)
- EventRelativity §9 (position determines event binder)
- This file §1–2 (position determines aspect scope → AE prediction)

The causal-model validation of the root + PFV case (formerly via
`CausalFrame`/`ComplementEntailing`) is now witnessed at the V2 SEM level
in study files. -/
theorem three_way_interaction :
    -- Content licensing: VP events lack content
    EventBinder.vpEvent.hasContent = false ∧
    -- Position → binder: low modals get VP events
    ModalPosition.belowAsp.defaultBinder = .vpEvent ∧
    -- Position → scope: low modals have aspect over them
    toAspectScope .belowAsp = .aspectOverModal ∧
    -- Prediction: root + PFV → AE
    actualityEntailmentPredicted .belowAsp .perfective = true ∧
    -- Prediction: epistemic + PFV → no AE
    actualityEntailmentPredicted .aboveAsp .perfective = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


end Semantics.Modality.ActualityEntailments
