import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Theories.Semantics.Causation.ComplementEntailing

/-!
# Actuality Entailments: Position × Aspect
  @cite{hacquard-2006} @cite{hacquard-2009} @cite{bhatt-1999} @cite{nadathur-2023}

Bridges **event-relative modality** (`EventRelativity.lean`) with the
**causal frame** (`ComplementEntailing.lean`) to derive actuality
entailments from the relative scope of aspect and modal.

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

## Bridge to @cite{nadathur-2023}

`ComplementEntailing.lean` formalizes the causal model: ability modals are
`CausalFrame World` with `actualization = .aspectual`.

- `actualityWithAspect .perfective w` = sufficiency ∧ actualization
  → root + PFV case (aspect over modal forces actualization)
- `actualityWithAspect .imperfective w` = sufficiency only
  → root + IMPF case (no completion required)

## Content Licensing Explains the Asymmetry

WHY are epistemic modals always above aspect? Content licensing
(EventRelativity §8): epistemic modal bases require a contentful event.
VP events lack content. Therefore epistemic modals cannot be bound by
aspect — they must be above AspP. Root modals need only circumstantial
backgrounds (any event type), so they CAN be below AspP.

The actuality entailment asymmetry follows from content licensing +
aspect scope, without stipulation.

-/

namespace Semantics.Modality.ActualityEntailments

open Semantics.Modality.EventRelativity
open CausalVerb
open Semantics.Attitudes.Intensional (World)
open Semantics.Tense.Aspect.Core (ViewpointAspectB)
open Core.StructuralEquationModel


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
-- § 4. Bridge to CausalFrame (@cite{nadathur-2023})
-- ════════════════════════════════════════════════════

/-! `ComplementEntailing.lean` formalizes the causal semantics: ability modals
    are `CausalFrame World` with `actualization = .aspectual`. The bridge:

    - `actualityWithAspect .perfective w` = `sufficientAt w ∧ actualizedAt w`
      → captures the root + PFV case
    - `actualityWithAspect .imperfective w` = `sufficientAt w`
      → captures the root + IMPF case

    The theorems below make this correspondence explicit. -/

/-- Root + PFV matches CausalFrame: perfective produces sufficiency ∧ actualization,
    and the theory predicts an actuality entailment. -/
theorem root_pfv_matches_causal_frame :
    actualityEntailmentPredicted .belowAsp .perfective = true ∧
    (∀ (f : CausalFrame World) (w : World),
      f.actualityWithAspect .perfective w =
        (f.sufficientAt w && f.actualizedAt w)) := by
  exact ⟨rfl, λ f w => by
    simp only [CausalFrame.actualityWithAspect]
    cases f.actualization <;> rfl⟩

/-- Root + IMPF matches CausalFrame (aspectual mode): imperfective produces
    sufficiency only, and the theory predicts no actuality entailment. -/
theorem root_impfv_matches_causal_frame :
    actualityEntailmentPredicted .belowAsp .imperfective = false ∧
    (∀ (f : CausalFrame World) (w : World),
      f.actualization = .aspectual →
      f.actualityWithAspect .imperfective w = f.sufficientAt w) :=
  ⟨rfl, λ _ _ h => by simp only [CausalFrame.actualityWithAspect, h]⟩

/-- The causal model (Nadathur) and the structural account (Hacquard) agree:
    the causal model explains WHY perfective ability entails the complement;
    the structural account explains WHY this arises only for root modals. -/
theorem causal_structural_agreement :
    -- Structural prediction: root + PFV → AE
    actualityEntailmentPredicted .belowAsp .perfective = true ∧
    -- Causal result: PFV + aspectual mode → complement actualized
    (∀ (f : CausalFrame World) (w : World)
      (hMode : f.actualization = .aspectual)
      (h : f.actualityWithAspect .perfective w = true),
      f.actualizedAt w = true) :=
  ⟨rfl, λ f w hMode h => CausalFrame.perfective_entails_complement f w h hMode⟩


-- ════════════════════════════════════════════════════
-- § 5. Content Licensing Explains the Asymmetry
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
-- § 6. The Full Picture: Three-Way Interaction
-- ════════════════════════════════════════════════════

/-- The actuality entailment pattern results from a three-way interaction
between content licensing, syntactic position, and viewpoint aspect.

This theorem chains together:
- EventRelativity §8 (content licensing determines available flavors)
- EventRelativity §9 (position determines event binder)
- This file §1–2 (position determines aspect scope → AE prediction)
- ComplementEntailing.lean (causal model validates the root + PFV case) -/
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
    actualityEntailmentPredicted .aboveAsp .perfective = false ∧
    -- Validation: PFV = sufficiency ∧ actualization for any CausalFrame
    (∀ (f : CausalFrame World) (w : World),
      f.actualityWithAspect .perfective w =
        (f.sufficientAt w && f.actualizedAt w)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, λ f _ => by
    simp only [CausalFrame.actualityWithAspect]; cases f.actualization <;> rfl⟩


end Semantics.Modality.ActualityEntailments
