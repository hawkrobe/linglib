import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Modality.EventRelativity

/-!
# Bridge: Psych Verb Contentfulness ↔ Modal Content Licensing

@cite{kim-2024} @cite{hacquard-2010} @cite{hacquard-2006}Connects @cite{kim-2024}'s causal source distinction for psych verbs to
Hacquard (2006, 2010)'s content licensing principle for modal flavor
availability.

## The Connection

@cite{kim-2024}: stative Class II psych verbs have **internal** causal source —
the stimulus is a mind-internal representation with propositional content.
The experiencer REPRESENTS the stimulus to themselves (intensional subject).

@cite{hacquard-2010}: epistemic modal bases require a **contentful** event — one
with propositional content CON(e). Speech acts and attitude events have
content; VP events do not.

The bridge: stative psych verbs' events are contentful (they involve mental
representation of propositional content), patterning with attitude verbs
rather than plain VP events. This predicts that modals embedded under
stative psych verbs should have access to epistemic readings — the psych
verb's event provides CON(e), just like an attitude verb's event does.

## Predictions

| Psych class | CausalSource | Content? | Epistemic modal? |
|------------|-------------|----------|-----------------|
| Stative (concern, interest) | internal | ✓ | ✓ (like attitude verbs) |
| Eventive (frighten, amuse) | external | ✗ | ✗ (like VP events) |

## Example

"The problem concerns John — it might be unsolvable."
- *concern* has internal causal source → contentful event
- *might* binds to the psych verb's event → CON(e) = John's representation
- Epistemic R available → "it might be unsolvable" = given John's mental
  representation of the problem, it might be unsolvable

-/

namespace Phenomena.PsychVerbs.Bridge.ContentLicensingBridge

open Semantics.Causation.PsychCausation
open Semantics.Modality.EventRelativity
open Core.ModalLogic (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Psych Event Content: Derived from Causal Source
-- ════════════════════════════════════════════════════

/-- Whether a psych verb's event has propositional content, derived from
the causal source (@cite{kim-2024} UPH).

Internal causal source → the experiencer's mental state involves
propositional content (they REPRESENT the stimulus to themselves).
This representation IS propositional content, analogous to CON(e)
for attitude verbs.

External causal source → the cause is a mind-external percept/event.
The verb's event is a plain causal event without propositional content,
patterning with VP events. -/
def psychEventHasContent (src : CausalSource) : Bool :=
  match src with
  | .internal => true   -- mental representation = contentful
  | .external => false  -- external percept = contentless

/-- Internal source → contentful (like attitude verbs). -/
theorem internal_is_contentful :
    psychEventHasContent .internal = true := rfl

/-- External source → contentless (like VP events). -/
theorem external_is_contentless :
    psychEventHasContent .external = false := rfl


-- ════════════════════════════════════════════════════
-- § 2. Bridge to Content Licensing
-- ════════════════════════════════════════════════════

/-- Psych verbs with internal causal source pattern with attitude verbs
(contentful events), not VP events (contentless). Both Kim's
`subjectIntensional` and Hacquard's `hasContent` detect the same
underlying property: propositional content in the event.

This theorem shows the structural parallel:
- Kim: internal → intensional subject (requires propositional content)
- Hacquard: attitude → hasContent (provides propositional content)
- Bridge: internal source ↔ contentful event -/
theorem intensionality_content_parallel :
    -- Kim: internal → intensional subject
    subjectIntensional .internal = true ∧
    subjectIntensional .external = false ∧
    -- Hacquard: attitude → contentful
    EventBinder.attitude.hasContent = true ∧
    EventBinder.vpEvent.hasContent = false ∧
    -- Bridge: the distinction aligns
    psychEventHasContent .internal = EventBinder.attitude.hasContent ∧
    psychEventHasContent .external = EventBinder.vpEvent.hasContent :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 3. Epistemic Availability Under Psych Verbs
-- ════════════════════════════════════════════════════

/-- Whether epistemic modals can project from a psych verb's event.
Directly parallels `EventBinder.canProjectEpistemic`. -/
def psychCanProjectEpistemic (src : CausalSource) : Bool :=
  psychEventHasContent src

/-- Stative psych verbs (internal source) license epistemic modals,
just like attitude verbs. -/
theorem stative_licenses_epistemic :
    psychCanProjectEpistemic .internal = true := rfl

/-- Eventive psych verbs (external source) do NOT license epistemic,
just like VP events. -/
theorem eventive_blocks_epistemic :
    psychCanProjectEpistemic .external = false := rfl

/-- The full parallel between psych verb events and Hacquard's
event binder hierarchy.

| Psych type | Event binder analog | Content? | Epistemic? |
|-----------|-------------------|----------|-----------|
| Stative (internal) | attitude | ✓ | ✓ |
| Eventive (external) | vpEvent | ✗ | ✗ |
| — (speech act) | speechAct | ✓ | ✓ | -/
theorem psych_binder_parallel :
    -- Stative psych ≈ attitude binder
    psychCanProjectEpistemic .internal =
      EventBinder.attitude.canProjectEpistemic ∧
    -- Eventive psych ≈ VP event binder
    psychCanProjectEpistemic .external =
      EventBinder.vpEvent.canProjectEpistemic :=
  ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 4. Available Flavors Under Psych Verbs
-- ════════════════════════════════════════════════════

/-- Available modal flavors for modals embedded under a psych verb,
derived from content licensing via the causal source. -/
def psychAvailableFlavors (src : CausalSource) : List ModalFlavor :=
  if psychEventHasContent src then [.epistemic, .circumstantial]
  else [.circumstantial]

/-- Stative psych → both flavors (like attitude embedding). -/
theorem stative_both_flavors :
    psychAvailableFlavors .internal = [.epistemic, .circumstantial] := rfl

/-- Eventive psych → circumstantial only (like VP embedding). -/
theorem eventive_circumstantial_only :
    psychAvailableFlavors .external = [.circumstantial] := rfl

/-- The available flavors match the corresponding EventBinder patterns. -/
theorem flavors_match_binders :
    psychAvailableFlavors .internal = EventBinder.attitude.availableFlavors ∧
    psychAvailableFlavors .external = EventBinder.vpEvent.availableFlavors :=
  ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 5. Predictions for Specific Verbs
-- ════════════════════════════════════════════════════

/-! These predictions could be tested with empirical data on modal
readings under psych verbs:

- "The problem concerns John — it might be unsolvable" (concern = internal)
  → epistemic *might* available (John's representation licenses CON(e))

- "The noise frightened John — ??it might be dangerous" (frighten = external)
  → epistemic *might* less natural (external cause provides no CON(e))

The eventive case is not ungrammatical (the modal can bind to the matrix
speech act event instead), but the psych verb's own event does not provide
the epistemic modal base. -/

/-- Stative verbs: the causal source is internal for both concern and interest.
Both should pattern like attitude verbs for content licensing. -/
theorem stative_verbs_are_contentful :
    psychEventHasContent .internal = true ∧
    psychCanProjectEpistemic .internal = true := ⟨rfl, rfl⟩

/-- Eventive verbs: the causal source is external for frighten, amuse, etc.
None should provide content for epistemic licensing. -/
theorem eventive_verbs_are_contentless :
    psychEventHasContent .external = false ∧
    psychCanProjectEpistemic .external = false := ⟨rfl, rfl⟩


end Phenomena.PsychVerbs.Bridge.ContentLicensingBridge
