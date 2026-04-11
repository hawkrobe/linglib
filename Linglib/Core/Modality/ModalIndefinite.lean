import Linglib.Core.Logic.ModalLogic

/-!
# Modal Indefinite Types
@cite{alonso-ovalle-menendez-benito-2010} @cite{alonso-ovalle-royer-2024}

Framework-agnostic types for recording cross-linguistic properties of modal
indefinites — indefinite determiners/DPs that conventionally encode a modal
component (e.g., Chuj *yalnhej*, Spanish *algún*, German *irgendein*).

## Three Dimensions of Variation

Following @cite{alonso-ovalle-royer-2024}:

1. **Status**: Is the modal component at-issue or not-at-issue?
2. **Content**: Which modal flavors does the component support?
3. **Upper-boundedness**: Does it impose an anti-singleton inference?

-/

namespace Core.ModalIndefinite

open Core.Modality (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Modal Component Status
-- ════════════════════════════════════════════════════

/-- Whether the modal component of a modal indefinite is at-issue
or not-at-issue.

Diagnostics:
- **At-issue**: targetable by direct denial ("No, that's not true —
  you know exactly which book you bought")
- **Not-at-issue**: targetable by "Hey, wait a minute!" but not by
  direct denial; projects under negation, questions, modals -/
inductive ModalComponentStatus where
  /-- Modal component is part of assertive content (challengeable
      by direct denial). Ex: Chuj *yalnhej*, Sp. *uno cualquiera*. -/
  | atIssue
  /-- Modal component is not part of assertive content: presupposed,
      conventionally implicated, or conversationally implicated.
      Projects or persists under embedding operators.
      Ex: Sp. *algún* (conv. implicature per @cite{alonso-ovalle-menendez-benito-2010}),
      Ger. *irgendein* (domain widening per @cite{kratzer-shimoyama-2002}). -/
  | notAtIssue
  deriving DecidableEq, Repr


-- ════════════════════════════════════════════════════
-- § 2. Anchor Constraint
-- ════════════════════════════════════════════════════

/-- Whether the anchoring function f has a definedness condition.
    @cite{alonso-ovalle-royer-2024} §4.1–4.2.

    Modal indefinites whose modal component is at-issue project their
    modal domain from an event argument via an anchoring function f.
    The key lexical distinction is whether f has no definedness condition
    (accepting any event) or presupposes normative content. Note that
    f's definedness controls which events CAN anchor the MI; content
    licensing (whether the event has propositional content) independently
    determines the resulting modal flavor. -/
inductive AnchorConstraint where
  /-- f has no definedness condition: defined for any event regardless
      of content. The anchor constraint does not restrict WHERE f can
      anchor. Whether the resulting background is epistemic, however,
      depends on the specific projection function f — not just on
      anchor definedness or content licensing. For *yalnhej*, f yields
      an epistemic background from contentful events; for *n'importe
      quel* and *un qualsiasi*, f always yields a circumstantial/
      indiscriminacy background regardless of the event's content
      (@cite{alonso-ovalle-royer-2024}, §6.2: "different functions
      projecting modal domains from those anchors").
      Ex: Chuj *yalnhej*, French *n'importe quel*, Italian *un qualsiasi*. -/
  | unrestricted
  /-- f presupposes that its event argument has normative content
      (a decision subevent of a volitional event). Speech acts lack
      normative content, so f(speech event) is undefined → no epistemic.
      Only yields RC readings (from volitional VP events).
      Ex: Spanish *uno cualquiera*. -/
  | volitionalOnly
  deriving DecidableEq, Repr


-- ════════════════════════════════════════════════════
-- § 3. Modal Indefinite Entry
-- ════════════════════════════════════════════════════

/-- A cross-linguistic modal indefinite entry parameterized along
@cite{alonso-ovalle-royer-2024} three dimensions of variation. -/
structure ModalIndefiniteEntry where
  /-- Language name -/
  language : String
  /-- Surface form -/
  form : String
  /-- Gloss or translation -/
  gloss : String
  /-- Dimension 1: Is the modal component at-issue? -/
  status : ModalComponentStatus
  /-- Dimension 2: Which modal flavors are available? -/
  flavors : List ModalFlavor
  /-- Dimension 3: Does it impose an upper bound (anti-singleton)? -/
  upperBounded : Bool
  /-- Is the available flavor sensitive to syntactic position? -/
  positionSensitive : Bool := false
  /-- Does the item have a plain/unremarkable (non-modal) reading in
      addition to its modal reading? (A-@cite{alonso-ovalle-royer-2024}, §5) -/
  hasUnremarkableReading : Bool := false
  /-- Can the item appear in predicative position?
      Correlates with unremarkable readings per A-@cite{alonso-ovalle-royer-2024}. -/
  canBePredicate : Bool := false
  /-- Anchor constraint on the anchoring function f.
      Only applicable to at-issue modal indefinites analyzed via
      event-relative anchoring (@cite{alonso-ovalle-royer-2024}).
      `none` for items with non-at-issue modal components
      (e.g., *algún*, *irgendein*) where the mechanism is
      conversational implicature or domain widening. -/
  anchorConstraint : Option AnchorConstraint := none
  /-- Whether the item is number-neutral (compatible with singular
      and plural reference). Chuj *yalnhej* is number-neutral
      (wh-phrase origin); Spanish *algún* is singular-only. -/
  numberNeutral : Bool := false
  /-- Source citation -/
  source : String := ""
  deriving Repr

def ModalIndefiniteEntry.hasEpistemic (e : ModalIndefiniteEntry) : Bool :=
  e.flavors.any (· == .epistemic)

def ModalIndefiniteEntry.hasCircumstantial (e : ModalIndefiniteEntry) : Bool :=
  e.flavors.any (· == .circumstantial)


end Core.ModalIndefinite
