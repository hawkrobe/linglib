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
-- § 2. Modal Indefinite Entry
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
  /-- Source citation -/
  source : String := ""
  deriving Repr

def ModalIndefiniteEntry.hasEpistemic (e : ModalIndefiniteEntry) : Bool :=
  e.flavors.any (· == .epistemic)

def ModalIndefiniteEntry.hasCircumstantial (e : ModalIndefiniteEntry) : Bool :=
  e.flavors.any (· == .circumstantial)


end Core.ModalIndefinite
