import Linglib.Semantics.Modality.ModalTypes

/-!
# Modal Indefinite Types

Framework-agnostic types for recording cross-linguistic properties of
modal indefinites — indefinites that conventionally encode a modal
component (Chuj *yalnhej*, Spanish *algún*, German *irgendein*) — along
[alonso-ovalle-royer-2024]'s dimensions of variation: status (§6.1),
content (§6.2), and upper-boundedness (within §6.2). Random-choice
readings are carried by the `.circumstantial` flavor.

Sibling of `Features/IndefiniteType.lean`, which classifies indefinites
by Degano & Aloni's variation/constancy types.

## Main declarations

* `ModalIndefiniteEntry` — a lexical entry over the three dimensions.
* `ModalComponentStatus`, `AnchorConstraint` — the status dimension and
  the definedness condition on the anchoring function f.
-/

namespace Features.ModalIndefinite

open Semantics.Modality (ModalFlavor)

/-! ### Modal component status -/

/-- Whether the modal component of a modal indefinite is at-issue
    (challengeable by direct denial) or not-at-issue (projects under
    negation, questions, and modals). -/
inductive ModalComponentStatus where
  /-- Part of assertive content. Ex: Chuj *yalnhej*, Sp. *uno cualquiera*. -/
  | atIssue
  /-- Presupposed or implicated rather than asserted. Ex: Sp. *algún*
      (conversational implicature per
      [alonso-ovalle-menendez-benito-2010]), Ger. *irgendein* (domain
      widening per [kratzer-shimoyama-2002]). -/
  | notAtIssue
  deriving DecidableEq, Repr

/-! ### Anchor constraint -/

/-- Whether the anchoring function f of an at-issue modal indefinite has
    a definedness condition ([alonso-ovalle-royer-2024] §4). -/
inductive AnchorConstraint where
  /-- f is defined for any event. For *yalnhej*, f yields an epistemic
      background from contentful events. French *n'importe quel* and
      Italian *un qualsiasi* express random choice only;
      [alonso-ovalle-royer-2024] (§6.2) leaves open whether that follows
      from an anchor constraint or from a different projection function,
      so their listing here picks no horn. -/
  | unrestricted
  /-- f presupposes normative content (a decision subevent of a
      volitional event), so only random-choice readings arise; on this
      analysis a speech event supplies no normative content, blocking
      epistemic readings. Ex: Spanish *uno cualquiera*. -/
  | volitionalOnly
  deriving DecidableEq, Repr

/-! ### Modal indefinite entry -/

/-- A modal indefinite entry over [alonso-ovalle-royer-2024]'s
    dimensions of variation. -/
structure ModalIndefiniteEntry where
  /-- Surface form -/
  form : String
  /-- Dimension 1: Is the modal component at-issue? -/
  status : ModalComponentStatus
  /-- Dimension 2: Which modal flavors are available? -/
  flavors : List ModalFlavor
  /-- Dimension 3: Does it impose an upper bound on witnesses in the
      described situation? (Distinct from
      [alonso-ovalle-menendez-benito-2010]'s anti-singleton domain
      constraint.) -/
  upperBounded : Bool
  /-- Does the item have a plain, non-modal reading in addition to its
      modal reading? ([alonso-ovalle-royer-2024], §5) -/
  hasUnremarkableReading : Bool := false
  /-- Can the item appear in predicative position? -/
  canBePredicate : Bool := false
  /-- Anchor constraint on the anchoring function f. `none` for
      not-at-issue items (conversational implicature, domain widening)
      and for at-issue items fitting neither constructor (Chuj *komon*:
      never epistemic, yet fine with non-volitional predicates). -/
  anchorConstraint : Option AnchorConstraint := none
  /-- Is the item number-neutral? Chuj *yalnhej* is; Spanish *algún* is
      singular-only. -/
  numberNeutral : Bool := false
  deriving Repr

/-- Whether the entry's modal component supports a given flavor. -/
def ModalIndefiniteEntry.hasFlavor (e : ModalIndefiniteEntry) (f : ModalFlavor) : Bool :=
  e.flavors.contains f

end Features.ModalIndefinite
