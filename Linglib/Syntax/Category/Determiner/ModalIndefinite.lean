import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Semantics.Modality.Anchor
import Linglib.Semantics.Presupposition.ContentLayer

/-!
# Modal indefinites

A modal indefinite is a determiner whose existential claim carries a modal component
(Spanish *algún* and *uno cualquiera*, German *irgendein*, Chuj *yalnhej*). The record
holds the dimensions along which they vary: the content layer of the component (at-issue,
or an implicature), the flavors it can take, whether the existential claim is
upper-bounded, the definedness condition on its anchor, and the lexical properties that
correlate with them.

## Main definitions

* `ModalIndefinite` — the determiner record.

## References

* [alonso-ovalle-royer-2024]
* [alonso-ovalle-menendez-benito-2010]
* [kratzer-shimoyama-2002]
-/

open Modality Semantics.ContentLayer

/-- A modal indefinite determiner. -/
structure ModalIndefinite extends Determiner where
  /-- The content layer of the modal component: at-issue, or an implicature. -/
  status : ContentLayer
  /-- The modal flavors the component can take. -/
  flavors : Finset ModalFlavor
  /-- Whether the existential claim excludes the whole domain satisfying the scope. -/
  upperBounded : Bool
  /-- Whether the item also has a non-modal reading on which the witness is unremarkable. -/
  hasUnremarkableReading : Bool := false
  /-- Whether the item can be a predicate. -/
  canBePredicate : Bool := false
  /-- The definedness condition on the anchor, for items whose component is projected
  from an event. -/
  anchorConstraint : Option AnchorConstraint := none
  /-- Whether the item is semantically number neutral. -/
  numberNeutral : Bool := false
  deriving DecidableEq
