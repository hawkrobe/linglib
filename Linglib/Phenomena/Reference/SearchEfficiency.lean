import Mathlib.Data.Rat.Defs
import Linglib.Core.PropertyDomain

/-!
# Search Efficiency in Reference Production

@cite{giles-etal-2026}


The search efficiency view of overinformativeness: speakers produce
redundant modifiers when the modifier facilitates the listener's
perceptual search for the referent. An expression is search-efficient
when its production cost (to the speaker) is outweighed by its search
benefit (to the listener).

## Three Factors

Search efficiency depends on three perceptual properties of the display:

1. **Discriminability**: How easy is it to tell the target's attribute
   value apart from distractors' values? High discriminability → easy
   search along that attribute. Operationalised via psychophysical
   staircases in @cite{giles-etal-2026}.

2. **Contextual distinctiveness**: What fraction of items in the display
   share the target's attribute value? When the target is unique on an
   attribute (high distinctiveness), mentioning that attribute enables
   immediate filtering.

3. **Display density**: How many items are in the display? More items →
   slower serial search, increasing the benefit of any filtering cue.

## Connection to RSA

In the cs-RSA framework (@cite{degen-etal-2020}), search efficiency
enters through the noise parameters. High discriminability corresponds
to a large noise gap (match − mismatch), which makes the redundant
modifier informative to L0 even when it doesn't change the Boolean
denotation.

The search efficiency view adds a *perceptual grounding* for the noise
parameters: they reflect the physical properties of the display, not
just abstract semantic noise.
-/

set_option autoImplicit false

namespace Phenomena.Reference.SearchEfficiency

-- ============================================================================
-- § Display Properties
-- ============================================================================

/-- A referential display characterised by its search-relevant properties.
    These three factors jointly determine the listener's search cost and
    the potential benefit of a redundant modifier.

    @cite{giles-etal-2026} Exp 1 manipulates discriminability ×
    sufficiency; Exp 2 compares attribute types (colour vs orientation)
    across display density and contextual distinctiveness levels. -/
structure SearchContext where
  /-- Display density: total number of objects in the display.
      More objects → slower serial search. -/
  displaySize : Nat
  /-- Contextual distinctiveness: number of objects sharing the
      target's value on the redundant attribute. 0 = target is
      unique; displaySize − 1 = all objects share the value. -/
  nDistractorsSharing : Nat
  /-- Perceptual discriminability of the redundant attribute:
      the noise gap (match − mismatch) from `RSA.Noise`.
      Range: 0 (no discrimination) to 1 (perfect). -/
  discriminability : ℚ
  /-- The redundant attribute's property domain. -/
  domain : Core.PropertyDomain
  deriving Repr

-- ============================================================================
-- § Information Sufficiency
-- ============================================================================

/-- Whether an attribute is informationally sufficient to identify the
    target: the attribute value uniquely picks out the target among all
    objects in the display. -/
inductive Sufficiency where
  /-- The attribute alone identifies the target. -/
  | sufficient
  /-- The attribute does not alone identify the target; it is redundant
      when paired with a sufficient attribute. -/
  | redundant
  deriving Repr, DecidableEq

/-- The experimental conditions from @cite{giles-etal-2026} Exp 1,
    defined by the sufficiency × discriminability interaction. -/
inductive DisplayType where
  /-- Sufficient attribute: high discriminability,
      Redundant attribute: low discriminability.
      Search efficiency predicts LOW overinformativeness:
      the sufficient attribute is already search-efficient. -/
  | sHighRLow
  /-- Sufficient attribute: low discriminability,
      Redundant attribute: high discriminability.
      Search efficiency predicts HIGH overinformativeness:
      the redundant attribute helps an otherwise difficult search. -/
  | sLowRHigh
  /-- Both attributes: high discriminability.
      Tests whether speakers mention all discriminable attributes or
      selectively overinform to help difficult searches. -/
  | baseline
  deriving Repr, DecidableEq

-- ============================================================================
-- § Search Efficiency Predictions
-- ============================================================================

/-- The core prediction of the search efficiency view: overinformativeness
    should track the interaction of sufficiency and discriminability.

    When the sufficient attribute is hard to search (low discriminability)
    and the redundant attribute is easy (high discriminability), speakers
    overinform to help the listener's search. When the sufficient attribute
    is already search-efficient, redundancy adds no benefit. -/
def searchEfficiencyPredicts (dt : DisplayType) : Bool :=
  match dt with
  | .sLowRHigh => true   -- high overinformativeness predicted
  | .baseline  => false  -- intermediate (lower than sLowRHigh)
  | .sHighRLow => false  -- low overinformativeness predicted

end Phenomena.Reference.SearchEfficiency
