/-
# Scale-Entailment Interaction

This module shows how monotonicity affects scalar implicatures.

## Key Insight

In **UE contexts** (default):
- Scale: some < all (all is informationally stronger)
- Speaker said "some"
- Alternative "all" was available but not used
- Implicature: speaker doesn't believe "all" holds

In **DE contexts** (negation, "no", restrictor of "every"):
- Entailment REVERSES
- "some" becomes informationally STRONGER than "all"
- "No one ate some" ⊢ "No one ate all" (not the other way!)
- No alternative to negate → no implicature

Reference: van Benthem (1986), Ladusaw (1980), Barwise & Cooper (1981)
-/

import Linglib.Theories.Montague.Entailment.Monotonicity
import Linglib.Theories.Montague.Scales

namespace Montague.Entailment.ScaleInteraction

open Montague.Entailment
open Montague.Entailment.Monotonicity
open Montague.Scales

/-
## How Monotonicity Affects Scalar Alternatives

Horn scales (from Scales.lean) are ordered by semantic strength.
In UE contexts, stronger terms are scalar alternatives.
In DE contexts, the scale REVERSES - weaker terms become alternatives.

This explains why "some → not all" is blocked in DE contexts:
- In UE: "all" is a stronger alternative to "some"
- In DE: "all" is NOT a stronger alternative (scale reversed)
-/

/--
**Scale Reversal in DE Contexts**

In UE context: "some" has stronger alternatives [most, all]
In DE context: "some" has only weaker alternatives [none] - it's now strongest!
-/
theorem scale_alternatives_reverse :
    scalarAlternativesInContext Quantifiers.quantScale .some_ .upward = [.most, .all] ∧
    scalarAlternativesInContext Quantifiers.quantScale .some_ .downward = [.none_] := by
  native_decide

/--
**DE Blocks "Some → Not All" Implicature**

The implicature requires "all" to be a stronger alternative.
In DE contexts, "all" is NOT in the alternatives - hence no implicature.
-/
theorem de_blocks_scalar_implicature :
    -- In UE, alternatives include "all"
    scalarAlternativesInContext Quantifiers.quantScale .some_ .upward = [.most, .all] ∧
    -- In DE, alternatives do NOT include "all"
    scalarAlternativesInContext Quantifiers.quantScale .some_ .downward = [.none_] := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Summary Table

| Context              | Position    | Monotonicity | Implicature? |
|---------------------|-------------|--------------|--------------|
| Simple predication  | scope       | UE           | Yes          |
| Negation            | argument    | DE           | Blocked      |
| "every"             | scope       | UE           | Yes          |
| "every"             | restrictor  | DE           | Blocked      |
| "some"              | scope       | UE           | Yes          |
| "no"                | scope       | DE           | Blocked      |

## Proven Monotonicity Properties

### DE (Downward Entailing) - blocks scalar implicatures
- `negation_is_DE`: ¬ is DE
- `no_scope_DE`: scope of "no" is DE
- `every_restr_DE`: restrictor of "every" is DE

### UE (Upward Entailing) - allows scalar implicatures
- `conjunction_second_UE`: ∧ is UE in second arg
- `disjunction_second_UE`: ∨ is UE in second arg
- `every_scope_UE`: scope of "every" is UE
- `some_scope_UE`: scope of "some" is UE

### Key Results
- `negation_reverses_example`: Concrete proof that negation reverses entailment
- `de_reverses_strength`: DE contexts reverse scalar strength ordering
- `scale_alternatives_reverse`: DE reverses which alternatives are "stronger"
- `de_blocks_scalar_implicature`: Explains why "not all" blocked in DE
-/

end Montague.Entailment.ScaleInteraction
