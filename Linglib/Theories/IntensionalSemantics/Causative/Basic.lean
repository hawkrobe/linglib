/-
# Nadathur & Lauer (2020): Causal Necessity and Sufficiency

Formalization of Nadathur & Lauer's (2020) analysis of causative verbs
"cause" and "make" in terms of causal necessity and sufficiency.

## Main Results

1. **"cause" asserts necessity**: "X caused Y" means Y counterfactually
   depended on X (without X, Y wouldn't have happened)

2. **"make" asserts sufficiency**: "X made Y happen" means X guaranteed Y
   (given X, Y was inevitable)

3. **These can come apart**: In overdetermination cases:
   - Lightning AND arsonist both present
   - "Lightning made the fire start" is TRUE (sufficient)
   - "Lightning caused the fire" is FALSE (not necessary - arsonist would have)

4. **Coercive implication**: "X made Y do Z" with volitional Z implies coercion

## Module Structure

- `Core.CausalModel`: Situations, causal laws, normal development
- `Sufficiency`: Causal sufficiency, semantics of "make"
- `Necessity`: Causal necessity, semantics of "cause"
- `Examples`: Fire scenario, circuit, causal chains
- `CoerciveImplication`: Volitionality and coercion inference
- `Integration`: Bridge to Grusdt et al. (2022) probabilistic model

## Usage

```lean
import Linglib.Theories.IntensionalSemantics.Causative.Basic

open Theories.NadathurLauer2020.Examples

-- Check if lightning is sufficient for fire
#eval causallySufficient fireDynamics Situation.empty lightning fire
-- => true

-- Check if lightning is necessary in overdetermination
#eval causallyNecessary fireDynamics bothCausesBackground lightning fire
-- => false
```

## Key Definitions

| Definition | Meaning |
|------------|---------|
| `Situation` | Partial valuation of variables |
| `CausalLaw` | If preconditions hold, effect follows |
| `CausalDynamics` | Collection of causal laws |
| `normalDevelopment` | Forward propagation to fixpoint |
| `causallySufficient` | Adding cause guarantees effect |
| `causallyNecessary` | Removing cause blocks effect |
| `makeSem` | Semantics of "make" (sufficiency) |
| `causeSem` | Semantics of "cause" (necessity + occurrence) |

## References

- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. Glossa 5(1), 49.
- Lewis, D. (1973). Counterfactuals. Blackwell.
- Pearl, J. (2000). Causality. Cambridge University Press.
- Grusdt, F., Lassiter, D. & Franke, M. (2022). Probabilistic modeling
  of rational communication with conditionals. Cognition.
-/

-- Re-export all submodules
import Linglib.Core.CausalModel
import Linglib.Theories.IntensionalSemantics.Causative.Sufficiency
import Linglib.Theories.IntensionalSemantics.Causative.Necessity
import Linglib.Theories.IntensionalSemantics.Causative.Builder
import Linglib.Theories.IntensionalSemantics.Causative.Examples
import Linglib.Theories.IntensionalSemantics.Causative.CoerciveImplication
import Linglib.Theories.IntensionalSemantics.Causative.Integration
import Linglib.Theories.IntensionalSemantics.Causative.GradedCausation
import Linglib.Theories.IntensionalSemantics.Causative.Implicative

namespace Theories.NadathurLauer2020

-- Re-export key definitions for convenience
export Core.CausalModel (
  Variable mkVar
  Situation CausalLaw CausalDynamics
)

export Sufficiency (
  causallySufficient makeSem
)

export Necessity (
  causallyNecessary causeSem actuallyCaused
)

export Builder (
  CausativeBuilder
)

-- Summary theorem: the main linguistic claim
/--
**Main Linguistic Claim**: "make" and "cause" are truth-conditionally distinct.

There exist scenarios where "X made Y happen" is true but "X caused Y" is false,
and vice versa.

This is demonstrated by the overdetermination examples in `Examples.lean`.
-/
theorem make_cause_truth_conditionally_distinct :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      makeSem dyn s c e ≠ causeSem dyn s c e :=
  Examples.make_cause_distinct

end Theories.NadathurLauer2020
