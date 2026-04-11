/-
# @cite{nadathur-lauer-2020}: Causal Necessity and Sufficiency

Formalization of @cite{nadathur-lauer-2020} analysis of causative verbs
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

- `Core.StructuralEquationModel`: Situations, causal laws, normal development
- `Sufficiency`: Causal sufficiency, semantics of "make"
- `Necessity`: Causal necessity, semantics of "cause"
- `CoerciveImplication`: Volitionality and coercion inference
- `Integration`: Bridge to @cite{grusdt-lassiter-franke-2022} probabilistic model

## Key Definitions

| Definition | Meaning |
|------------|---------|
| `Situation` | Partial valuation of variables |
| `CausalLaw` | If preconditions hold, effect follows |
| `CausalDynamics` | Collection of causal laws |
| `normalDevelopment` | Forward propagation to fixpoint |
| `causallySufficient` | Adding cause guarantees effect (@cite{nadathur-lauer-2020} Def 23) |
| `causallyNecessary` | Supersituation necessity (@cite{nadathur-2024} Def 10b) |
| `makeSem` | Semantics of "make" (sufficiency) |
| `causeSem` | Semantics of "cause" (necessity + occurrence) |

-/

-- Re-export all submodules
import Linglib.Core.StructuralEquationModel
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Causation.CCSelection
import Linglib.Theories.Semantics.Causation.Builder
import Linglib.Theories.Semantics.Causation.CoerciveImplication
import Linglib.Theories.Semantics.Causation.Integration
import Linglib.Theories.Semantics.Causation.GradedCausation
import Linglib.Theories.Semantics.Causation.CausalStrength
import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Causation.ComplementEntailing
import Linglib.Theories.Semantics.Causation.CausalClosure
import Linglib.Theories.Semantics.Causation.DegreeCausation
import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Causation.PsychCausalLink

namespace NadathurLauer2020

-- Re-export key definitions for convenience
export Core.StructuralEquationModel (
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

export Causation.CCSelection (
  CCSelectionMode completesForEffect ccConstraintSatisfied
)

-- Summary theorem: the main linguistic claim
/--
**Main Linguistic Claim**: "make" and "cause" are truth-conditionally distinct.

There exist scenarios where "X made Y happen" is true but "X caused Y" is false,
and vice versa.

Witnessed by disjunctive overdetermination: lightning OR arsonist → fire.
With both present, lightning is sufficient (makeSem = true) but not necessary
(causeSem = false) because the arsonist backup blocks but-for. -/
theorem make_cause_truth_conditionally_distinct :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      makeSem dyn s c e ≠ causeSem dyn s c e := by
  open Core.StructuralEquationModel in
  exact ⟨.disjunctiveCausation (mkVar "l") (mkVar "a") (mkVar "f"),
         Situation.empty.extend (mkVar "l") true |>.extend (mkVar "a") true,
         mkVar "l", mkVar "f", by native_decide⟩

end NadathurLauer2020
