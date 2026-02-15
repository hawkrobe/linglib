/-
# Examples: Fire, Circuit, and Overdetermination

Concrete examples demonstrating the necessity/sufficiency distinction
from Nadathur & Lauer (2020).

## Fire Scenario (Section 3.1)

The classic overdetermination case:
- Lightning strikes
- Arsonist is also present
- Both could independently cause the fire

Key results:
- Lightning is **sufficient** (adding it → fire)
- Lightning is **NOT necessary** (arsonist would have caused fire anyway)
- Arsonist is **sufficient** (adding it → fire)
- Arsonist is **NOT necessary** (lightning would have caused fire anyway)

## Circuit Scenario

A simpler scenario with a single cause:
- Short circuit occurs
- Fire results
- No other potential causes

Key results:
- Short circuit is both **sufficient** AND **necessary**
- This is the "cause" ∩ "make" case

## References

- Nadathur & Lauer (2020), Section 3
-/

import Linglib.Theories.IntensionalSemantics.Causative.Sufficiency
import Linglib.Theories.IntensionalSemantics.Causative.Necessity

namespace NadathurLauer2020.Examples

open Core.Causation
open NadathurLauer2020.Sufficiency
open NadathurLauer2020.Necessity

-- Fire Scenario: Overdetermination

section FireScenario

/-- Lightning variable -/
def lightning : Variable := mkVar "lightning"

/-- Arsonist variable -/
def arsonist : Variable := mkVar "arsonist"

/-- Fire variable -/
def fire : Variable := mkVar "fire"

/--
Fire dynamics: lightning OR arsonist causes fire.

This is disjunctive causation: either cause alone is sufficient.
-/
def fireDynamics : CausalDynamics :=
  CausalDynamics.disjunctiveCausation lightning arsonist fire

/--
Background where only lightning is present.
-/
def lightningOnlyBackground : Situation :=
  Situation.empty.extend lightning true

/--
Background where only arsonist is present.
-/
def arsonistOnlyBackground : Situation :=
  Situation.empty.extend arsonist true

/--
Background where both causes are present (overdetermination).
-/
def bothCausesBackground : Situation :=
  Situation.empty.extend lightning true |>.extend arsonist true

-- Fire Scenario: Sufficiency Results

/--
**Lightning is sufficient for fire** (in empty background).

"The lightning made the fire start" is true because:
adding lightning to the empty background produces fire.
-/
theorem lightning_sufficient_empty :
    causallySufficient fireDynamics Situation.empty lightning fire = true := by
  native_decide

/--
**Arsonist is sufficient for fire** (in empty background).

"The arsonist made the fire start" is true because:
adding arsonist to the empty background produces fire.
-/
theorem arsonist_sufficient_empty :
    causallySufficient fireDynamics Situation.empty arsonist fire = true := by
  native_decide

/--
**Lightning is still sufficient in overdetermination**.

Even when arsonist is also present, lightning alone would have been enough.
-/
theorem lightning_sufficient_overdetermination :
    causallySufficient fireDynamics bothCausesBackground lightning fire = true := by
  simp only [causallySufficient, bothCausesBackground, fireDynamics,
             CausalDynamics.disjunctiveCausation]
  native_decide

-- Fire Scenario: Necessity Results

/--
**Lightning is necessary for fire** (when it's the only cause).

"The lightning caused the fire" is true when only lightning is present:
without lightning, no fire.
-/
theorem lightning_necessary_solo :
    causallyNecessary fireDynamics lightningOnlyBackground lightning fire = true := by
  native_decide

/--
**Lightning is NOT necessary in overdetermination**.

"The lightning caused the fire" is FALSE when both causes are present:
without lightning, arsonist would have caused the fire anyway.

This is the key overdetermination result!
-/
theorem lightning_not_necessary_overdetermination :
    causallyNecessary fireDynamics bothCausesBackground lightning fire = false := by
  native_decide

/--
**Arsonist is NOT necessary in overdetermination**.

Symmetrically, arsonist isn't necessary when lightning is also present.
-/
theorem arsonist_not_necessary_overdetermination :
    causallyNecessary fireDynamics bothCausesBackground arsonist fire = false := by
  native_decide

-- Fire Scenario: Cause vs Make

/--
**Overdetermination: "make" but NOT "cause"**

In the overdetermination scenario:
- "The lightning made the fire start" is TRUE (sufficiency)
- "The lightning caused the fire" is FALSE (necessity fails)

This demonstrates the semantic difference between "make" and "cause".
-/
theorem overdetermination_make_not_cause :
    makeSem fireDynamics bothCausesBackground lightning fire = true ∧
    causeSem fireDynamics bothCausesBackground lightning fire = false := by
  constructor <;> native_decide

/--
**Solo cause: both "make" AND "cause"**

When lightning is the only cause:
- "The lightning made the fire start" is TRUE
- "The lightning caused the fire" is TRUE

Both verbs are felicitous when there's no overdetermination.
-/
theorem solo_make_and_cause :
    makeSem fireDynamics lightningOnlyBackground lightning fire = true ∧
    causeSem fireDynamics lightningOnlyBackground lightning fire = true := by
  constructor <;> native_decide

end FireScenario

-- Circuit Scenario: Simple Causation

section CircuitScenario

/-- Short circuit variable -/
def shortCircuit : Variable := mkVar "short_circuit"

/-- Building fire variable -/
def buildingFire : Variable := mkVar "building_fire"

/--
Circuit dynamics: short circuit causes fire.

Simple causation: one cause, one effect.
-/
def circuitDynamics : CausalDynamics :=
  ⟨[CausalLaw.simple shortCircuit buildingFire]⟩

/--
Background where short circuit occurred.
-/
def circuitBackground : Situation :=
  Situation.empty.extend shortCircuit true

/--
**Short circuit is sufficient for fire**.
-/
theorem circuit_sufficient :
    causallySufficient circuitDynamics Situation.empty shortCircuit buildingFire = true := by
  native_decide

/--
**Short circuit is necessary for fire** (when it's the only cause).
-/
theorem circuit_necessary :
    causallyNecessary circuitDynamics circuitBackground shortCircuit buildingFire = true := by
  native_decide

/--
**Both "make" and "cause" are true for simple causation**.
-/
theorem circuit_both_verbs :
    makeSem circuitDynamics circuitBackground shortCircuit buildingFire = true ∧
    causeSem circuitDynamics circuitBackground shortCircuit buildingFire = true := by
  constructor <;> native_decide

end CircuitScenario

-- Causal Chain Example

section ChainScenario

/-- Initial cause -/
def flip : Variable := mkVar "flip"

/-- Intermediate event -/
def switch : Variable := mkVar "switch"

/-- Final effect -/
def light : Variable := mkVar "light"

/--
Chain dynamics: flip → switch → light

Causal chain: initial cause triggers intermediate which triggers final effect.
-/
def chainDynamics : CausalDynamics :=
  CausalDynamics.causalChain flip switch light

/--
Background where flip occurred.
-/
def chainBackground : Situation :=
  Situation.empty.extend flip true

/--
**Flip is sufficient for light** (through the chain).
-/
theorem chain_sufficient :
    causallySufficient chainDynamics Situation.empty flip light = true := by
  native_decide

/--
**Flip is necessary for light** (as the initial cause).
-/
theorem chain_necessary :
    causallyNecessary chainDynamics chainBackground flip light = true := by
  native_decide

/--
**Switch is also necessary for light** (as intermediate).

Note: The chain dynamics flip → switch → light means switch depends on flip.
When we test necessity of switch, we set switch=false and check if light still happens.
But flip=true triggers switch=true again through the dynamics, so this is subtle.

In this model, with flip already in background, removing switch doesn't help
because flip will re-trigger switch. This shows the interaction between
necessity testing and causal chains.
-/
theorem chain_intermediate_result :
    let background := Situation.empty.extend flip true |>.extend switch true
    -- In this dynamics, switch is NOT necessary because flip re-triggers it
    causallyNecessary chainDynamics background switch light = false := by
  native_decide

end ChainScenario

-- Conjunctive Causation Example

section ConjunctiveScenario

/-- Match -/
def match_ : Variable := mkVar "match"

/-- Oxygen -/
def oxygen : Variable := mkVar "oxygen"

/-- Combustion -/
def combustion : Variable := mkVar "combustion"

/--
Conjunctive dynamics: match AND oxygen → combustion

Both conditions required for the effect.
-/
def conjDynamics : CausalDynamics :=
  CausalDynamics.conjunctiveCausation match_ oxygen combustion

/--
Background where oxygen is present (enabling condition).
-/
def oxygenBackground : Situation :=
  Situation.empty.extend oxygen true

/--
**Match alone is NOT sufficient** (in empty background).
-/
theorem match_not_sufficient_alone :
    causallySufficient conjDynamics Situation.empty match_ combustion = false := by
  native_decide

/--
**Match IS sufficient** when oxygen is present.
-/
theorem match_sufficient_with_oxygen :
    causallySufficient conjDynamics oxygenBackground match_ combustion = true := by
  native_decide

/--
**Match is necessary for combustion** (given oxygen).
-/
theorem match_necessary_with_oxygen :
    let background := oxygenBackground.extend match_ true
    causallyNecessary conjDynamics background match_ combustion = true := by
  native_decide

/--
**Oxygen is also necessary** (given match).

Both conjuncts are necessary when both are present.
-/
theorem oxygen_necessary_with_match :
    let background := Situation.empty.extend match_ true |>.extend oxygen true
    causallyNecessary conjDynamics background oxygen combustion = true := by
  native_decide

end ConjunctiveScenario

-- Summary Theorems

/--
**Main result 1**: Sufficiency does not entail necessity.

Demonstrated by the overdetermination fire scenario.
-/
theorem main_sufficiency_not_necessity :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      causallySufficient dyn s c e = true ∧
      causallyNecessary dyn s c e = false := by
  use fireDynamics, bothCausesBackground, lightning, fire
  exact ⟨by native_decide, by native_decide⟩

/--
**Main result 2**: Necessity does not entail sufficiency (in empty background).

Demonstrated by conjunctive causation.
-/
theorem main_necessity_not_sufficiency_empty :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      -- Necessary in a specific background
      causallyNecessary dyn s c e = true ∧
      -- But not sufficient in empty background
      causallySufficient dyn Situation.empty c e = false := by
  let background := Situation.empty.extend oxygen true |>.extend match_ true
  use conjDynamics, background, match_, combustion
  constructor
  · -- match is necessary (given oxygen)
    native_decide
  · -- match alone is not sufficient
    native_decide

/--
**Main result 3**: "make" and "cause" have distinct truth conditions.

There exist scenarios where one is true and the other is false.
-/
theorem make_cause_distinct :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      makeSem dyn s c e ≠ causeSem dyn s c e := by
  use fireDynamics, bothCausesBackground, lightning, fire
  simp only [makeSem, causeSem, ne_eq]
  native_decide

end NadathurLauer2020.Examples
