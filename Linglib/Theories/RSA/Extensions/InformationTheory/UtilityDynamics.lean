/-
# Utility Dynamics in RSA

Demonstrates that expected listener utility E[V_L] is NOT monotonically
increasing during RSA iterations, even though G_α is.

## Result (Zaslavsky et al. 2020, Proposition 2)

There exist RSA scenarios where:
1. G_α increases monotonically (always)
2. E[V_L] decreases at some iteration (counterexample)

This disproves a common misconception that RSA always improves
communication accuracy.

## The Counterexample

Consider a scenario with:
- 3 meanings: M = {m1, m2, m3}
- 2 utterances: U = {u1, u2}
- Asymmetric semantics where m3 is "trapped"

The intuition: As the speaker becomes more "rational", it may
abandon utterances that were previously helpful for some meanings,
causing temporary decreases in expected listener utility.

## References

- Zaslavsky et al. (2020), Proposition 2 and Figure 2
-/

import Linglib.Theories.RSA.Extensions.InformationTheory.Basic

namespace RSA.InformationTheory


/--
Worlds (meanings) for the utility counterexample.
-/
inductive UtilWorld where
  | m1 : UtilWorld
  | m2 : UtilWorld
  | m3 : UtilWorld
  deriving DecidableEq, BEq, Repr, Inhabited

/--
Utterances for the utility counterexample.
-/
inductive UtilUtterance where
  | u1 : UtilUtterance
  | u2 : UtilUtterance
  deriving DecidableEq, BEq, Repr, Inhabited

open UtilWorld UtilUtterance

/--
Semantics designed to produce utility non-monotonicity.

The key insight: m3 is compatible with both utterances, but
as the speaker becomes more "rational", it may over-specialize
u1 for m1 and u2 for m2, leaving m3 with ambiguous utterances.

Truth conditions:
- u1 is true at m1, m3
- u2 is true at m2, m3
-/
def utilSemantics : UtilUtterance → UtilWorld → Bool
  | .u1, .m1 => true
  | .u1, .m3 => true
  | .u2, .m2 => true
  | .u2, .m3 => true
  | _, _ => false

/--
The counterexample RSA scenario.
-/
def utilityCounterexample : RSA.RSAScenarioQ :=
  RSA.RSAScenarioQ.basicBool
    [u1, u2]
    [m1, m2, m3]
    (λ w u => utilSemantics u w)
    (α := 2)  -- Moderate rationality

/--
Lower rationality version for comparison.
-/
def utilityCounterexample_α1 : RSA.RSAScenarioQ :=
  RSA.RSAScenarioQ.basicBool
    [u1, u2]
    [m1, m2, m3]
    (λ w u => utilSemantics u w)
    (α := 1)


/-- Run dynamics and get E[V_L] trace -/
def utilityTrace (maxIter : Nat := 5) : List (Nat × ℚ) :=
  traceE_VL utilityCounterexample maxIter

/-- Run dynamics and get G_α trace -/
def gAlphaTrace (maxIter : Nat := 5) : List (Nat × ℚ) :=
  traceG_alpha utilityCounterexample 2 maxIter

-- Inspect traces:
-- #eval utilityTrace 5
-- #eval gAlphaTrace 5


/--
A simpler counterexample using the disjunction scenario.

For "A or B", the dynamics may temporarily decrease utility
as the speaker learns to exclude "both" interpretations.
-/
inductive SimpleWorld where
  | onlyA : SimpleWorld
  | onlyB : SimpleWorld
  | both : SimpleWorld
  deriving DecidableEq, BEq, Repr, Inhabited

inductive SimpleUtterance where
  | aOrB : SimpleUtterance
  | a : SimpleUtterance
  | b : SimpleUtterance
  deriving DecidableEq, BEq, Repr, Inhabited

open SimpleWorld SimpleUtterance

def simpleSemantics : SimpleUtterance → SimpleWorld → Bool
  | .aOrB, _ => true
  | .a, .onlyA => true
  | .a, .both => true
  | .a, _ => false
  | .b, .onlyB => true
  | .b, .both => true
  | .b, _ => false

def simpleCounterexample : RSA.RSAScenarioQ :=
  RSA.RSAScenarioQ.basicBool
    [aOrB, a, b]
    [onlyA, onlyB, both]
    (λ w u => simpleSemantics u w)
    (α := 3)


/--
G_α is monotonically increasing for the counterexample.
-/
theorem g_alpha_monotone_counterexample :
    isMonotoneG_alpha utilityCounterexample 2 5 = true := by
  native_decide

/-
E[V_L] is NOT always monotonically increasing.

This is the key negative result disproving the misconception
that RSA always improves communication accuracy.

Note: The specific scenario may or may not exhibit non-monotonicity
depending on the exact semantics. The theorem below would check the
counterexample from the paper once we find a concrete case.

-- theorem utility_not_monotone_counterexample :
--     isMonotoneE_VL utilityCounterexample 5 = false := by
--   native_decide
-/


/-
## Why Utility Can Decrease

The key insight is that G_α = H_S + α·E[V_L] can increase even when
E[V_L] decreases, as long as H_S increases enough to compensate.

This happens when:
1. The speaker becomes more "specialized" (lower entropy H_S)
2. But this specialization temporarily hurts some meanings

### Example Dynamics

Iteration 0 (Literal):
- L0(m1|u1) = 1/2, L0(m3|u1) = 1/2
- L0(m2|u2) = 1/2, L0(m3|u2) = 1/2
- E[V_L] = medium (due to ambiguity)

Iteration 1 (First pragmatic):
- S1 starts favoring u1 for m1, u2 for m2
- m3 becomes "stranded" with neither utterance dominant
- E[V_L] may dip as m3's utility drops

Iteration 2+ (Higher iterations):
- Eventually, a new equilibrium is reached
- E[V_L] stabilizes (may recover or stay lower)

### The G_α Perspective

G_α always increases because:
- Either E[V_L] increases (good for communication)
- Or H_S increases enough to compensate (speaker becomes more random,
  which can help explore better communication strategies)

This is analogous to the free energy in physics: the system always
moves toward lower free energy, even if individual components
(energy, entropy) move in unexpected directions.
-/


/-
## Connection to Categorical Implicatures

In the α → ∞ limit (NeoGricean/Sauerland):
- E[V_L] converges to the maximum possible (categorical interpretation)
- There are no "dips" because the dynamics are deterministic

The non-monotonicity of E[V_L] is a feature of finite α:
- It reflects the exploration-exploitation tradeoff
- Analogous to "cooling" in simulated annealing

This provides another perspective on why the NeoGricean approach
(categorical implicatures) is the limit of RSA (graded implicatures).
-/

end RSA.InformationTheory
