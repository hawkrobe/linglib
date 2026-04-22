import Linglib.Core.Causal.V2.Mechanism.Defs
import Linglib.Core.Causal.V2.Mechanism.PMF
import Mathlib.Data.Rat.Defs
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Mechanism.NoisyOr: Noisy-OR Parameterization (V2)

Migrates the parameter struct from the old `Core/Causal/BayesNet.lean`
into the new `Mechanism` framework. A `NoisyOrParams` describes a single
inhibitory link's parameters: background rate `P(C | ¬A)` and causal
power `P(C | A) − P(C | ¬A)`.

Phase A scope: only the parameter struct + single-parent mechanism
constructor. Multi-parent noisy-OR (combining `n` independent links)
is deferred to Phase B+ when consumers need it.

The old `BayesNet.WorldState` (joint distribution over two binary
variables) is NOT migrated here — it's an output distribution, not a
mechanism. If consumers need it, a separate `Core/Causal/Distribution.lean`
is the right home.
-/

namespace Core.Causal.V2.Mechanism

/-- Noisy-OR parameters for a single inhibitory link. Migrated from
    `Core.Causal.BayesNet.NoisyOR`. -/
structure NoisyOrParams where
  /-- Background rate: `P(effect | ¬cause)`. -/
  background : ℚ
  /-- Causal power: `P(effect | cause) − P(effect | ¬cause)`. -/
  power : ℚ
  deriving Repr, DecidableEq

namespace NoisyOrParams

/-- `P(effect | cause)`. -/
def pEffectGivenCause (n : NoisyOrParams) : ℚ := n.background + n.power

/-- `P(effect | ¬cause)`. -/
def pEffectGivenNotCause (n : NoisyOrParams) : ℚ := n.background

/-- Validity: both conditional probabilities lie in `[0, 1]`. -/
def isValid (n : NoisyOrParams) : Prop :=
  0 ≤ n.background ∧ n.background ≤ 1 ∧
  0 ≤ n.background + n.power ∧ n.background + n.power ≤ 1

instance (n : NoisyOrParams) : Decidable n.isValid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Deterministic cause: `P(effect|cause) = 1`, `P(effect|¬cause) = 0`. -/
def ofDeterministic : NoisyOrParams := ⟨0, 1⟩

/-- No effect: `P(effect|cause) = P(effect|¬cause) = 0`. -/
def noEffect : NoisyOrParams := ⟨0, 0⟩

/-- Always-on: `P(effect|cause) = P(effect|¬cause) = 1`. -/
def alwaysOn : NoisyOrParams := ⟨1, 0⟩

end NoisyOrParams

end Core.Causal.V2.Mechanism
