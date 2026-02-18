import Linglib.Theories.Pragmatics.RSA.Extensions.InformationTheory.Basic

/-!
# Utility Non-Monotonicity with α < 1 (Stub)

Formalizes Proposition 2 from Zaslavsky et al. (2020):

> Expected listener utility E[V_L] can decrease during RSA iterations,
> even though G_α increases monotonically.

This result distinguishes RSA from pure information-theoretic optimization:
the objective G_α can improve while actual communication accuracy temporarily
decreases.

## Counterexample Requirements (from Zaslavsky et al. 2020, page 3)

Three conditions are necessary for utility non-monotonicity:

1. Graded lexicon: φ(m,u) ∈ (0,1], not binary {0,1}.
2. α < 1: Below the rate-distortion critical point.
3. Non-maximal initial entropy: Start from (L₀, S₁), not uniform.

Old RSAScenarioQ-based counterexample removed; restate using RSAConfig.

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human
  pragmatic reasoning. arXiv:2005.06641, Proposition 2 and Figure 3.
-/
