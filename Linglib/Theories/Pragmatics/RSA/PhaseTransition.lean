import Linglib.Theories.Pragmatics.RSA.Extensions.InformationTheory.Basic

/-!
# Rate-Distortion View of RSA (Stub)

Formalizes the main results from Zaslavsky, Hu & Levy (2020),
"A Rate-Distortion view of human pragmatic reasoning" (arXiv:2005.06641).

## Results (to be restated for RSAConfig)

1. **Proposition 1** (SM §B, Eq. 7-9): RSA dynamics implement alternating
   maximization of G_α. Each step is an argmax, so G_α is monotonically
   non-decreasing across iterations.

2. **Proposition 2** (main text p.3): E[V_L] can decrease even as G_α
   increases — disconfirming the conjecture that RSA maximizes expected
   listener utility.

3. **Proposition 3** (SM §C): Phase transition at α = 1.

Old RSAScenarioQ-based proofs removed; restate using RSAConfig.

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human
  pragmatic reasoning. arXiv:2005.06641.
- Cover, T. M. & Thomas, J. A. (2006). Elements of Information Theory.
-/
