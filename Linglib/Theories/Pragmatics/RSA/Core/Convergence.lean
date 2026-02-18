import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Basic
import Linglib.Theories.Pragmatics.RSA.Core.GibbsVariational

/-!
# RSA Convergence Theory (Stub)

Proves that RSA dynamics converge by showing G_α is monotonically increasing.

## Results (to be restated for RSAConfig)

1. Concavity: G_α is concave in S (fixed L) and concave in L (fixed S)
2. Alternating maximization: RSA speaker/listener updates maximize G_α
3. Monotonicity: G_α(S_t, L_t) ≤ G_α(S_{t+1}, L_{t+1}) for all t
4. Convergence: RSA dynamics converge to a fixed point

Old RSAScenarioR-based proofs removed; restate using RSAConfig.

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human
  pragmatic reasoning. Proposition 1.
- Csiszár, I. & Tusnády, G. (1984). Information geometry and alternating
  minimization procedures.
-/
