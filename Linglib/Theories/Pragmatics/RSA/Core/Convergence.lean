import Linglib.Theories.Pragmatics.RSA.Core.Config

/-!
# RSA Convergence Theory (Stub)
@cite{csiszr-tusndy-1984} @cite{zaslavsky-hu-levy-2020}

Proves that RSA dynamics converge by showing G_α is monotonically increasing.

## Results (to be restated for RSAConfig)

1. Concavity: G_α is concave in S (fixed L) and concave in L (fixed S)
2. Alternating maximization: RSA speaker/listener updates maximize G_α
3. Monotonicity: G_α(S_t, L_t) ≤ G_α(S_{t+1}, L_{t+1}) for all t
4. Convergence: RSA dynamics converge to a fixed point

Old RSAScenarioR-based proofs removed; restate using RSAConfig.

-/
