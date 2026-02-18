import Linglib.Theories.Pragmatics.NeoGricean.ScalarImplicatures.Basic
import Linglib.Theories.Pragmatics.RSA.ScalarImplicatures.Basic

/-!
# NeoGricean vs RSA Comparison

Proves that NeoGricean and RSA derive the same scalar implicature
from "some" → "not all".

## Architecture

Both theories consume the same `SemDeriv.Derivation` (syntax-agnostic interface):

```
         SemDeriv.Derivation
         (from CCG, HPSG, etc.)
                  │
         ┌───────┴───────┐
         ▼               ▼
    NeoGricean          RSA
         │               │
         ▼               ▼
    ¬Bel(all)      P(¬all) high
         │               │
         └───────┬───────┘
                 ▼
         BOTH derive "not all"
```

## Status

The ℚ-based RSA computation functions have been removed. RSA-dependent
comparisons need to be re-derived using the new RSAConfig framework.

## Result

`scalar_implicature_agreement`: Both theories derive "not all" from "some"
-/

namespace Phenomena.ScalarImplicatures.CompareAgreement

open NeoGricean.ScalarImplicatures

/-
## The Core Agreement

Both NeoGricean and RSA derive "not all" from "some students sleep":

**NeoGricean**: Derives categorically that ¬Bel_S(all), which with competence
strengthens to Bel_S(¬all).

**RSA**: Derives probabilistically that P(w1,w2) > P(w3), meaning the listener
assigns higher probability to "some but not all" worlds than to "all" world.

The derivations are structurally different but agree on the outcome.
-/

/--
**NeoGricean side**: "some" derives "not all" implicature.
-/
theorem neogricean_derives_not_all :
    hasImplicature someStudentsSleep_result "all" = true := by
  native_decide

/--
**Agreement on DE Blocking**

NeoGricean explicitly blocks scalar implicatures in downward-entailing contexts.
-/
theorem de_blocking :
    hasImplicature someStudentsSleep_DE_result "all" = false := by
  native_decide

/-
## Correspondence Between Frameworks

| NeoGricean Concept | RSA Counterpart | Agreement |
|-------------------|-----------------|-----------|
| ¬Bel_S(ψ) | P_L1(ψ-worlds) < 0.5 | Both: speaker didn't say stronger |
| Bel_S(¬ψ) | P_L1(¬ψ-worlds) high | Both: implicate negation |
| Horn scale | Utterance alternatives | Both: compare to stronger forms |
| Competence | Speaker optimality (α) | Both: assume informative speaker |
| DE blocking | Reversed informativity | Both: context affects alternatives |

The frameworks differ in mechanism but agree on predictions:
- NeoGricean: Categorical (yes/no implicature)
- RSA: Probabilistic (degree of preference)

RSA-side theorems are sorry'd pending RSAConfig re-implementation.
-/

end Phenomena.ScalarImplicatures.CompareAgreement
