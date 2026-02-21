import Linglib.Core.Scale
import Linglib.Core.EpistemicScale
import Linglib.Theories.Semantics.Modality.Kratzer
import Linglib.Theories.Semantics.Modality.ProbabilityOrdering
import Linglib.Theories.Pragmatics.RSA.Core.Config

/-!
# Kratzer–Epistemic–RSA Bridge

This file traces the dependency chain from Kratzer's ordering source
semantics down to RSA's `worldPrior`, via Holliday & Icard's (2013)
epistemic likelihood logics:

```
Kratzer ordering source  A : List (BProp World)
    ↓  atLeastAsGoodAs (subset inclusion on satisfied propositions)
World preorder  ge_w : World → World → Prop
    ↓  halpernLift (Lewis's l-lifting)
EpistemicSystemW
    ↓  + totality, transitivity, additivity
EpistemicSystemFA
    ↓  theorem8a (|World4| = 4 < 5, so FA = FP∞)
FinAddMeasure
    ↓  mu {w} → worldPrior
RSAConfig.worldPrior
```

§1 and §2 are definitions (no sorry). §3–§4 are conjectures (sorry)
that state what additional conditions are needed to traverse the full
pipeline.

## References

- Kratzer, A. (1981). The Notional Category of Modality.
- Kratzer, A. (2012). Modals and Conditionals. OUP. Ch. 2 §2.4.
- Holliday, W. & Icard, T. (2013). Measure Semantics and Qualitative
  Semantics for Epistemic Modals. SALT 23.
- Kraft, C., Pratt, J. & Seidenberg, A. (1959). Intuitive Probability
  on Finite Sets. Annals of Mathematical Statistics 30.
-/

namespace Comparisons.KratzerEpistemicRSA

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional
open Core.Scale

-- ══════════════════════════════════════════════════════════════════════
-- §1. Kratzer ordering → EpistemicSystemW (definition, no sorry)
-- ══════════════════════════════════════════════════════════════════════

/-- Convert Kratzer's Bool-valued `atLeastAsGoodAs` to a Prop-valued
    world preorder, suitable for `halpernLift`. -/
def kratzerWorldGe (A : List (BProp World)) (w z : World) : Prop :=
  atLeastAsGoodAs A w z = true

/-- Kratzer's ordering is reflexive (Prop version). -/
theorem kratzerWorldGe_refl (A : List (BProp World)) (w : World) :
    kratzerWorldGe A w w :=
  ordering_reflexive A w

/-- Applying Lewis's l-lifting to Kratzer's world ordering yields
    EpistemicSystemW. This connects Kratzer modal semantics to
    Holliday & Icard's weakest epistemic likelihood logic. -/
def kratzerToSystemW (A : List (BProp World)) : EpistemicSystemW World :=
  halpernSystemW (kratzerWorldGe A) (kratzerWorldGe_refl A)

-- ══════════════════════════════════════════════════════════════════════
-- §3. The Kratzer–RSA pipeline (conjectures, sorry)
-- ══════════════════════════════════════════════════════════════════════

/-- **Conjecture**: For `World` (= `World4`, 4 elements), if a Kratzer
    ordering source induces an l-lifted system that satisfies the FA
    axioms (totality, transitivity, qualitative additivity), then by
    Kraft–Pratt–Seidenberg (Theorem 8a, since |World4| = 4 < 5), the
    system is representable by a finitely additive measure, yielding
    an RSA world prior.

    This states the full Kratzer → RSA pipeline for the concrete
    4-world type used throughout linglib's modal and RSA formalizations.

    The key gap is that not every Kratzer ordering source yields an
    l-lifted system satisfying FA — the hypothesis `hFA` captures the
    additional conditions needed (totality, transitivity, additivity
    of the lifted relation). -/
theorem kratzer_to_rsa_prior
    (A : List (BProp World))
    (hFA : ∀ (A' B' : Set World),
      (kratzerToSystemW A).ge A' B' ∨ (kratzerToSystemW A).ge B' A')
    (hTrans : ∀ (A' B' C' : Set World),
      (kratzerToSystemW A).ge A' B' → (kratzerToSystemW A).ge B' C' →
      (kratzerToSystemW A).ge A' C')
    (hAdd : EpistemicAxiom.A (kratzerToSystemW A).ge) :
    ∃ (prior : World → ℚ), ∀ w, 0 ≤ prior w :=
  sorry -- Combine: kratzerToSystemW → EpistemicSystemFA → theorem8a → toWorldPrior

-- ══════════════════════════════════════════════════════════════════════
-- §4. ProbabilityOrdering round-trip (conjecture, sorry)
-- ══════════════════════════════════════════════════════════════════════

open Semantics.Modality.ProbabilityOrdering in
/-- **Conjecture**: The probability-ordering round-trip is consistent.

    Starting from a probability assignment P:
    1. `probToOrdering P` yields a Kratzer ordering source
    2. `atLeastAsGoodAs` gives a world preorder
    3. `halpernLift` gives an epistemic system
    4. If FA holds, representation theorem gives measure μ
    5. `toWorldPrior` extracts μ({w})

    The round-trip prior `μ({w})` should be consistent with the
    original `P(w)` — not necessarily equal (since the l-lifting and
    representation may lose information), but preserving the same
    ordering: P(w) ≥ P(z) ↔ μ({w}) ≥ μ({z}).

    This conjecture makes precise what "consistent" means: the
    probability ordering is preserved through the pipeline.

    Note: `probToOrdering` is world-independent (`probToOrdering_const`),
    so the choice of evaluation world `w₀` is arbitrary. -/
theorem prob_ordering_roundtrip
    (P : ProbAssignment)
    (w₀ : World)
    (hPos : ∀ w, 0 < P w)
    (hFA : ∀ (A B : Set World),
      (kratzerToSystemW ((probToOrdering P) w₀)).ge A B ∨
      (kratzerToSystemW ((probToOrdering P) w₀)).ge B A) :
    ∃ (prior : World → ℚ),
      (∀ w, 0 ≤ prior w) ∧
      (∀ w z : World, P w ≥ P z → prior w ≥ prior z) :=
  sorry -- Requires: l-lift preserves probability ranking; representation theorem

end Comparisons.KratzerEpistemicRSA
