import Linglib.Core.Basic

/-! # Conjunction Distribution: Empirical Data

Theory-neutral empirical judgments about conjunction distribution with
attitude verbs (Bondarenko & Elliott 2026).

The empirical generalization: some attitude verbs distribute over
conjunction in their complement, and some do not.

  "John believes p and q" ↔ "John believes p and John believes q"   ✓
  "John is surprised that p and q" ↛ "John is surprised that p ..."  ✗

## References

- Bondarenko, T. & Elliott, P.D. (2026). Monotonicity via mereology.
  @cite{bondarenko-elliott-2026}
-/

namespace Phenomena.Complementation.Attitudes.ConjunctionDistribution

/-- A single empirical datum about conjunction distribution.
    Records whether a given verb distributes over conjunction in its
    clausal complement. -/
structure ConjDistDatum where
  /-- Citation form of the verb -/
  verb : String
  /-- Does "V(p and q)" entail "V(p) and V(q)"? -/
  distributes : Bool
  /-- Source citation -/
  citation : String
  deriving Repr, BEq

/-- Empirical data from Bondarenko & Elliott (2026) §1.
    Upward-monotone attitudes distribute; non-monotone ones do not. -/
def data : List ConjDistDatum := [
  -- Upward-monotone: distribute
  ⟨"believe",      true,  "B&E 2026, §1"⟩,
  ⟨"know",         true,  "B&E 2026, §1"⟩,
  ⟨"think",        true,  "B&E 2026, §1"⟩,
  ⟨"hope",         true,  "B&E 2026, §1"⟩,
  ⟨"want",         true,  "B&E 2026, §1"⟩,
  ⟨"expect",       true,  "B&E 2026, §1"⟩,
  -- Non-monotone: do not distribute
  ⟨"be surprised", false, "B&E 2026, §1"⟩,
  ⟨"regret",       false, "B&E 2026, §1"⟩,
]

/-- Count of distributing verbs in the dataset. -/
theorem distributing_count : (data.filter (·.distributes)).length = 6 := rfl

/-- Count of non-distributing verbs in the dataset. -/
theorem non_distributing_count : (data.filter (! ·.distributes)).length = 2 := rfl

end Phenomena.Complementation.Attitudes.ConjunctionDistribution
