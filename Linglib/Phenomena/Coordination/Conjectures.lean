import Linglib.Phenomena.Coordination.Typology

/-!
# Coordination Conjectures

Open problems in coordination typology stated as `sorry`-marked theorems.
These are genuinely open questions where no existing theory derives the
prediction from first principles.

Unlike proved theorems in `Typology.lean`, these mark the frontier of
what M&S decomposition + processing theory should explain.
-/

namespace Phenomena.Coordination.Conjectures

open Phenomena.Coordination.Typology
open Phenomena.Coordination.Studies.BillEtAl2025

/--
**Open problem: predict the Bill et al. (2025) acquisition asymmetry.**

No existing account predicts the full cross-linguistic pattern:
- M&S (2016) + Transparency Principle → predicts J-MU easiest. Wrong for Georgian.
- Szabolcsi (2015) → alternative quantifier-particle analysis. Doesn't predict it.
- Haslinger et al. (2019) → plural/distributive analysis. Doesn't predict it.

A complete theory should derive: when MU is morphologically bound, J-MU
incurs extra acquisition cost (segmentation difficulty outweighs transparency
benefit). When MU is free, no such cost arises, yielding the Hungarian null.

This requires a processing/acquisition model where morphological complexity
(boundness) and syntactic transparency (overt form-meaning mapping) are
competing factors. The `sorry` marks this as the central open gap in the
coordination typology — the M&S categories describe the space but don't yet
predict which regions are hard to acquire.

[sorry: requires a cost metric that weights segmentation difficulty against
transparency benefit; no existing theory provides this] -/
theorem predict_acquisition_asymmetry
    (sys : ConjunctionSystem)
    (h_all : hasAllThreeStrategies sys = true)
    (h_bound : sys.muBoundness = some .bound) :
    -- When MU is bound and all three strategies exist,
    -- there should exist a cost metric under which J-MU is harder than J-only.
    ∃ (costMetric : ConjunctionStrategy → ConjunctionSystem → Nat),
      costMetric .jMu sys > costMetric .jOnly sys := by
  sorry

end Phenomena.Coordination.Conjectures
