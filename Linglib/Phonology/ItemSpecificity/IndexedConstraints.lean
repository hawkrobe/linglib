import Linglib.Phonology.ItemSpecificity.Defs
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.OptimalityTheory.Basic

/-!
# Indexed Constraints
[pater-2010]

The conservative frequency-conditioning theory: frequency does not enter
the grammar at all; instead, lexically-indexed constraints partition the
lexicon into fixed sublexica (typically two: a high-frequency or
"core" stratum and a low-frequency or "peripheral" stratum) with their
own constraint rankings.

The interface to `ItemSpecificity.HasTokenFreq` is *one bit per item*:
`isCore` thresholds log-frequency at a fixed cutoff. Within a stratum,
no further frequency dependence — the strongest contrast with
`ScaledWeights`, where every log-frequency unit shifts the weight
linearly.

## Empirical signature

Indexed-constraint theories predict **discontinuous** frequency effects:
two distinct distributions, with no in-stratum gradience. Where the
empirical distribution is gradient and continuous in log-frequency
(e.g., the Breiss-Katsuda-Kawahara compounds in
`Studies/BreissKatsudaKawahara2026.lean`), this
theory under-fits relative to `ScaledWeights` /
`RepresentationStrength`.
-/

namespace Constraints.ItemSpecificity.Indexed

open Constraints.ItemSpecificity
open Constraints OptimalityTheory

-- ============================================================================
-- § 1: Stratification
-- ============================================================================

/-- A two-stratum lexical partition: an item is "core" iff its
    log-frequency reaches `cutoff`. Discrete by construction.

    Implemented as an alias of `ItemSpecificity.isAboveThreshold` so the
    shared decidability instance carries through; the `abbrev` form
    means `unfold isCore` reduces directly to the inequality. -/
abbrev isCore {α : Type} [HasTokenFreq α] (cutoff : ℝ) (a : α) : Prop :=
  isAboveThreshold cutoff a

-- ============================================================================
-- § 2: Constraint indexing
-- ============================================================================

/-- An *indexed constraint* fires only on items in a particular stratum.
    `mkCoreOnly cutoff base` returns a constraint that evaluates to
    `base.eval c` when `c` is in the core stratum, `0` otherwise.

    This is the formalization of [pater-2010]'s lexically-indexed
    markedness/faithfulness: the same structural penalty applies, but
    only to a sublexicon. -/
noncomputable def mkCoreOnly {α : Type} [HasTokenFreq α] (cutoff : ℝ)
    (base : NamedConstraint α) : NamedConstraint α :=
  { name := base.name ++ "[core]"
    family := base.family
    eval := fun c => if isCore cutoff c then base.eval c else 0 }

/-- The peripheral counterpart: fires on items below the cutoff. -/
noncomputable def mkPeripheralOnly {α : Type} [HasTokenFreq α] (cutoff : ℝ)
    (base : NamedConstraint α) : NamedConstraint α :=
  { name := base.name ++ "[periph]"
    family := base.family
    eval := fun c => if isCore cutoff c then 0 else base.eval c }

-- ============================================================================
-- § 3: Discontinuity (the empirical signature of the theory)
-- ============================================================================

/-- Indexed constraints produce **the same** violation count for any two
    items on the same side of the cutoff, regardless of their
    log-frequency. This is the discontinuity claim that distinguishes
    indexed-constraint theories from scaled-weights theories. -/
theorem mkCoreOnly_constant_within_stratum
    {α : Type} [HasTokenFreq α] (cutoff : ℝ) (base : NamedConstraint α)
    (c1 c2 : α) (h1 : isCore cutoff c1) (h2 : isCore cutoff c2)
    (hbase : base.eval c1 = base.eval c2) :
    (mkCoreOnly cutoff base).eval c1 = (mkCoreOnly cutoff base).eval c2 := by
  simp [mkCoreOnly, h1, h2, hbase]

end Constraints.ItemSpecificity.Indexed
