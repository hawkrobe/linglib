import Linglib.Theories.Phonology.LexicalFrequency.Defs
import Linglib.Core.Constraint.OT.Basic

/-!
# Indexed Constraints
@cite{pater-2010}

The conservative frequency-conditioning theory: frequency does not enter
the grammar at all; instead, lexically-indexed constraints partition the
lexicon into fixed sublexica (typically two: a high-frequency or
"core" stratum and a low-frequency or "peripheral" stratum) with their
own constraint rankings.

The interface to `LexicalFrequency.HasTokenFreq` is *one bit per item*:
`isCore` thresholds log-frequency at a fixed cutoff. Within a stratum,
no further frequency dependence — the strongest contrast with
`ScaledWeights`, where every log-frequency unit shifts the weight
linearly.

## Empirical signature

Indexed-constraint theories predict **discontinuous** frequency effects:
two distinct distributions, with no in-stratum gradience. Where the
empirical distribution is gradient and continuous in log-frequency
(e.g., the Breiss-Katsuda-Kawahara compounds in
`Phenomena/Phonology/Studies/BreissKatsudaKawahara2026.lean`), this
theory under-fits relative to `ScaledWeights` /
`RepresentationStrength`.
-/

namespace Phonology.LexicalFrequency.Indexed

open Phonology.LexicalFrequency
open Core.Constraint.OT (NamedConstraint ConstraintFamily)

-- ============================================================================
-- § 1: Stratification
-- ============================================================================

/-- A two-stratum lexical partition: an item is "core" iff its
    log-frequency exceeds `cutoff`. Discrete by construction. -/
def isCore {α : Type} [HasTokenFreq α] (cutoff : ℝ) (a : α) : Prop :=
  tokenLogFreq a ≥ cutoff

/-- Classical decidability — `Real`'s order is decidable only via
    `Classical.dec`, so all consumers downstream become `noncomputable`.
    Acceptable for theory specifications; concrete fitting routines
    work over rationals or use a thresholded comparison directly. -/
noncomputable instance {α : Type} [HasTokenFreq α] (cutoff : ℝ) :
    DecidablePred (isCore (α := α) cutoff) := fun _ => Classical.dec _

-- ============================================================================
-- § 2: Constraint indexing
-- ============================================================================

/-- An *indexed constraint* fires only on items in a particular stratum.
    `mkCoreOnly cutoff base` returns a constraint that evaluates to
    `base.eval c` when `c` is in the core stratum, `0` otherwise.

    This is the formalization of @cite{pater-2010}'s lexically-indexed
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

end Phonology.LexicalFrequency.Indexed
