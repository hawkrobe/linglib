import Mathlib.Order.RelClasses
import Mathlib.Order.Defs.Unbundled
import Linglib.Core.Probability.Finite
import Linglib.Core.Scales.HasMeasure
import Linglib.Core.Scales.HasComparison
import Linglib.Core.Scales.LawfulComparison
import Linglib.Core.Scales.HasPositiveForm

/-!
# Probabilistic Gradability — Lassiter–Goodman threshold-prior account

@cite{lassiter-goodman-2017}

A gradable adjective is parameterized by (i) a sharp measure function
`measure : α → δ` on a linearly-ordered codomain, and (ii) a probability
distribution `thresholdPrior : PMF δ` over candidate thresholds. The
sharpness of the measure is preserved at the comparative layer (Kim is
taller than Lee iff `measure Kim > measure Lee` — definitionally
identical to the Kennedy framework). The probabilistic apparatus enters
only at the **positive form**: the smooth-threshold posterior probability
that an entity exceeds a threshold sampled from the prior.

## Where the framework actually disagrees with Kennedy

L&G inherit Kennedy's transitive linear-comparative semantics by
construction (`HasComparison.comparativeGreater a b := measure a >
measure b`). The cross-framework disagreement therefore lives at
`HasPositiveForm`, NOT at `HasComparison`:

- Kennedy: `isPositive θ a := measure a > θ` (sharp threshold)
- L&G: `isPositive prior a := P(threshold < measure a) > 1/2`
  (posterior mass below `measure a` — the "more likely than not"
  threshold-relative probability).

Phase E's `Disagreements.lean` will state this contrast as
`lassiterGoodman_predicts_smooth_threshold_unlike_kennedy`. This file
provides the substrate the disagreement theorem refers to.

## Bridges to existing infrastructure

* `Theories/Semantics/Probabilistic/SDS/ThresholdSemantics.lean` already
  axiomatizes the abstract `ThresholdPredicate` shape that L&G, Tessler-
  Goodman generics, and Morzycki gradable nouns share. The class here
  is the L&G specialization typed against the global `HasMeasure`/
  `HasComparison`/`HasPositiveForm` substrate; the SDS file remains the
  cross-domain comparison layer.
* `Phenomena/Gradability/Studies/LassiterGoodman2017PMF.lean` houses the
  L&G empirical-replication infrastructure (joint world-threshold
  posterior, sorites bounds, antonym symmetry). That file consumes
  `PMF.posterior` directly — independent of the typeclass machinery
  here, which is for cross-framework reasoning rather than within-paper
  empirical reconstruction.

## Scope (master plan v4 conservative cut)

This file lands `LassiterGoodmanAdjective` only. The companion
intransitive-comparison framework `MajorityComparison` (Tversky 1969 /
Fishburn 1991) is queued for a follow-up sub-phase.
-/

namespace Semantics.Gradability.Probabilistic

open Core.Scale (HasMeasure HasComparison LawfulComparison HasPositiveForm)
open scoped ENNReal

/-- A Lassiter–Goodman gradable adjective: a sharp measure into a
    discrete codomain plus a prior over candidate thresholds.

    `α` is the entity type, `δ` is the codomain (typically a `Degree max`
    or `Fin n` for finite scales). The `LinearOrder δ` ensures the
    underlying comparative is transitive; `Fintype δ` is required for
    `PMF` to support exhaustive computation of the threshold posterior.

    The measure function is sharp (each `α` maps to a single `δ`) — the
    probabilistic apparatus enters only via `thresholdPrior`.

    `δ` is an `outParam` so that downstream typeclass instances
    (`HasMeasure`, `HasComparison`, `LawfulComparison`, `HasPositiveForm`)
    can be synthesized from `[LassiterGoodmanAdjective α δ]` alone. The
    multi-dim case (one `α` measured along several dimensions) is handled
    via newtype wrappers per master-plan-v4 — same convention mathlib
    uses for `Additive`/`Multiplicative`. -/
class LassiterGoodmanAdjective (α : Type) (δ : outParam Type)
    [LinearOrder δ] [Fintype δ] where
  /-- The sharp measure function (e.g., height of an entity). -/
  measure : α → δ
  /-- The prior distribution over candidate thresholds. -/
  thresholdPrior : PMF δ

variable {α δ : Type} [LinearOrder δ] [Fintype δ]

/-- Lassiter-Goodman provides a `HasMeasure` instance: the sharp measure
    function is exactly the `HasMeasure.degree` field. Wired here rather
    than via a global `HasMeasure` instance because the framework's
    multi-dim story (an entity simultaneously measured by height and
    weight) is mediated through distinct `LassiterGoodmanAdjective`
    values in different universes. Master-plan-v4 do-no-harm constraint
    on `outParam`. -/
instance lgHasMeasure [l : LassiterGoodmanAdjective α δ] : HasMeasure α δ where
  degree := l.measure

/-- The L&G comparative is sharp: `a` is taller than `b` iff
    `measure a > measure b` in the underlying linear order. Definitionally
    identical to the Kennedy comparative — the cross-framework
    disagreement is at the positive form, not here. -/
instance lgHasComparison [l : LassiterGoodmanAdjective α δ] : HasComparison α where
  comparativeGreater a b := l.measure a > l.measure b

/-- The L&G comparative inherits its lawfulness from the linear order on
    the measurement codomain. Pulled back through `measure`, irreflexivity
    and transitivity of `<` on `δ` give the corresponding properties on
    `α`. -/
instance lgLawfulComparison [LassiterGoodmanAdjective α δ] : LawfulComparison α where
  isStrictOrder :=
    { irrefl := fun _ => lt_irrefl _
      trans := fun _ _ _ hab hbc => lt_trans hbc hab }

/-- Lassiter-Goodman positive form: an entity `a` is "tall" relative to
    a threshold prior iff the prior mass strictly below `measure a`
    exceeds 1/2 — the smooth-threshold "more likely than not"
    interpretation.

    `Source = PMF δ` distinguishes L&G from Kennedy's `Source = δ` (sharp
    threshold) and Klein's `Source = Set α` (comparison class). The
    different `Source` types are the type-level signature of the
    framework disagreement at the positive form. -/
instance lgHasPositiveForm [l : LassiterGoodmanAdjective α δ] :
    HasPositiveForm α (PMF δ) where
  isPositive prior a := PMF.massBelow prior (l.measure a) > (1/2 : ℝ≥0∞)

/-- The L&G threshold posterior: probability that the threshold lies
    strictly below the entity's measured value, i.e. the posterior
    probability that `a` falls in the predicate's positive extension.
    Equivalent to `PMF.massBelow l.thresholdPrior (l.measure a)`. -/
noncomputable def thresholdPosterior [l : LassiterGoodmanAdjective α δ]
    (a : α) : ℝ≥0∞ :=
  PMF.massBelow l.thresholdPrior (l.measure a)

-- Synthesis smoke tests (master-plan E.2 verification pattern).
section InferInstance
variable [LassiterGoodmanAdjective α δ]
example : HasMeasure α δ := inferInstance
example : HasComparison α := inferInstance
example : LawfulComparison α := inferInstance
example : HasPositiveForm α (PMF δ) := inferInstance
end InferInstance

end Semantics.Gradability.Probabilistic
