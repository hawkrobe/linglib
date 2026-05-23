import Linglib.Core.Scales.Extent
import Linglib.Semantics.Degree.Comparative

/-!
# LITTLE: Degree Negation

The LITTLE operator @cite{heim-2006} @cite{buring-2007} as degree-predicate
complementation: `short = LITTLE tall`, `less = LITTLE -er`,
`fewer = LITTLE many`. Semantically, `⟦LITTLE⟧(P)(d) = ¬P(d)`. On extents,
LITTLE maps `posExt` to `negExt`; on intervals (see `Intervals.lean §6`), it
inverts the measured region.

@cite{buring-2007} uses LITTLE to analyse cross-polar nomalies:
"the ladder was shorter than the house was high" works because
`MORE [LITTLE long] -er` can be reinterpreted as `LITTLE-er long` (the
"more-to-less metamorphosis").

## Main definitions

* `littlePred` — degree-predicate complement, `⟦LITTLE⟧ = λP.λd. ¬ P d`

## Main theorems

* `little_posExt_eq_negExt` — the formal content of "short = LITTLE tall"
* `little_involution` — LITTLE is its own inverse
* `little_reverses_comparison` — LITTLE flips comparison direction
-/

namespace Semantics.Degree.Little

open Semantics.Degree.Comparative (comparativeSem ScaleDirection taller_shorter_antonymy)

/-- LITTLE on degree predicates: complementation. -/
def littlePred {D : Type*} (P : D → Prop) : D → Prop :=
  fun d => ¬ P d

/-- LITTLE maps the positive extent to the negative extent:
`LITTLE({d | d ≤ μ(x)}) = {d | μ(x) < d}`. The formal content of
"short = LITTLE tall" — the degree predicate for 'short' is the
complement of the degree predicate for 'tall', exactly the relation
between `posExt` and `negExt` from @cite{kennedy-1999}. -/
theorem little_posExt_eq_negExt {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (x : Entity) (d : D) :
    littlePred (· ∈ Core.Scale.posExt μ x) d ↔ d ∈ Core.Scale.negExt μ x := by
  simp [littlePred, Core.Scale.posExt, Core.Scale.negExt]

/-- LITTLE is an involution: double degree negation cancels. -/
theorem little_involution {D : Type*} (P : D → Prop) (d : D) :
    littlePred (littlePred P) d ↔ P d := by
  simp [littlePred]

/-- LITTLE reverses the comparison direction: "A is LITTLE-er Adj than B"
↔ "B is Adj-er than A". Delegates to `taller_shorter_antonymy`. -/
theorem little_reverses_comparison {Entity α : Type*} [LinearOrder α]
    (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔ comparativeSem μ b a .negative :=
  taller_shorter_antonymy μ a b

end Semantics.Degree.Little
