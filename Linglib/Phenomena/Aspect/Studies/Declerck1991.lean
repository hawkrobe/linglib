import Linglib.Core.Time.Reichenbach
import Linglib.Core.Time.Boundedness

/-!
# @cite{declerck-1991}: Bounded / Unbounded Sentences (ch. 3)
@cite{declerck-1991}

Declerck (1991, *A Comprehensive Descriptive Grammar of English*)
distinguishes **bounded** vs **unbounded** sentences: a sentence is
bounded if it represents a situation as reaching a terminal point,
and unbounded otherwise. The contrast is not lexical (it is sentence-
level, not verb-level) and is distinct from the telic/atelic
Aktionsart distinction (compare *Bill ran five miles* — bounded —
with *Bill was running five miles* — unbounded; the same telic VP
participates in both).

This file covers the Bounded/Unbounded substance from Ch. 3 §1.2.
Declerck's broader Ch. 2–4 / Ch. 7 sections on temporal domain,
false tense, conditionals, and the perfect/preterit time-sphere
contrast live in `Phenomena/TenseAspect/Studies/Declerck1991.lean`.

## Empirical anchors (verified vs PDF, Declerck 1991 ch. 3)

- *John read the letter.* (bounded — situation ends when letter ends.)
- *John was reading a letter.* (unbounded — no claim of completion.)
- *John drank whisky.* (unbounded — no terminal point.)
- *John drank five glasses of whisky.* (bounded — five glasses bounds it.)
- *John drank glasses of whisky.* (unbounded — bare-plural object.)
- *Bill ran the 100 metres.* (bounded.)
- *Bill was running the 100 metres.* (unbounded — progressive removes boundedness.)
- *John drew a triangle.* (bounded; cannot infer from progressive.)
- *John drank coffee.* (unbounded; can infer from progressive.)
- *Bill will sleep / will be sleeping in the attic.* (both unbounded.)

## Declerck's discourse-level examples (ch. 2, also relevant)

- (1a) *I left while Bill was sleeping and Mary was having a bath.*
  (Three situations simultaneous within one temporal domain.)
- (1b) *Suddenly the phone rang. Jill stood up from her chair, went
  over to the telephone and picked up the receiver.* (Bounded
  preterites in successive clauses — sequential ordering by domain
  shift, no relative tense forms.)

## Why no `BoundedFrame` struct

A previous formalization in `HeimKratzer1998Data.lean` paired a
Reichenbach frame with a `SituationBoundedness` value in a
`BoundedFrame` struct. The audit flagged this as a thin two-field
wrapper (per memory `feedback_no_thin_bundled_struct`): boundedness
characterizes the predicate-over-interval, not the (S, P, R, E)
frame; pairing them obscures that they are orthogonal pieces of
data. This file uses plain `ReichenbachFrame ℤ` defs whose names
record the boundedness in prose; consumers needing the
boundedness label can use `SituationBoundedness` directly.

## Theorem honesty

The "sequential ordering" / "simultaneity" / "inclusion" claims
Declerck makes about PUTI (Principle of Unmarked Temporal
Interpretation, terminology used in HK1998Data) are **pragmatic
defaults**, not logical entailments. The frames below are
constructed to illustrate the default temporal arrangement of two
situations under each combination, and the per-pair ordering
theorems verify *that* the constructed frames satisfy *that*
arrangement — they do not derive the PUTI default from anything.

-/

namespace Phenomena.Aspect.Studies.Declerck1991

open Core.Time.Reichenbach
open Core.Time (SituationBoundedness)


-- ════════════════════════════════════════════════════════════════
-- § Frames illustrating Declerck's bounded/unbounded sequencing
-- ════════════════════════════════════════════════════════════════

/-! Frame names carry the boundedness label in prose. To pair a frame
    with `SituationBoundedness` for downstream theorems, consumers
    instantiate the pair at use site (e.g. `(arrivedFrame, .bounded)`). -/

/-- "He arrived." — bounded (achievement). Schematic event time -5. -/
def arrivedFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -5
  eventTime := -5

/-- "He sat down." — bounded (achievement). After arriving, by PUTI default. -/
def satDownFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -4
  eventTime := -4

/-- "It was raining." — unbounded (state/activity). -/
def rainingFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- "The wind was blowing." — unbounded (activity), simultaneous with raining
    by PUTI default. -/
def windBlowingFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- "He was reading." — unbounded (activity). Frame for the mixed-inclusion case. -/
def readingFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- "The phone rang." — bounded (achievement), included in reading interval
    by PUTI default. -/
def phoneRangFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3


-- ════════════════════════════════════════════════════════════════
-- § Per-pair ordering verifications
-- ════════════════════════════════════════════════════════════════

/-- Bounded + bounded → sequential: arrival precedes sitting in the
    constructed frames. Illustrative of Declerck's "bounded
    preterites shift domain → temporal order recovered from order of
    mention" point. -/
theorem bounded_sequential :
    arrivedFrame.eventTime < satDownFrame.eventTime := by decide

/-- Unbounded + unbounded → simultaneous: raining and wind-blowing
    share an event time in the constructed frames, illustrating
    Declerck's "three situations simultaneous" example (1a). -/
theorem unbounded_simultaneous :
    rainingFrame.eventTime = windBlowingFrame.eventTime := rfl

/-- Mixed bounded + unbounded → temporal inclusion: phone ringing
    falls within reading in the constructed frames. -/
theorem mixed_inclusion :
    phoneRangFrame.eventTime = readingFrame.eventTime := rfl

end Phenomena.Aspect.Studies.Declerck1991
