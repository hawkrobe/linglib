import Linglib.Pragmatics.SocialMeaning.IndexicalField
import Mathlib.Tactic.NormNum

/-!
# Labov (2012): Dialect Diversity in America

This file formalizes the one quantitative observation of [labov-2012] that the library
consumes: the President's rate of the *-in'* variant of (ING) on three occasions of
increasing formality, a Father's Day barbecue, the interview that followed it, and a scripted
convention address, the book's illustration of the style shifting shared across the speech
community, its hidden consensus on the variable. `obama_ING` records the three rates and
`obama_ING_monotone` their strict decrease with formality, the intra-speaker counterpart of the
class-and-style stratification of [labov-2006]; `Studies/Burnett2019.lean` derives the
direction of this shift from a speaker's social-meaning game.

## Implementation notes

The three contexts are the book's own occasions rather than the interview styles of
[labov-2006], and the observation is kept as a single record. The percentages are the book's;
the figure and page on which they appear were not checked against a copy of the book.

## References

* [labov-2012]
* [labov-2006]
-/

namespace Labov2012

/-- One speaker's rate of a variant on three occasions of increasing formality. -/
structure StyleShiftObs where
  /-- The casual occasion. -/
  casual : ℚ
  /-- The careful occasion. -/
  careful : ℚ
  /-- The formal occasion. -/
  formal : ℚ

-- UNVERIFIED: the book's Chapter 2 figure of the President's (ING) rates, cited here from
-- the earlier version of this file; the values agree with published summaries of the book.
/-- The President's rate of *-in'*: 72% chatting at a barbecue, 33% answering questions at the
ceremony that followed, 3% in the scripted acceptance speech. -/
def obama_ING : StyleShiftObs where
  casual := 72/100
  careful := 33/100
  formal := 3/100

/-- The rate of *-in'* falls strictly with the formality of the occasion. -/
theorem obama_ING_monotone :
    obama_ING.casual > obama_ING.careful ∧ obama_ING.careful > obama_ING.formal := by
  norm_num [obama_ING]

end Labov2012
