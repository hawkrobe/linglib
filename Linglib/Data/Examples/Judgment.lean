/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Judgments

This file defines `Judgment`, the mark a paper puts before an example, the CLDF 1.3
`grammaticalityJudgement` of [forkel-etal-2024]: unmarked, `?`, `??`, `#` or `*`.

## Main definitions

* `Judgment`: the five marks.
* `Judgment.rank`: the position of a mark on the scale, and the `LinearOrder` lifted along it.

## Implementation notes

* The marks are ordered by severity, so `≤` reads "at most as acceptable as" and a study writes
  `.marginal ≤ e.judgment` for an example the paper accepts with at most one question mark. The
  order is a modelling convention rather than a scale from the literature. It ranks `#` above `*`
  because an example marked `#` is well formed but infelicitous; the two constructors keep the
  difference in kind.
* A split mark a paper prints, such as `*/??` for speakers who differ, is several marks for one
  sentence. An example records the first as its `judgment` and each further mark as an
  `alsoJudged` paper feature, and a study reading them all reads a `List Judgment`. Gradient
  ratings are results, recorded in `Data/Experiments/`.

## References

* [forkel-etal-2024]
-/

@[expose] public section

/-- The mark a paper puts before an example. -/
inductive Judgment where
  /-- The paper accepts the example and leaves it unmarked. -/
  | acceptable
  /-- The mark `?` calls the example marginal. -/
  | marginal
  /-- The mark `??` calls the example questionable. -/
  | questionable
  /-- The mark `#` calls the example well formed but infelicitous or semantically anomalous. -/
  | unacceptable
  /-- The mark `*` calls the example ungrammatical. -/
  | ungrammatical
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The position of a mark on the scale, `ungrammatical` lowest. -/
def Judgment.rank : Judgment → Fin 5
  | .ungrammatical => 0
  | .unacceptable => 1
  | .questionable => 2
  | .marginal => 3
  | .acceptable => 4

instance : LinearOrder Judgment := LinearOrder.lift' Judgment.rank (by decide)
