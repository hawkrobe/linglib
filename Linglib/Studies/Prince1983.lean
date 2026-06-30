import Linglib.Phonology.Prosody.Word

/-!
# Relating to the grid: the End Rule ([prince-1983])

[prince-1983]'s *Relating to the Grid* reads a metrical **grid** off a prosodic tree by the
Relative Prominence Projection Rule ([liberman-prince-1977]) — formalised as
`Prosody.gridColumns` — and observes that a **uniform** metrical tree (every constituent
strong on the same side) projects to a grid whose single strongest column sits at one **end**:
the *End Rule*.

This file stress-tests the grid projection against that prediction. A uniformly right-strong
(iambic) word and a uniformly left-strong (trochaic) word project, by `decide`, to staircase
column profiles whose strict maximum is the rightmost (resp. leftmost) syllable — the End Rule,
recovered through `Prosody.gridColumns`. It also leans on the projection's information loss:
the grid records *where* the prominence peak is, not the bracketing that produced it
(`Prosody.toGrid_not_injective`).
-/

namespace Prince1983

open Prosody Features.Prosody RootedTree

/-! ### Uniform metrical words

Every foot is binary; the head sits consistently on the right (iambic) or the left (trochaic),
and the head foot likewise — so the head-projection chain runs to one edge of the word. -/

/-- A head (strong) syllable. -/
def σh : Tree := .node { level := .σ, isHead := true } []
/-- A weak syllable. -/
def σw : Tree := .node { level := .σ, isHead := false } []
/-- A head (strong) foot over `cs`. -/
def ftH (cs : List Tree) : Tree := .node { level := .f, isHead := true } cs
/-- A weak foot over `cs`. -/
def ftW (cs : List Tree) : Tree := .node { level := .f, isHead := false } cs
/-- A prosodic word over `cs`. -/
def om (cs : List Tree) : Tree := .node { level := .ω } cs

/-- A uniformly **right-strong** word: the head foot is rightmost and every foot is iambic
    (head syllable rightmost), so prominence climbs toward the right edge. -/
def rightStrong : Tree := om [ftW [σw, σh], ftH [σw, σh]]

/-- A uniformly **left-strong** word: the head foot is leftmost and every foot is trochaic
    (head syllable leftmost), so prominence climbs toward the left edge. -/
def leftStrong : Tree := om [ftH [σh, σw], ftW [σh, σw]]

/-! ### The End Rule -/

/-- **End Rule, right** ([prince-1983]): the rightmost grid column strictly dominates every
    other — the prominence peak is at the right edge. -/
def EndRuleRight (t : Tree) : Prop :=
  ∀ h ∈ (gridColumns t).dropLast, h < (gridColumns t).getLast?.getD 0
instance (t : Tree) : Decidable (EndRuleRight t) := by unfold EndRuleRight; infer_instance

/-- **End Rule, left** ([prince-1983]): the leftmost grid column strictly dominates every
    other — the prominence peak is at the left edge. -/
def EndRuleLeft (t : Tree) : Prop :=
  ∀ h ∈ (gridColumns t).tail, h < (gridColumns t).headD 0
instance (t : Tree) : Decidable (EndRuleLeft t) := by unfold EndRuleLeft; infer_instance

/-! ### The RPPR projects uniform trees to End-Rule grids -/

/-- The right-strong word projects to a staircase peaking at the right edge. -/
theorem gridColumns_rightStrong : gridColumns rightStrong = [1, 2, 1, 3] := by decide

/-- The left-strong word projects to a staircase peaking at the left edge. -/
theorem gridColumns_leftStrong : gridColumns leftStrong = [3, 1, 2, 1] := by decide

/-- **End Rule (right):** a uniformly right-strong word is strongest at its right edge. -/
theorem endRuleRight_rightStrong : EndRuleRight rightStrong := by decide

/-- **End Rule (left):** a uniformly left-strong word is strongest at its left edge. -/
theorem endRuleLeft_leftStrong : EndRuleLeft leftStrong := by decide

end Prince1983
