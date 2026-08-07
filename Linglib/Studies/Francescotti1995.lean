import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Semantics.Focus.Particles

/-!
# Francescotti 1995 — the felicity condition of *even*

[francescotti-1995] defends the Implicature Account of *even* against
[lycan-1991]'s quantifier approach and revises its felicity condition
(§IV, p. 162): an *even*-sentence is felicitous iff its *even*-less
core `S*` is more surprising than most of its true neighbors — pace
[bennett-1982], for whom one true neighbor suffices, and
[karttunen-peters-1979], who require all.

`EvenThreshold` compares the three conditions on the paper's two
counterexamples (§I, pp. 155–156); the characters and dialectic are the
paper's, the surprise levels and extra classmates ours. The paper's
further requirement that neighbors be contextually determined, true,
and part of a more general truth with `S*` is held fixed as background.
The gradient discussion (pp. 163–164) contributes the margin dimension
(`meanExcess`) and the proportion dimension, threshold work done by the
vagueness of "most".
-/

namespace Francescotti1995

open Focus.Particles (evenPresup)

/-! ### The three threshold conditions -/

/-- How many true neighbors `S*` must exceed in surprise for *even* to
be felicitous: at least one ([bennett-1982], §I), all
([karttunen-peters-1979]), or most ([francescotti-1995] §IV, p. 162). -/
inductive EvenThreshold where
  /-- `S*` more surprising than at least one true neighbor. -/
  | existential
  /-- `S*` more surprising than all true neighbors. -/
  | universal
  /-- `S*` more surprising than most (a strict majority of the) true
  neighbors. -/
  | most
  deriving DecidableEq, Repr

variable {α : Type*} (prejacent : α) (alternatives : List α)
  (moreSurprising : α → α → Prop) [DecidableRel moreSurprising]

/-- Number of alternatives the prejacent exceeds in surprise. -/
def countExceeded : Nat :=
  alternatives.countP fun a => decide (moreSurprising prejacent a)

/-- The *even* felicity condition, parameterized by threshold. -/
def evenPresupWith (threshold : EvenThreshold) : Prop :=
  match threshold with
  | .existential => 0 < countExceeded prejacent alternatives moreSurprising
  | .universal => countExceeded prejacent alternatives moreSurprising = alternatives.length
  | .most => alternatives.length < 2 * countExceeded prejacent alternatives moreSurprising

instance (threshold : EvenThreshold) :
    Decidable (evenPresupWith prejacent alternatives moreSurprising threshold) := by
  unfold evenPresupWith; cases threshold <;> infer_instance

/-- The existential threshold is [bennett-1982]'s condition (iii). -/
theorem evenPresupWith_existential_iff :
    evenPresupWith prejacent alternatives moreSurprising .existential ↔
      ∃ a ∈ alternatives, moreSurprising prejacent a := by
  simp [evenPresupWith, countExceeded, List.countP_pos_iff]

/-- The universal threshold is [karttunen-peters-1979]'s "least likely"
condition. -/
theorem evenPresupWith_universal_iff :
    evenPresupWith prejacent alternatives moreSurprising .universal ↔
      ∀ a ∈ alternatives, moreSurprising prejacent a := by
  simp [evenPresupWith, countExceeded, List.countP_eq_length]

/-- The universal threshold coincides with the traditional scalar
presupposition of *even* (`Focus.Particles.evenPresup`). -/
theorem evenPresup_iff_universal {W : Type*}
    (r : Set W → Set W → Prop) [DecidableRel r] (p : Set W) (alts : List (Set W)) :
    evenPresup r p alts ↔ evenPresupWith p alts r .universal :=
  (evenPresupWith_universal_iff ..).symm

/-! ### The two counterexamples (§I, pp. 155–156) -/

/-- A numeric *even* scenario: surprise levels for `S*` and its true
neighbors (higher = more surprising), plus the reported felicity. -/
structure EvenScenario where
  /-- Surprise level of `S*`. -/
  prejacent : Nat
  /-- Surprise levels of the contextually-determined true neighbors. -/
  neighbors : List Nat
  /-- Reported felicity of the *even*-sentence. -/
  felicitous : Bool
  deriving Repr

/-- A threshold matches a scenario when its predicted felicity agrees
with the reported judgment. -/
def Matches (t : EvenThreshold) (s : EvenScenario) : Prop :=
  evenPresupWith s.prejacent s.neighbors (· > ·) t ↔ s.felicitous

instance (t : EvenThreshold) (s : EvenScenario) : Decidable (Matches t s) :=
  inferInstanceAs (Decidable (_ ↔ _))

/-- The passing scenario ((5), p. 155): Albert, one of the best students,
passes unsurprisingly (2), Marie the very best (1), and three weaker
classmates pass surprisingly (5, 7, 8; the roster completion is ours).
"Even Albert passed the exam" is infelicitous. -/
def scenario1 : EvenScenario :=
  { prejacent := 2, neighbors := [1, 5, 7, 8], felicitous := false }

/-- The failing scenario ((1), p. 156): everyone fails; Albert's failure
is very surprising (8), Marie's would be more so (9), the weaker
classmates' are not (3, 2, 1). "Even Albert failed the exam" is
felicitous. -/
def scenario2 : EvenScenario :=
  { prejacent := 8, neighbors := [9, 3, 2, 1], felicitous := true }

/-- The one-neighbor condition wrongly licenses "Even Albert passed the
exam", though it gets the failing scenario right. -/
theorem bennett_too_weak :
    ¬ Matches .existential scenario1 ∧ Matches .existential scenario2 := by decide

/-- The all-neighbors condition wrongly blocks "Even Albert failed the
exam", since Marie is even less likely to fail. -/
theorem karttunen_peters_too_strong :
    Matches .universal scenario1 ∧ ¬ Matches .universal scenario2 := by decide

/-- The most-threshold predicts both judgments correctly. -/
theorem francescotti_correct :
    Matches .most scenario1 ∧ Matches .most scenario2 := by decide

/-! ### Gradient felicity (pp. 163–164)

Felicity varies in degree in two ways: by how much `S*` surpasses its
neighbors in surprise, and by how many it surpasses — the latter is
threshold work done by the vagueness of "most". -/

/-- Mean surprise margin over the neighbors exceeded: the paper's first
gradient dimension, rendered numerically. -/
def meanExcess (s : EvenScenario) : Rat :=
  let exceeded := s.neighbors.filter (· < s.prejacent)
  if exceeded.length = 0 then 0
  else exceeded.foldl (fun (acc : Rat) (n : Nat) => acc + (s.prejacent : Rat) - (n : Rat)) 0 /
    exceeded.length

/-- Andre is by far the tallest ((21), pp. 163–164): "Even Andre cannot
reach the top shelf" is very felicitous. -/
def scenarioAndreFar : EvenScenario :=
  { prejacent := 9, neighbors := [3, 4, 5, 2, 3], felicitous := true }

/-- Andre is tallest by only a small margin (p. 163): the sentence is
still felicitous, but less so. -/
def scenarioAndreBarely : EvenScenario :=
  { prejacent := 6, neighbors := [5, 5, 4, 5, 5], felicitous := true }

/-- Both Andre scenarios exceed every neighbor, but the by-far scenario
does so by a larger mean margin. -/
theorem andre_margin :
    meanExcess scenarioAndreBarely < meanExcess scenarioAndreFar := by
  norm_num [meanExcess, scenarioAndreBarely, scenarioAndreFar]

/-- Andre is barely in the taller half of a half-tall, half-short
reference class (p. 164): not taller than the majority, so the sentence
is infelicitous. -/
def scenarioAndreHalf : EvenScenario :=
  { prejacent := 8, neighbors := [9, 9, 1, 1], felicitous := false }

/-- Exceeding exactly half the neighbors is not "most": the threshold
correctly predicts infelicity. -/
theorem andre_half_infelicitous : Matches .most scenarioAndreHalf := by decide

end Francescotti1995
