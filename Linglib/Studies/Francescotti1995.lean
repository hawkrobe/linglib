import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Semantics.Focus.Particles

/-!
# Francescotti 1995 — *Even*: the implicature account revised
[francescotti-1995]

Francescotti defends the Implicature Account of *even* against
[lycan-1991]'s quantifier approach (§II–III) and revises its felicity
condition (§IV, p. 162): an *even*-sentence `S` is felicitous iff its
*even*-less core `S*` is more surprising than MOST of its true
neighbors — pace [bennett-1982], for whom one true neighbor suffices
(§I), and [karttunen-peters-1979], who require all ("Bill is the least
likely to like Mary", p. 12). Conclusion (§V): (a) *even* contributes
conventional implicature, not truth conditions; (b) it is epistemic
(unexpectedness); (c) scalar; (d) the most-threshold condition.

`EvenThreshold` compares the three conditions on the paper's two
counterexamples (§I, pp. 155–156), encoded as numeric surprise
scenarios: the characters and dialectic are the paper's, the surprise
levels and the completion of the classmate roster are ours. The paper's
clause (i) — neighbors are contextually determined, true, and share a
more general truth with `S*` — is held fixed as background; only the
surprise-comparison clause (ii) varies. The gradient discussion
(pp. 163–164) is formalized as the two dimensions the paper names:
margin of surprise (`meanExcess`, the Andre contrast) and proportion of
neighbors exceeded (threshold work done by the vagueness of "most").
-/

namespace Francescotti1995

open Focus.Particles (TraditionalEven)

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
presupposition of *even* (`Focus.Particles.TraditionalEven`). -/
theorem traditionalEven_presup_iff_universal {W : Type*}
    (te : TraditionalEven (World := W)) [DecidableRel te.likelihood] :
    te.presupposition ↔
      evenPresupWith te.prejacent te.alternatives te.likelihood .universal :=
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

/-- "Even Albert passed the exam" (paper (5), p. 155): Albert is "one of
the best chemistry students in the history of Madison High", Marie the
very best, so his passing (2) exceeds only her passing (1) in surprise —
infelicitous. The three classmates whose passing is genuinely surprising
(5, 7, 8) complete the true-neighbor roster; the completion is ours. -/
def scenario1 : EvenScenario :=
  { prejacent := 2, neighbors := [1, 5, 7, 8], felicitous := false }

/-- "Even Albert failed the exam" (paper (1), p. 156): "everyone in the
class failed the chemistry exam, and this includes Albert, which is very
surprising" — felicitous even though Marie (9) is "less likely than
Albert to fail" (8). The weaker classmates fail unsurprisingly (3, 2, 1). -/
def scenario2 : EvenScenario :=
  { prejacent := 8, neighbors := [9, 3, 2, 1], felicitous := true }

/-- Bennett's one-neighbor condition is too weak (p. 155): it wrongly
licenses "Even Albert passed" via the Marie neighbor, though it handles
the failing case. -/
theorem bennett_too_weak :
    ¬ Matches .existential scenario1 ∧ Matches .existential scenario2 := by decide

/-- The all-neighbors condition is "much too strong" (p. 156): Marie's
being even less likely to fail wrongly blocks "Even Albert failed". -/
theorem kp_too_strong :
    Matches .universal scenario1 ∧ ¬ Matches .universal scenario2 := by decide

/-- Francescotti's most-threshold (§IV, p. 162) matches both judgments. -/
theorem francescotti_correct :
    Matches .most scenario1 ∧ Matches .most scenario2 := by decide

/-! ### Gradient felicity (pp. 163–164)

"'Even'-sentences vary in degrees of felicity in at least two different
ways": by how much `S*` surpasses its neighbors in surprise, and by how
many it surpasses. The margin dimension is a genuine degree
(`meanExcess`); the proportion dimension is threshold work "nicely
captured by the vagueness of the word 'most'". -/

/-- Mean surprise margin over the neighbors exceeded — our numeric
rendering of the paper's "surpasses its neighbors in surprise to a
greater degree". -/
def meanExcess (s : EvenScenario) : Rat :=
  let exceeded := s.neighbors.filter (· < s.prejacent)
  if exceeded.length = 0 then 0
  else exceeded.foldl (fun (acc : Rat) (n : Nat) => acc + (s.prejacent : Rat) - (n : Rat)) 0 /
    exceeded.length

/-- "Andre is by far the tallest person" (paper (21), pp. 163–164):
"Even Andre cannot reach the top shelf" is very felicitous. -/
def scenarioAndreFar : EvenScenario :=
  { prejacent := 9, neighbors := [3, 4, 5, 2, 3], felicitous := true }

/-- "If Andre were the tallest person, but only by a small margin ...
it would not be as felicitous" (p. 163). -/
def scenarioAndreBarely : EvenScenario :=
  { prejacent := 6, neighbors := [5, 5, 4, 5, 5], felicitous := true }

/-- The margin dimension: both Andre scenarios exceed all five
neighbors, but the by-far scenario does so by a larger mean margin. -/
theorem andre_margin :
    meanExcess scenarioAndreBarely < meanExcess scenarioAndreFar := by
  norm_num [meanExcess, scenarioAndreBarely, scenarioAndreFar]

/-- The proportion dimension (p. 164): half the reference class is over
6′5″, half under 5′, and Andre is in the taller half "but just barely".
He is "not taller than the majority of people in the group" — exceeding
exactly half fails the strict-majority reading of "most" — so (21) is
infelicitous despite Andre being significantly taller than average. -/
def scenarioAndreHalf : EvenScenario :=
  { prejacent := 8, neighbors := [9, 9, 1, 1], felicitous := false }

/-- Exactly-half exceedance is not "most": the threshold correctly
predicts infelicity for the half-and-half reference class. -/
theorem andre_half_infelicitous : Matches .most scenarioAndreHalf := by decide

end Francescotti1995
