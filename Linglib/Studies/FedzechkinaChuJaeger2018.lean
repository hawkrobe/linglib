import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Linglib.Syntax.DependencyGrammar.Length
import Linglib.Syntax.DependencyGrammar.Dominance
import Linglib.Morphology.Word.Basic

/-!
# Fedzechkina, Chu and Jaeger (2018): Human information processing shapes language change

This file formalizes [fedzechkina-chu-jaeger-2018]'s test of dependency-length minimization
as a learning bias. Learners of two miniature languages with free subject–object order and
object case marking — one verb-final with prenominal postpositional phrases, one verb-initial
with postnominal prepositional phrases — heard subject-first and object-first orders equally
often and only sentences whose two arguments were both short or both long; in production
with one long argument they ordered long before short in the verb-final language and short
before long in the verb-initial one, the orders that shorten the verb's dependencies (Fig. 1),
and their sentences had shorter dependencies than the input (Fig. 5). The four sentences of
Fig. 1 are dependency graphs on the substrate, `verbDependencyLength` is the paper's measure —
the distance in words from the verb to the closest boundary of each argument — and
`totalLength` on the substrate orders the two word orders the same way. In general
`dependencyLength adjacent far` depends only on the argument next to the verb, so the order
placing the shorter argument next to the verb is preferred (`preferred_le`), and the preferred
orders of the two languages are opposite for every long argument (`preferred_ne`), the pattern
of Fig. 4. With the paper's constituent lengths a sentence with one long argument has
dependency length 3 or 6, so the input's expected length is 9/2 whatever the overall order
frequency (`mean_of_no_preference`), and a learner's mean length is bounded below by
`minMean` of their overall subject-first frequency, the lower lines of Fig. 5
(`minMean_le_mean`, `mean_attains_minMean`): the minimum is reachable only with perfectly
flexible order, and fixed order returns the input length.

## Implementation notes

* The paper measures a dependency from the verb to the closest boundary of the argument. In
  its languages the argument's head noun sits at that boundary — the noun phrases are
  head-final in the verb-final language and head-initial in the verb-initial one — so the
  substrate's head-to-head `Nat.dist` gives the same numbers; the graphs carry the noun-phrase
  internal arcs as well, whose lengths are the same under both orders.
* A long argument is a noun with an adpositional phrase of three words (Fig. 2), a short one a
  bare noun; the lengths 3 and 6 and the input mean 9/2 are computed from these.
* The measured means (Fig. 5) and the regressions of Fig. 4 stay in the paper; the file
  derives the predictions they test.

## References

* [fedzechkina-chu-jaeger-2018]
* [fedzechkina-newport-2012]
* [fedzechkina-newport-2017]
* [gildea-temperley-2010]
* [arnold-wasow-losongco-ginstrom-2000]
-/

namespace FedzechkinaChuJaeger2018

open DependencyGrammar Morphology

/-! ### The dependency lengths of a verb-peripheral transitive sentence -/

/-- The verb's two dependencies in a sentence with the verb at one end: one to the argument
next to it, spanning one word, and one to the far argument, spanning the adjacent argument and
one more word — a length that depends only on the argument next to the verb (Fig. 1). -/
def dependencyLength (adjacent : ℕ) (_far : ℕ) : ℕ := 1 + (adjacent + 1)

theorem dependencyLength_eq (adjacent far : ℕ) : dependencyLength adjacent far = adjacent + 2 := by
  unfold dependencyLength; omega

/-- Placing the shorter argument next to the verb never lengthens the dependencies. -/
theorem dependencyLength_le {a b : ℕ} (h : a ≤ b) :
    dependencyLength a b ≤ dependencyLength b a := by
  simp only [dependencyLength_eq]; omega

theorem dependencyLength_lt {a b : ℕ} (h : a < b) :
    dependencyLength a b < dependencyLength b a := by
  simp only [dependencyLength_eq]; omega

/-- The verb's position. -/
inductive HeadPosition where
  | final
  | initial
  deriving DecidableEq, Repr

/-- The order of the two arguments. -/
inductive Order where
  | SO
  | OS
  deriving DecidableEq, Repr

/-- The argument roles. -/
inductive Role where
  | subject
  | object
  deriving DecidableEq, Repr

/-- The argument next to the verb: the second argument in a verb-final sentence, the first in a
verb-initial one. -/
def adjacent : HeadPosition → Order → Role
  | .final, .SO => .object
  | .final, .OS => .subject
  | .initial, .SO => .subject
  | .initial, .OS => .object

/-- The order that puts the other argument next to the verb when `long` is the long one: long
before short in the verb-final language, short before long in the verb-initial one. -/
def preferred : HeadPosition → Role → Order
  | .final, .subject => .SO
  | .final, .object => .OS
  | .initial, .subject => .OS
  | .initial, .object => .SO

/-- The verb's dependency length in the order `o` when `long` has length `ℓ` and the other
argument length `s`. -/
def lengthOf (h : HeadPosition) (long : Role) (ℓ s : ℕ) (o : Order) : ℕ :=
  if adjacent h o = long then dependencyLength ℓ s else dependencyLength s ℓ

theorem adjacent_preferred (h : HeadPosition) (r : Role) : adjacent h (preferred h r) ≠ r := by
  cases h <;> cases r <;> decide

/-- The preferred order has dependency length `s + 2` and the other `ℓ + 2`, so it is never
longer, and strictly shorter when the long argument is longer. -/
theorem preferred_le (h : HeadPosition) (r : Role) {ℓ s : ℕ} (hs : s ≤ ℓ) (o : Order) :
    lengthOf h r ℓ s (preferred h r) ≤ lengthOf h r ℓ s o := by
  unfold lengthOf
  rw [if_neg (adjacent_preferred h r)]
  split
  · exact dependencyLength_le hs
  · exact le_rfl

theorem preferred_lt (h : HeadPosition) (r : Role) {ℓ s : ℕ} (hs : s < ℓ) {o : Order}
    (ho : o ≠ preferred h r) : lengthOf h r ℓ s (preferred h r) < lengthOf h r ℓ s o := by
  unfold lengthOf
  rw [if_neg (adjacent_preferred h r)]
  split
  · exact dependencyLength_lt hs
  · exact absurd (by cases h <;> cases r <;> cases o <;> simp_all [adjacent, preferred]) ho

/-- The two languages prefer opposite surface orders for the same long argument: long before
short when verb-final, short before long when verb-initial (Fig. 4). -/
theorem preferred_ne (r : Role) : preferred .final r ≠ preferred .initial r := by
  cases r <;> decide

/-! ### Fig. 1 on the substrate -/

/-- The verb-final language's sentence with a long object, subject first: MOUNTIE [[RED STOOL
ON] HUNTER-OBJ] PUNCH. -/
def verbFinalSO : Graph 6 :=
  .ofArcs [Word.mk' "rizba" .NOUN, Word.mk' "redal" .ADJ, Word.mk' "lanferda" .NOUN,
      Word.mk' "sool" .ADP, Word.mk' "barsadi" .NOUN, Word.mk' "kyse" .VERB]
    5 [(5, 0, .nsubj), (5, 4, .obj), (4, 2, .nmod), (2, 1, .amod), (2, 3, .case_)]

/-- The same sentence object first: [[RED STOOL ON] HUNTER-OBJ] MOUNTIE PUNCH. -/
def verbFinalOS : Graph 6 :=
  .ofArcs [Word.mk' "redal" .ADJ, Word.mk' "lanferda" .NOUN, Word.mk' "sool" .ADP,
      Word.mk' "barsadi" .NOUN, Word.mk' "rizba" .NOUN, Word.mk' "kyse" .VERB]
    5 [(5, 4, .nsubj), (5, 3, .obj), (3, 1, .nmod), (1, 0, .amod), (1, 2, .case_)]

/-- The verb-initial language's sentence subject first: PUNCH MOUNTIE [HUNTER-OBJ [ON RED
STOOL]]. -/
def verbInitialSO : Graph 6 :=
  .ofArcs [Word.mk' "kyse" .VERB, Word.mk' "rizba" .NOUN, Word.mk' "barsadi" .NOUN,
      Word.mk' "sool" .ADP, Word.mk' "redal" .ADJ, Word.mk' "lanferda" .NOUN]
    0 [(0, 1, .nsubj), (0, 2, .obj), (2, 5, .nmod), (5, 3, .case_), (5, 4, .amod)]

/-- The same sentence object first: PUNCH [HUNTER-OBJ [ON RED STOOL]] MOUNTIE. -/
def verbInitialOS : Graph 6 :=
  .ofArcs [Word.mk' "kyse" .VERB, Word.mk' "barsadi" .NOUN, Word.mk' "sool" .ADP,
      Word.mk' "redal" .ADJ, Word.mk' "lanferda" .NOUN, Word.mk' "rizba" .NOUN]
    0 [(0, 5, .nsubj), (0, 1, .obj), (1, 4, .nmod), (4, 2, .case_), (4, 3, .amod)]

theorem fig1_isTree :
    verbFinalSO.IsTree ∧ verbFinalOS.IsTree ∧ verbInitialSO.IsTree ∧ verbInitialOS.IsTree := by
  decide

/-- The paper's measure: the summed lengths of the verb's dependencies, from the root to its
arguments. -/
def verbDependencyLength {n : ℕ} (g : Graph n) : ℕ :=
  ∑ w ∈ g.children g.root, Nat.dist g.root w

/-- The numbers of Fig. 1: 5 + 1 against 2 + 1 in the verb-final language, 1 + 2 against
1 + 5 in the verb-initial one, as `dependencyLength` with a long argument of four words. -/
theorem fig1_verbDependencyLength :
    verbDependencyLength verbFinalSO = dependencyLength 4 1 ∧
    verbDependencyLength verbFinalOS = dependencyLength 1 4 ∧
    verbDependencyLength verbInitialSO = dependencyLength 1 4 ∧
    verbDependencyLength verbInitialOS = dependencyLength 4 1 := by
  decide

/-- The substrate's total dependency length orders the two word orders the same way: the
noun-phrase internal arcs contribute equally. -/
theorem fig1_totalLength :
    verbFinalOS.totalLength < verbFinalSO.totalLength ∧
    verbInitialSO.totalLength < verbInitialOS.totalLength := by
  decide

/-! ### The input and the bound of Fig. 5 -/

/-- The length of a sentence with one long argument of four words and one short argument of
one word, the long one next to the verb or not. -/
def longAdjacent : ℚ := dependencyLength 4 1

def shortAdjacent : ℚ := dependencyLength 1 4

/-- The mean length over the test scenes, half with a long subject and half with a long
object, of a learner who uses subject-first order with frequency `qS` on the former and `qO`
on the latter. -/
def mean (h : HeadPosition) (qS qO : ℚ) : ℚ :=
  (qS * lengthOf' h .subject .SO + (1 - qS) * lengthOf' h .subject .OS) / 2 +
    (qO * lengthOf' h .object .SO + (1 - qO) * lengthOf' h .object .OS) / 2
where
  /-- The length of the order `o` when `long` is the long argument. -/
  lengthOf' (h : HeadPosition) (long : Role) (o : Order) : ℚ :=
    if adjacent h o = long then longAdjacent else shortAdjacent

/-- Without a length-based ordering preference the mean is the input's 9/2, whatever the
overall order frequency. -/
theorem mean_of_no_preference (h : HeadPosition) (q : ℚ) : mean h q q = 9 / 2 := by
  cases h <;> simp [mean, mean.lengthOf', adjacent, longAdjacent, shortAdjacent,
    dependencyLength] <;> ring

/-- The least mean length compatible with an overall subject-first frequency `p`: the lower
lines of Fig. 5, 3 at perfect flexibility and the input's 9/2 at fixed order. -/
def minMean (p : ℚ) : ℚ := 9 / 2 - 3 * min p (1 - p)

theorem minMean_half : minMean (1 / 2) = 3 := by norm_num [minMean]

theorem minMean_zero : minMean 0 = 9 / 2 := by norm_num [minMean]

theorem minMean_one : minMean 1 = 9 / 2 := by norm_num [minMean]

/-- A learner's mean length is at least `minMean` of their overall subject-first frequency. -/
theorem minMean_le_mean (h : HeadPosition) {qS qO : ℚ} (hS : 0 ≤ qS ∧ qS ≤ 1)
    (hO : 0 ≤ qO ∧ qO ≤ 1) : minMean ((qS + qO) / 2) ≤ mean h qS qO := by
  obtain ⟨hS0, hS1⟩ := hS
  obtain ⟨hO0, hO1⟩ := hO
  have h1 : 9 / 2 - 3 * ((qS + qO) / 2) ≤ mean h qS qO := by
    cases h <;> simp [mean, mean.lengthOf', adjacent, longAdjacent, shortAdjacent,
      dependencyLength] <;> linarith
  have h2 : 9 / 2 - 3 * (1 - (qS + qO) / 2) ≤ mean h qS qO := by
    cases h <;> simp [mean, mean.lengthOf', adjacent, longAdjacent, shortAdjacent,
      dependencyLength] <;> linarith
  unfold minMean
  rcases min_choice ((qS + qO) / 2) (1 - (qS + qO) / 2) with hm | hm <;> rw [hm] <;> assumption

/-- The bound is attained: subject-first order is spent first on the scenes where it shortens
dependencies — long-subject scenes in the verb-final language, long-object scenes in the
verb-initial one. -/
theorem mean_attains_minMean (h : HeadPosition) {p : ℚ} (hp : 0 ≤ p ∧ p ≤ 1) :
    ∃ qS qO, 0 ≤ qS ∧ qS ≤ 1 ∧ 0 ≤ qO ∧ qO ≤ 1 ∧ (qS + qO) / 2 = p ∧
      mean h qS qO = minMean p := by
  obtain ⟨hp0, hp1⟩ := hp
  rcases le_or_gt p (1 / 2) with hle | hlt
  · have hm : min p (1 - p) = p := min_eq_left (by linarith)
    cases h
    · exact ⟨2 * p, 0, by linarith, by linarith, le_rfl, by norm_num, by ring, by
        simp [mean, mean.lengthOf', adjacent, longAdjacent, shortAdjacent, dependencyLength,
          minMean, hm]
        linarith⟩
    · exact ⟨0, 2 * p, le_rfl, by norm_num, by linarith, by linarith, by ring, by
        simp [mean, mean.lengthOf', adjacent, longAdjacent, shortAdjacent, dependencyLength,
          minMean, hm]
        linarith⟩
  · have hm : min p (1 - p) = 1 - p := min_eq_right (by linarith)
    cases h
    · exact ⟨1, 2 * p - 1, by norm_num, le_rfl, by linarith, by linarith, by ring, by
        simp [mean, mean.lengthOf', adjacent, longAdjacent, shortAdjacent, dependencyLength,
          minMean, hm]
        linarith⟩
    · exact ⟨2 * p - 1, 1, by linarith, by linarith, by norm_num, le_rfl, by ring, by
        simp [mean, mean.lengthOf', adjacent, longAdjacent, shortAdjacent, dependencyLength,
          minMean, hm]
        linarith⟩

end FedzechkinaChuJaeger2018
