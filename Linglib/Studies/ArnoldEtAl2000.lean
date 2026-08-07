import Linglib.Phonology.Constraints.Defs
import Linglib.Features.Givenness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Heaviness vs. newness in constituent ordering

[arnold-wasow-losongco-ginstrom-2000] use a corpus analysis (the
Aligned-Hansard corpus: *bring … to* and *take … into account* for heavy
NP shift, *give* for the dative alternation) and an elicitation
experiment (directors instructing actors to give objects to toy animals)
to disentangle two confounded predictors of English postverbal ordering:
heaviness (relative word count; [behaghel-1909]'s law of growing
constituents, "end weight") and newness (given-before-new, coded with
[prince-1992]'s discourse-given/new distinction, the corpus's few
inferables collapsed into given). Both factors independently predict
ordering in both constructions (§2 corpus, §3 experiment), and §5 reads
the interaction pattern as "a constraint-based system, where the
strength of a constraint is greater when competing constraints are
weak".

The two factors are weighted markedness constraints `*HEAVY-FIRST` and
`*NEW-FIRST` over the binary ordering candidates
([goldwater-johnson-2003]'s MaxEnt encoding of the paper's
soft-constraint architecture). The harmony difference between the two
orders decomposes additively into signed per-constraint preferences
(`score_diff_eq_components`), so independence, composition, and the
constraint-strength interaction are one-step consequences; a
pure-heaviness and a pure-newness contrast pair witness that neither
factor reduces to the other.
-/

namespace ArnoldEtAl2000

open Constraints Features

/-! ### Phrases, orderings, and candidates -/

/-- A constituent characterized by the two dimensions
    [arnold-wasow-losongco-ginstrom-2000] measure: word count
    (heaviness) and discourse status (newness). Concrete syntactic
    structure is abstracted away — these two scalars exhaust what the
    paper's regressions condition on. -/
structure Phrase where
  wordCount : Nat
  discourse : BinaryGivenness
  deriving DecidableEq

/-- The two constituents of a binary postverbal alternation. For the
    dative alternation, `(theme, goal)`; for heavy NP shift, `(direct
    object, prepositional phrase)`. The constraints below are
    construction-neutral. -/
abbrev Pair := Phrase × Phrase

/-- Which of the two constituents occupies the second (sentence-final)
    slot. For DA (pair = theme, goal): `themeLast` is the double object
    (*give the white rabbit the carrot*), `goalLast` the prepositional
    dative (*give the carrot to the white rabbit*). For HNPS (pair =
    direct object, PP): `themeLast` is the *shifted* `V PP DO`,
    `goalLast` the canonical `V DO PP`. -/
inductive Order where
  | themeLast
  | goalLast
  deriving DecidableEq

abbrev Candidate := Pair × Order

/-! ### The two constraints -/

/-- `*HEAVY-FIRST`: violated when the first (verb-adjacent) constituent
    is strictly heavier than the second — the markedness encoding of
    [behaghel-1909]'s law of growing constituents. -/
def heavyFirst : Constraint Candidate :=
  fun ((th, gl), o) =>
    match o with
    | .themeLast => if gl.wordCount > th.wordCount then 1 else 0
    | .goalLast  => if th.wordCount > gl.wordCount then 1 else 0

/-- `*NEW-FIRST`: violated when the first constituent is discourse-new
    while the second is discourse-given — the markedness encoding of the
    given-before-new principle ([prince-1981],
    [gundel-hedberg-zacharski-1993]). -/
def newFirst : Constraint Candidate :=
  fun ((th, gl), o) =>
    match o with
    | .themeLast =>
      if gl.discourse = .new ∧ th.discourse = .given then 1 else 0
    | .goalLast  =>
      if th.discourse = .new ∧ gl.discourse = .given then 1 else 0

/-- The two-constraint set as a `CON` over the ordering candidates. -/
def con : CON Candidate 2 := ![heavyFirst, newFirst]

/-- The weight vector pairing with `con`: `wH` weights `*HEAVY-FIRST`,
    `wN` weights `*NEW-FIRST`. -/
def gW (wH wN : ℝ) : Fin 2 → ℝ := ![wH, wN]

/-! ### Per-constraint signed preferences -/

/-- The heaviness constraint's signed preference for `themeLast` over
    `goalLast` on a pair: `+1` when the theme (`p.1`) is heavier (so
    placing it last avoids violation), `-1` when the goal (`p.2`) is
    heavier, `0` when they are equal. -/
def heavyDiff (p : Pair) : ℝ :=
  (if p.1.wordCount > p.2.wordCount then (1:ℝ) else 0) -
  (if p.2.wordCount > p.1.wordCount then (1:ℝ) else 0)

/-- The newness constraint's signed preference for `themeLast` over
    `goalLast` on a pair: `+1` when the theme is new and the goal given
    (so placing the theme last respects given-before-new), `-1` in the
    mirror case, `0` otherwise. -/
def newDiff (p : Pair) : ℝ :=
  (if p.1.discourse = .new ∧ p.2.discourse = .given then (1:ℝ) else 0) -
  (if p.2.discourse = .new ∧ p.1.discourse = .given then (1:ℝ) else 0)

/-- The harmony-score difference decomposes additively into per-constraint
    signed preferences scaled by their weights. Every prediction theorem
    below is a one-step consequence. -/
theorem score_diff_eq_components (wH wN : ℝ) (p : Pair) :
    harmonyScore con (gW wH wN) (p, .themeLast) -
    harmonyScore con (gW wH wN) (p, .goalLast) =
      wH * heavyDiff p + wN * newDiff p := by
  obtain ⟨th, gl⟩ := p
  rw [harmonyScore_eq_neg_sum, harmonyScore_eq_neg_sum]
  simp only [con, gW, heavyFirst, newFirst, heavyDiff, newDiff, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

/-- `heavyDiff` is positive iff the theme (`p.1`) is strictly heavier
    than the goal — i.e., `*HEAVY-FIRST` prefers `themeLast`. -/
theorem heavyDiff_pos_iff {p : Pair} :
    0 < heavyDiff p ↔ p.1.wordCount > p.2.wordCount := by
  unfold heavyDiff
  split_ifs with h1 h2 <;> norm_num <;> omega

/-- `newDiff` is positive iff the theme is new while the goal is
    given — i.e., `*NEW-FIRST` prefers `themeLast`. -/
theorem newDiff_pos_iff {p : Pair} :
    0 < newDiff p ↔ p.1.discourse = .new ∧ p.2.discourse = .given := by
  unfold newDiff
  split_ifs with h1 h2 <;> norm_num <;> simp_all

/-! ### Independence — the central paper claim, derived -/

/-- **Heaviness independently predicts ordering.** With the newness
    weight zeroed out, a positive heaviness weight makes the order
    placing the heavier constituent last strictly preferred. -/
theorem heaviness_independently_predicts {p : Pair} {wH : ℝ}
    (hH : 0 < wH) (h : 0 < heavyDiff p) :
    harmonyDominates con (gW wH 0) (p, .themeLast) (p, .goalLast) := by
  rw [harmonyDominates_iff, ← sub_pos, score_diff_eq_components]
  simpa using mul_pos hH h

/-- **Newness independently predicts ordering.** With the heaviness
    weight zeroed out, a positive newness weight makes the order
    placing the new constituent last strictly preferred. -/
theorem newness_independently_predicts {p : Pair} {wN : ℝ}
    (hN : 0 < wN) (h : 0 < newDiff p) :
    harmonyDominates con (gW 0 wN) (p, .themeLast) (p, .goalLast) := by
  rw [harmonyDominates_iff, ← sub_pos, score_diff_eq_components]
  simpa using mul_pos hN h

/-- **Both factors compose additively.** When neither factor opposes
    `themeLast` and at least one strictly favors it, `themeLast` wins;
    no separate interaction term is stipulated. -/
theorem both_factors_compose {p : Pair} {wH wN : ℝ}
    (hH : 0 ≤ wH) (hN : 0 ≤ wN)
    (hHeavy : 0 ≤ heavyDiff p) (hNew : 0 ≤ newDiff p)
    (hStrict : 0 < wH * heavyDiff p ∨ 0 < wN * newDiff p) :
    harmonyDominates con (gW wH wN) (p, .themeLast) (p, .goalLast) := by
  rw [harmonyDominates_iff, ← sub_pos, score_diff_eq_components]
  have h1 : 0 ≤ wH * heavyDiff p := mul_nonneg hH hHeavy
  have h2 : 0 ≤ wN * newDiff p := mul_nonneg hN hNew
  rcases hStrict with hs | hs <;> linarith

/-- **Tradeoff.** When heaviness and newness conflict, the prediction
    depends on which side has the larger weighted contribution — the
    constraint-based architecture the paper argues for. -/
theorem tradeoff_resolved_by_weights {p : Pair} {wH wN : ℝ}
    (h : 0 < wH * heavyDiff p + wN * newDiff p) :
    harmonyDominates con (gW wH wN) (p, .themeLast) (p, .goalLast) := by
  rw [harmonyDominates_iff, ← sub_pos, score_diff_eq_components]
  exact h

/-! ### Constraint-strength interaction

In the corpus study the dative regressions had both main effects and no
newness × heaviness interaction; the experiment showed one — "heaviness
had the largest effect on utterances where both constituents were
given" (§5). In additive harmony the pattern is immediate: when one
constraint's differential is zero, the entire harmony difference is
borne by the other constraint, undiluted. -/

/-- When the newness constraint is neutral on a pair (both constituents
    share givenness status), the harmony difference is exactly the
    weighted heaviness term. -/
theorem heaviness_dominates_when_newness_neutral
    (wH wN : ℝ) {p : Pair} (hN : newDiff p = 0) :
    harmonyScore con (gW wH wN) (p, .themeLast) -
    harmonyScore con (gW wH wN) (p, .goalLast) = wH * heavyDiff p := by
  rw [score_diff_eq_components, hN, mul_zero, add_zero]

/-- When the heaviness constraint is neutral on a pair (equal lengths),
    the harmony difference is exactly the weighted newness term. -/
theorem newness_dominates_when_heaviness_neutral
    (wH wN : ℝ) {p : Pair} (hH : heavyDiff p = 0) :
    harmonyScore con (gW wH wN) (p, .themeLast) -
    harmonyScore con (gW wH wN) (p, .goalLast) = wN * newDiff p := by
  rw [score_diff_eq_components, hH, mul_zero, zero_add]

/-! ### Contrast pairs and non-reducibility -/

/-- A heavy-goal contrast: light theme, heavy goal, both new — only
    heaviness discriminates. -/
def heavyGoalContrast : Pair :=
  ({ wordCount := 1, discourse := .new },
   { wordCount := 8, discourse := .new })

/-- A pure-newness contrast in the experiment's *give*-frame (*give the
    carrot to the white rabbit*): lengths matched, theme new, goal
    given — only newness discriminates. -/
def newThemeContrast : Pair :=
  ({ wordCount := 1, discourse := .new  },
   { wordCount := 1, discourse := .given })

@[simp] theorem heavyDiff_heavyGoalContrast : heavyDiff heavyGoalContrast = -1 := by
  norm_num [heavyDiff, heavyGoalContrast]

@[simp] theorem newDiff_heavyGoalContrast : newDiff heavyGoalContrast = 0 := by
  simp [newDiff, heavyGoalContrast]

@[simp] theorem heavyDiff_newThemeContrast : heavyDiff newThemeContrast = 0 := by
  simp [heavyDiff, newThemeContrast]

@[simp] theorem newDiff_newThemeContrast : newDiff newThemeContrast = 1 := by
  norm_num [newDiff, newThemeContrast]
  decide

/-- **Non-reducibility witness.** `heavyGoalContrast` activates *only*
    heaviness, `newThemeContrast` *only* newness: a theory
    operationalizing one factor collapses one contrast to the trivial
    baseline, contradicting the paper's findings. -/
theorem heaviness_and_newness_genuinely_independent :
    newDiff heavyGoalContrast = 0 ∧ heavyDiff heavyGoalContrast ≠ 0 ∧
    heavyDiff newThemeContrast = 0 ∧ newDiff newThemeContrast ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- Pure-heaviness grammar predicts goal-last (heavier-last) on the
    heavy-goal contrast. -/
theorem heavy_goal_predicts_goalLast :
    harmonyDominates con (gW 1 0)
      (heavyGoalContrast, .goalLast) (heavyGoalContrast, .themeLast) := by
  rw [harmonyDominates_iff, ← sub_pos, ← neg_sub, score_diff_eq_components]
  norm_num

/-- Pure-newness grammar predicts theme-last (given-first) on the
    pure-newness contrast. -/
theorem new_theme_predicts_themeLast :
    harmonyDominates con (gW 0 1)
      (newThemeContrast, .themeLast) (newThemeContrast, .goalLast) :=
  newness_independently_predicts one_pos (by simp)

end ArnoldEtAl2000
