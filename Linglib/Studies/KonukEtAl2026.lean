import Linglib.Semantics.Causation.Strength
import Linglib.Semantics.Plurality.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Konuk, Quillien and Mascarenhas (2026): Plural Causes

This file formalizes [konuk-et-al-2026]'s account of plural causes in causal selection: a
conjunction of events such as *A and B* is a candidate cause in its own right, scored by the
counterfactual dependence of the outcome on the compound binary variable that is true when
both hold. The Necessity–Sufficiency Model of [icard-et-al-2017], the substrate's
`Causation.Strength.nsm`, applies to the compound with the compound's own prior, its
necessity the probability that the outcome fails where the compound fails, and its sufficiency
the probability that forcing the compound on restores an absent outcome
(`Compound.score`). In Experiment 1 a player wins with two colored balls from three urns of
probabilities 0.05, 0.5 and 0.95; with the counterfactual worlds drawn from the priors, the
score of a pair is in closed form one minus the chance that exactly one of its urns and the
third all come out colored (`score_pair`), so the pair of the intermediate and high urns
scores 39/40 while the pair of the low and intermediate urns scores 21/40, though the low and
high urns are alike on their own: plural judgments are not linear in singular ones
(`antilinearity`). In Experiment 2 the rule is (A ∧ B) ∨ (C ∧ D): only pairs within a
disjunct are sufficient for a win (`sufficient_pairs`), and losing rounds are scored against
the homogeneous loss ¬A ∧ ¬B ∧ ¬C ∧ ¬D, the plural negation of the winning conditions
in the sense of [kriz-spector-2021], rather than the classical negation, (2) and (3):
under the classical loss no single white ball is necessary in the overdetermined negative round,
under the homogeneous loss each is (`overdetermined_negative`), and in the triple-negative
round the representation negates as homogeneously as the facts allow (`triple_negative`).

## Implementation notes

* Worlds are tuples of Booleans, so probabilities are finite sums over products of Booleans
  and the closed form is proved by expanding them; the stability parameter is set to 0, the
  paper's own exposition, so that sampling propensities are the priors.
* The fitted parameters, s = 0.71 in Experiment 1 and the mixture weight w = 0.77 of the two
  loss representations in Experiment 2, and the Counterfactual Effect Size Model are not
  represented.

## References

* [konuk-et-al-2026]
* [icard-et-al-2017]
* [kriz-spector-2021]
-/

namespace KonukEtAl2026

open Causation.Strength

variable {W : Type*} [Fintype W]

/-- The mass of the worlds passing a test, under a distribution over worlds. -/
def mass (p : W → ℚ) (S : W → Bool) : ℚ := ∑ w, if S w then p w else 0

/-- A compound cause: the test that all its variables hold, and the intervention that sets
them all true. -/
structure Compound (W : Type*) where
  holds : W → Bool
  on : W → W

namespace Compound

variable (p : W → ℚ) (f : W → Bool) (C : Compound W)

/-- Necessity: the probability, over the worlds where the compound fails, that the outcome
fails. -/
def necessity : ℚ := mass p (λ w => !C.holds w && !f w) / mass p (λ w => !C.holds w)

/-- Sufficiency: the probability, over the worlds where compound and outcome both fail, that
forcing the compound on produces the outcome. -/
def sufficiency : ℚ :=
  mass p (λ w => !C.holds w && !f w && f (C.on w)) / mass p (λ w => !C.holds w && !f w)

/-- The score of a compound: [icard-et-al-2017]'s model applied to the compound variable,
its prior the mass of the worlds where it holds. -/
def score : ℚ := nsm (mass p C.holds) (C.sufficiency p f) (C.necessity p f)

/-- A compound is sufficient for an outcome when forcing it on produces the outcome in every
world. -/
def Sufficient : Prop := ∀ w, f (C.on w) = true

instance : Decidable (C.Sufficient f) := inferInstanceAs (Decidable (∀ w, f (C.on w) = true))

end Compound

/-! ### Experiment 1: the threshold game -/

/-- A round of the threshold game: whether each of the three urns gave a colored ball. -/
abbrev Round₁ := Bool × Bool × Bool

/-- The player wins with two colored balls or more. -/
def win₁ : Round₁ → Bool
  | (a, b, c) => (a && b) || (a && c) || (b && c)

/-- Independent draws with the urns' probabilities: the counterfactual distribution with the
stability parameter at 0. -/
def draws (pA pB pC : ℚ) : Round₁ → ℚ
  | (a, b, c) =>
    (if a then pA else 1 - pA) * (if b then pB else 1 - pB) * (if c then pC else 1 - pC)

/-- The pair of the first two urns as a compound cause. -/
def pair : Compound Round₁ := ⟨λ w => w.1 && w.2.1, λ w => (true, true, w.2.2)⟩

/-- The pair is sufficient for a win. -/
theorem pair_sufficient : pair.Sufficient win₁ := by decide

/-- The score of a pair in closed form: its sufficiency is one, and its necessity carries the
worlds where neither urn gives a colored ball or exactly one does and the third does not, so
the score is one minus the probability that exactly one of the pair and the third urn give
colored balls. -/
theorem score_pair {pA pB pC : ℚ} (hA : 0 < pA ∧ pA < 1) (hB : 0 < pB ∧ pB < 1)
    (hC : 0 < pC ∧ pC < 1) :
    pair.score (draws pA pB pC) win₁ = 1 - (pA * (1 - pB) + (1 - pA) * pB) * pC := by
  have hn : mass (draws pA pB pC) (λ w => !pair.holds w) = 1 - pA * pB := by
    simp only [mass, Fintype.sum_prod_type, Fintype.sum_bool, pair, draws]
    simp; ring
  have hnf : mass (draws pA pB pC) (λ w => !pair.holds w && !win₁ w) =
      (1 - pA) * (1 - pB) + (pA * (1 - pB) + (1 - pA) * pB) * (1 - pC) := by
    simp only [mass, Fintype.sum_prod_type, Fintype.sum_bool, pair, draws, win₁]
    simp; ring
  have hnfs : mass (draws pA pB pC) (λ w => !pair.holds w && !win₁ w && win₁ (pair.on w)) =
      (1 - pA) * (1 - pB) + (pA * (1 - pB) + (1 - pA) * pB) * (1 - pC) := by
    simp only [mass, Fintype.sum_prod_type, Fintype.sum_bool, pair, draws, win₁]
    simp; ring
  have hc : mass (draws pA pB pC) pair.holds = pA * pB := by
    simp only [mass, Fintype.sum_prod_type, Fintype.sum_bool, pair, draws]
    simp; ring
  have hn0 : (1 : ℚ) - pA * pB ≠ 0 := by nlinarith [hA.1, hA.2, hB.1, hB.2]
  have hnf0 : (1 - pA) * (1 - pB) + (pA * (1 - pB) + (1 - pA) * pB) * (1 - pC) ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 hA.2) (sub_pos.2 hB.2))
      (mul_nonneg (add_nonneg (mul_nonneg hA.1.le (sub_nonneg.2 hB.2.le))
        (mul_nonneg (sub_nonneg.2 hA.2.le) hB.1.le)) (sub_nonneg.2 hC.2.le)))
  rw [Compound.score, Compound.sufficiency, Compound.necessity, hn, hnf, hnfs, hc, nsm,
    div_self hnf0]
  field_simp
  ring

/-- The urns' probabilities: low, intermediate and high. -/
def pLow : ℚ := 1 / 20
def pInt : ℚ := 1 / 2
def pHigh : ℚ := 19 / 20

/-- Anti-linearity: the pair of the intermediate and high urns scores 39/40 and the pair of
the low and intermediate urns 21/40, so plural scores are not a linear combination of
singular ones, the low and high urns being alike. -/
theorem antilinearity :
    pair.score (draws pInt pHigh pLow) win₁ = 39 / 40 ∧
      pair.score (draws pLow pInt pHigh) win₁ = 21 / 40 ∧
      pair.score (draws pLow pInt pHigh) win₁ < pair.score (draws pInt pHigh pLow) win₁ := by
  rw [score_pair (by norm_num [pInt]) (by norm_num [pHigh]) (by norm_num [pLow]),
    score_pair (by norm_num [pLow]) (by norm_num [pInt]) (by norm_num [pHigh])]
  norm_num [pLow, pInt, pHigh]

/-! ### Experiment 2: the disjunctive rule -/

/-- A round with four urns. -/
abbrev Round₂ := Bool × Bool × Bool × Bool

/-- The player wins with two purple balls, from A and B, or two yellow, from C and D, (1). -/
def win₂ : Round₂ → Bool
  | (a, b, c, d) => (a && b) || (c && d)

/-- The classical loss, (3): the negation of the winning conditions. -/
def lossClassical (w : Round₂) : Bool := !win₂ w

/-- The homogeneous loss, (2): the plural negation of the winning conditions. -/
def lossStrong : Round₂ → Bool
  | (a, b, c, d) => !a && !b && !c && !d

/-- The urn `i`'s draw in a round. -/
def draw : Round₂ → Fin 4 → Bool
  | (a, b, c, d), i => ![a, b, c, d] i

/-- Setting urn `i`'s draw. -/
def set (w : Round₂) (i : Fin 4) (b : Bool) : Round₂ :=
  (if i = 0 then b else w.1, if i = 1 then b else w.2.1, if i = 2 then b else w.2.2.1,
    if i = 3 then b else w.2.2.2)

/-- The homogeneous loss is the plural negation of the draws in the sense of
[kriz-spector-2021]: none of the urns gives a colored ball. -/
theorem lossStrong_iff_noneSatisfy (w : Round₂) :
    lossStrong w = true ↔ Plurality.noneSatisfy (λ i (_ : Unit) => draw w i = true) Finset.univ () := by
  revert w; decide

/-- The homogeneous loss is strictly stronger than the classical one. -/
theorem lossStrong_lt_classical :
    (∀ w, lossStrong w = true → lossClassical w = true) ∧
      ∃ w, lossClassical w = true ∧ lossStrong w = false := by
  decide

/-- Only the pairs within a disjunct are sufficient for a win: A ∧ B and C ∧ D, not the
crossing pairs. -/
theorem sufficient_pairs :
    Compound.Sufficient win₂ ⟨λ w => w.1 && w.2.1, λ w => (true, true, w.2.2.1, w.2.2.2)⟩ ∧
      Compound.Sufficient win₂ ⟨λ w => w.2.2.1 && w.2.2.2, λ w => (w.1, w.2.1, true, true)⟩ ∧
      ¬ Compound.Sufficient win₂ ⟨λ w => w.1 && w.2.2.1, λ w => (true, w.2.1, true, w.2.2.2)⟩ ∧
      ¬ Compound.Sufficient win₂ ⟨λ w => w.2.1 && w.2.2.2, λ w => (w.1, true, w.2.2.1, true)⟩ := by
  decide

/-- The triple-positive round, colored balls from A, B and D: the pair A ∧ B wins on its own
and D is idle, the win surviving its removal. -/
theorem triple_positive :
    win₂ (true, true, false, false) = true ∧ win₂ (set (true, true, false, true) 3 false) = true := by
  decide

/-- The overdetermined negative round, white balls from every urn: under the classical loss no
single white ball is necessary, the loss surviving any one urn's colored ball, while under the
homogeneous loss every white ball is. -/
theorem overdetermined_negative :
    (∀ i, lossClassical (set (false, false, false, false) i true) = true) ∧
      ∀ i, lossStrong (set (false, false, false, false) i true) = false := by
  decide

/-- The triple-negative round, white balls from A, B and D and a colored one from C: under the
classical loss D's white ball is indispensable while A's and B's are redundant with each other,
and the homogeneous representation compatible with the facts, ¬A ∧ ¬B ∧ ¬D, makes each of
the three indispensable. -/
theorem triple_negative :
    let actual : Round₂ := (false, false, true, false)
    lossClassical (set actual 3 true) = false ∧ lossClassical (set actual 0 true) = true ∧
      lossClassical (set actual 1 true) = true ∧
      ∀ i ∈ ({0, 1, 3} : Finset (Fin 4)),
        ¬ Plurality.noneSatisfy (λ j (_ : Unit) => draw (set actual i true) j = true)
          {0, 1, 3} () := by
  decide

end KonukEtAl2026
