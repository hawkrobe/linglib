import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Paape and Vasishth (2026): Context Ameliorates but Does Not Eliminate Garden-Pathing

This file formalizes the latent-process model of [paape-vasishth-2026], a replication of the
complement-clause/relative-clause study of [altmann-garnham-dennis-1992] in which referential
context, one or two candidate referents for a definite, is crossed with disambiguation
towards the complement clause, the relative clause, or an unambiguous relative clause
(`Disambiguation`, `ReferentialContext`, `Condition.IsMatch`). Reading times at the
disambiguating region are a mixture over the leaves of a multinomial processing tree: an
inattentive reader guesses, an attentive one is garden-pathed with some probability, a
garden-pathed reader triages or reanalyses, reanalysis is overt, a regression, or covert and
in situ, covert reanalysis may be postponed to the spillover region, and either kind may fail
(`Outcome`, `Params.prob`). The leaf probabilities sum to one and the marginal probabilities
of garden-pathing, of a regression, and of acceptance are the products the tree prescribes
(`Params.prob_sum`, `Params.mass_gardenPathed`, `Params.mass_regression`,
`Params.accept_eq`). The reason for the mixture is that a comparison of condition means
cannot separate an effect of context on first-pass attachment from an effect on reanalysis
cost: two parameterizations differing in exactly those two quantities have the same mean
reading time and different mixing proportions (`mean_not_identifiable`).

The fitted model without triage predicts held-out data better than factorial models and than
surprisal from four language models, and its estimates support three conclusions:
relative-clause disambiguation is garden-pathed more often than complement-clause
disambiguation in both contexts; a supporting context lowers the relative-clause garden-path
rate without eliminating it, while raising the complement-clause rate; and covert reanalysis
is costlier for the relative clause than for the complement clause and costlier under
mismatch than under match, so context acts on attachment and on reanalysis alike.

## Implementation notes

Parameters and costs are rational and unconstrained, since the tree's identities do not need
them to lie in the unit interval. The posterior estimates, the Bayes factors of the factorial
analysis, and the cross-validation ranking are reported in prose only, and the inattentive
reader's acceptance bias is a parameter of the tree rather than the value the paper fixes
from its earlier work.

## References

* [paape-vasishth-2026]
* [altmann-garnham-dennis-1992]
-/

namespace PaapeVasishth2026

/-! ### The design -/

/-- The three disambiguations of the temporarily ambiguous string, *told the woman that he'd
risked his life for ...*. -/
inductive Disambiguation where
  | complementClause
  | relativeClause
  | unambiguousRelativeClause
  deriving DecidableEq

/-- The disambiguation resolves to a relative clause. -/
def Disambiguation.IsRelative : Disambiguation → Prop
  | .complementClause => False
  | .relativeClause | .unambiguousRelativeClause => True

instance : DecidablePred Disambiguation.IsRelative
  | .complementClause => .isFalse id
  | .relativeClause | .unambiguousRelativeClause => .isTrue trivial

/-- Whether the discourse offers the definite one candidate referent or two. -/
inductive ReferentialContext where
  | uniqueReferent
  | nonUniqueReferents
  deriving DecidableEq

/-- A context supports the relative clause when the bare definite cannot pick out its referent
and the complement clause when it can. -/
def ReferentialContext.Supports : ReferentialContext → Disambiguation → Prop
  | .nonUniqueReferents, d => d.IsRelative
  | .uniqueReferent, d => ¬ d.IsRelative

instance : ∀ (r : ReferentialContext) (d : Disambiguation), Decidable (r.Supports d)
  | .nonUniqueReferents, d => inferInstanceAs (Decidable d.IsRelative)
  | .uniqueReferent, d => inferInstanceAs (Decidable (¬ d.IsRelative))

/-- A cell of the three-by-two design. -/
structure Condition where
  disambiguation : Disambiguation
  context : ReferentialContext
  deriving DecidableEq

/-- Context and disambiguation match. -/
def Condition.IsMatch (c : Condition) : Prop := c.context.Supports c.disambiguation

instance (c : Condition) : Decidable c.IsMatch :=
  inferInstanceAs (Decidable (c.context.Supports c.disambiguation))

/-- The crossover of the design: two referents support the relative clause and one the
complement clause. -/
theorem match_cells :
    (⟨.relativeClause, .nonUniqueReferents⟩ : Condition).IsMatch ∧
      ¬ (⟨.relativeClause, .uniqueReferent⟩ : Condition).IsMatch ∧
      (⟨.complementClause, .uniqueReferent⟩ : Condition).IsMatch ∧
      ¬ (⟨.complementClause, .nonUniqueReferents⟩ : Condition).IsMatch := by
  decide

/-! ### The processing tree -/

/-- The leaves of the tree: each is a path of latent decisions and determines the costs paid,
whether a regression is observed, and the response. -/
inductive Outcome where
  | inattentive
  | correctFirstPass
  | triage
  | overtSuccess
  | overtFail
  | covertImmediateSuccess
  | covertImmediateFail
  | covertPostponedSuccess
  | covertPostponedFail
  deriving DecidableEq

/-- The leaves. -/
def Outcome.all : List Outcome :=
  [.inattentive, .correctFirstPass, .triage, .overtSuccess, .overtFail,
    .covertImmediateSuccess, .covertImmediateFail, .covertPostponedSuccess,
    .covertPostponedFail]

theorem Outcome.mem_all (o : Outcome) : o ∈ Outcome.all := by cases o <;> simp [Outcome.all]

/-- The trial was garden-pathed. -/
def Outcome.IsGardenPathed (o : Outcome) : Prop := o ≠ .inattentive ∧ o ≠ .correctFirstPass

/-- The trial shows a first-pass regression: only overt reanalysis rereads earlier material. -/
def Outcome.HasRegression (o : Outcome) : Prop := o = .overtSuccess ∨ o = .overtFail

/-- The attentive reader arrives at the correct analysis. -/
def Outcome.IsSuccess (o : Outcome) : Prop :=
  o = .correctFirstPass ∨ o = .overtSuccess ∨ o = .covertImmediateSuccess ∨
    o = .covertPostponedSuccess

instance : DecidablePred Outcome.IsGardenPathed := λ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred Outcome.HasRegression := λ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred Outcome.IsSuccess := λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The branching probabilities: attentive reading, garden-pathing, triage rather than
reanalysis, covert rather than overt reanalysis, postponement of covert reanalysis, success of
each kind of reanalysis, and the inattentive reader's bias towards acceptance. -/
structure Params where
  attentive : ℚ
  gardenPath : ℚ
  triage : ℚ
  covert : ℚ
  postpone : ℚ
  covertSuccess : ℚ
  overtSuccess : ℚ
  bias : ℚ

namespace Params

variable (p : Params)

/-- The probability of a garden-pathed trial that is reanalysed. -/
def reanalysed : ℚ := p.attentive * p.gardenPath * (1 - p.triage)

/-- The probability of a leaf: the product of the branch probabilities on its path. -/
def prob : Outcome → ℚ
  | .inattentive => 1 - p.attentive
  | .correctFirstPass => p.attentive * (1 - p.gardenPath)
  | .triage => p.attentive * p.gardenPath * p.triage
  | .overtSuccess => p.reanalysed * (1 - p.covert) * p.overtSuccess
  | .overtFail => p.reanalysed * (1 - p.covert) * (1 - p.overtSuccess)
  | .covertImmediateSuccess => p.reanalysed * p.covert * (1 - p.postpone) * p.covertSuccess
  | .covertImmediateFail => p.reanalysed * p.covert * (1 - p.postpone) * (1 - p.covertSuccess)
  | .covertPostponedSuccess => p.reanalysed * p.covert * p.postpone * p.covertSuccess
  | .covertPostponedFail => p.reanalysed * p.covert * p.postpone * (1 - p.covertSuccess)

/-- The probability of the leaves satisfying a predicate. -/
def mass (P : Outcome → Prop) [DecidablePred P] : ℚ :=
  (Outcome.all.map λ o => if P o then p.prob o else 0).sum

/-- The leaf probabilities sum to one. -/
theorem prob_sum : (Outcome.all.map p.prob).sum = 1 := by
  simp [Outcome.all, prob, reanalysed]; ring

/-- The probability of garden-pathing: attentive reading times the garden-path probability. -/
theorem mass_gardenPathed : p.mass Outcome.IsGardenPathed = p.attentive * p.gardenPath := by
  simp [mass, Outcome.all, Outcome.IsGardenPathed, prob, reanalysed]; ring

/-- The probability of a regression: reanalysis that is overt. -/
theorem mass_regression : p.mass Outcome.HasRegression = p.reanalysed * (1 - p.covert) := by
  simp [mass, Outcome.all, Outcome.HasRegression, prob]; ring

/-- The probability of acceptance: the inattentive guess, the correct first pass, and the
successful reanalyses, postponement being immaterial to success. -/
def accept : ℚ := p.prob .inattentive * p.bias + p.mass Outcome.IsSuccess

theorem accept_eq :
    p.accept = (1 - p.attentive) * p.bias + p.attentive * (1 - p.gardenPath) +
      p.reanalysed * ((1 - p.covert) * p.overtSuccess + p.covert * p.covertSuccess) := by
  simp [accept, mass, Outcome.all, Outcome.IsSuccess, prob]; ring

end Params

/-! ### Reading times as a mixture -/

/-- The costs at the disambiguating region: attending, being garden-pathed, reanalysing in
situ, and launching a regression; postponed covert reanalysis is paid at the spillover region
instead. -/
structure Costs where
  attention : ℚ
  gardenPath : ℚ
  covert : ℚ
  regression : ℚ

/-- The cost a leaf pays at the disambiguating region, above non-decision time. -/
def Costs.at (k : Costs) : Outcome → ℚ
  | .inattentive => 0
  | .correctFirstPass => k.attention
  | .triage => k.attention + k.gardenPath
  | .overtSuccess | .overtFail => k.attention + k.gardenPath + k.regression
  | .covertImmediateSuccess | .covertImmediateFail => k.attention + k.gardenPath + k.covert
  | .covertPostponedSuccess | .covertPostponedFail => k.attention + k.gardenPath

/-- The mean reading time at the disambiguating region: the mixture of the leaf costs. -/
def mean (p : Params) (k : Costs) : ℚ := (Outcome.all.map λ o => p.prob o * k.at o).sum

/-- A condition mean cannot tell an effect on first-pass attachment from an effect on
reanalysis cost: two parameterizations with different garden-path probabilities and different
covert reanalysis costs have the same mean but different mixing proportions. -/
theorem mean_not_identifiable :
    ∃ (p p' : Params) (k k' : Costs), p.gardenPath ≠ p'.gardenPath ∧ k.covert ≠ k'.covert ∧
      mean p k = mean p' k' ∧
      p.prob .covertImmediateSuccess ≠ p'.prob .covertImmediateSuccess :=
  ⟨⟨1, 1/2, 0, 1, 0, 1, 1, 1⟩, ⟨1, 1/4, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 400, 0⟩, ⟨0, 0, 800, 0⟩,
    by norm_num, by norm_num, by norm_num [mean, Outcome.all, Params.prob, Params.reanalysed,
      Costs.at], by norm_num [Params.prob, Params.reanalysed]⟩

end PaapeVasishth2026
