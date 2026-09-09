import Linglib.Semantics.Polarity.Licensing
import Linglib.Fragments.English.PolarityItems
import Mathlib.Probability.ConditionalProbability

/-!
# Denić et al. (2021): The influence of polarity items on inferential judgments

This file formalizes the four experiments of [denic-homer-rothschild-chemla-2021] on whether
polarity items change the monotonicity inferences people draw. Negative polarity items are
licensed in downward-entailing environments and not in upward-entailing ones,
[fauconnier-1975] and [ladusaw-1979], and positive polarity items take no narrow scope in the
former, so a polarity item is at least a probabilistic signal of monotonicity, and the
experiments ask whether its presence in a premise moves the ratings of the subset-to-superset
and superset-to-subset inferences that [szabolcsi-bott-mcelree-2008] had found unaffected. The
environments are three upward-entailing, three downward-entailing, two non-monotone and two
doubly negative ones, (14) to (24); their monotonicity is read off the natural-logic signatures
of the licensing substrate, so that the doubly negative environments, a downward-entailing
operator inside another, come out upward entailing globally and downward entailing at the
position of the item, where it is licensed, §5, and the valid inference direction of each
environment follows. The ratings of the two directions are combined into a directional rating,
the upward rating and the complement of the downward one, which averages out any yes-bias a
polarity item might introduce, §3.2. In non-monotone environments a negative polarity item
lowers the directional rating in every experiment and in the meta-analysis, and in doubly
negative environments a positive polarity item raises it, in Experiment 3 and the meta-analysis,
§8.1, while the plain environments show smaller or no effects, §8.3: the environments in which
negative polarity items are licensed are all perceived as not upward entailing, even the doubly
negative ones, §9, as [chemla-homer-rothschild-2011] had found subjective monotonicity to
predict acceptability. Of the three routes from polarity items to inferences, §10, the meaning
route rests on the domain widening of the scalar theories, (30), under which the sentence with
the item is stronger and the widened predicate no less probable given any evidence, (34).

## Implementation notes

The signatures of the downward-entailing and doubly negative environments are the Strawson
signatures of the licensing contexts of `LicensingContext.properties`; the upward-entailing
ones carry the monotone signature and the non-monotone ones the signature of arbitrary
functions, the coarsest consistent with the paper's classification. The results are the
directional means and the posterior probabilities of the effects as the paper reports them, with
its criterion that a posterior above 0.975 corresponds to a two-sided test at the 0.05 level and
above 0.95 to a one-sided one, §3.3; standard deviations and credible intervals are not carried,
and the analyses by inferential dimension of Table 1 and the interactions of §8.3 are recorded in
the data only. Locators follow the penultimate draft, lingbuzz 005977, whose section structure
is the published article's.

## References

* [denic-homer-rothschild-chemla-2021]
* [fauconnier-1975]
* [ladusaw-1979]
* [szabolcsi-bott-mcelree-2008]
* [chemla-homer-rothschild-2011]
-/

namespace DenicEtAl2021

open NaturalLogic Polarity English.PolarityItems

/-! ### Environments and their monotonicity, §3.1.2 and §5 -/

/-- The paper's four classes of environment. -/
inductive Kind
  | UE
  | DE
  | NM
  | DN
  deriving DecidableEq, Repr

/-- The ten environments of Experiments 1 to 4, (14) to (24). -/
inductive Environment
  | positive
  | every
  | many
  | negative
  | no
  | few
  | exactly12
  | only12
  | everyNot
  | noWithout
  deriving DecidableEq, Fintype, Repr

/-- The class the paper assigns each environment. -/
def Environment.kind : Environment → Kind
  | .positive | .every | .many => .UE
  | .negative | .no | .few => .DE
  | .exactly12 | .only12 => .NM
  | .everyNot | .noWithout => .DN

/-- The signature of the position of the polarity item in each environment: the licensing
substrate's rows for the downward-entailing ones, the product of two such rows for the doubly
negative ones, and the monotone and the arbitrary signature for the upward-entailing and
non-monotone ones. -/
def Environment.signature : Environment → Signature
  | .positive | .every | .many => .mono
  | .negative => LicensingContext.negation.properties.strawsonSignature
  | .no => LicensingContext.nobody.properties.strawsonSignature
  | .few => LicensingContext.few.properties.strawsonSignature
  | .exactly12 | .only12 => .all
  | .everyNot => Signature.contextProjectivity
      [LicensingContext.universalRestrictor.properties.strawsonSignature,
        LicensingContext.negation.properties.strawsonSignature]
  | .noWithout => Signature.contextProjectivity
      [LicensingContext.nobody.properties.strawsonSignature,
        LicensingContext.withoutClause.properties.strawsonSignature]

/-- The polarity of a class: the doubly negative environments are upward entailing, §5. -/
def Kind.polarity : Kind → ContextPolarity
  | .UE | .DN => .upward
  | .DE => .downward
  | .NM => .nonMonotonic

/-- The paper's classification is the polarity of the signatures. -/
theorem polarity_eq (e : Environment) : e.signature.toContextPolarity = e.kind.polarity := by
  cases e <;> decide

/-- §5: a doubly negative environment is upward entailing globally, the composition of two
downward-entailing operators, while the position of the item inside the inner operator is
downward entailing. -/
theorem dn_global_upward_local_downward :
    Environment.everyNot.signature.toContextPolarity = .upward ∧
      LicensingContext.universalRestrictor.properties.strawsonSignature.toContextPolarity =
        .downward ∧
      LicensingContext.negation.properties.strawsonSignature.toContextPolarity = .downward ∧
      Environment.noWithout.signature.toContextPolarity = .upward ∧
      LicensingContext.withoutClause.properties.strawsonSignature.toContextPolarity =
        .downward := by
  decide

/-- The two orders of a superset–subset pair of verb phrases. -/
inductive Direction
  | subsetToSuperset
  | supersetToSubset
  deriving DecidableEq, Repr

/-- An inference is valid in an environment when its signature projects forward entailment
accordingly: preserved for the subset-to-superset direction, reversed for the other. -/
def Valid (e : Environment) : Direction → Prop
  | .subsetToSuperset => Signature.project .forward e.signature = .forward
  | .supersetToSubset => Signature.project .forward e.signature = .reverse

instance (e : Environment) : DecidablePred (Valid e) := λ d => by
  cases d <;> unfold Valid <;> infer_instance

/-- §3.1.2 and §6.1.2: only the superset-to-subset inference is valid in a downward-entailing
environment, only the subset-to-superset one in an upward-entailing or doubly negative one,
and neither in a non-monotone one. -/
theorem valid_iff (e : Environment) (d : Direction) :
    Valid e d ↔ (e.kind.polarity = .upward ∧ d = .subsetToSuperset) ∨
      (e.kind.polarity = .downward ∧ d = .supersetToSubset) := by
  cases e <;> cases d <;> decide

/-- The tested negative polarity items, *any*, *ever* and *at all*, are licensed by the
substrate in the three downward-entailing environments and in the inner operators of the two
doubly negative ones, where the local monotonicity is downward, §5. -/
theorem npis_licensed :
    ∀ c ∈ [LicensingContext.negation, .nobody, .few, .universalRestrictor, .withoutClause],
      c.licenses any ∧ c.licenses ever ∧ c.licenses atAll := by
  decide

/-! ### Directional ratings, §3.2 -/

/-- The directional rating of an inference: the rating of a subset-to-superset inference as
given, that of a superset-to-subset inference reversed, so that both measure how far upward
inferences follow and downward ones do not. -/
def directional : Direction → ℚ → ℚ
  | .subsetToSuperset, r => r
  | .supersetToSubset, r => 100 - r

/-- A yes-bias raising the ratings of both directions by the same amount leaves the mean
directional rating unchanged, the motivation for the measure. -/
theorem directional_bias_cancels (u d b : ℚ) :
    (directional .subsetToSuperset (u + b) + directional .supersetToSubset (d + b)) / 2 =
      (directional .subsetToSuperset u + directional .supersetToSubset d) / 2 := by
  simp only [directional]; ring

/-! ### Results, §3.2, §4.2, §6.2, §7.2 and §8.1 -/

/-- The polarity item condition of a premise. -/
inductive PI
  | npi
  | ppi
  | noPI
  deriving DecidableEq, Repr

/-- The experiments testing the non-monotone environments. -/
inductive Test
  | exp1
  | exp2
  | exp3
  | exp4
  deriving DecidableEq, Repr

/-- The experiments testing the doubly negative environments. -/
inductive DNTest
  | exp3
  | exp4
  deriving DecidableEq, Repr

/-- Mean directional ratings, in percent, of the non-monotone environments by polarity item
condition. -/
def nmMean : Test → PI → ℚ
  | .exp1, .npi => 55.3
  | .exp1, .ppi => 59.7
  | .exp1, .noPI => 60
  | .exp2, .npi => 54.7
  | .exp2, .ppi => 60.1
  | .exp2, .noPI => 59.2
  | .exp3, .npi => 55.9
  | .exp3, .ppi => 57.9
  | .exp3, .noPI => 57.1
  | .exp4, .npi => 56.3
  | .exp4, .ppi => 56.4
  | .exp4, .noPI => 59.3

/-- Mean directional ratings, in percent, of the doubly negative environments by polarity
item condition. -/
def dnMean : DNTest → PI → ℚ
  | .exp3, .npi => 53.7
  | .exp3, .ppi => 61.8
  | .exp3, .noPI => 56.9
  | .exp4, .npi => 52.6
  | .exp4, .ppi => 61.6
  | .exp4, .noPI => 56.3

/-- A negative polarity item lowers the mean directional rating of the non-monotone
environments in every experiment. -/
theorem npi_lowers_nm (t : Test) : nmMean t .npi < nmMean t .noPI := by
  cases t <;> norm_num [nmMean]

/-- A positive polarity item raises the mean directional rating of the doubly negative
environments in both experiments testing them. -/
theorem ppi_raises_dn (t : DNTest) : dnMean t .noPI < dnMean t .ppi := by
  cases t <;> norm_num [dnMean]

/-- The analyses of the non-monotone environments: the four experiments and their
meta-analysis. -/
inductive Analysis
  | exp1
  | exp2
  | exp3
  | exp4
  | pooled
  deriving DecidableEq, Repr

/-- The analyses of the doubly negative environments. -/
inductive DNAnalysis
  | exp3
  | exp4
  | pooled
  deriving DecidableEq, Repr

/-- The posterior probability that a negative polarity item decreases, and that a positive one
increases, the directional rating in the non-monotone environments. -/
def nmPosterior : Analysis → Bool → ℚ
  | .exp1, true => 0.999
  | .exp1, false => 0.552
  | .exp2, true => 0.999
  | .exp2, false => 0.84
  | .exp3, true => 0.965
  | .exp3, false => 0.88
  | .exp4, true => 0.984
  | .exp4, false => 0.104
  | .pooled, true => 0.999
  | .pooled, false => 0.817

/-- The same posteriors for the doubly negative environments. -/
def dnPosterior : DNAnalysis → Bool → ℚ
  | .exp3, true => 0.887
  | .exp3, false => 0.998
  | .exp4, true => 0.924
  | .exp4, false => 0.838
  | .pooled, true => 0.96
  | .pooled, false => 0.999

/-- §3.3: a posterior above 0.975 corresponds to a two-sided test at the 0.05 level. -/
def TwoSided (p : ℚ) : Prop := 0.975 < p

/-- §3.3: a posterior above 0.95 corresponds to a one-sided test at the 0.05 level. -/
def OneSided (p : ℚ) : Prop := 0.95 < p

/-- Negative polarity items in non-monotone environments: strong evidence in every
experiment, at the two-sided level in Experiments 1, 2 and 4 and in the meta-analysis. -/
theorem npi_nm_evidence :
    (∀ a, OneSided (nmPosterior a true)) ∧ TwoSided (nmPosterior .exp1 true) ∧
      TwoSided (nmPosterior .exp2 true) ∧ TwoSided (nmPosterior .exp4 true) ∧
      TwoSided (nmPosterior .pooled true) :=
  ⟨λ a => by cases a <;> norm_num [nmPosterior, OneSided], by norm_num [nmPosterior, TwoSided],
    by norm_num [nmPosterior, TwoSided], by norm_num [nmPosterior, TwoSided],
    by norm_num [nmPosterior, TwoSided]⟩

/-- Positive polarity items in non-monotone environments: no evidence at either level in any
analysis. -/
theorem ppi_nm_no_evidence (a : Analysis) : ¬ OneSided (nmPosterior a false) := by
  cases a <;> norm_num [nmPosterior, OneSided]

/-- Positive polarity items in doubly negative environments: strong evidence in Experiment 3
and in the meta-analysis, none in Experiment 4. -/
theorem ppi_dn_evidence :
    TwoSided (dnPosterior .exp3 false) ∧ TwoSided (dnPosterior .pooled false) ∧
      ¬ OneSided (dnPosterior .exp4 false) := by
  norm_num [dnPosterior, TwoSided, OneSided]

/-- Negative polarity items in doubly negative environments: evidence only from the
meta-analysis, and only at the one-sided level, §8.1. -/
theorem npi_dn_evidence :
    OneSided (dnPosterior .pooled true) ∧ ¬ TwoSided (dnPosterior .pooled true) ∧
      ¬ OneSided (dnPosterior .exp3 true) ∧ ¬ OneSided (dnPosterior .exp4 true) := by
  norm_num [dnPosterior, TwoSided, OneSided]

/-! ### The meaning route, §10.2 -/

/-- Under the scalar theories, §1, an item widens the domain of its predicate, (30), so in an
antitone position the sentence with the item is the stronger one: the licensing condition of
those theories. -/
theorem npi_strengthens {α β : Type*} [Preorder α] [Preorder β] {f : α → β}
    (hf : Antitone f) {birds anyBirds : α} (h : birds ≤ anyBirds) : f anyBirds ≤ f birds :=
  hf h

open MeasureTheory ProbabilityTheory in
/-- (34): the widened predicate is at least as probable as the plain one given any evidence,
the premise of the probabilistic version of the meaning route. -/
theorem widening_condProb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (doves birds anyBirds : Set Ω) (h : birds ⊆ anyBirds) :
    μ[birds | doves] ≤ μ[anyBirds | doves] :=
  measure_mono h

end DenicEtAl2021
