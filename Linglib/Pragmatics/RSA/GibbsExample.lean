import Mathlib.Probability.UniformOn
import Linglib.Pragmatics.RSA.Gibbs

/-!
# Worked example: the Frank–Goodman reference-game speaker  [frank-goodman-2012]

The canonical RSA result — *the pragmatic speaker prefers the more informative
description* — worked end-to-end on the Measure/Kernel-native foundation of
`Linglib.Pragmatics.RSA.Gibbs`. It is the template for Measure-native RSA
studies: the speaker is `RSA.Gibbs.speaker`, a `MeasureTheory.Measure.tilted`
Gibbs measure over a probability prior (here `ProbabilityTheory.uniformOn`), and
the predictions are theorems about that measure rather than about a bespoke
`PMF.softmax` reimplementation.

## Scenario

A speaker refers to a target object with one of two *true* descriptions. Because
every alternative applies to the target, the literal listener never assigns the
target probability `0`, so the informativity utility `log L0` is finite (the
example is log-`0`-free):

* `blue` — applies to two objects, so the literal listener splits its mass and
  lands on the target with probability `1/2`;
* `circle` — uniquely identifies the target, so the literal listener is certain
  (`1`).

The informativity utility is `score u = log (L0target u)` (rationality `α = 1`,
no cost term), and `rgSpeaker = speaker (uniformOn univ) score`.

## Main statements

* `prefers_circle` — the speaker assigns strictly more mass to `circle` than to
  `blue`: it prefers the uniquely-identifying description. A direct instance of
  `RSA.Gibbs.speaker_lt_iff_score_lt`, reducing to `log (1/2) < log 1`.
* `rgSpeaker_isGreatest` — the reference-game speaker is the **rational
  optimizer**: it attains the greatest expected-utility-minus-KL-cost over all
  candidate utterance distributions. A direct instance of
  `RSA.Gibbs.speaker_isGreatest` (the Gibbs / Donsker–Varadhan principle).
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace RSA.Gibbs.FrankGoodman

/-- The two true descriptions of the target in the reference game. -/
inductive Utterance
  | blue
  | circle
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Utterance := ⊤

instance : MeasurableSingletonClass Utterance := ⟨fun _ => trivial⟩

instance : Inhabited Utterance := ⟨.circle⟩

/-- Literal-listener probability of the target given each (true) utterance:
`blue` applies to two objects (`1/2`), `circle` uniquely identifies (`1`). -/
noncomputable def L0target : Utterance → ℝ
  | .blue => 1 / 2
  | .circle => 1

/-- Informativity utility (rationality `α = 1`, no cost): the log of the
literal-listener target probability, `score u = log (L0(target | u))`. -/
noncomputable def score : Utterance → ℝ := fun u => Real.log (L0target u)

/-- The reference-game speaker as a Gibbs measure over the uniform utterance
prior: `RSA.Gibbs.speaker (uniformOn univ) score`. -/
noncomputable def rgSpeaker : Measure Utterance :=
  RSA.Gibbs.speaker (uniformOn (Set.univ : Set Utterance)) score

/-- **The speaker prefers the uniquely-identifying description**: it assigns
strictly more mass to `circle` than to `blue`. The measure theory is hidden in
`RSA.Gibbs.speaker_uniformOn_lt_iff_score_lt` — the prediction reduces in one `rw`
to the informativity comparison `log (1/2) < log 1`. -/
theorem prefers_circle : rgSpeaker {Utterance.blue} < rgSpeaker {Utterance.circle} := by
  rw [rgSpeaker, RSA.Gibbs.speaker_uniformOn_lt_iff_score_lt]
  show Real.log (L0target .blue) < Real.log (L0target .circle)
  rw [L0target, L0target, Real.log_one]
  exact Real.log_neg (by norm_num) (by norm_num)

/-- **The reference-game speaker is the rational optimizer**: among all candidate
utterance distributions absolutely continuous w.r.t. the uniform prior, the
speaker attains the greatest expected-utility-minus-KL-cost
`q ↦ 𝔼_q[score] − KL(q ‖ uniformOn univ)`, the optimum being the free energy
`(uniformOn univ).logIntegralExp score`. A direct instance of the Gibbs /
Donsker–Varadhan variational principle `RSA.Gibbs.speaker_isGreatest`; all
integrability hypotheses are automatic over the finite utterance type. -/
theorem rgSpeaker_isGreatest :
    IsGreatest
      {x : ℝ | ∃ q : Measure Utterance, IsProbabilityMeasure q ∧
        q ≪ uniformOn (Set.univ : Set Utterance) ∧
        Integrable (llr q (uniformOn (Set.univ : Set Utterance))) q ∧
        Integrable score q ∧
        x = (∫ u, score u ∂q) - (klDiv q (uniformOn (Set.univ : Set Utterance))).toReal}
      ((uniformOn (Set.univ : Set Utterance)).logIntegralExp score) := by
  haveI : IsFiniteMeasure
      (RSA.Gibbs.speaker (uniformOn (Set.univ : Set Utterance)) score) :=
    inferInstanceAs (IsFiniteMeasure ((uniformOn (Set.univ : Set Utterance)).tilted score))
  exact RSA.Gibbs.speaker_isGreatest (uniformOn (Set.univ : Set Utterance)) score
    Integrable.of_finite Integrable.of_finite Integrable.of_finite

end RSA.Gibbs.FrankGoodman
