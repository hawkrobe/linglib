import Linglib.Data.ScalarDiversity.VanTielEtAl2016

/-!
# [van-tiel-geurts-2016] — Scalar Diversity

Do all scalar expressions yield scalar implicatures at comparable rates? The
*uniformity assumption* — implicit in decades of SI research fixated on
⟨some, all⟩ and ⟨or, and⟩ — predicts yes. [van-tiel-geurts-2016] show it is
false: across 43 lexical scales the rate of upper-bounding inference ranges
continuously from 4% (⟨content, happy⟩) to 100% (⟨cheap, free⟩), and ⟨some, all⟩
turns out to be an *extreme* case, not a representative one.

The analytical question is what explains the variation. The paper contrasts two
families of factor. *Availability* (how likely the hearer thinks the speaker
considered the stronger alternative) is operationalised four ways — association
strength (cloze), grammatical class, word frequency, LSA relatedness — and **none**
predicts the rates. *Distinctness* (how easy the scalemates are to tell apart) is
operationalised two ways — semantic distance and boundedness — and **both** do.
The two-stage model of scalar inference explains why: diversity lives in the
*competence* step, which is better warranted when the scalemates are distinct.

## Data
The 43-scale matrix (Table 3) is canonical JSON at
`Data/ScalarDiversity/VanTielEtAl2016.json`, generated into kernel-reducible
typed `ScaleDatum` literals (`Data/ScalarDiversity/VanTielEtAl2016.lean`, via
`scripts/gen_scalardiversity.py`); `Studies/Ronai2024` reuses the same typed
`Scales.*` rows. The schema is `Data.ScalarDiversity.Schema`.

## Main results
* `si_range` — SI rates span 4–100% (scalar diversity; uniformity is false).
* `someAll_above_median` — the ⟨some, all⟩ workhorse sits near the ceiling.
* `bounded_total_exceeds_nonbounded` — bounded scales project far more (the
  dominant distinctness factor, read off the SI data).
* `closed_class_subsumes_bounded` — grammatical class (an availability proxy) is
  confounded with boundedness, explaining its non-significance.
* `two_stage_inference`, `primary_underdetermines_si` — the Soames/Sauerland
  epistemic model: diversity is variation in whether the competence step fires.

## Empirical findings (prose)
Experiment 1 (inference task, neutral content, N = 25) and Experiment 2
(non-neutral content, N = 29) correlate at r = .91. The mixed model (Table 5)
found only the distinctness measures significant — semantic distance (β = 0.65,
Z = 2.36, p = .018, R² = .027) and boundedness (β = −1.87, Z = −4.72, p < .001,
R² = .108) — and all four availability measures null: association strength
(β = 0.16, p = .611), grammatical class (β = −0.38, p = .606), relative frequency
(β = −0.15, p = .461), LSA (β = 0.01, p = .355). Full model R² = .52 (.22 fixed);
boundedness alone ≈ 10× the availability variance combined.
-/

namespace VanTielEtAl2016

/-! ### Partitions and counts -/

/-- Number of scales tested. -/
def numScales : Nat := allScales.length

/-- Bounded scales (stronger term denotes an endpoint). -/
def boundedScales : List ScaleDatum := allScales.filter (·.bounded)

/-- Non-bounded scales. -/
def nonBoundedScales : List ScaleDatum := allScales.filter (!·.bounded)

/-- Number of bounded scales. -/
def numBounded : Nat := boundedScales.length

/-- Number of non-bounded scales. -/
def numNonBounded : Nat := nonBoundedScales.length

#guard numScales == 43
#guard numBounded == 21
#guard numNonBounded == 22
#guard numBounded + numNonBounded == numScales

/-! ### Scalar diversity is real -/

/-- SI rates span 96 percentage points: 4% to 100%. ⟨content, happy⟩ is the
    floor, ⟨cheap, free⟩ the ceiling — the uniformity assumption is false. -/
theorem si_range :
    allScales.all (·.siRateExp1 ≥ 4) ∧
    allScales.all (·.siRateExp1 ≤ 100) ∧
    allScales.any (·.siRateExp1 == 4) ∧
    allScales.any (·.siRateExp1 == 100) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⟨some, all⟩ — the "workhorse" of SI research — sits near the top at 96%, far
    above the mean. Generalizing from ⟨some, all⟩ to all scales is unjustified. -/
theorem someAll_above_median : Scales.someAll.siRateExp1 > 50 := by decide

/-- Experiments 1 and 2 agree directionally: no scale reverses from high to low
    or vice versa (>50% in one experiment and <15% in the other). -/
theorem exp1_exp2_directional_agreement :
    allScales.all (fun s =>
      !(s.siRateExp1 > 50 && s.siRateExp2 < 15) &&
      !(s.siRateExp2 > 50 && s.siRateExp1 < 15)) = true := by
  decide

/-! ### Explaining diversity: distinctness, not availability

Of the six predictors in the mixed model (Table 5), only the two *distinctness*
measures contribute; the four *availability* measures are null (see the prose
findings above). The qualitative content is carried structurally here:
`bounded_total_exceeds_nonbounded` (boundedness, the dominant distinctness
factor) and `closed_class_subsumes_bounded` (why the grammatical-class
availability proxy washes out once boundedness is in the model). -/

/-- Bounded scales yield far more SIs than non-bounded scales: their total SI
    rate (Exp 1) exceeds the non-bounded total even though there are fewer of
    them (the paper reports means ≈ 62% vs ≈ 25%). The dominant factor, read
    directly off the per-scale data. -/
theorem bounded_total_exceeds_nonbounded :
    (boundedScales.map (·.siRateExp1)).foldl (· + ·) 0 >
    (nonBoundedScales.map (·.siRateExp1)).foldl (· + ·) 0 := by decide

/-- Every closed-class scale in this sample is also bounded. So the apparent
    grammatical-class effect is subsumed by boundedness — why class is a
    non-significant predictor once boundedness is in the model. -/
theorem closed_class_subsumes_bounded :
    allScales.all (fun s => !s.category.isClosedClass || s.bounded) = true := by
  decide

/-! ### The two-stage model of scalar inference (§6)

Following [soames-1982] and [sauerland-2004], a scalar inference from φ[α] to
¬φ[β] is computed in two steps. The *primary* step yields that the speaker does
not believe the stronger alternative (¬Bel_S φ[β]). A *competence* assumption —
the speaker is opinionated about φ[β] (Bel_S φ[β] ∨ Bel_S ¬φ[β]) — upgrades this
to the scalar inference Bel_S ¬φ[β]. Scalar diversity is variation in whether the
competence step fires: it is better warranted when the scalemates are *distinct*
(bounded or semantically distant), which is exactly why distinctness, not
availability, predicts the rates. -/

/-- The two-stage (epistemic) model: the primary inference together with the
    competence assumption *yields* the scalar inference. The conclusion is derived
    from the premises, not stipulated. -/
theorem two_stage_inference {belStronger belNotStronger : Prop}
    (primary : ¬ belStronger) (competence : belStronger ∨ belNotStronger) :
    belNotStronger :=
  competence.resolve_left primary

/-- Competence is load-bearing: the primary step alone leaves the stronger
    alternative epistemically open (the speaker may be agnostic), so no scalar
    inference follows. Cross-scale variation in this step is where diversity
    lives. -/
theorem primary_underdetermines_si :
    ∃ belStronger belNotStronger : Prop, ¬ belStronger ∧ ¬ belNotStronger :=
  ⟨False, False, not_false, not_false⟩

end VanTielEtAl2016
