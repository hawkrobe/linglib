import Linglib.Core.Probability.Confirmation
import Linglib.Semantics.Conditionals.Probabilistic
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{chung-mascarenhas-2024} — Modality, expected utility, and hypothesis testing

A single lexical entry for `must`, parameterized by a set `R` of
"relevant propositions". For deontics, `R = R_D` (rules/ideals);
`E[μ_R ∣ φ]` is then the expected utility of `φ`. For epistemics,
`R = R_E` (relevant known facts/evidence); `E[μ_R ∣ φ]` is what C&M
call the *explanatory value* of `φ`, equal to the sum of likelihoods
`Σ_i P(e_i ∣ φ)` (their eq. 12, which follows by definition once
`μ_R = Confirmation.countMeasure R`).

Headline operator (C&M (6)):

  ⟦must φ⟧^w = (E_w[μ_R ∣ φ] > θ) ∧ ∀ψ ∈ Alt(φ). (E_w[μ_R ∣ ψ] ≤ θ)

## What this file contains

* `mustCM`, `oughtCM`, `mustCMWithPlausibility` — the operator, the
  Sloman-style weak-necessity variant, and C&M §5's plausibility patch
  as a separate `def` (so the patch stays reviewable).
* `Miners` — the @cite{kolodny-macfarlane-2010} deontic scenario as a
  six-world PMF setup with `idealsRD` (paper notation `R_D`).
* `ModalLinda` — C&M's modal-conjunction-fallacy numerical claims as ℚ
  values with the headline inequality `explanatoryValueTeller <
  explanatoryValueFeministTeller` proven (= the modal conjunction
  fallacy at the operator's numerical level).
* `ModalLawyers` — same shape for C&M's base-rate-neglect prediction.
* `ya_exhaustification_yields_mustCM` — the Korean compositional
  derivation (C&M §4): the `-(e)ya` exhaustifier IS the second conjunct
  of `mustCM`.

The Linda and Lawyers files do not set up full PMFs (the joint
distributions over hypothesis-and-evidence are not pinned down by
C&M's text). The numerical-claim level is sufficient to document
the operator's predicted direction without committing to modeling
choices not in the paper.

## Cross-references

* `Studies/VonFintelIatridou2005.lean` §6 —
  C&M's exhaustification realises @cite{sloman-1970}'s "only
  candidate" / vF&I's *have-to* vs *ought-to* distinction.
* `Studies/Lassiter2017.lean` — Lassiter's `want`
  on the same EV substrate (`PMF.condExpect`); C&M's `must` differs
  by (i) the exhaustification clause, (ii) count-valued `μ_R` vs
  Lassiter's free-form `value`, (iii) likelihood-based epistemic
  reading vs Lassiter's posterior.
-/

namespace ChungMascarenhas2024

open PMF PMF.Confirmation
open scoped ENNReal
open BigOperators

/-! ### The operator -/

/-- @cite{chung-mascarenhas-2024} (6): `must φ` iff `E_w[μ_R ∣ φ]`
exceeds the contextual threshold `θ` AND no alternative does. -/
def mustCM {W : Type*} [Fintype W] (p : PMF W) (R : Finset (Set W))
    (φ : Set W) (alts : Finset (Set W)) (θ : ℝ≥0∞) : Prop :=
  sumLikelihoods p R φ > θ ∧ ∀ ψ ∈ alts, sumLikelihoods p R ψ ≤ θ

/-- The @cite{sloman-1970}-flavored *ought*: drop the exhaustification
clause. @cite{vonfintel-iatridou-2005} §6 identifies this with the
weak-necessity modal across teleological and deontic flavors. -/
def oughtCM {W : Type*} [Fintype W] (p : PMF W) (R : Finset (Set W))
    (φ : Set W) (θ : ℝ≥0∞) : Prop :=
  sumLikelihoods p R φ > θ

/-- @cite{chung-mascarenhas-2024} §5: `mustCM` with the additional
plausibility requirement `P(φ) ≥ θplaus`. Kept as a separate `def`
rather than baked into `mustCM`, so the §5 patch (which C&M concede
is not derived from the core) stays reviewable. -/
def mustCMWithPlausibility {W : Type*} [Fintype W] (p : PMF W)
    (R : Finset (Set W)) (φ : Set W) (alts : Finset (Set W))
    (θ θplaus : ℝ≥0∞) : Prop :=
  mustCM p R φ alts θ ∧ p.probOfSet φ ≥ θplaus

/-! ### Miners scenario @cite{kolodny-macfarlane-2010}

Six worlds = (block-action) × (miners-location):
* `w0` = block-A, miners-in-A: 10 saved
* `w1` = block-A, miners-in-B:  0 saved
* `w2` = block-B, miners-in-A:  0 saved
* `w3` = block-B, miners-in-B: 10 saved
* `w4` = block-neither, miners-in-A: 9 saved
* `w5` = block-neither, miners-in-B: 9 saved

Uniform prior over the 6 worlds — equivalent (under independence of
action and location) to a uniform prior on miners-location with
action a free choice. `idealsRD` (paper notation `R_D`) is
`{1 saved, 2 saved, ..., 10 saved}`, following
@cite{cariani-kaufmann-kaufmann-2013}. -/

namespace Miners

/-- World type: six (action × miners-location) combinations. -/
abbrev World := Fin 6

/-- Block-A. -/
def blockA : Set World := λ w => w.val = 0 ∨ w.val = 1
/-- Block-B. -/
def blockB : Set World := λ w => w.val = 2 ∨ w.val = 3
/-- Block-neither. -/
def blockNeither : Set World := λ w => w.val = 4 ∨ w.val = 5

/-- Miners in shaft A. -/
def minersInA : Set World := λ w => w.val = 0 ∨ w.val = 2 ∨ w.val = 4
/-- Miners in shaft B. -/
def minersInB : Set World := λ w => w.val = 1 ∨ w.val = 3 ∨ w.val = 5

/-- Miners saved at each world (C&M Table 1). -/
def minersSaved : World → ℕ := λ w =>
  match w.val with
  | 0 => 10
  | 1 => 0
  | 2 => 0
  | 3 => 10
  | 4 => 9
  | 5 => 9
  | _ => 0

/-- Uniform PMF over the 6 worlds. -/
noncomputable def prior : PMF World := PMF.uniformOfFintype World

open Classical in
/-- The relevant-ideals set, paper notation `R_D`: the set of worlds
where at least `k` miners are saved, for `k = 1, ..., 10`.
`μ_R(w) = minersSaved w` by construction. -/
noncomputable def idealsRD : Finset (Set World) :=
  (Finset.range 10).image (λ k => {w | minersSaved w ≥ k + 1})

end Miners

/-! ### Modal Linda @cite{tversky-kahneman-1983}

C&M §3.2 + (30)/(31): the salient evidence from the Linda description
projects to two propositions about Linda — concern with social
justice (`socialJustice`) and anti-nuclear-protests participation
(`antiNuclearProtests`). Conditional probabilities given each
hypothesis:

* `P(socialJustice ∣ teller) = 0.3`, `P(antiNuclear ∣ teller) = 0.2`
* `P(socialJustice ∣ feministTeller) = 0.8`,
  `P(antiNuclear ∣ feministTeller) = 0.7`

C&M predict the modal conjunction fallacy: under any threshold `θ`
with `0.5 < θ < 1.5`, *Linda must be a feminist bank teller* is true
while *Linda must be a bank teller* is false.

We do not set up the full joint PMF over hypothesis-and-evidence
(those weights are not pinned down by C&M). The numerical-claim
level is sufficient to document the prediction. -/

namespace ModalLinda

/-- `P(socialJustice ∣ teller) = 0.3` per C&M (30). -/
def prSocialJusticeGivenTeller : ℚ := 3 / 10
/-- `P(antiNuclearProtests ∣ teller) = 0.2` per C&M (30). -/
def prAntiNuclearGivenTeller : ℚ := 2 / 10
/-- `P(socialJustice ∣ feministTeller) = 0.8` per C&M (31). -/
def prSocialJusticeGivenFeministTeller : ℚ := 8 / 10
/-- `P(antiNuclearProtests ∣ feministTeller) = 0.7` per C&M (31). -/
def prAntiNuclearGivenFeministTeller : ℚ := 7 / 10

/-- `E[μ_R ∣ teller] = 0.5` per C&M (32). -/
def explanatoryValueTeller : ℚ :=
  prSocialJusticeGivenTeller + prAntiNuclearGivenTeller

/-- `E[μ_R ∣ feministTeller] = 1.5` per C&M (33). -/
def explanatoryValueFeministTeller : ℚ :=
  prSocialJusticeGivenFeministTeller + prAntiNuclearGivenFeministTeller

/-- The modal conjunction fallacy as a numerical inequality: the
conjunctive hypothesis has strictly higher explanatory value. Any
threshold `θ` between the two predicts the *must*-conjunction true
and the bare *must*-claim false. -/
theorem feministTeller_strictly_higher :
    explanatoryValueTeller < explanatoryValueFeministTeller := by
  unfold explanatoryValueTeller explanatoryValueFeministTeller
    prSocialJusticeGivenTeller prAntiNuclearGivenTeller
    prSocialJusticeGivenFeministTeller prAntiNuclearGivenFeministTeller
  norm_num

end ModalLinda

/-! ### Modal Lawyers and Engineers @cite{kahneman-tversky-1973}

C&M §3.3 + (37)/(38): two evidence pieces from the Jack description —
absence of interest in political/social issues (`notPoliticalSocial`)
and enjoyment of mathematical puzzles (`enjoysMath`).

* `P(notPoliticalSocial ∣ engineer) = 0.78`, `P(math ∣ engineer) = 0.55`
* `P(notPoliticalSocial ∣ lawyer) = 0.35`, `P(math ∣ lawyer) = 0.28`

C&M predict base-rate neglect at the modal level: under any threshold
`θ` with `0.63 < θ < 1.33`, *Jack must be an engineer* is true
irrespective of the prior split between lawyers and engineers.

Same caveat as ModalLinda. -/

namespace ModalLawyers

/-- `P(notPoliticalSocial ∣ engineer) = 0.78` per C&M (37). -/
def prNotPoliticalGivenEngineer : ℚ := 78 / 100
/-- `P(enjoysMath ∣ engineer) = 0.55` per C&M (37). -/
def prMathGivenEngineer : ℚ := 55 / 100
/-- `P(notPoliticalSocial ∣ lawyer) = 0.35` per C&M (38). -/
def prNotPoliticalGivenLawyer : ℚ := 35 / 100
/-- `P(enjoysMath ∣ lawyer) = 0.28` per C&M (38). -/
def prMathGivenLawyer : ℚ := 28 / 100

/-- `E[μ_R ∣ engineer] = 1.33` per C&M (39). -/
def explanatoryValueEngineer : ℚ :=
  prNotPoliticalGivenEngineer + prMathGivenEngineer

/-- `E[μ_R ∣ lawyer] = 0.63` per C&M (40). -/
def explanatoryValueLawyer : ℚ :=
  prNotPoliticalGivenLawyer + prMathGivenLawyer

/-- Base-rate neglect as a numerical inequality: the engineer
hypothesis has strictly higher explanatory value than the lawyer
hypothesis, irrespective of prior. -/
theorem engineer_strictly_higher :
    explanatoryValueLawyer < explanatoryValueEngineer := by
  unfold explanatoryValueLawyer explanatoryValueEngineer
    prNotPoliticalGivenLawyer prMathGivenLawyer
    prNotPoliticalGivenEngineer prMathGivenEngineer
  norm_num

end ModalLawyers

/-! ### Compositional Korean derivation (C&M §4)

The Korean conditional evaluative `cip-ey iss-eya toy-n-ta` ('lit.
only if at home, it suffices' ≈ 'must be home') is, per C&M, the
transparent compositional form of English *must*:

1. the evaluative predicate `toy` 'EVAL' as the measure function `μ_R`
2. the conditional `if φ, EVAL` as `E_w[μ_R ∣ φ]` (their eq. 44, our
   `Semantics.Conditionals.Probabilistic.condIf`)
3. the exhaustifier `-(e)ya` 'only-if' adding the alternative
   negation: `∀ψ ∈ Alt(φ). E_w[μ_R ∣ ψ] ≤ θ`

The composition (their (48)) yields `mustCM` exactly. -/

/-- @cite{chung-mascarenhas-2024} (48): adding the `-(e)ya`
exhaustifier to `Θ(⟦if φ, EVAL⟧^w)` yields `mustCM φ`. Trivial by
definition: the exhaustifier IS the second conjunct of `mustCM`. The
named theorem documents the compositional claim for cross-references. -/
theorem ya_exhaustification_yields_mustCM {W : Type*} [Fintype W]
    (p : PMF W) (R : Finset (Set W)) (φ : Set W)
    (alts : Finset (Set W)) (θ : ℝ≥0∞)
    (hThresh : sumLikelihoods p R φ > θ)
    (hExhaust : ∀ ψ ∈ alts, sumLikelihoods p R ψ ≤ θ) :
    mustCM p R φ alts θ :=
  ⟨hThresh, hExhaust⟩

end ChungMascarenhas2024
