import Linglib.Discourse.QUD.AtIssueness
import Linglib.Pragmatics.Expressives.Basic
import Linglib.Data.Generalizations.Projectivity
import Mathlib.Tactic.Linarith

/-!
# [tonhauser-beaver-degen-2018]: How Projective Is Projective Content?

The paper's central contribution is the **Gradient Projection Principle** (GPP):

> "If content C is expressed by a constituent embedded under an
> entailment-canceling operator, then C projects to the extent that it is not
> at-issue."

It makes gradient the binary *Projection Principle* of the pragmatic account
([simons-tonhauser-beaver-roberts-2010], [roberts-2012]) — "projects iff not
at-issue". This file formalizes the principle and its structural consequences,
not the experimental tables, taking the tight reading of "to the extent that":
projection degree equals not-at-issueness. The empirical claim is a gradient
correlation with item-level variance, not this identity (cf. the dependency's
`MonotoneAntiCorrelation` docstring).

## Main definitions
* `gppProjection` — the GPP map, the complement of at-issueness (`Set.Icc.symm`).
* `pottsProjection` — [potts-2005]'s rival: CI projects maximally, at-issueness-blind.
* both are run against the pooled per-expression data
  (`Generalizations.Projectivity.allData`).

## Main results
* `gppProjection_antitone` — the GPP as order-reversal.
* `gpp_excludes_atIssue` — recovers the binary Projection Principle as a threshold collapse.
* `gpp_below_potts_of_atIssue`, `gpp_eq_potts_iff_backgrounded` — contra
  [potts-2005]: the accounts agree only on fully-backgrounded content.
* `gpp_beats_potts_below_diagonal` — on low-projectivity items the GPP beats Potts.

## Implementation notes
Degrees and thresholds are the `Rat01` types from `Discourse.AtIssueness`; the GPP
map is the `Rat01` complement. Potts's maximal projection is grounded in
`Pragmatics.Expressives.TwoDimProp.ci_projects_through_neg`.
-/

namespace TonhauserBeaverDegen2018

open Discourse.AtIssueness
open Core.Order (Rat01)
open Pragmatics.Expressives
open Generalizations.Projectivity

/-! ### The Gradient Projection Principle -/

/-- The GPP map: projection degree is the complement of at-issueness — content
    projects to the extent it is not at-issue ([tonhauser-beaver-degen-2018]). -/
def gppProjection (ai : AtIssuenessDegree) : ProjectivityDegree := Set.Icc.symm ai

/-- The GPP as order-reversal: more at-issue content is no more projective. -/
theorem gppProjection_antitone : Antitone gppProjection := Set.Icc.symm_antitone

/-- Fully not-at-issue content (at-issueness `0`) projects maximally. -/
theorem gppProjection_zero : gppProjection 0 = 1 := Set.Icc.symm_zero

/-- Fully at-issue content (at-issueness `1`) does not project. -/
theorem gppProjection_one : gppProjection 1 = 0 := Set.Icc.symm_one

/-! ### Recovering the binary Projection Principle

The binary principle ([simons-tonhauser-beaver-roberts-2010]) — projects iff not
at-issue — is the threshold collapse of the gradient GPP. -/

/-- The GPP projects past `θ` iff at-issueness is below the complementary threshold. -/
theorem gpp_projects_iff (ai θ : Rat01) :
    isProjective (gppProjection ai) θ ↔ ai.val < (Set.Icc.symm θ).val := by
  simp only [isProjective, Core.Order.Comparison.mem_over,
    Core.Order.Comparison.rel, gppProjection, Set.Icc.coe_symm_eq]
  constructor <;> intro h <;> linarith

/-- The binary Projection Principle: never both at-issue and projecting at
    complementary thresholds. -/
theorem gpp_excludes_atIssue (ai θ : Rat01) :
    ¬ (isAtIssue ai (Set.Icc.symm θ) ∧ isProjective (gppProjection ai) θ) := by
  rintro ⟨ha, hp⟩
  simp only [isAtIssue, Core.Order.Comparison.mem_over,
    Core.Order.Comparison.rel, Set.Icc.coe_symm_eq] at ha
  rw [gpp_projects_iff, Set.Icc.coe_symm_eq] at hp
  linarith

/-! ### Contra Potts

[potts-2005] predicts CI content (appositives, NRRCs, expressives) projects
maximally and obligatorily — its CI dimension is unchanged by every
entailment-canceling operator. The GPP ties projection to at-issueness, so any
at-issue content projects below the ceiling; the two agree only for
fully-backgrounded content. -/

/-- [potts-2005]'s prediction: CI content projects maximally (degree `1`),
    regardless of at-issueness. -/
def pottsProjection (_ : AtIssuenessDegree) : ProjectivityDegree := 1

@[simp] theorem pottsProjection_val (ai : AtIssuenessDegree) :
    (pottsProjection ai).val = 1 := rfl

/-- Potts's prediction is at-issueness-blind — the same for all content, which
    the GPP denies. -/
theorem potts_atIssue_blind (ai₁ ai₂ : AtIssuenessDegree) :
    pottsProjection ai₁ = pottsProjection ai₂ := rfl

/-- Potts's maximal projection abstracts the operator-invariance of the CI
    dimension: negation leaves CI content unchanged ([potts-2005]). -/
theorem potts_ci_invariant_under_neg {W : Type*} (p : TwoDimProp W) :
    (TwoDimProp.neg p).ci = p.ci := TwoDimProp.ci_projects_through_neg p

/-- Contra [potts-2005]: any at-issue content (at-issueness `> 0`) projects
    strictly below Potts's ceiling — the structural form of "appositives are not
    maximally projective". -/
theorem gpp_below_potts_of_atIssue {ai : AtIssuenessDegree} (h : 0 < ai.val) :
    (gppProjection ai).val < (pottsProjection ai).val := by
  simp only [gppProjection, Set.Icc.coe_symm_eq, pottsProjection_val]; linarith

/-- The GPP and Potts agree iff the content is fully backgrounded (at-issueness `0`). -/
theorem gpp_eq_potts_iff_backgrounded (ai : AtIssuenessDegree) :
    gppProjection ai = pottsProjection ai ↔ ai = 0 :=
  Set.Icc.symm_eq_one

/-- Potts files appositives in the independent CI dimension — the source of the
    maximal-projection prediction the GPP refines. -/
theorem appositive_potts_independent : appositiveProperties.independent = true := rfl

/-! ### The GPP as a `MonotoneAntiCorrelation`

`Discourse.AtIssueness.MonotoneAntiCorrelation` (built for this paper, consumed by
`Studies/SolstadBott2024`) bundles anti-correlated pairs; the GPP produces one
from any list of at-issueness values. -/

/-- Any list of at-issueness values, paired with their GPP projection, forms a
    `MonotoneAntiCorrelation`. -/
def gppAntiCorrelation (ais : List ℚ) : MonotoneAntiCorrelation where
  pairs := ais.map (fun a => ⟨a, 1 - a⟩)
  anticorrelated := by
    intro i j h
    simp only [List.get_eq_getElem, List.getElem_map] at h ⊢
    linarith

/-! ### Illustrations from the paper

The paper's qualitative findings instantiate the GPP: stated as hypotheses on
at-issueness, the projectivity ordering follows from `gppProjection_antitone`. -/

/-- Since `only` is more at-issue than an NRRC, the GPP predicts it projects no
    more ([tonhauser-beaver-degen-2018]). -/
theorem only_no_more_projective_than_nrrc
    {onlyAI nrrcAI : AtIssuenessDegree} (h : nrrcAI ≤ onlyAI) :
    gppProjection onlyAI ≤ gppProjection nrrcAI :=
  gppProjection_antitone h

/-- At-issue appositive content projects sub-maximally — the GPP reading of the
    central result against [potts-2005]. -/
theorem appositive_not_maximally_projective
    {apposAI : AtIssuenessDegree} (h : 0 < apposAI.val) :
    (gppProjection apposAI).val < 1 := by
  have := gpp_below_potts_of_atIssue h
  simpa using this

/-! ### Predicting against the data

`gppProjection` and `pottsProjection` map at-issueness to predicted
projectivity; the paper's per-expression means are pooled in
`Generalizations.Projectivity.allData` (artifact-sourced rows in
`Data.Examples.TonhauserBeaverDegen2018`). The
means are continuous, so per-row predictions are *computed* over `allData` (string
`paperFeatures` and `ℚ` do not reduce in the kernel); the *provable* content is
each account's systematic error. -/

/-- The GPP errs on any content whose projectivity differs from its
    not-at-issueness — the off-diagonal rows (`establish` below it, occasion verbs
    above it). -/
theorem gpp_errs_off_diagonal (d : ProjectionDatum)
    (h : d.projectivity.val ≠ d.notAtIssueness.val) :
    0 < predictionError gppProjection d := by
  rw [predictionError, gppProjection, abs_pos]
  intro hc; apply h
  simp only [ProjectionDatum.notAtIssueness, Set.Icc.coe_symm_eq] at *
  linarith [sub_eq_zero.mp hc]

/-- Potts over-predicts every content below the ceiling (projectivity `< 1`). -/
theorem potts_errs_subceiling (d : ProjectionDatum)
    (h : d.projectivity.val < 1) :
    0 < predictionError pottsProjection d := by
  rw [predictionError, abs_pos]
  simp only [pottsProjection_val]
  intro hc; linarith [sub_eq_zero.mp hc]

/-- Below both its not-at-issueness and the ceiling, the GPP is strictly closer to
    the observation than Potts — the low-projectivity items the paper highlights. -/
theorem gpp_beats_potts_below_diagonal (d : ProjectionDatum)
    (h1 : d.projectivity.val < d.notAtIssueness.val) (h2 : d.notAtIssueness.val < 1) :
    predictionError gppProjection d < predictionError pottsProjection d := by
  rw [predictionError, predictionError, gppProjection]
  simp only [pottsProjection_val, ProjectionDatum.notAtIssueness, Set.Icc.coe_symm_eq] at *
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
  linarith

end TonhauserBeaverDegen2018
