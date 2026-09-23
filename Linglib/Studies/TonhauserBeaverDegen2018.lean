module

public import Linglib.Data.Generalizations.Projectivity

/-!
# Tonhauser, Beaver and Degen (2018): How Projective Is Projective Content? Gradience in Projectivity and At-Issueness

This file formalizes the Gradient Projection Principle of [tonhauser-beaver-degen-2018], (7):
content expressed by a constituent embedded under an entailment-cancelling operator projects
to the extent that it is not at-issue. Projectivity, the extent to which a listener takes the
speaker of the embedding utterance to be committed to the content, and at-issueness are
gradient properties measured on the unit interval, so the principle is the involution
`Set.Icc.symm`, `gppProjection`. Its prediction is that content that is more not-at-issue is
more projective, `gppProjection_antitone`, and restricted to binary at-issueness it is the
Projection Principle of [simons-tonhauser-beaver-roberts-2010] and
[beaver-roberts-simons-tonhauser-2017], projects iff not at-issue, `gppProjection_eq_one_iff`.
The analyses of projection the paper reviews predict projection at the ceiling for every
presupposition not under a plug or a filter, [karttunen-1973], [gazdar-1979] and global
accommodation after [heim-1983] and [van-der-sandt-1992], as [potts-2005]'s two-dimensional
analysis does for conventional implicatures: `ceilingProjection`, which agrees with the
principle exactly on fully not-at-issue content, `gppProjection_eq_ceiling_iff`. Against an
observed content, the ceiling errs whenever projectivity is below the ceiling and the principle
whenever it is off the diagonal, `ceilingProjection_error_pos` and `gppProjection_error_pos`;
below both, the principle is the closer, `gpp_error_lt_ceiling`.

## Implementation notes

Degrees are `Set.Icc (0 : ℚ) 1`, and an observed content is a `ProjectionDatum` of
`Generalizations.Projectivity`, which pools the by-expression means of Experiments 1a and 1b
from `Data.Examples.TonhauserBeaverDegen2018` with those of [solstad-bott-2024]; the theorems
are about each account's error on a datum, not about the pool. The experiments are reported
in prose. Projectivity was measured by the *certain that* diagnostic, whether the speaker of
a polar question is certain of the content, and at-issueness by the *asking whether*
diagnostic in Experiments 1a and 1b and by a direct dissent diagnostic in 2a and 2b, each
content instantiated by many lexical contents. Across the 19 projective contents, of nine
syntactically heterogeneous expressions and twelve clause-embedding predicates, projectivity
ranged from the near-ceiling appositive contents and the complement of *be annoyed* to the
prejacent of *only* and the complement of *establish*, in more than two classes cutting
across the hard/soft trigger and factive/semi-factive distinctions; not-at-issueness predicted
projectivity in three of the four experiments, with by-expression, by-lexical-content and
by-participant variability besides, and the two at-issueness diagnostics correlated. The
paper leaves open whether at-issueness causes projection.

## References

* [tonhauser-beaver-degen-2018]
* [simons-tonhauser-beaver-roberts-2010]
* [beaver-roberts-simons-tonhauser-2017]
* [karttunen-1973]
* [gazdar-1979]
* [heim-1983]
* [van-der-sandt-1992]
* [potts-2005]
* [solstad-bott-2024]
-/

@[expose] public section

namespace TonhauserBeaverDegen2018

open Generalizations.Projectivity

/-! ### The Gradient Projection Principle -/

/-- (7): content projects to the extent that it is not at-issue. -/
def gppProjection : Set.Icc (0 : ℚ) 1 → Set.Icc (0 : ℚ) 1 := Set.Icc.symm

/-- More not-at-issue content is more projective. -/
theorem gppProjection_antitone : Antitone gppProjection := Set.Icc.symm_antitone

/-- Restricted to binary at-issueness, the principle is the Projection Principle: content
projects fully iff it is not at-issue at all. -/
theorem gppProjection_eq_one_iff {ai : Set.Icc (0 : ℚ) 1} : gppProjection ai = 1 ↔ ai = 0 :=
  Set.Icc.symm_eq_one

/-- Fully at-issue content does not project. -/
theorem gppProjection_eq_zero_iff {ai : Set.Icc (0 : ℚ) 1} : gppProjection ai = 0 ↔ ai = 1 :=
  Set.Icc.symm_eq_zero

/-! ### Projection at the ceiling -/

/-- Projection at the ceiling whatever the at-issueness: what [karttunen-1973], [gazdar-1979]
and global accommodation predict for a presupposition not under a plug or a filter, and
[potts-2005] for a conventional implicature. -/
def ceilingProjection (_ : Set.Icc (0 : ℚ) 1) : Set.Icc (0 : ℚ) 1 := 1

@[simp] theorem ceilingProjection_val (ai : Set.Icc (0 : ℚ) 1) :
    (ceilingProjection ai).val = 1 := rfl

/-- The principle and the ceiling agree exactly on fully not-at-issue content. -/
theorem gppProjection_eq_ceiling_iff {ai : Set.Icc (0 : ℚ) 1} :
    gppProjection ai = ceilingProjection ai ↔ ai = 0 :=
  Set.Icc.symm_eq_one

/-! ### Errors on an observed content -/

/-- The ceiling errs on any content observed below it. -/
theorem ceilingProjection_error_pos (d : ProjectionDatum) (h : d.projectivity.val < 1) :
    0 < predictionError ceilingProjection d := by
  rw [predictionError, abs_pos, ceilingProjection_val]
  intro hc
  linarith [sub_eq_zero.mp hc]

/-- The principle errs on any content whose projectivity differs from its not-at-issueness. -/
theorem gppProjection_error_pos (d : ProjectionDatum)
    (h : d.projectivity.val ≠ d.notAtIssueness.val) :
    0 < predictionError gppProjection d := by
  rw [predictionError, gppProjection, abs_pos]
  intro hc
  apply h
  simp only [ProjectionDatum.notAtIssueness, Set.Icc.coe_symm_eq] at *
  linarith [sub_eq_zero.mp hc]

/-- On content observed below both its not-at-issueness and the ceiling, the principle is
strictly closer than the ceiling. -/
theorem gpp_error_lt_ceiling (d : ProjectionDatum)
    (h1 : d.projectivity.val < d.notAtIssueness.val) (h2 : d.notAtIssueness.val < 1) :
    predictionError gppProjection d < predictionError ceilingProjection d := by
  rw [predictionError, predictionError, gppProjection]
  simp only [ceilingProjection_val, ProjectionDatum.notAtIssueness, Set.Icc.coe_symm_eq] at *
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
  linarith

end TonhauserBeaverDegen2018
