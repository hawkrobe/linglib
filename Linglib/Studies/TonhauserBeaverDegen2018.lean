import Linglib.Discourse.AtIssueness
import Linglib.Pragmatics.Expressives.Basic
import Linglib.Data.Examples.TonhauserBeaverDegen2018

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
* `gppProjection` — the GPP map, the complement of at-issueness (`Rat01.compl`).
* `pottsProjection` — [potts-2005]'s rival: CI projects maximally, at-issueness-blind.
* `ProjectionAccount` / `ProjectionDatum` / `allData` — the predict signature a
  theory implements and the artifact-sourced pool it runs against.

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
open Data.Examples (LinguisticExample SourceRef)

/-! ### The Gradient Projection Principle -/

/-- The GPP map: projection degree is the complement of at-issueness — content
    projects to the extent it is not at-issue ([tonhauser-beaver-degen-2018]). -/
def gppProjection (ai : AtIssuenessDegree) : ProjectivityDegree := Rat01.compl ai

/-- The GPP as order-reversal: more at-issue content is no more projective. -/
theorem gppProjection_antitone : Antitone gppProjection := Rat01.compl_antitone

/-- Fully not-at-issue content (at-issueness `0`) projects maximally. -/
theorem gppProjection_zero : gppProjection Rat01.zero = Rat01.one := by
  apply Subtype.ext; simp [gppProjection, Rat01.zero, Rat01.one]

/-- Fully at-issue content (at-issueness `1`) does not project. -/
theorem gppProjection_one : gppProjection Rat01.one = Rat01.zero := by
  apply Subtype.ext; simp [gppProjection, Rat01.zero, Rat01.one]

/-! ### Recovering the binary Projection Principle

The binary principle ([simons-tonhauser-beaver-roberts-2010]) — projects iff not
at-issue — is the threshold collapse of the gradient GPP. -/

/-- The GPP projects past `θ` iff at-issueness is below the complementary threshold. -/
theorem gpp_projects_iff (ai θ : Rat01) :
    isProjective (gppProjection ai) θ ↔ ai.val < (Rat01.compl θ).val := by
  simp only [isProjective, Rat01.exceeds, gppProjection, Rat01.compl_val]
  constructor <;> intro h <;> linarith

/-- The binary Projection Principle: never both at-issue and projecting at
    complementary thresholds. -/
theorem gpp_excludes_atIssue (ai θ : Rat01) :
    ¬ (isAtIssue ai (Rat01.compl θ) ∧ isProjective (gppProjection ai) θ) := by
  rintro ⟨ha, hp⟩
  simp only [isAtIssue, Rat01.exceeds, Rat01.compl_val] at ha
  rw [gpp_projects_iff, Rat01.compl_val] at hp
  linarith

/-! ### Contra Potts

[potts-2005] predicts CI content (appositives, NRRCs, expressives) projects
maximally and obligatorily — its CI dimension is unchanged by every
entailment-canceling operator. The GPP ties projection to at-issueness, so any
at-issue content projects below the ceiling; the two agree only for
fully-backgrounded content. -/

/-- [potts-2005]'s prediction: CI content projects maximally (degree `1`),
    regardless of at-issueness. -/
def pottsProjection (_ : AtIssuenessDegree) : ProjectivityDegree := Rat01.one

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
  simp only [gppProjection, pottsProjection, Rat01.compl_val, Rat01.one]; linarith

/-- The GPP and Potts agree iff the content is fully backgrounded (at-issueness `0`). -/
theorem gpp_eq_potts_iff_backgrounded (ai : AtIssuenessDegree) :
    gppProjection ai = pottsProjection ai ↔ ai = Rat01.zero := by
  constructor
  · intro h
    apply Subtype.ext
    have hv : (gppProjection ai).val = (pottsProjection ai).val := by rw [h]
    simp only [gppProjection, pottsProjection, Rat01.compl_val, Rat01.one] at hv
    simp only [Rat01.zero]; linarith
  · intro h; subst h; apply Subtype.ext
    simp [gppProjection, pottsProjection, Rat01.zero, Rat01.one]

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
  simpa [pottsProjection, Rat01.one] using this

/-! ### Representing the data for theories to predict against

The per-expression means (Exps 1a/1b plus main-clause controls) are
artifact-sourced rows in `Data.Examples.TonhauserBeaverDegen2018`; `fromExample`
lifts them to the `allData` pool any `ProjectionAccount` runs against. The means
are continuous, so per-row predictions are *computed* (string `paperFeatures` and
`ℚ` do not reduce in the kernel); the *provable* content is each account's
systematic error — the GPP over-predicts content projecting below its
not-at-issueness, Potts over-predicts everything sub-ceiling, and where both do
the GPP is closer. -/

/-- A theory of projection: predict a content's projectivity from its at-issueness. -/
abbrev ProjectionAccount := AtIssuenessDegree → ProjectivityDegree

/-- Observed projectivity and not-at-issueness means for one expression. -/
structure ProjectionDatum where
  expression     : String
  projectivity   : ProjectivityDegree
  notAtIssueness : Rat01
  source         : SourceRef
  deriving Repr

/-- Parse a percent-integer string (e.g. `"96"`) into a `Rat01`; `none` if
    non-numeric or out of range. -/
def parsePercent (s : String) : Option Rat01 :=
  match s.toNat? with
  | some n =>
      if h : n ≤ 100 then
        some (ofPercent (n : ℚ) (by exact_mod_cast Nat.zero_le n) (by exact_mod_cast h))
      else none
  | none => none

/-- Lift a `LinguisticExample` to a `ProjectionDatum` via its `expression`,
    `projectivity`, and `notAtIssueness` keys; `none` if any is missing. -/
def fromExample (e : LinguisticExample) : Option ProjectionDatum :=
  match e.paperFeatures.lookup "expression",
        (e.paperFeatures.lookup "projectivity").bind parsePercent,
        (e.paperFeatures.lookup "notAtIssueness").bind parsePercent with
  | some expr, some p, some na =>
      some { expression := expr, projectivity := p, notAtIssueness := na, source := e.source }
  | _, _, _ => none

/-- The observed projection pool, derived from the generated `Examples.all` rows. -/
def allData : List ProjectionDatum :=
  Examples.all.filterMap fromExample

/-- An account's absolute error on an observation. -/
def predictionError (acc : ProjectionAccount) (d : ProjectionDatum) : ℚ :=
  |(acc (Rat01.compl d.notAtIssueness)).val - d.projectivity.val|

/-- An account predicts an observation within tolerance `ε`. -/
def predictsWithin (ε : ℚ) (acc : ProjectionAccount) (d : ProjectionDatum) : Prop :=
  predictionError acc d ≤ ε

instance (ε : ℚ) (acc : ProjectionAccount) (d : ProjectionDatum) :
    Decidable (predictsWithin ε acc d) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The GPP over-predicts every content projecting below its not-at-issueness —
    the `establish`, `reveal`, and `confess` rows. -/
theorem gpp_errs_below_diagonal (d : ProjectionDatum)
    (h : d.projectivity.val < d.notAtIssueness.val) :
    0 < predictionError gppProjection d := by
  rw [predictionError, gppProjection, Rat01.compl_compl, abs_pos]
  intro hc; linarith [sub_eq_zero.mp hc]

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
  rw [predictionError, predictionError, gppProjection, Rat01.compl_compl]
  simp only [pottsProjection_val]
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
  linarith

end TonhauserBeaverDegen2018
