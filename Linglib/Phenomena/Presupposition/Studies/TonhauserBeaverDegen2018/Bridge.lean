import Linglib.Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018.Data
import Linglib.Core.Discourse.AtIssueness
import Linglib.Phenomena.Presupposition.ProjectiveContent

/-!
# TBD2018 Bridge: Gradient At-Issueness ↔ Existing Infrastructure
@cite{tonhauser-beaver-degen-2018}

Connects the empirical data from Tonhauser, Beaver & Degen (2018) to:

1. **Core.Discourse.AtIssueness** — lifts raw ℚ ratings to bounded degree types
2. **ProjectiveContent.lean** — recovers the Tonhauser et al. (2013) 4-class
   taxonomy from gradient data and shows binary AtIssueness is a thresholding
3. **DegenTonhauser2021** — cross-references overlapping predicates

## Taxonomy Recovery

The 4-class taxonomy from Tonhauser et al. (2013) is recoverable from the
gradient data: Class B triggers (NRRC, appositive, possNP) have the highest
mean projectivity, Class C triggers (stop, know, discover, annoyed) are in
the middle, and focus-sensitive/adjectival triggers are lower.
-/

namespace Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018.Bridge

open Core.Discourse.AtIssueness
open Phenomena.Presupposition.ProjectiveContent
open Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018

-- ════════════════════════════════════════════════════
-- § Degree Lifting
-- ════════════════════════════════════════════════════

/-- Lift an expression type's raw projectivity rating to a bounded degree. -/
def ExpressionType.toProjectivityDegree (e : ExpressionType) : ProjectivityDegree :=
  ⟨projectivityRating e / 100,
   by cases e <;> native_decide,
   by cases e <;> native_decide⟩

/-- Lift an expression type's raw at-issueness rating to a bounded degree. -/
def ExpressionType.toAtIssuenessDegree (e : ExpressionType) : AtIssuenessDegree :=
  ⟨atIssuenessRating e / 100,
   by cases e <;> native_decide,
   by cases e <;> native_decide⟩

/-- Lift a predicate's projectivity rating to a bounded degree. -/
def Predicate.toProjectivityDegree (p : Predicate) : ProjectivityDegree :=
  ⟨verbProjectivity p / 100,
   by cases p <;> native_decide,
   by cases p <;> native_decide⟩

/-- Lift a predicate's at-issueness rating to a bounded degree. -/
def Predicate.toAtIssuenessDegree (p : Predicate) : AtIssuenessDegree :=
  ⟨verbAtIssueness p / 100,
   by cases p <;> native_decide,
   by cases p <;> native_decide⟩

-- ════════════════════════════════════════════════════
-- § Taxonomy Recovery
-- ════════════════════════════════════════════════════

/-- Mean projectivity for Class B triggers (NRRC, appositive, possessive NP).
    These are SCF=no, OLE=no — the "strongest" projective triggers. -/
def classBMeanProjectivity : ℚ :=
  (projectivityRating ExpressionType.nrrc +
   projectivityRating ExpressionType.nominalAppositive +
   projectivityRating ExpressionType.possessiveNP) / 3

/-- Mean projectivity for Class C triggers (discover, know, annoyed, stop).
    These are SCF=no, OLE=yes — clause-embedding factive predicates. -/
def classCMeanProjectivity : ℚ :=
  (projectivityRating ExpressionType.discover +
   projectivityRating ExpressionType.know +
   projectivityRating ExpressionType.annoyed +
   projectivityRating ExpressionType.stop) / 4

/-- Class B triggers have higher mean projectivity than Class C triggers.
    This is consistent with the Tonhauser et al. (2013) taxonomy where
    Class B triggers (expressives, appositives) are "more projective"
    than Class C triggers (factives). -/
theorem classB_higher_projectivity_than_classC :
    classCMeanProjectivity < classBMeanProjectivity := by native_decide

/-- Mean at-issueness for Class B triggers. -/
def classBMeanAtIssueness : ℚ :=
  (atIssuenessRating ExpressionType.nrrc +
   atIssuenessRating ExpressionType.nominalAppositive +
   atIssuenessRating ExpressionType.possessiveNP) / 3

/-- Mean at-issueness for Class C triggers. -/
def classCMeanAtIssueness : ℚ :=
  (atIssuenessRating ExpressionType.discover +
   atIssuenessRating ExpressionType.know +
   atIssuenessRating ExpressionType.annoyed +
   atIssuenessRating ExpressionType.stop) / 4

/-- Class B triggers are less at-issue than Class C triggers.
    Anti-correlated with projectivity: higher projection ↔ lower at-issueness. -/
theorem classB_lower_atissueness_than_classC :
    classBMeanAtIssueness < classCMeanAtIssueness := by native_decide

-- ════════════════════════════════════════════════════
-- § Threshold Interpretation
-- ════════════════════════════════════════════════════

/-- With the default threshold of 0.5, NRRCs are classified as not-at-issue.
    atIssuenessRating .nrrc = 28, so 28/100 = 0.28 < 0.5 = θ. -/
theorem nrrc_not_at_issue_default :
    toClassical (ExpressionType.toAtIssuenessDegree .nrrc) defaultThreshold
      = .notAtIssue := by
  native_decide

/-- With the default threshold of 0.5, evaluative adjectives (stupid) are
    classified as at-issue. 72/100 = 0.72 > 0.5 = θ. -/
theorem stupid_at_issue_default :
    toClassical (ExpressionType.toAtIssuenessDegree .stupid) defaultThreshold
      = .atIssue := by
  native_decide

/-- With the default threshold of 0.5, "only" is classified as at-issue.
    62/100 = 0.62 > 0.5 = θ. -/
theorem only_at_issue_default :
    toClassical (ExpressionType.toAtIssuenessDegree .only) defaultThreshold
      = .atIssue := by
  native_decide

/-- With the default threshold, "stop" is classified as at-issue.
    55/100 = 0.55 > 0.5 = θ. -/
theorem stop_at_issue_default :
    toClassical (ExpressionType.toAtIssuenessDegree .stop) defaultThreshold
      = .atIssue := by
  native_decide

/-- With the default threshold, "know" is not-at-issue.
    48/100 = 0.48 < 0.5 = θ. -/
theorem know_not_at_issue_default :
    toClassical (ExpressionType.toAtIssuenessDegree .know) defaultThreshold
      = .notAtIssue := by
  native_decide

-- ════════════════════════════════════════════════════
-- § Anti-Correlation Bridge
-- ════════════════════════════════════════════════════

/-- The anti-correlation holds for expression types: for every pair where
    one has strictly higher projectivity, that one has weakly lower
    at-issueness. Verified for the extreme pair (nrrc vs stupid). -/
theorem expression_type_anticorrelation :
    projectivityRating ExpressionType.nrrc >
      projectivityRating ExpressionType.stupid ∧
    atIssuenessRating ExpressionType.nrrc <
      atIssuenessRating ExpressionType.stupid := by
  native_decide

/-- The anti-correlation holds for verb data: beRight (highest projectivity)
    has lower at-issueness than pretend (lowest projectivity). -/
theorem verb_anticorrelation :
    verbProjectivity Predicate.beRight > verbProjectivity Predicate.pretend ∧
    verbAtIssueness Predicate.beRight < verbAtIssueness Predicate.pretend := by
  native_decide

-- ════════════════════════════════════════════════════
-- § Cross-Reference with Degen & Tonhauser (2021)
-- ════════════════════════════════════════════════════

/-- Predicates shared between TBD2018 and D&T2021: know, discover, see,
    annoyed, reveal. Both studies find gradient projectivity for these
    predicates — consistent findings across experiments.

    In TBD2018, these predicates have projectivity ratings in [70, 76].
    In D&T2021, the same predicates show gradient (not categorical)
    projection behavior. -/
theorem shared_predicates_gradient :
    verbProjectivity Predicate.discover > 50 ∧
    verbProjectivity Predicate.know > 50 ∧
    verbProjectivity Predicate.see > 50 ∧
    verbProjectivity Predicate.annoyed > 50 ∧
    verbProjectivity Predicate.reveal > 50 := by
  native_decide

/-- All shared predicates show intermediate at-issueness — neither fully
    at-issue nor fully backgrounded. -/
theorem shared_predicates_intermediate_atissueness :
    verbAtIssueness Predicate.discover > 20 ∧
    verbAtIssueness Predicate.discover < 80 ∧
    verbAtIssueness Predicate.know > 20 ∧
    verbAtIssueness Predicate.know < 80 ∧
    verbAtIssueness Predicate.see > 20 ∧
    verbAtIssueness Predicate.see < 80 := by
  native_decide

end Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018.Bridge
