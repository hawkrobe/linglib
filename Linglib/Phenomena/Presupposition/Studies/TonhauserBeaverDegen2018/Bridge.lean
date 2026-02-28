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
3. **AntiCorrelation** — instantiates the deterministic anti-monotonicity
   property for Exp 1b verb data

## Taxonomy Recovery

The 4-class taxonomy from Tonhauser et al. (2013) is recoverable from the
gradient data: Class B triggers (NRRC, appositive, possNP) have the highest
mean projectivity, Class C triggers (stop, know, discover, annoyed) are in
the middle, and focus-sensitive/adjectival triggers are lower.

## Gradient Projection Principle

The GPP predicts that not-at-issueness positively correlates with projectivity.
The Exp 1b data satisfies the deterministic (monotone) version: every pair
of predicates where one has strictly lower at-issueness also has weakly
higher projectivity. Exp 1a shows a strong but non-monotone relationship
(r = .85; possNP and NomApp are non-monotone).
-/

namespace Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018.Bridge

open Core.Discourse.AtIssueness
open Phenomena.Presupposition.ProjectiveContent
open Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018

-- ════════════════════════════════════════════════════
-- § Degree Lifting
-- ════════════════════════════════════════════════════

/-- Lift an expression type's projectivity rating to a bounded degree. -/
def ExpressionType.toProjectivityDegree (e : ExpressionType) : ProjectivityDegree :=
  ⟨projectivityRating e,
   by cases e <;> native_decide,
   by cases e <;> native_decide⟩

/-- Lift an expression type's at-issueness to a bounded degree. -/
def ExpressionType.toAtIssuenessDegree (e : ExpressionType) : AtIssuenessDegree :=
  ⟨atIssuenessRating e,
   by cases e <;> native_decide,
   by cases e <;> native_decide⟩

/-- Lift a predicate's projectivity rating to a bounded degree. -/
def Predicate.toProjectivityDegree (p : Predicate) : ProjectivityDegree :=
  ⟨verbProjectivity p,
   by cases p <;> native_decide,
   by cases p <;> native_decide⟩

/-- Lift a predicate's at-issueness to a bounded degree. -/
def Predicate.toAtIssuenessDegree (p : Predicate) : AtIssuenessDegree :=
  ⟨verbAtIssueness p,
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
    Class B triggers (appositives, NRRCs) are "more projective"
    than Class C triggers (factives). -/
theorem classB_higher_projectivity_than_classC :
    classCMeanProjectivity < classBMeanProjectivity := by native_decide

/-- Mean not-at-issueness for Class B triggers. -/
def classBMeanNotAtIssueness : ℚ :=
  (notAtIssuenessRating ExpressionType.nrrc +
   notAtIssuenessRating ExpressionType.nominalAppositive +
   notAtIssuenessRating ExpressionType.possessiveNP) / 3

/-- Mean not-at-issueness for Class C triggers. -/
def classCMeanNotAtIssueness : ℚ :=
  (notAtIssuenessRating ExpressionType.discover +
   notAtIssuenessRating ExpressionType.know +
   notAtIssuenessRating ExpressionType.annoyed +
   notAtIssuenessRating ExpressionType.stop) / 4

/-- Class B triggers are more not-at-issue than Class C triggers.
    Consistent with GPP: higher not-at-issueness ↔ higher projectivity. -/
theorem classB_higher_notAtIssueness_than_classC :
    classCMeanNotAtIssueness < classBMeanNotAtIssueness := by native_decide

-- ════════════════════════════════════════════════════
-- § Threshold Interpretation
-- ════════════════════════════════════════════════════

/-- With the default threshold of 0.5, all 9 expression types are
    classified as not-at-issue (at-issueness ≤ 0.27 for all types).
    This is expected: the paper specifically tested projective
    contents, which are by definition not-at-issue. -/
theorem all_expression_types_not_at_issue :
    ∀ e : ExpressionType,
      toClassical (ExpressionType.toAtIssuenessDegree e) defaultThreshold
        = .notAtIssue := by
  intro e; cases e <;> native_decide

/-- For Exp 1b predicates, only establish is classified as at-issue
    with the default threshold (at-issueness = 53/100 > 0.5).
    All other predicates have at-issueness < 0.5. -/
theorem establish_at_issue_default :
    toClassical (Predicate.toAtIssuenessDegree .establish) defaultThreshold
      = .atIssue := by
  native_decide

/-- All predicates except establish are classified as not-at-issue
    with the default threshold. -/
theorem non_establish_not_at_issue (p : Predicate) (h : p ≠ .establish) :
    toClassical (Predicate.toAtIssuenessDegree p) defaultThreshold
      = .notAtIssue := by
  cases p <;> first | native_decide | exact absurd rfl h

-- ════════════════════════════════════════════════════
-- § Gradient Projection Principle: Anti-Monotonicity
-- ════════════════════════════════════════════════════

/-- The GPP anti-monotonicity property holds for Exp 1b verb data:
    for any two predicates, if one has strictly higher at-issueness,
    it has weakly lower projectivity.

    This is the deterministic version of the GPP. The statistical
    version (r = .99) is a weaker claim.

    Proof: exhaustive check over all 12 × 12 = 144 predicate pairs. -/
theorem exp1b_gpp_antimonotone :
    ∀ (p q : Predicate),
      verbAtIssueness p < verbAtIssueness q →
      verbProjectivity q ≤ verbProjectivity p := by
  intro p q; cases p <;> cases q <;> native_decide

/-- Exp 1a is NOT fully anti-monotone: possNP has higher
    not-at-issueness than NomApp (93 vs 91) but lower projectivity
    (93 vs 94). This shows the GPP is a statistical generalization
    (r = .85), not a deterministic law, for heterogeneous types. -/
theorem exp1a_non_monotone_witness :
    notAtIssuenessRating ExpressionType.possessiveNP >
      notAtIssuenessRating ExpressionType.nominalAppositive ∧
    projectivityRating ExpressionType.possessiveNP <
      projectivityRating ExpressionType.nominalAppositive := by
  native_decide

-- ════════════════════════════════════════════════════
-- § Cross-Reference with Degen & Tonhauser (2021)
-- ════════════════════════════════════════════════════

/-- Predicates shared between TBD2018 Exp 1b and D&T2021:
    be annoyed, confess, discover, establish, reveal, see (6 of 12).
    Both studies find gradient projectivity — consistent findings
    across experiments.

    TBD2018 projectivity: beAnnoyed .94, confess .65, discover .86,
    establish .43, reveal .77, see .90. -/
theorem shared_predicates_gradient :
    verbProjectivity Predicate.beAnnoyed > 1/2 ∧
    verbProjectivity Predicate.discover > 1/2 ∧
    verbProjectivity Predicate.reveal > 1/2 ∧
    verbProjectivity Predicate.see > 1/2 := by
  native_decide

/-- Among shared predicates, discover shows intermediate
    at-issueness — neither fully at-issue nor fully backgrounded. -/
theorem shared_predicates_intermediate_atissueness :
    verbAtIssueness Predicate.discover > 0 ∧
    verbAtIssueness Predicate.discover < 1/2 ∧
    verbAtIssueness Predicate.beAnnoyed > 0 ∧
    verbAtIssueness Predicate.beAnnoyed < 1/2 := by
  native_decide

end Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018.Bridge
