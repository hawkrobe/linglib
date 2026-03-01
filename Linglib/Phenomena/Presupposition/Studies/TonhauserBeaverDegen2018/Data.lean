import Linglib.Core.Discourse.AtIssueness

/-!
# Tonhauser, Beaver & Degen (2018): How Projective Is Projective Content?
@cite{tonhauser-beaver-degen-2018} @cite{potts-2005} @cite{simons-roberts-2010} @cite{tonhauser-beaver-roberts-simons-2013}Empirical data from "How projective is projective content? Gradience in
projectivity and at-issueness." Journal of Semantics 35(3): 495–542.

## Key Findings

1. **Projectivity is gradient**, not binary. Even "strong" projective triggers
   like NRRCs show mean projectivity ≈ .96, not 1.0.
2. **Not-at-issueness is gradient** and **positively correlated** with
   projectivity: r = .85 across 9 expression types (Exp 1a), r = .99
   across 12 predicates (Exp 1b).
3. **Appositives are not maximally projective**, contra Potts (2005).
4. **Within-type variation**: different lexical items of the same type
   yield different ratings.

## Gradient Projection Principle (GPP)

The paper's central theoretical contribution (p. 497, ex. 7):

  "If content C is expressed by a constituent embedded under an
   entailment-canceling operator, then C projects to the extent that
   it is not at-issue."

This generalizes Simons et al.'s (2010) Pragmatic Account by replacing
the binary at-issue/not-at-issue distinction with a gradient one.

## Experiments

- **Exp 1a**: 9 expression types — projectivity + not-at-issueness
  (asking whether diagnostic). 190 participants.
- **Exp 1b**: 12 clause-embedding predicates — same diagnostics.
  235 participants (after exclusions).
- **Exp 2a/2b**: Replications with direct dissent diagnostic (not formalized here).

## Data

Values are approximate means read from Figures 3 and 6. The paper reports
ranges in text (e.g., projectivity .76–.96 for Exp 1a) but does not
provide a table of exact per-expression means. Textually confirmed values
are annotated.

The scale is 0–1 (proportion of "yes" responses). The paper measures
**not-at-issueness** via the "asking whether" diagnostic: higher values
mean the content is MORE not-at-issue (more backgrounded).

-/

namespace Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018

-- ════════════════════════════════════════════════════
-- § Experiment 1a: Nine Expression Types
-- ════════════════════════════════════════════════════

/-- The 9 expression types tested in Experiment 1a.

    All are **non-SCF** (Strong Contextual Felicity = no), chosen to
    isolate projectivity and at-issueness variation (p. 504).

    - Class B (SCF=no, OLE=no): NRRC, nominal appositive, possessive NP
    - Class C (SCF=no, OLE=yes): discover, know, be annoyed, stop
    - Focus-sensitive: only
    - Evaluative adjective: be stupid to -/
inductive ExpressionType where
  | nrrc              -- non-restrictive relative clause
  | nominalAppositive -- nominal appositive
  | possessiveNP      -- possessive NP (existence of possessor)
  | discover          -- factive verb "discover"
  | know              -- factive verb "know"
  | annoyed           -- emotive factive "be annoyed"
  | stop              -- change-of-state "stop"
  | only              -- focus-sensitive "only"
  | stupid            -- evaluative adjective "be stupid to"
  deriving DecidableEq, Repr, BEq

/-- Mean projectivity rating from Experiment 1a (0–1 scale).

    Values approximate means from Figure 3. Text (p. 507) confirms:
    - only = .76 (minimum)
    - NRRC = .96 and be annoyed = .96 (maximum, "close to ceiling") -/
def projectivityRating : ExpressionType → ℚ
  | .nrrc              => 96/100  -- text: .96
  | .nominalAppositive => 94/100
  | .possessiveNP      => 93/100
  | .discover          => 88/100
  | .know              => 91/100
  | .annoyed           => 96/100  -- text: .96
  | .stop              => 88/100
  | .only              => 76/100  -- text: .76
  | .stupid            => 86/100

/-- Mean not-at-issueness rating from Experiment 1a (0–1 scale).
    Measured via the "asking whether" diagnostic.

    Higher = more not-at-issue (more backgrounded).

    Values approximate means from Figure 3. Text (p. 508) confirms:
    - only = .73 (minimum)
    - NRRC = .96 (maximum) -/
def notAtIssuenessRating : ExpressionType → ℚ
  | .nrrc              => 96/100  -- text: .96
  | .nominalAppositive => 91/100
  | .possessiveNP      => 93/100
  | .discover          => 84/100
  | .know              => 88/100
  | .annoyed           => 94/100
  | .stop              => 78/100
  | .only              => 73/100  -- text: .73
  | .stupid            => 82/100

/-- At-issueness = 1 − not-at-issueness. Higher = more at-issue.
    Derived from the paper's direct measurements. -/
def atIssuenessRating (e : ExpressionType) : ℚ := 1 - notAtIssuenessRating e

-- ════════════════════════════════════════════════════
-- § Experiment 1b: Twelve Clause-Embedding Predicates
-- ════════════════════════════════════════════════════

/-- The 12 clause-embedding predicates from Experiment 1b (p. 511).

    Semantic classes (per paper):
    - Emotive: be amused, be annoyed
    - Cognitive: be aware, discover, find out, learn, notice, realize, establish
    - Sensory: see
    - Communication: confess, reveal -/
inductive Predicate where
  | beAmused
  | beAnnoyed
  | beAware
  | confess
  | discover
  | establish
  | findOut
  | learn
  | notice
  | realize
  | reveal
  | see
  deriving DecidableEq, Repr, BEq

/-- Mean projectivity ratings for the 12 predicates from Exp 1b (0–1 scale).
    Values approximate means from Figure 6. -/
def verbProjectivity : Predicate → ℚ
  | .establish  => 43/100
  | .confess    => 65/100
  | .reveal     => 77/100
  | .learn      => 82/100
  | .discover   => 86/100
  | .findOut    => 90/100
  | .see        => 90/100
  | .beAmused   => 92/100
  | .realize    => 92/100
  | .beAware    => 93/100
  | .notice     => 94/100
  | .beAnnoyed  => 94/100

/-- Mean not-at-issueness ratings for the 12 predicates from Exp 1b (0–1 scale).
    Values approximate means from Figure 6. -/
def verbNotAtIssueness : Predicate → ℚ
  | .establish  => 47/100
  | .confess    => 56/100
  | .reveal     => 68/100
  | .learn      => 73/100
  | .discover   => 78/100
  | .findOut    => 82/100
  | .see        => 83/100
  | .beAmused   => 85/100
  | .realize    => 86/100
  | .beAware    => 87/100
  | .notice     => 88/100
  | .beAnnoyed  => 89/100

/-- At-issueness = 1 − not-at-issueness for predicates. -/
def verbAtIssueness (p : Predicate) : ℚ := 1 - verbNotAtIssueness p

-- ════════════════════════════════════════════════════
-- § Regression Coefficients
-- ════════════════════════════════════════════════════

/-- Regression coefficient: not-at-issueness predicts projectivity.
    Exp 1a (p. 508–509): β = 0.37, SE = 0.10, t = 3.70, p < .003.
    Exp 1b (p. 514):     β = 0.34, SE = 0.04, t = 9.31, p < .0001.

    The effect is significant in both experiments. -/
structure RegressionEffect where
  beta : ℚ
  se : ℚ
  deriving Repr

def exp1aRegression : RegressionEffect := ⟨37/100, 10/100⟩
def exp1bRegression : RegressionEffect := ⟨34/100, 4/100⟩

-- ════════════════════════════════════════════════════
-- § Correlation Coefficients
-- ════════════════════════════════════════════════════

/-- Pearson r for not-at-issueness × projectivity (positive correlation).
    "Collapsing" = computed over expression-type/predicate means.
    "Not collapsing" = computed over individual items.

    Exp 1a (p. 508): r = .85 (collapsing), r = .45 (not collapsing)
    Exp 1b (p. 514): r = .99 (collapsing), r = .44 (not collapsing) -/
structure CorrelationData where
  collapsing : ℚ
  notCollapsing : ℚ
  deriving Repr

def exp1aCorrelation : CorrelationData := ⟨85/100, 45/100⟩
def exp1bCorrelation : CorrelationData := ⟨99/100, 44/100⟩

-- ════════════════════════════════════════════════════
-- § Verification Theorems: Exp 1a
-- ════════════════════════════════════════════════════

/-- NRRC and be annoyed are tied for most projective (text: .96). -/
theorem nrrc_annoyed_most_projective : ∀ e : ExpressionType,
    projectivityRating e ≤ projectivityRating .nrrc := by
  intro e; cases e <;> native_decide

/-- only is the least projective at .76 (text confirms). -/
theorem only_least_projective : ∀ e : ExpressionType,
    projectivityRating .only ≤ projectivityRating e := by
  intro e; cases e <;> native_decide

/-- NRRC has the highest not-at-issueness at .96 (text confirms). -/
theorem nrrc_most_notAtIssue : ∀ e : ExpressionType,
    notAtIssuenessRating e ≤ notAtIssuenessRating .nrrc := by
  intro e; cases e <;> native_decide

/-- only has the lowest not-at-issueness at .73 (text confirms). -/
theorem only_least_notAtIssue : ∀ e : ExpressionType,
    notAtIssuenessRating .only ≤ notAtIssuenessRating e := by
  intro e; cases e <;> native_decide

/-- Appositives are not maximally projective, contra Potts (2005).
    Potts predicted CI content (including appositives) should project
    obligatorily. The data shows 94/100 — high but not 1.0. -/
theorem appositives_not_maximally_projective :
    projectivityRating .nominalAppositive < 1 := by native_decide

/-- Within-type variation: factive predicates differ in projectivity.
    discover (.88) vs know (.91) — both traditionally "factive" but
    different ratings. -/
theorem within_type_variation :
    projectivityRating .discover ≠ projectivityRating .know := by
  native_decide

/-- GPP supported for Exp 1a extremes: only has highest at-issueness
    and lowest projectivity; NRRC has lowest at-issueness and highest
    projectivity. -/
theorem gpp_extreme_pair_exp1a :
    atIssuenessRating .only > atIssuenessRating .nrrc ∧
    projectivityRating .only < projectivityRating .nrrc := by
  native_decide

-- ════════════════════════════════════════════════════
-- § Verification Theorems: Exp 1b
-- ════════════════════════════════════════════════════

/-- be annoyed has the highest projectivity among the 12 predicates.
    (Tied with notice at .94.) -/
theorem beAnnoyed_highest_verb_projectivity :
    ∀ p : Predicate, verbProjectivity p ≤ verbProjectivity .beAnnoyed := by
  intro p; cases p <;> native_decide

/-- establish has the lowest projectivity (.43) — notably below .50,
    suggesting it may not even be a projective trigger. -/
theorem establish_lowest_verb_projectivity :
    ∀ p : Predicate, verbProjectivity .establish ≤ verbProjectivity p := by
  intro p; cases p <;> native_decide

/-- establish is the only predicate with projectivity below the
    midpoint .50, suggesting it may not be a projective trigger. -/
theorem establish_below_midpoint :
    verbProjectivity .establish < 1/2 := by native_decide

/-- GPP supported for Exp 1b extremes: establish has highest
    at-issueness and lowest projectivity. -/
theorem gpp_extreme_pair_exp1b :
    verbAtIssueness .establish > verbAtIssueness .beAnnoyed ∧
    verbProjectivity .establish < verbProjectivity .beAnnoyed := by
  native_decide

/-- All predicates except establish have projectivity ≥ .65. -/
theorem non_establish_above_65 : ∀ p : Predicate,
    p ≠ .establish → 65/100 ≤ verbProjectivity p := by
  intro p hp; cases p <;> first | native_decide | exact absurd rfl hp

-- ════════════════════════════════════════════════════
-- § Tukey Groupings
-- ════════════════════════════════════════════════════

/-- The top group of Exp 1a (Table 1): {NRRC, annoyed, NomApp, possNP, know}
    show no significant pairwise differences in projectivity.
    These form the "high projectivity" cluster (.91–.96). -/
theorem exp1a_top_group_tight_range :
    projectivityRating .nrrc - projectivityRating .know ≤ 6/100 := by
  native_decide

/-- only is significantly different from all other expression types
    (Table 1: all pairwise comparisons significant at p < .001). -/
theorem only_separated_from_top :
    projectivityRating .nrrc - projectivityRating .only ≥ 15/100 := by
  native_decide

/-- The top group of Exp 1b (Table 3): {annoyed, notice, aware, realize,
    amused, see, findOut} show no significant pairwise differences.
    These form the "high projectivity" cluster (.90–.94). -/
theorem exp1b_top_group_tight_range :
    verbProjectivity .beAnnoyed - verbProjectivity .findOut ≤ 5/100 := by
  native_decide

/-- establish is clearly separated from the top group
    (Table 3: all pairwise comparisons significant at p < .001). -/
theorem establish_separated_from_top :
    verbProjectivity .beAnnoyed - verbProjectivity .establish ≥ 40/100 := by
  native_decide

end Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018
