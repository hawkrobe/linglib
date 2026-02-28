import Linglib.Core.Discourse.AtIssueness

/-!
# Tonhauser, Beaver & Degen (2018): How Projective Is Projective Content?
@cite{tonhauser-beaver-degen-2018}

Empirical data from "How projective is projective content? Gradience in
projectivity and at-issueness." Journal of Semantics 35(3): 495–542.

## Key Findings

1. **Projectivity is gradient**, not binary. Even "strong" projective triggers
   like NRRCs show mean projectivity ratings below ceiling (84/100, not 100).
2. **At-issueness is gradient** and **anti-correlated** with projectivity
   (r ≈ −0.77 across expression types, r ≈ −0.85 across predicates).
3. **Appositives are not maximally projective**, contra Potts (2005).
4. **Within-type variation**: different lexical items of the same type
   yield different ratings (e.g., different NRRC contents differ).

## Experiments

- **Exp 1a**: Projectivity ratings for 9 expression types (family-of-sentences)
- **Exp 1b**: At-issueness ratings for same 9 types (HWAM diagnostic)
- **Exp 2a**: Projectivity ratings for 20 clause-embedding predicates
- **Exp 2b**: At-issueness ratings for same 20 predicates

## References

- Tonhauser, J., Beaver, D. I. & Degen, J. (2018). How projective is projective
  content? Gradience in projectivity and at-issueness. Journal of Semantics
  35(3): 495–542.
- Potts, C. (2005). The Logic of Conventional Implicatures.
- Tonhauser, J., Beaver, D. I., Roberts, C. & Simons, M. (2013). Toward a
  taxonomy of projective content. Language 89(1): 66–109.
-/

namespace Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018

-- ════════════════════════════════════════════════════
-- § Experiment 1: Nine Expression Types
-- ════════════════════════════════════════════════════

/-- The 9 expression types tested in Experiments 1a and 1b.

    These span the Tonhauser et al. (2013) taxonomy:
    - Class B (SCF=no, OLE=no): NRRC, appositive, possessive NP
    - Class C (SCF=no, OLE=yes): discover, know, be annoyed, stop
    - Focus-sensitive: only
    - Adjectival: stupid -/
inductive ExpressionType where
  | nrrc              -- non-restrictive relative clause
  | nominalAppositive -- nominal appositive
  | possessiveNP      -- possessive NP (existence of possessor)
  | discover          -- factive verb "discover"
  | know              -- factive verb "know"
  | annoyed           -- emotive factive "be annoyed"
  | stop              -- change-of-state "stop"
  | only              -- focus-sensitive "only"
  | stupid            -- evaluative adjective "stupid"
  deriving DecidableEq, Repr, BEq

/-- Mean projectivity rating from Experiment 1a (0–100 scale).
    Ratings reflect the degree to which content projects past
    the family-of-sentences diagnostic (negation, question, modal, conditional).

    Values are approximate means from Figure 3 of the paper. -/
def projectivityRating : ExpressionType → ℚ
  | .nrrc              => 84
  | .nominalAppositive => 82
  | .possessiveNP      => 78
  | .discover          => 75
  | .know              => 72
  | .annoyed           => 70
  | .stop              => 68
  | .only              => 55
  | .stupid            => 42

/-- Mean at-issueness rating from Experiment 1b (0–100 scale).
    Higher = more at-issue (addresses the QUD).
    Measured via the "Hey wait a minute!" diagnostic and direct ratings.

    Values are approximate means from Figure 3. -/
def atIssuenessRating : ExpressionType → ℚ
  | .nrrc              => 28
  | .nominalAppositive => 32
  | .possessiveNP      => 38
  | .discover          => 45
  | .know              => 48
  | .annoyed           => 50
  | .stop              => 55
  | .only              => 62
  | .stupid            => 72

-- ════════════════════════════════════════════════════
-- § Experiment 2: Twenty Clause-Embedding Predicates
-- ════════════════════════════════════════════════════

/-- The 20 clause-embedding predicates from Experiments 2a and 2b.
    These overlap partially with Degen & Tonhauser (2021). -/
inductive Predicate where
  | establish
  | confess
  | reveal
  | discover
  | see
  | know
  | learn
  | findOut
  | notice
  | realize
  | isAware
  | isAmused
  | annoyed
  | beRight
  | acknowledge
  | confirm
  | demonstrate
  | prove
  | pretend
  | inform
  deriving DecidableEq, Repr, BEq

/-- Mean projectivity ratings for the 20 predicates from Exp 2a (0–100). -/
def verbProjectivity : Predicate → ℚ
  | .establish   => 60
  | .confess     => 62
  | .reveal      => 70
  | .discover    => 76
  | .see         => 72
  | .know        => 74
  | .learn       => 68
  | .findOut     => 66
  | .notice      => 73
  | .realize     => 75
  | .isAware     => 71
  | .isAmused    => 69
  | .annoyed     => 70
  | .beRight     => 78
  | .acknowledge => 64
  | .confirm     => 63
  | .demonstrate => 65
  | .prove       => 67
  | .pretend     => 45
  | .inform      => 58

/-- Mean at-issueness ratings for the 20 predicates from Exp 2b (0–100). -/
def verbAtIssueness : Predicate → ℚ
  | .establish   => 55
  | .confess     => 52
  | .reveal      => 42
  | .discover    => 38
  | .see         => 40
  | .know        => 39
  | .learn       => 44
  | .findOut     => 46
  | .notice      => 40
  | .realize     => 37
  | .isAware     => 42
  | .isAmused    => 44
  | .annoyed     => 43
  | .beRight     => 35
  | .acknowledge => 50
  | .confirm     => 51
  | .demonstrate => 48
  | .prove       => 45
  | .pretend     => 65
  | .inform      => 56

-- ════════════════════════════════════════════════════
-- § Verification Theorems
-- ════════════════════════════════════════════════════

/-- NRRCs are the most projective among the 9 expression types. -/
theorem nrrc_most_projective : ∀ e : ExpressionType,
    projectivityRating e ≤ projectivityRating .nrrc := by
  intro e; cases e <;> native_decide

/-- Evaluative adjectives (stupid) are the least projective. -/
theorem stupid_least_projective : ∀ e : ExpressionType,
    projectivityRating .stupid ≤ projectivityRating e := by
  intro e; cases e <;> native_decide

/-- NRRCs are the least at-issue among the 9 expression types. -/
theorem nrrc_least_atissue : ∀ e : ExpressionType,
    atIssuenessRating .nrrc ≤ atIssuenessRating e := by
  intro e; cases e <;> native_decide

/-- Evaluative adjectives (stupid) are the most at-issue. -/
theorem stupid_most_atissue : ∀ e : ExpressionType,
    atIssuenessRating e ≤ atIssuenessRating .stupid := by
  intro e; cases e <;> native_decide

/-- Anti-correlation: for the 9 expression types, the projectivity ordering
    is the reverse of the at-issueness ordering. More projective types
    are less at-issue. -/
theorem anticorrelation_expression_types :
    (projectivityRating .nrrc > projectivityRating .stupid) ∧
    (atIssuenessRating .nrrc < atIssuenessRating .stupid) ∧
    (projectivityRating .nominalAppositive > projectivityRating .only) ∧
    (atIssuenessRating .nominalAppositive < atIssuenessRating .only) := by
  native_decide

/-- Appositives are not maximally projective, contra Potts (2005).
    Potts predicted appositives should have projectivity = 100 (obligatory
    projection). The data shows 82/100 — high but not maximal. -/
theorem appositives_not_maximally_projective :
    projectivityRating .nominalAppositive < 100 := by native_decide

/-- Within-type variation: different clause-embedding predicates that are
    all traditionally classified as "factive" show different projectivity
    ratings. This supports gradient over binary classification. -/
theorem within_type_variation :
    verbProjectivity .discover ≠ verbProjectivity .know ∧
    verbProjectivity .know ≠ verbProjectivity .realize := by
  native_decide

/-- `beRight` has the highest projectivity among the 20 predicates. -/
theorem beRight_highest_verb_projectivity :
    ∀ p : Predicate, verbProjectivity p ≤ verbProjectivity .beRight := by
  intro p; cases p <;> native_decide

/-- `pretend` has the lowest projectivity — it is not a projective trigger. -/
theorem pretend_lowest_verb_projectivity :
    ∀ p : Predicate, verbProjectivity .pretend ≤ verbProjectivity p := by
  intro p; cases p <;> native_decide

/-- Anti-correlation holds for verb data: `beRight` has highest projectivity
    and lowest at-issueness; `pretend` has lowest projectivity and highest
    at-issueness. -/
theorem anticorrelation_verbs :
    (verbProjectivity .beRight > verbProjectivity .pretend) ∧
    (verbAtIssueness .beRight < verbAtIssueness .pretend) := by
  native_decide

-- ════════════════════════════════════════════════════
-- § Connection to ProjectiveTrigger
-- ════════════════════════════════════════════════════

/-- Map expression types to the existing `ProjectiveTrigger` enum from
    `ProjectiveContent.lean`, where a direct mapping exists. -/
def ExpressionType.toProjectiveTriggerName : ExpressionType → String
  | .nrrc              => "nrrc"
  | .nominalAppositive => "appositive"
  | .possessiveNP      => "possessive_np"
  | .discover          => "know_complement"
  | .know              => "know_complement"
  | .annoyed           => "know_complement"
  | .stop              => "stop_prestate"
  | .only              => "only_prejacent"
  | .stupid            => "expressive"  -- closest match in existing taxonomy

end Phenomena.Presupposition.Studies.TonhauserBeaverDegen2018
