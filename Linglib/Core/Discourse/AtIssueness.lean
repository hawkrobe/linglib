import Linglib.Core.Discourse.QUD
import Linglib.Core.Scales.Scale
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Gradient At-Issueness and Projectivity
@cite{roberts-2012} @cite{tonhauser-beaver-degen-2018}

At-issueness and projectivity are **gradient**, not binary, and **anti-correlated**.
Tonhauser, Beaver & Degen (2018) report r = .85 (9 expression types) and
r = .99 (12 predicates) for the positive correlation between not-at-issueness
and projectivity, equivalently a negative correlation between at-issueness
and projectivity. This module lifts at-issueness from a binary enum (Roberts 2012)
to a bounded rational degree with threshold semantics, mirroring the pattern
used for gradable adjectives (degree > θ → positive meaning).

## Design

The structural parallel to adjective semantics is:

| Adjective               | At-issueness                   |
|--------------------------|--------------------------------|
| `Degree max` (Fin)       | `AtIssuenessDegree` (ℚ ∈ [0,1]) |
| `Threshold max`          | `AtIssuenessThreshold`         |
| `positiveMeaning d θ`    | `isAtIssue d θ`                |

We use `ℚ` with bound proofs rather than `Degree max` (= `Fin (max + 1)`)
because at-issueness is a continuous expression-level property — `ℚ` is more
natural and avoids an arbitrary `max` parameter.

-/

namespace Core.Discourse.AtIssueness

open Core.Scale (Boundedness)

-- ════════════════════════════════════════════════════
-- § Degree Types
-- ════════════════════════════════════════════════════

/-- A degree of at-issueness, bounded in [0, 1].
    0 = fully backgrounded (not at-issue), 1 = fully at-issue. -/
structure AtIssuenessDegree where
  value : ℚ
  nonneg : 0 ≤ value
  le_one : value ≤ 1
  deriving Repr

/-- A degree of projectivity, bounded in [0, 1].
    0 = no projection, 1 = obligatory projection. -/
structure ProjectivityDegree where
  value : ℚ
  nonneg : 0 ≤ value
  le_one : value ≤ 1
  deriving Repr

/-- Contextual threshold for at-issueness classification.
    Content with degree above this threshold counts as at-issue. -/
structure AtIssuenessThreshold where
  value : ℚ
  nonneg : 0 ≤ value
  le_one : value ≤ 1
  deriving Repr

/-- Contextual threshold for projectivity classification. -/
structure ProjectivityThreshold where
  value : ℚ
  nonneg : 0 ≤ value
  le_one : value ≤ 1
  deriving Repr

-- ════════════════════════════════════════════════════
-- § Threshold Semantics
-- ════════════════════════════════════════════════════

/-- Content is at-issue when its at-issueness degree exceeds the threshold.
    Mirrors `positiveMeaning` from `Adjective/Theory.lean`. -/
def isAtIssue (d : AtIssuenessDegree) (θ : AtIssuenessThreshold) : Bool :=
  decide (θ.value < d.value)

/-- Content is projective when its projectivity degree exceeds the threshold. -/
def isProjective (d : ProjectivityDegree) (θ : ProjectivityThreshold) : Bool :=
  decide (θ.value < d.value)

-- ════════════════════════════════════════════════════
-- § Classical Recovery
-- ════════════════════════════════════════════════════

/-- Binary at-issueness, recoverable from gradient degree + threshold.
    This is the same enum as in `ProjectiveContent.lean`, now derived. -/
inductive AtIssuenessClassical where
  | atIssue
  | notAtIssue
  deriving DecidableEq, Repr, BEq

/-- Recover binary classification from gradient degree and threshold. -/
def toClassical (d : AtIssuenessDegree) (θ : AtIssuenessThreshold) : AtIssuenessClassical :=
  if isAtIssue d θ then .atIssue else .notAtIssue

/-- Default threshold at 0.5, matching the midpoint of the [0, 1] scale. -/
def defaultThreshold : AtIssuenessThreshold :=
  ⟨1/2, by norm_num, by norm_num⟩

/-- Default projectivity threshold at 0.5. -/
def defaultProjectivityThreshold : ProjectivityThreshold :=
  ⟨1/2, by norm_num, by norm_num⟩

-- ════════════════════════════════════════════════════
-- § Anti-Correlation
-- ════════════════════════════════════════════════════

/-- A pair of at-issueness and projectivity ratings for a single expression. -/
structure GradientPair where
  atIssueness : ℚ
  projectivity : ℚ
  deriving Repr

/-- Anti-correlation property: across a list of expression ratings,
    higher at-issueness systematically co-occurs with lower projectivity.

    Tonhauser, Beaver & Degen (2018) report r = .85 across 9 expression
    types (Exp 1a) and r = .99 across 12 clause-embedding predicates
    (Exp 1b), for the positive correlation between not-at-issueness and
    projectivity. This is equivalent to an anti-correlation between
    at-issueness and projectivity.

    This structure captures the deterministic (monotone) version of the
    Gradient Projection Principle. The statistical version uses Pearson r. -/
structure AntiCorrelation where
  /-- The paired ratings -/
  pairs : List GradientPair
  /-- For any two items, if one has higher at-issueness, it should
      have lower projectivity (qualitative anti-correlation). -/
  anticorrelated : ∀ (i j : Fin pairs.length),
    (pairs.get i).atIssueness < (pairs.get j).atIssueness →
    (pairs.get j).projectivity ≤ (pairs.get i).projectivity

-- ════════════════════════════════════════════════════
-- § QUD Connection
-- ════════════════════════════════════════════════════

/-- Qualitative connection between QUD and at-issueness: content that
    doesn't distinguish QUD cells has low at-issueness.

    Roberts (2012): at-issue content is content that addresses the QUD.
    Content that yields the same truth value across all worlds within
    each QUD cell is backgrounded (not at-issue).

    The full measure-theoretic version would compute mutual information
    between content and QUD partition. -/
def atIssuenessFromQUD {M : Type*} (q : QUD M)
    (content : M → Bool) (worlds : List M) : AtIssuenessDegree :=
  -- If content is constant across all worlds (doesn't distinguish anything),
  -- at-issueness is 0. If it varies within QUD cells, it's more at-issue.
  -- This is a qualitative approximation; the full version needs measure theory.
  let varies := worlds.any λ w₁ =>
    worlds.any λ w₂ => q.sameAnswer w₁ w₂ && (content w₁ != content w₂)
  if varies then
    ⟨1, by norm_num, le_refl 1⟩
  else
    ⟨0, le_refl 0, by norm_num⟩

-- ════════════════════════════════════════════════════
-- § Order Instances
-- ════════════════════════════════════════════════════

instance : LE AtIssuenessDegree where
  le a b := a.value ≤ b.value

instance : LE ProjectivityDegree where
  le a b := a.value ≤ b.value

instance : Preorder AtIssuenessDegree where
  le_refl a := @le_refl ℚ _ a.value
  le_trans a b c (hab : a.value ≤ b.value) (hbc : b.value ≤ c.value) :=
    @le_trans ℚ _ a.value b.value c.value hab hbc

instance : Preorder ProjectivityDegree where
  le_refl a := @le_refl ℚ _ a.value
  le_trans a b c (hab : a.value ≤ b.value) (hbc : b.value ≤ c.value) :=
    @le_trans ℚ _ a.value b.value c.value hab hbc

/-- Both at-issueness and projectivity are closed-bounded scales on [0, 1]. -/
def atIssuenessBoundedness : Boundedness := .closed
def projectivityBoundedness : Boundedness := .closed

-- ════════════════════════════════════════════════════
-- § Smart Constructors
-- ════════════════════════════════════════════════════

/-- Construct an at-issueness degree from a rational in [0, 100],
    normalizing to [0, 1]. Useful for entering experimental ratings. -/
def AtIssuenessDegree.ofPercent (n : ℚ) (h0 : 0 ≤ n) (h1 : n ≤ 100) :
    AtIssuenessDegree :=
  ⟨n / 100, div_nonneg h0 (by norm_num), by linarith⟩

/-- Construct a projectivity degree from a rational in [0, 100],
    normalizing to [0, 1]. -/
def ProjectivityDegree.ofPercent (n : ℚ) (h0 : 0 ≤ n) (h1 : n ≤ 100) :
    ProjectivityDegree :=
  ⟨n / 100, div_nonneg h0 (by norm_num), by linarith⟩

end Core.Discourse.AtIssueness
