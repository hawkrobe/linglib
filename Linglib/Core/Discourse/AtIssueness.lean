import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Core.Scales.Scale
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Gradient At-Issueness and Projectivity
@cite{roberts-2012} @cite{tonhauser-beaver-degen-2018}

At-issueness and projectivity are **gradient**, not binary, and **anti-correlated**.
@cite{tonhauser-beaver-degen-2018} report r = .85 (9 expression types) and
r = .99 (12 predicates) for the positive correlation between not-at-issueness
and projectivity, equivalently a negative correlation between at-issueness
and projectivity. This module lifts at-issueness from a binary enum
to a bounded rational degree with threshold semantics, mirroring the pattern
used for gradable adjectives (degree > θ → positive meaning).

## Design

All four degree/threshold types are `Rat01` (= `↥(Set.Icc (0 : ℚ) 1)`)
from `Core.Scales.Scale`. The type aliases document intent but share
infrastructure (order instances, smart constructors, etc.).

| Adjective               | At-issueness                   |
|--------------------------|--------------------------------|
| `Degree max` (Fin)       | `AtIssuenessDegree` (`Rat01`)  |
| `Threshold max`          | `AtIssuenessThreshold` (`Rat01`) |
| `positiveMeaning d θ`    | `isAtIssue d θ`                |

-/

namespace Core.Discourse.AtIssueness

open Core.Scale (Boundedness Rat01)

-- ════════════════════════════════════════════════════
-- § Degree Types
-- ════════════════════════════════════════════════════

/-- A degree of at-issueness ∈ [0, 1].
    0 = fully backgrounded (not at-issue), 1 = fully at-issue. -/
abbrev AtIssuenessDegree := Rat01

/-- A degree of projectivity ∈ [0, 1].
    0 = no projection, 1 = obligatory projection. -/
abbrev ProjectivityDegree := Rat01

/-- Contextual threshold for at-issueness classification.
    Content with degree above this threshold counts as at-issue. -/
abbrev AtIssuenessThreshold := Rat01

/-- Contextual threshold for projectivity classification. -/
abbrev ProjectivityThreshold := Rat01

-- ════════════════════════════════════════════════════
-- § Threshold Semantics
-- ════════════════════════════════════════════════════

/-- Content is at-issue when its at-issueness degree exceeds the threshold.
    Mirrors `positiveMeaning` from `Adjective/Theory.lean`. -/
def isAtIssue (d : AtIssuenessDegree) (θ : AtIssuenessThreshold) : Prop :=
  Rat01.exceeds d θ

instance (d : AtIssuenessDegree) (θ : AtIssuenessThreshold) :
    Decidable (isAtIssue d θ) :=
  inferInstanceAs (Decidable (Rat01.exceeds d θ))

/-- Content is projective when its projectivity degree exceeds the threshold. -/
def isProjective (d : ProjectivityDegree) (θ : ProjectivityThreshold) : Prop :=
  Rat01.exceeds d θ

instance (d : ProjectivityDegree) (θ : ProjectivityThreshold) :
    Decidable (isProjective d θ) :=
  inferInstanceAs (Decidable (Rat01.exceeds d θ))

-- ════════════════════════════════════════════════════
-- § Classical Recovery
-- ════════════════════════════════════════════════════

/-- Binary at-issueness, recoverable from gradient degree + threshold.
    This is the same enum as in `ProjectiveContent.lean`, now derived. -/
inductive AtIssuenessClassical where
  | atIssue
  | notAtIssue
  deriving DecidableEq, Repr

/-- Recover binary classification from gradient degree and threshold. -/
def toClassical (d : AtIssuenessDegree) (θ : AtIssuenessThreshold) : AtIssuenessClassical :=
  if isAtIssue d θ then .atIssue else .notAtIssue

/-- Default threshold at 0.5, matching the midpoint of the [0, 1] scale. -/
def defaultThreshold : AtIssuenessThreshold := Rat01.half

/-- Default projectivity threshold at 0.5. -/
def defaultProjectivityThreshold : ProjectivityThreshold := Rat01.half

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

    @cite{tonhauser-beaver-degen-2018} report r = .85 across 9 expression
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

    @cite{roberts-2012}: at-issue content is content that addresses the QUD.
    Content that yields the same truth value across all worlds within
    each QUD cell is backgrounded (not at-issue).

    The full measure-theoretic version would compute mutual information
    between content and QUD partition. -/
def atIssuenessFromQUD {M : Type*} (q : QUD M)
    (content : M → Bool) (worlds : List M) : AtIssuenessDegree :=
  let varies := worlds.any λ w₁ =>
    worlds.any λ w₂ => q.sameAnswer w₁ w₂ && (content w₁ != content w₂)
  if varies then
    ⟨1, by norm_num, le_refl 1⟩
  else
    ⟨0, le_refl 0, by norm_num⟩

-- ════════════════════════════════════════════════════
-- § Boundedness
-- ════════════════════════════════════════════════════

/-- Both at-issueness and projectivity are closed-bounded scales on [0, 1]. -/
def atIssuenessBoundedness : Boundedness := .closed
def projectivityBoundedness : Boundedness := .closed

-- ════════════════════════════════════════════════════
-- § Smart Constructors
-- ════════════════════════════════════════════════════

/-- Construct a degree from a rational in [0, 100], normalizing to [0, 1].
    Useful for entering experimental ratings. -/
def ofPercent (n : ℚ) (h0 : 0 ≤ n) (h1 : n ≤ 100) : Rat01 :=
  ⟨n / 100, div_nonneg h0 (by norm_num), by linarith⟩

end Core.Discourse.AtIssueness
