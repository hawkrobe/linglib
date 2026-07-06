import Linglib.Semantics.Questions.Partition.QUD
import Linglib.Semantics.Questions.PrecisionProjection
import Linglib.Discourse.QUD.Basic
import Linglib.Core.Order.Boundedness
import Linglib.Core.Order.Rat01
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
/-!
# Gradient At-Issueness and Projectivity
[roberts-2012] [tonhauser-beaver-degen-2018]
Tonhauser-Beaver-Degen 2018's gradient at-issueness model: degrees
and thresholds in `Rat01`, with at-issueness anti-correlated with
projectivity. Mirrors the gradable-adjective pattern (degree > θ →
positive meaning).
-/
namespace Discourse.AtIssueness
open Core.Order (Boundedness Rat01)
/-! ### Degree Types -/
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
/-! ### Threshold Semantics -/
/-- Content is at-issue when its degree exceeds the threshold. -/
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
/-! ### Classical Recovery -/
/-- Binary at-issueness, recoverable from gradient degree + threshold. -/
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
/-! ### Anti-Correlation -/
/-- A pair of at-issueness and projectivity ratings for a single expression. -/
structure GradientPair where
  atIssueness : ℚ
  projectivity : ℚ
  deriving Repr
/-- A monotone-anti-correlation bundle: every pair ordering on at-issueness
    forces the reverse weak ordering on projectivity. This is a *structural*
    strengthening of the empirical Gradient Projection Principle of
    [tonhauser-beaver-degen-2018], who establish a gradient negative
    correlation across content classes (with substantial within-class and
    item-level variance), not a deterministic monotone pairing across every
    stimulus pair. Suitable for analytical scenarios where the strict-monotone
    fragment is the object of study; not a faithful summary of the paper's
    empirical claim. -/
structure MonotoneAntiCorrelation where
  pairs : List GradientPair
  anticorrelated : ∀ (i j : Fin pairs.length),
    (pairs.get i).atIssueness < (pairs.get j).atIssueness →
    (pairs.get j).projectivity ≤ (pairs.get i).projectivity
/-! ### QUD Connection -/
/-- Qualitative QUD-based at-issueness: content varying within QUD cells
    counts as at-issue ([roberts-2012]). -/
def atIssuenessFromQUD {M : Type*} (q : QUD M)
    (content : M → Bool) (worlds : List M) : AtIssuenessDegree :=
  let varies := worlds.any λ w₁ =>
    worlds.any λ w₂ => q.sameAnswer w₁ w₂ && (content w₁ != content w₂)
  if varies then
    ⟨1, by norm_num, le_refl 1⟩
  else
    ⟨0, le_refl 0, by norm_num⟩
/-! ### Boundedness -/
/-- Both at-issueness and projectivity are closed-bounded scales on [0, 1]. -/
def atIssuenessBoundedness : Boundedness := .closed
def projectivityBoundedness : Boundedness := .closed
/-! ### Smart Constructors -/
/-- Construct a degree from [0, 100], normalizing to [0, 1]. -/
def ofPercent (n : ℚ) (h0 : 0 ≤ n) (h1 : n ≤ 100) : Rat01 :=
  ⟨n / 100, div_nonneg h0 (by norm_num), by linarith⟩
end Discourse.AtIssueness
