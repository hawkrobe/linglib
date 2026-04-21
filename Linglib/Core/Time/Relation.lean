import Mathlib.Order.Basic

/-!
# Point temporal relations

The point analogue of `AllenRelation` (which operates on intervals).
A `Relation` is a domain-flavored selector over the standard partition
of pairs of times: before, after, overlapping, ≤, ≥, unrestricted.

Used by tense (past/present/future via `Core.Time.Tense.GramTense.toRelation`),
evidential semantics (`EPCondition.toRelation`), and modal-base time
analyses (`MBTProfile.toRelation` in Huijsmans 2025) — each domain
provides a name for one shape from the same partition.
-/

namespace Core.Time

/-- Temporal relation type for tense operators.
    Relates two times (typically event time and reference/speech time).
    The point analogue of `AllenRelation` (which operates on intervals). -/
inductive Relation where
  | before       -- t₁ < t₂
  | after        -- t₁ > t₂
  | overlapping  -- t₁ ◦ t₂ (simplified to equality for points)
  | notAfter     -- t₁ ≤ t₂
  | notBefore    -- t₁ ≥ t₂
  | unrestricted -- True (no constraint)
  deriving DecidableEq, Repr

namespace Relation

/-- Evaluate a temporal relation on two times -/
def eval {Time : Type*} [LinearOrder Time] :
    Relation → Time → Time → Prop
  | .before, t₁, t₂ => t₁ < t₂
  | .after, t₁, t₂ => t₁ > t₂
  | .overlapping, t₁, t₂ => t₁ = t₂
  | .notAfter, t₁, t₂ => t₁ ≤ t₂
  | .notBefore, t₁, t₂ => t₁ ≥ t₂
  | .unrestricted, _, _ => True

instance {Time : Type*} [LinearOrder Time] [DecidableEq Time]
    (r : Relation) (t₁ t₂ : Time) : Decidable (r.eval t₁ t₂) := by
  cases r <;> simp [eval] <;> infer_instance

end Relation

end Core.Time
