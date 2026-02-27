import Linglib.Core.Case.Basic

/-!
# Split-Ergative Conditioning @cite{blake-1994}

Blake (1994, Ch. 4) documents that **split-ergative** systems condition the
choice between ergative and accusative alignment on factors such as
tense/aspect (Hindi: perfective → ERG), person/animacy (Dyirbal: 3rd → ERG),
clause type, or NP type.

The `SplitErgativity` structure captures this: parameterized by a `Factor`
type and a predicate `ergCondition` that determines which factor values
trigger ergative alignment.

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press. Ch. 4.
- Dixon, R. M. W. (1994). *Ergativity*. Cambridge University Press.
-/

namespace Core

-- ============================================================================
-- § 1: Split-Ergative System
-- ============================================================================

/-- A split-ergative system: the alignment varies by some conditioning factor.

    The `ergCondition` predicate returns `true` for factor values that trigger
    ergative alignment, `false` for those that trigger accusative. -/
structure SplitErgativity (Factor : Type) where
  /-- Predicate: does this factor value trigger ergative alignment? -/
  ergCondition : Factor → Bool

/-- Alignment selected by a split-ergative system for a given factor value. -/
def SplitErgativity.alignment {Factor : Type} (split : SplitErgativity Factor)
    (f : Factor) : AlignmentFamily :=
  if split.ergCondition f then .ergative else .accusative

-- ============================================================================
-- § 2: Example: Hindi Tense/Aspect Split
-- ============================================================================

/-- Simple tense/aspect factor for split-ergative conditioning. -/
inductive Aspect where
  | perfective
  | imperfective
  deriving DecidableEq, BEq, Repr

/-- Hindi-style split: perfective → ergative, imperfective → accusative
    (Blake 1994, Ch. 4, pp. 107–110). -/
def hindiSplit : SplitErgativity Aspect :=
  { ergCondition := fun a => a == .perfective }

theorem hindi_perfective_erg :
    hindiSplit.alignment .perfective = .ergative := rfl

theorem hindi_imperfective_acc :
    hindiSplit.alignment .imperfective = .accusative := rfl

end Core
