import Linglib.Core.Case.Basic
import Linglib.Core.Prominence

/-!
# Split-Ergative Conditioning @cite{blake-1994}

Blake (1994, Ch. 4) documents that **split-ergative** systems condition the
choice between ergative and accusative alignment on one or more of these
factors:

- **Tense/aspect**: perfective → ergative, imperfective → accusative (Hindi,
  pp. 107–110)
- **Person/animacy**: SAP (1st/2nd) → accusative, 3rd → ergative (Dyirbal,
  pp. 104–107)
- **Clause type**: main clause → ergative, subordinate → accusative
- **NP type**: full NP → ergative, pronoun → accusative (many Australian)

These conditioning factors interact with the prominence scales already
formalized in `Core.Prominence` (Aissen 2003, Just 2024). The key insight
(Silverstein 1976): ergative marking correlates with **low prominence** of
the A argument (non-topical, non-definite, full NP), while accusative marking
correlates with **high prominence** (topical, definite, pronominal).

## References

- Blake, B. J. (1994). *Case*. Cambridge University Press. Ch. 4.
- Silverstein, M. (1976). Hierarchy of features and ergativity. In Dixon, R.
  M. W. (ed.), *Grammatical Categories in Australian Languages*. AIAS.
- Dixon, R. M. W. (1994). *Ergativity*. Cambridge University Press.
- Aissen, J. (2003). Differential Object Marking: Iconicity vs. Economy.
  *NLLT* 21(3): 435–483.
-/

namespace Core

open Core.Prominence

-- ============================================================================
-- § 1: Split Conditioning Domain
-- ============================================================================

/-- The domain that conditions a split-ergative system.

    Each constructor represents a parameter space: the system is ergative
    for some values and accusative for others. -/
inductive SplitDomain where
  /-- Split conditioned by tense/aspect (e.g., Hindi: perfective → ERG) -/
  | tenseAspect
  /-- Split conditioned by person or animacy hierarchy (e.g., Dyirbal) -/
  | personAnimacy
  /-- Split conditioned by clause type (main vs. subordinate) -/
  | clauseType
  /-- Split conditioned by NP type (full NP vs. pronoun) -/
  | npType
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Split-Ergative System
-- ============================================================================

/-- A split-ergative system: the alignment varies by some conditioning factor.

    The `ergCondition` predicate returns `true` for factor values that trigger
    ergative alignment, `false` for those that trigger accusative. -/
structure SplitErgativity (Factor : Type) where
  /-- Which conditioning domain this split belongs to -/
  domain : SplitDomain
  /-- Predicate: does this factor value trigger ergative alignment? -/
  ergCondition : Factor → Bool

/-- Alignment selected by a split-ergative system for a given factor value. -/
def SplitErgativity.alignment {Factor : Type} (split : SplitErgativity Factor)
    (f : Factor) : AlignmentFamily :=
  if split.ergCondition f then .ergative else .accusative

-- ============================================================================
-- § 3: Prominence-Based Splits (Silverstein 1976)
-- ============================================================================

/-- Silverstein's hierarchy predicts that ergative marking targets the
    **less prominent** end of the animacy/definiteness scale. More prominent
    NPs (pronouns, 1st/2nd person) get accusative treatment.

    Given a prominence threshold, NPs at or above the threshold get accusative
    alignment; those below get ergative. -/
def silverstein (threshold : Nat) (npProminence : Nat) : AlignmentFamily :=
  if npProminence ≥ threshold then .accusative else .ergative

-- ============================================================================
-- § 4: Example Split Systems
-- ============================================================================

/-- Simple tense/aspect split: a Boolean factor (true = perfective). -/
inductive Aspect where
  | perfective
  | imperfective
  deriving DecidableEq, BEq, Repr

/-- Hindi-style split: perfective → ergative, imperfective → accusative. -/
def hindiSplit : SplitErgativity Aspect :=
  { domain := .tenseAspect
    ergCondition := fun a => a == .perfective }

theorem hindi_perfective_erg :
    hindiSplit.alignment .perfective = .ergative := rfl

theorem hindi_imperfective_acc :
    hindiSplit.alignment .imperfective = .accusative := rfl

/-- Dyirbal-style split by animacy: human/animate → ACC, inanimate → ERG. -/
def dyirbalSplit : SplitErgativity AnimacyLevel :=
  { domain := .personAnimacy
    ergCondition := fun a => a == .inanimate }

theorem dyirbal_human_acc :
    dyirbalSplit.alignment .human = .accusative := rfl

theorem dyirbal_inanimate_erg :
    dyirbalSplit.alignment .inanimate = .ergative := rfl

-- ============================================================================
-- § 5: Silverstein Properties
-- ============================================================================

/-- With a high threshold, everything below is ergative. -/
theorem silverstein_low_erg :
    silverstein 5 0 = .ergative := rfl

/-- With a low threshold, most NPs get accusative treatment. -/
theorem silverstein_high_acc :
    silverstein 1 3 = .accusative := rfl

/-- At the threshold boundary, the NP gets accusative treatment (≥). -/
theorem silverstein_at_threshold :
    silverstein 3 3 = .accusative := rfl

/-- Below the threshold → ergative. -/
theorem silverstein_below_threshold :
    silverstein 3 2 = .ergative := rfl

/-- Silverstein is monotone: if prominence p₁ ≥ p₂ and p₂ gets accusative,
    then p₁ gets accusative. (Higher prominence → more likely accusative.) -/
theorem silverstein_monotone (threshold p₁ p₂ : Nat)
    (h_ge : p₁ ≥ p₂) (h_acc : silverstein threshold p₂ = .accusative) :
    silverstein threshold p₁ = .accusative := by
  simp only [silverstein] at *
  split at h_acc
  · split
    · rfl
    · omega
  · contradiction

end Core
