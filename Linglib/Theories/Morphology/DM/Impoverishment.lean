import Linglib.Theories.Syntax.Minimalism.Core.Features

/-!
# Impoverishment (Distributed Morphology)
@cite{halle-marantz-1993} @cite{bonet-1991}

Impoverishment is a postsyntactic operation that deletes features from
a terminal node before Vocabulary Insertion. It is the DM mechanism for
deriving syncretism: when two morphosyntactic contexts share an exponent,
this can be explained by one context losing a distinguishing feature,
making it fall together with the other at VI.

## Architecture

An Impoverishment rule specifies:
1. A **trigger condition**: which features/contexts license deletion
2. A **target**: which feature(s) are deleted

After Impoverishment applies, the terminal has fewer features, which
may cause a less specific Vocabulary Item to be inserted (yielding
syncretism or default morphology).

## Connection to Mam

@cite{scott-2023} (ch. 4) analyzes pronoun reduction in SJA Mam as
deletion of the pronominal base morpheme when its features are
redundantly expressed by agreement. This is structurally parallel to
Impoverishment: features on the pronoun node are deleted (at PF) when
they are recoverable from agreement, yielding a reduced form.
-/

namespace Morphology.DM.Impoverishment

open Minimalism

-- ============================================================================
-- § 1: Impoverishment Rule
-- ============================================================================

/-- An Impoverishment rule: deletes features matching a condition from
    a feature bundle.

    - `condition`: which features trigger Impoverishment (the structural
      context / feature environment)
    - `target`: which feature to delete when the condition is met -/
structure ImpoverishmentRule where
  /-- Does this rule apply in the given feature context? -/
  condition : FeatureBundle → Bool
  /-- Which feature type is deleted? -/
  target : FeatureVal

-- ============================================================================
-- § 2: Applying Impoverishment
-- ============================================================================

/-- Delete all features matching `target` from a bundle. -/
def deleteFeature (fb : FeatureBundle) (target : FeatureVal) : FeatureBundle :=
  fb.filter (λ f => !f.featureType.sameType target)

/-- Apply an Impoverishment rule: if the condition is met, delete the
    target feature; otherwise return the bundle unchanged. -/
def applyImpoverishment (rule : ImpoverishmentRule) (fb : FeatureBundle) :
    FeatureBundle :=
  if rule.condition fb then deleteFeature fb rule.target
  else fb

/-- Apply a sequence of Impoverishment rules in order. -/
def applyImpoverishmentChain (rules : List ImpoverishmentRule)
    (fb : FeatureBundle) : FeatureBundle :=
  rules.foldl (λ acc rule => applyImpoverishment rule acc) fb

-- ============================================================================
-- § 3: Redundancy-Based Impoverishment
-- ============================================================================

/-- A feature is redundant when it is recoverable from another source
    (e.g., agreement morphology on the verb). This is the mechanism
    underlying pronoun reduction in Mam (@cite{scott-2023}, ch. 4):
    when all features of the pronominal base are also expressed by
    agreement, the base is deleted at PF.

    `recoverable` lists the features that are independently expressed
    (e.g., by agreement). `pronFeatures` lists the features on the
    pronoun. The pronoun base is deleted iff all its features are
    recoverable. -/
def allRecoverable (recoverable pronFeatures : List FeatureVal) : Bool :=
  pronFeatures.all (λ f => recoverable.any (f.sameType ·))

/-- Build a redundancy-based Impoverishment rule: delete `target` when
    the bundle contains features that are all recoverable from `source`. -/
def redundancyRule (source : List FeatureVal) (target : FeatureVal) :
    ImpoverishmentRule :=
  { condition := λ fb =>
      let feats := fb.map GramFeature.featureType
      allRecoverable source feats
  , target := target }

-- ============================================================================
-- § 4: Verification
-- ============================================================================

/-- Deleting a feature then deleting it again is the same as deleting once.
    (Filter is idempotent when the predicate is stable.) -/
theorem deleteFeature_idempotent (fb : FeatureBundle) (target : FeatureVal) :
    deleteFeature (deleteFeature fb target) target = deleteFeature fb target := by
  simp only [deleteFeature, List.filter_filter]
  congr 1
  ext f
  simp only [Bool.and_self]

end Morphology.DM.Impoverishment
