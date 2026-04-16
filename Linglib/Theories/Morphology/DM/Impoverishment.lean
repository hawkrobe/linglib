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

A rule is evaluated against a `Neighborhood` — the focus terminal plus
its immediately adjacent terminals — and a `Prop`-valued condition.
The `focus`/context split is what licenses the
**paradigmatic / syntagmatic** distinction structurally: a rule whose
condition factors through `Neighborhood.focus` is *paradigmatic* (refers
to one node only); otherwise it is *syntagmatic*. This is a
**theorem about the rule**, not a stipulation, so paradigmatic-vs-
syntagmatic claims can be discharged by proof rather than annotation.

## Connection to Mam

@cite{scott-2023} (ch. 4) analyzes pronoun reduction in SJA Mam as
deletion of the pronominal base morpheme when its features are
redundantly expressed by agreement. This is structurally parallel to
Impoverishment: features on the pronoun node are deleted (at PF) when
they are recoverable from agreement, yielding a reduced form. Mam's
rule is paradigmatic — see `Phenomena/Agreement/Studies/Scott2023.lean`.
-/

namespace Morphology.DM.Impoverishment

open Minimalism

-- ============================================================================
-- § 1: Neighborhoods
-- ============================================================================

/-- The local context a postsyntactic rule may inspect. The `focus` bundle
    is the terminal targeted for deletion; `leftCtx` and `rightCtx` are
    the bundles of immediately adjacent terminals (left- and right-adjacent
    in the morphological structure).

    Splitting `focus` from context is what makes the
    paradigmatic/syntagmatic distinction structural. A condition that
    only inspects `focus` is paradigmatic by construction; one that
    reads `leftCtx` or `rightCtx` is syntagmatic. -/
structure Neighborhood where
  focus    : FeatureBundle
  leftCtx  : List FeatureBundle := []
  rightCtx : List FeatureBundle := []
  deriving Repr

/-- A bundle, viewed as a context-free neighborhood. -/
def Neighborhood.ofBundle (fb : FeatureBundle) : Neighborhood :=
  { focus := fb }

-- ============================================================================
-- § 2: Impoverishment Rule
-- ============================================================================

/-- An Impoverishment rule deletes `target` from the focus terminal when
    `condition` holds over the neighborhood.

    `condition` is `Prop`-valued (the mathlib idiom — see CHANGELOG entry
    for `GroszJoshiWeinstein1995.lean` and the OT/Conditionals migrations);
    a `DecidablePred` witness is carried alongside so that
    `applyImpoverishment` reduces by `decide` on concrete inputs. -/
structure ImpoverishmentRule where
  /-- Does this rule apply at the given neighborhood? -/
  condition : Neighborhood → Prop
  /-- Decidability witness, exposed as an instance (see below). -/
  decCond : DecidablePred condition
  /-- Which feature type is deleted from the focus bundle. -/
  target : FeatureVal

/-- Expose the rule's decidability as an instance so that
    `if rule.condition n then ... else ...` elaborates. -/
instance (rule : ImpoverishmentRule) (n : Neighborhood) :
    Decidable (rule.condition n) := rule.decCond n

-- ============================================================================
-- § 3: Paradigmatic / Syntagmatic — a Theorem, not a Label
-- ============================================================================

/-- A rule is **paradigmatic** iff its condition factors through the
    focus bundle: any two neighborhoods with the same focus agree on
    the condition. This is the structural counterpart of
    @cite{arregi-nevins-2012}'s "rule conditioned by the features of
    only one node."

    Crucially, this is a **theorem about a rule**, not a flag. Smart
    constructors below (`paradigmatic`, `syntagmatic`) discharge it
    automatically when the condition is built focus-only. -/
def Paradigmatic (r : ImpoverishmentRule) : Prop :=
  ∀ n₁ n₂ : Neighborhood, n₁.focus = n₂.focus → (r.condition n₁ ↔ r.condition n₂)

/-- A rule is **syntagmatic** iff it is not paradigmatic — i.e., there
    exist neighborhoods agreeing on focus that disagree on the condition,
    so the condition genuinely depends on context. -/
def Syntagmatic (r : ImpoverishmentRule) : Prop := ¬ Paradigmatic r

-- ============================================================================
-- § 4: Smart Constructors
-- ============================================================================

/-- Build a paradigmatic rule from a focus-only Boolean check. The
    `Paradigmatic` proof is automatic via `paradigmatic_isParadigmatic`. -/
def paradigmatic (focusCheck : FeatureBundle → Bool) (target : FeatureVal) :
    ImpoverishmentRule where
  condition n := focusCheck n.focus = true
  decCond n := inferInstanceAs (Decidable (focusCheck n.focus = true))
  target := target

/-- A rule built by `paradigmatic` is paradigmatic by construction. -/
theorem paradigmatic_isParadigmatic
    (focusCheck : FeatureBundle → Bool) (target : FeatureVal) :
    Paradigmatic (paradigmatic focusCheck target) := by
  intro n₁ n₂ hfoc
  simp only [paradigmatic, hfoc]

/-- Build a (potentially) syntagmatic rule from a full-neighborhood
    Boolean check. Whether the result is genuinely syntagmatic depends
    on `cond` — verify with a separate `Syntagmatic` proof if needed. -/
def syntagmatic (cond : Neighborhood → Bool) (target : FeatureVal) :
    ImpoverishmentRule where
  condition n := cond n = true
  decCond n := inferInstanceAs (Decidable (cond n = true))
  target := target

-- ============================================================================
-- § 5: Applying Impoverishment
-- ============================================================================

/-- Delete all features matching `target` from a bundle. -/
def deleteFeature (fb : FeatureBundle) (target : FeatureVal) : FeatureBundle :=
  fb.filter (λ f => !f.featureType.sameType target)

/-- Apply an Impoverishment rule at a neighborhood: when the condition
    holds, return the focus with `target` deleted; otherwise return the
    focus unchanged. -/
def applyImpoverishment (rule : ImpoverishmentRule) (n : Neighborhood) :
    FeatureBundle :=
  if rule.condition n then deleteFeature n.focus rule.target else n.focus

/-- Apply a sequence of rules. Each rule sees the *updated* focus from
    prior rules, but the surrounding context bundles are held fixed for
    the duration of the chain (one cycle of impoverishment, in DM terms). -/
def applyImpoverishmentChain (rules : List ImpoverishmentRule)
    (n : Neighborhood) : FeatureBundle :=
  rules.foldl (init := n.focus)
    (λ focusAcc rule => applyImpoverishment rule { n with focus := focusAcc })

/-- Convenience: apply a rule to a bare focus bundle with no surrounding
    context. Useful for paradigmatic rules where context is irrelevant. -/
def ImpoverishmentRule.applyToBundle (rule : ImpoverishmentRule)
    (fb : FeatureBundle) : FeatureBundle :=
  applyImpoverishment rule (Neighborhood.ofBundle fb)

-- ============================================================================
-- § 6: Redundancy-Based Impoverishment
-- ============================================================================

/-- A feature is redundant when it is recoverable from another source
    (e.g., agreement morphology on the verb). This is the mechanism
    underlying pronoun reduction in Mam (@cite{scott-2023}, ch. 4):
    when all features of the pronominal base are also expressed by
    agreement, the base is deleted at PF. -/
def allRecoverable (recoverable pronFeatures : List FeatureVal) : Bool :=
  pronFeatures.all (λ f => recoverable.any (f.sameType ·))

/-- Build a redundancy-based Impoverishment rule. The condition only
    inspects the focus bundle, so the rule is paradigmatic by
    construction. -/
def redundancyRule (source : List FeatureVal) (target : FeatureVal) :
    ImpoverishmentRule :=
  paradigmatic
    (λ fb => allRecoverable source (fb.map GramFeature.featureType))
    target

/-- Redundancy rules are paradigmatic. -/
theorem redundancyRule_isParadigmatic (source : List FeatureVal)
    (target : FeatureVal) : Paradigmatic (redundancyRule source target) :=
  paradigmatic_isParadigmatic _ _

-- ============================================================================
-- § 7: Verification
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
