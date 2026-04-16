import Linglib.Theories.Morphology.DM.Impoverishment

/-!
# Metathesis (Distributed Morphology)
@cite{harris-halle-2005} @cite{arregi-nevins-2012} @cite{middleton-2026}

Metathesis is a postsyntactic operation that swaps the linear order of
two adjacent terminals before Vocabulary Insertion. It is part of the
linearization-and-after stage of the modular postsyntax of
@cite{arregi-nevins-2012}: structural operations (Impoverishment) feed
linear ones (Metathesis), not vice versa.

Like `ImpoverishmentRule`, a metathesis rule is keyed on a
`Neighborhood` and carries a decidable condition. The structural
change is to swap two distinguished feature *types* in the focus
bundle: the rule names a pair of feature types and exchanges the
positions of the first occurrences of each.

This file provides only the rule type, smart constructor, and
applicator. The architectural claim that metathesis follows
impoverishment is encoded in
`Theories/Morphology/DM/PostsyntacticDerivation.lean` and verified
against the Taos data in
`Phenomena/Allomorphy/Studies/Middleton2026.lean`.
-/

namespace Morphology.DM.Metathesis

open Minimalism Morphology.DM.Impoverishment

-- ============================================================================
-- § 1: Metathesis Rule
-- ============================================================================

/-- A Metathesis rule swaps the linear order of two feature types in the
    focus bundle when its condition holds.

    `swapFst` and `swapSnd` name the two feature *types* (matched via
    `FeatureVal.sameType`) whose first occurrences in the focus should
    exchange positions. The directionality matches the Arregi & Nevins
    notation `[[X] ⟩ ⟨ [Y]] / Z`: read "swap X and Y in environment Z." -/
structure MetathesisRule where
  condition : Neighborhood → Prop
  decCond : DecidablePred condition
  swapFst : FeatureVal
  swapSnd : FeatureVal

instance (rule : MetathesisRule) (n : Neighborhood) :
    Decidable (rule.condition n) := rule.decCond n

-- ============================================================================
-- § 2: Smart Constructor
-- ============================================================================

/-- Build a metathesis rule from a Boolean condition over the focus
    bundle (paradigmatic-style — the most common case in the Taos rules
    of @cite{middleton-2026}, where the condition refers only to the
    feature inventory of the same node being reordered). -/
def focusRule (focusCheck : FeatureBundle → Bool)
    (swapFst swapSnd : FeatureVal) : MetathesisRule where
  condition n := focusCheck n.focus = true
  decCond n := inferInstanceAs (Decidable (focusCheck n.focus = true))
  swapFst := swapFst
  swapSnd := swapSnd

-- ============================================================================
-- § 3: Applying Metathesis
-- ============================================================================

/-- Index of the first feature in `fb` whose type matches `fv`. -/
def indexOfType (fb : FeatureBundle) (fv : FeatureVal) : Option Nat :=
  fb.findIdx? (λ f => f.featureType.sameType fv)

/-- Swap the elements at positions `i` and `j` in a list. Out-of-bounds
    indices leave the list unchanged. -/
def swapAt {α : Type _} (l : List α) (i j : Nat) : List α :=
  match l[i]?, l[j]? with
  | some xi, some xj => (l.set i xj).set j xi
  | _, _ => l

/-- Apply a metathesis rule at a neighborhood: when the condition holds,
    locate the first occurrences of `swapFst` and `swapSnd` in the focus
    and exchange their positions; otherwise return the focus unchanged. -/
def applyMetathesis (rule : MetathesisRule) (n : Neighborhood) :
    FeatureBundle :=
  if rule.condition n then
    match indexOfType n.focus rule.swapFst, indexOfType n.focus rule.swapSnd with
    | some i, some j => swapAt n.focus i j
    | _, _ => n.focus
  else n.focus

/-- Apply a sequence of metathesis rules left-to-right. Each rule sees
    the focus as updated by prior rules; surrounding context is held
    fixed (one cycle of metathesis, in DM terms). -/
def applyMetathesisChain (rules : List MetathesisRule) (n : Neighborhood) :
    FeatureBundle :=
  rules.foldl (init := n.focus)
    (λ focusAcc rule => applyMetathesis rule { n with focus := focusAcc })

/-- Convenience: apply a rule to a bare focus bundle with no context. -/
def MetathesisRule.applyToBundle (rule : MetathesisRule)
    (fb : FeatureBundle) : FeatureBundle :=
  applyMetathesis rule (Neighborhood.ofBundle fb)

end Morphology.DM.Metathesis
