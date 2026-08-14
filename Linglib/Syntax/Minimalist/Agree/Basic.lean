import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Minimalist.Phase.Basic
import Linglib.Syntax.Minimalist.Probe.Transmission

/-!
# Agree (Minimalist Feature Checking)

Formalization of Agree following [chomsky-2000] and [adger-2003].

Agree is the mechanism by which features are checked/valued:
1. A **probe** (head with unvalued feature) searches its c-command domain
2. It finds the closest **goal** (element with matching valued feature)
3. The probe's feature is valued by copying from the goal
4. Both features are then checked (and may delete at PF/LF)

This file states Agree's structural conditions over `SyntacticObject`
trees (c-command locality, horizons, phase-boundedness) and the valuation
step over `FeatureBundle`s. Bundles live in a *feature assignment*
`LIToken → FeatureBundle` rather than in the carrier — the free-Merge core
keeps `SO₀` features atomic (`Features/Slot.lean`) — and a constituent
exposes its projecting head's bundle through selection-driven labeling
(`headBundle`). The feature *types* live in `Features.lean`; the search
kernel and failure model ([preminger-2014] Ch. 5) in `Probe/Basic.lean`;
richer satisfaction conditions ([deal-2024], [keine-2019]) in
`Probe/Satisfaction.lean`; the Case Filter in `Syntax/Case/Filter.lean`.
-/

namespace Minimalist

open SyntacticObject

/-! ### Agree relations

Feature bundles live in a *feature assignment* `LIToken → FeatureBundle`,
not in the carrier (`Features/Slot.lean`). A constituent exposes its
projecting head's bundle through selection-driven labeling
(`SyntacticObject.selHead`), so an Agree relation's feature conditions and
its structural conditions are read off one tree and one assignment. -/

/-- The feature bundle `s` exposes to Agree under the assignment `feats`:
    its projecting head's bundle. An unlabelable constituent exposes no
    features (`⊥`), so it can neither probe nor serve as a goal. -/
def headBundle (feats : LIToken → FeatureBundle) (s : SyntacticObject) : FeatureBundle :=
  (s.selHead.map feats).getD ⊥

@[simp] theorem headBundle_lexLeaf (feats : LIToken → FeatureBundle) (tok : LIToken) :
    headBundle feats (lexLeaf tok) = feats tok := rfl

/-- Valid Agree under a feature assignment: `probe` c-commands `goal` in
    `root`, the probe's head bears an unvalued `t`-slot, and the goal's head
    bears a valued one. -/
def validAgree (feats : LIToken → FeatureBundle) (root probe goal : SyntacticObject)
    (t : FeatureType) : Prop :=
  cCommandsIn root probe goal ∧
  (headBundle feats probe).hasUnvaluedFeature t = true ∧
  (headBundle feats goal).hasValuedFeature t = true

instance (feats : LIToken → FeatureBundle) (root probe goal : SyntacticObject)
    (t : FeatureType) : Decidable (validAgree feats root probe goal t) := by
  unfold validAgree; infer_instance

/-- Nothing Agrees with itself: one slot cannot be both unvalued and valued.
    Irreflexivity is a fact about the assignment being a single source of
    feature truth, not about c-command (a multiply-occurring subterm can
    c-command itself). -/
theorem validAgree_irrefl (feats : LIToken → FeatureBundle) (root s : SyntacticObject)
    (t : FeatureType) : ¬ validAgree feats root s s t := by
  rintro ⟨-, hu, hv⟩
  cases h : headBundle feats s t <;>
    simp [FeatureBundle.hasUnvaluedFeature, FeatureBundle.hasValuedFeature,
      Features.FeatureSlot.isUnvalued, Features.FeatureSlot.isValued, h] at hu hv

/-! ### Locality: closest goal

"Closest matching goal, no intervener" is canonically the list engine
`Probe.search` (`Probe/Basic.lean`, `search_eq_some_iff_closest`, with `pred`
playing `Probe.vis`). `SyntacticObject` is a commutative magma with no
canonical c-command linearization, so the tree↔list bridge is not
definitional; `isClosestGoalIn` is the decidable tree-native presentation. -/

/-- `goal` is a closest `pred`-goal for `probe` in `root`: `pred`-matching and
    c-commanded by `probe`, with no `pred`-matching node c-commanded by `probe`
    c-commanding `goal`. -/
def isClosestGoalIn (root probe goal : SyntacticObject)
    (pred : SyntacticObject → Bool) : Prop :=
  cCommandsIn root probe goal ∧ pred goal = true ∧
    ¬∃ x ∈ root.subtrees,
      x ≠ goal ∧ pred x = true ∧ cCommandsIn root probe x ∧ cCommandsIn root x goal

instance (root probe goal : SyntacticObject) (pred : SyntacticObject → Bool) :
    Decidable (isClosestGoalIn root probe goal pred) := by
  unfold isClosestGoalIn
  have : Decidable (∃ x ∈ root.subtrees,
      x ≠ goal ∧ pred x = true ∧ cCommandsIn root probe x ∧ cCommandsIn root x goal) :=
    Multiset.decidableExistsMultiset
  infer_instance

/-! ### Horizons ([keine-2019]) -/

/-- Per-vertex horizon predicate: leaf with category = horizonCat. -/
private def isHorizonLeafFor (horizonCat : Cat) (n : SyntacticObject) : Prop :=
  match getLIToken n with
  | some tok => tok.item.outerCat = horizonCat
  | none => False

instance (horizonCat : Cat) (n : SyntacticObject) :
    Decidable (isHorizonLeafFor horizonCat n) := by
  unfold isHorizonLeafFor
  cases getLIToken n <;> infer_instance

/-- `target` is behind a horizon of category `horizonCat` for `probe` in
    `root`: some `horizonCat` leaf sits in `probe`'s search domain and
    c-commands `target`, rendering it invisible ([keine-2019]).

    Example: N° is a horizon for wh-probes ([aissen-polian-2025]). In
    `[DP D° [PossP Psr N°]]`, N° c-commands Psr, so wh-probes on C° cannot
    reach Psr; D° is not c-commanded by N°, so the whole DP stays visible
    for pied-piping.

    The canonical list-native horizon specification is `Probe.Profile`
    (`Probe/Profile.lean`); this is the tree-native presentation. -/
def behindHorizonIn (root probe target : SyntacticObject)
    (horizonCat : Cat) : Prop :=
  ∃ n ∈ root.subtrees,
    isHorizonLeafFor horizonCat n ∧ cCommandsIn root n target ∧ cCommandsIn root probe n

instance (root probe target : SyntacticObject) (horizonCat : Cat) :
    Decidable (behindHorizonIn root probe target horizonCat) :=
  Multiset.decidableExistsMultiset

/-! ### Feature valuation -/

/-- Apply Agree: value the probe's feature from the goal.
    Matching is by *dimension* (`ftype.dimension`), so a probe with
    `[uPerson:_]` is valued by a goal with `[Person:3rd]` — the placeholder
    value is irrelevant. If the goal has a valued feature at the dimension and
    the probe's slot there is unvalued, the probe's slot is set to that value. -/
def applyAgree (probeFeats goalFeats : FeatureBundle) (ftype : FeatureVal) :
    Option FeatureBundle :=
  match getValuedFeature goalFeats ftype with
  | none => none
  | some v =>
    some <| if (probeFeats ftype.dimension).isUnvalued
            then Function.update probeFeats ftype.dimension (.valued v)
            else probeFeats

/-! ### Phase-bounded Agree -/

/-- Agree bounded by the Phase Impenetrability Condition: valid Agree whose
    goal every phase admits extraction from (`Phase.admitsExtraction`). Under
    `strong`/`weak` this blocks goals frozen in a phase interior; under
    `linearizationBound` ([sande-clem-dabkowski-2026]) the phasehood layer is
    transparent and locality falls to Cyclic Linearization. -/
def validAgreeWithPIC (strength : PICStrength) (phases : List Phase)
    (feats : LIToken → FeatureBundle) (root probe goal : SyntacticObject)
    (t : FeatureType) : Prop :=
  validAgree feats root probe goal t ∧ ∀ ph ∈ phases, admitsExtraction strength ph goal

instance (strength : PICStrength) (phases : List Phase)
    (feats : LIToken → FeatureBundle) (root probe goal : SyntacticObject)
    (t : FeatureType) :
    Decidable (validAgreeWithPIC strength phases feats root probe goal t) := by
  unfold validAgreeWithPIC; infer_instance

/-! ### `applyAgree` as a `Probe` transmission -/

/-- The φ-probe: relativized search ([bejar-rezac-2003]/[preminger-2014]) for a
    goal bearing a valued `ftype` feature. -/
def phiProbe (ftype : FeatureVal) : Probe FeatureBundle :=
  Probe.ofVis (fun gf => (getValuedFeature gf ftype).isSome)

/-- **`applyAgree` is the φ goal→probe transmission.** A φ-Agree is
    `Probe.transmit` of the φ-probe with the valuation `applyAgree`: search the
    goal sequence for a `ftype`-bearing goal, then value the probe's features
    from it. This recognizes the standalone `applyAgree` as the transmission
    step of the unified Agree operation (`Probe/Transmission.lean`), rather than
    a parallel mechanism. (The probe→goal direction — dependent case — and a
    full clause's worth of valuations are *folds* of `transmit`s: the
    composition axis, not a single transmit.) -/
theorem applyAgree_is_phi_transmit (probeFeats : FeatureBundle) (ftype : FeatureVal)
    {goals : List FeatureBundle} {gf : FeatureBundle}
    (h : (phiProbe ftype).search goals = some gf) :
    (phiProbe ftype).transmit (fun g pf => (applyAgree pf g ftype).getD pf)
        probeFeats goals
      = (applyAgree probeFeats gf ftype).getD probeFeats := by
  unfold phiProbe at h ⊢
  exact Probe.transmit_ofVis_eq_of_search h

end Minimalist
