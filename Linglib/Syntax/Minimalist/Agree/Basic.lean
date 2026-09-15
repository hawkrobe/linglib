import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Minimalist.Probe.Basic
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm

/-!
# Agree: closest goals, horizons, and valuation

This file defines the structural conditions of Agree over syntactic objects and its valuation
step over feature bundles. A closest goal for a probe is a node of the probe's c-command domain
that satisfies the probe's relativization and that no other such node asymmetrically
c-commands, which is the Minimal Link Condition of [chomsky-1995] with mutually c-commanding
candidates equidistant. A target lies behind a horizon for a probe when a leaf of the horizon
category lies in the probe's domain and c-commands the target, so that the probe's search
terminates before reaching it ([keine-2019]). Valuation copies a goal's value into an unvalued
probe slot and is inflationary in the subsumption order on bundles, so Agree only adds
information.

The closest-goal predicate is the tree-native form of the list search `Probe.search`. A probe's
search over an enumeration of its domain sorted by c-command finds one of its closest visible
goals (`isClosestGoalIn_of_search_eq_some`).

## Main definitions

* `Minimalist.SyntacticObject.isClosestGoalIn`, `Minimalist.SyntacticObject.behindHorizonIn`
* `Minimalist.FeatureBundle.valueAt`, `Minimalist.FeatureBundle.applyAgree`

## References

* [chomsky-1995], [chomsky-2000]
* [keine-2019]
* [aissen-polian-2025]
-/

namespace Minimalist

namespace SyntacticObject

variable {root probe goal : SyntacticObject} {pred : SyntacticObject → Prop}

/-! ### Closest goals -/

/-- A closest `pred`-goal for `probe` in `root` is a node of `probe`'s c-command domain
satisfying `pred` that no other `pred`-node of the domain asymmetrically c-commands. Mutually
c-commanding candidates are equidistant and do not block each other. -/
def isClosestGoalIn (root probe goal : SyntacticObject) (pred : SyntacticObject → Prop) : Prop :=
  goal ∈ domainIn root probe ∧ pred goal ∧
    ∀ x ∈ domainIn root probe, pred x → ¬ asymCCommandsIn root x goal

instance [DecidablePred pred] (root probe goal : SyntacticObject) :
    Decidable (isClosestGoalIn root probe goal pred) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ x ∈ domainIn root probe, _))

/-- A probe's search over an enumeration of its domain sorted by c-command finds one of its
closest visible goals. -/
theorem isClosestGoalIn_of_search_eq_some {p : Probe SyntacticObject} {dom : List SyntacticObject}
    (hdom : (dom : Multiset SyntacticObject) = domainIn root probe)
    (hord : dom.Pairwise λ x y => ¬ asymCCommandsIn root y x)
    (h : p.search dom = some goal) :
    isClosestGoalIn root probe goal (p.vis ·) := by
  refine ⟨?_, Probe.visible_of_search_eq_some h, λ x hx hvx hasym => ?_⟩
  · rw [← hdom]; exact Multiset.mem_coe.2 (Probe.mem_of_search_eq_some h)
  · rw [← hdom] at hx
    exact Probe.not_rel_of_search_eq_some hord h x (Multiset.mem_coe.1 hx) hvx
      (λ e => hasym.2 (e ▸ hasym.1)) hasym

/-- Sisters are equidistant. A closest goal need only be free of asymmetric c-command by the
`pred`-nodes of the domain that are not its sisters, since a sister never asymmetrically
c-commands it. -/
theorem isClosestGoalIn_iff_forall_not_sister :
    isClosestGoalIn root probe goal pred ↔
      goal ∈ domainIn root probe ∧ pred goal ∧ ∀ x ∈ domainIn root probe, pred x →
        ¬ areSistersIn root x goal → ¬ asymCCommandsIn root x goal :=
  and_congr_right λ _ => and_congr_right λ _ => forall₂_congr λ _ _ => imp_congr_right λ _ =>
    ⟨λ h _ => h, λ h hasym => (em _).elim (λ hs => not_asymCCommandsIn_of_areSistersIn hs hasym)
      (λ hs => h hs hasym)⟩

/-! ### Horizons -/

/-- A target lies behind a horizon of category `c` for `probe` in `root` when a `c` leaf of
`probe`'s c-command domain c-commands it, so that `probe`'s search terminates before reaching it
([keine-2019]). With N a horizon for the wh-probe on C, the D head of `[DP D [PossP Psr N]]`
stays visible while the possessor, c-commanded by N, does not ([aissen-polian-2025]). -/
def behindHorizonIn (root probe target : SyntacticObject) (c : Cat) : Prop :=
  ∃ n ∈ domainIn root probe, isLeafOf c n ∧ cCommandsIn root n target

instance (root probe target : SyntacticObject) (c : Cat) :
    Decidable (behindHorizonIn root probe target c) :=
  Multiset.decidableExistsMultiset

end SyntacticObject

namespace FeatureBundle

variable (probe goal : FeatureBundle) (t : FeatureType)

/-! ### Valuation -/

/-- The bundle `b` with dimension `t` valued by `v` when its slot is unvalued; a valued or absent
slot is left as it is. -/
def valueAt (b : FeatureBundle) (t : FeatureType) (v : t.ValueOf) : FeatureBundle :=
  Function.update b t ((b t).valueWith v)

@[simp] theorem valueAt_apply_self (b : FeatureBundle) (v : t.ValueOf) :
    b.valueAt t v t = (b t).valueWith v := by
  simp [valueAt]

/-- Valuation is inflationary in the subsumption order, so Agree only adds information. -/
theorem le_valueAt (b : FeatureBundle) (v : t.ValueOf) : b ≤ b.valueAt t v :=
  le_update_self_iff.mpr (FeatureSlot.le_valueWith v _)

/-- The probe's bundle valued from the goal's value at dimension `t`, or `none` when the goal has
no value to transmit. -/
def applyAgree : Option FeatureBundle :=
  (goal.getValuedFeature t).map (probe.valueAt t)

@[simp] theorem applyAgree_bot : probe.applyAgree ⊥ t = none := rfl

theorem applyAgree_eq_none_iff : probe.applyAgree goal t = none ↔ ¬ goal.hasValuedFeature t := by
  cases h : goal t <;> simp [applyAgree, getValuedFeature, hasValuedFeature, FeatureSlot.value?,
    FeatureSlot.isValued, h]

/-- A probe valued by Agree only gains information. -/
theorem le_of_applyAgree_eq_some {probe' : FeatureBundle}
    (h : probe.applyAgree goal t = some probe') : probe ≤ probe' := by
  obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact le_valueAt t probe v

end FeatureBundle

end Minimalist
