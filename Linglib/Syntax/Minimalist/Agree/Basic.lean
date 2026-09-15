import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Minimalist.Probe.Basic
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm

/-!
# Agree: closest goals, horizons, and valuation

This file defines the structural conditions of Agree over syntactic objects and its valuation
step over feature bundles. A goal is a *closest goal* for a probe when it lies in the probe's
c-command domain, satisfies the probe's relativization, and no other such node asymmetrically
c-commands it: the Minimal Link Condition of [chomsky-1995], with mutually c-commanding
candidates equidistant. A target is *behind a horizon* for a probe when a leaf of the horizon
category lies in the probe's domain and c-commands the target, so the probe's search terminates
before reaching it ([keine-2019]). Valuation copies a goal's value into an unvalued probe slot
and is inflationary in the subsumption order on bundles: Agree only adds information.

The closest-goal predicate is the tree-native form of the list search `Probe.search`: when a
goal sequence enumerates the probe's domain with no later goal asymmetrically c-commanding an
earlier one, the goal the search finds is a closest goal (`isClosestGoalIn_of_search`).

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

/-- `goal` is a closest `pred`-goal for `probe` in `root`: `probe` c-commands `goal`, `goal`
satisfies `pred`, and no `pred`-node in `probe`'s c-command domain asymmetrically c-commands
`goal`. Mutually c-commanding candidates are equidistant and do not block each other. -/
def isClosestGoalIn (root probe goal : SyntacticObject) (pred : SyntacticObject → Prop) : Prop :=
  cCommandsIn root probe goal ∧ pred goal ∧
    ∀ x ∈ root.subtrees, pred x → cCommandsIn root probe x → ¬ asymCCommandsIn root x goal

instance [DecidablePred pred] (root probe goal : SyntacticObject) :
    Decidable (isClosestGoalIn root probe goal pred) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ x ∈ root.subtrees, _))

/-- The goal a list search finds over the probe's domain is a closest goal, provided the
sequence enumerates the domain and no later goal asymmetrically c-commands an earlier one: the
tree-native predicate agrees with the list engine `Probe.search`. -/
theorem isClosestGoalIn_of_search [DecidablePred pred] {dom : List SyntacticObject}
    (hdom : ∀ x ∈ root.subtrees, cCommandsIn root probe x → x ∈ dom)
    (hcc : ∀ x ∈ dom, cCommandsIn root probe x)
    (hord : dom.Pairwise λ x y => ¬ asymCCommandsIn root y x)
    (h : (Probe.ofVis λ x => decide (pred x)).search dom = some goal) :
    isClosestGoalIn root probe goal pred := by
  obtain ⟨hvis, l₁, l₂, rfl, hl₁⟩ := Probe.search_eq_some_iff_closest.mp h
  refine ⟨hcc goal (by simp), of_decide_eq_true hvis, λ x hx hpx hcx hasym => ?_⟩
  rcases List.mem_append.mp (hdom x hx hcx) with hx₁ | hx₂
  · exact absurd hpx (by simpa [Probe.ofVis] using hl₁ x hx₁)
  · rcases List.mem_cons.mp hx₂ with rfl | hx₂
    · exact hasym.2 hasym.1
    · exact (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1 x hx₂ hasym

/-! ### Horizons -/

/-- `target` is behind a horizon of category `c` for `probe` in `root`: a `c` leaf in `probe`'s
c-command domain c-commands `target`, so `probe`'s search terminates before reaching it
([keine-2019]). With N a horizon for the wh-probe on C, the D head of `[DP D [PossP Psr N]]`
stays visible while the possessor, c-commanded by N, does not ([aissen-polian-2025]). -/
def behindHorizonIn (root probe target : SyntacticObject) (c : Cat) : Prop :=
  ∃ n ∈ root.subtrees, isLeafOf c n ∧ cCommandsIn root probe n ∧ cCommandsIn root n target

instance (root probe target : SyntacticObject) (c : Cat) :
    Decidable (behindHorizonIn root probe target c) :=
  Multiset.decidableExistsMultiset

/-! ### Witnesses -/

private def T₀ : PlanarSyntacticObject := .leaf ⟨.simple .T [], 1⟩
private def V₀ : PlanarSyntacticObject := .leaf ⟨.simple .V [], 2⟩
private def N₀ : PlanarSyntacticObject := .leaf ⟨.simple .N [], 3⟩
private def D₁ : PlanarSyntacticObject := .leaf ⟨.simple .D [], 4⟩
private def D₂ : PlanarSyntacticObject := .leaf ⟨.simple .D [], 5⟩

/-- `[T [D₁ [V [N D₂]]]]`. -/
private def twoD : PlanarSyntacticObject := {T₀, {D₁, {V₀, {N₀, D₂}}}}

/-- `[T [D₁ D₂]]`. -/
private def sisters : PlanarSyntacticObject := {T₀, {D₁, D₂}}

/-- The higher D is the closest D-goal and shields the lower one. -/
example : isClosestGoalIn twoD T₀ D₁ (isLeafOf .D) ∧
    ¬ isClosestGoalIn twoD T₀ D₂ (isLeafOf .D) := by decide

/-- Sisters are equidistant: both are closest goals. -/
example : isClosestGoalIn sisters T₀ D₁ (isLeafOf .D) ∧
    isClosestGoalIn sisters T₀ D₂ (isLeafOf .D) := by decide

/-- The lower D lies behind the N horizon; the higher one does not. -/
example : behindHorizonIn twoD T₀ D₂ .N ∧ ¬ behindHorizonIn twoD T₀ D₁ .N := by decide

end SyntacticObject

namespace FeatureBundle

variable (probe goal : FeatureBundle) (t : FeatureType)

/-! ### Valuation -/

/-- Value dimension `t` of `b` with `v` when its slot is unvalued; a valued or absent slot is
left as it is. -/
def valueAt (b : FeatureBundle) (t : FeatureType) (v : t.ValueOf) : FeatureBundle :=
  Function.update b t ((b t).valueWith v)

@[simp] theorem valueAt_apply_self (b : FeatureBundle) (v : t.ValueOf) :
    b.valueAt t v t = (b t).valueWith v := by
  simp [valueAt]

/-- Valuation is inflationary in the subsumption order: Agree only adds information. -/
theorem le_valueAt (b : FeatureBundle) (v : t.ValueOf) : b ≤ b.valueAt t v :=
  le_update_self_iff.mpr (FeatureSlot.le_valueWith v _)

/-- Apply Agree at dimension `t`: the probe's bundle valued from the goal's value at `t`, or
`none` when the goal has no value to transmit. -/
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
