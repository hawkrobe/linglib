import Linglib.Features.Case.Capabilities
import Linglib.Syntax.Minimalist.Features

/-!
# Case in the Minimalist feature system

This file gives the Agree-based account of structural case its feature-level
form: T, v and P carry a valued Case feature they assign to the closest DP
([chomsky-2001]), a DP carries [uCase] until some head values it, and the Case
Filter is the convergence condition that no DP reach the interfaces unvalued.

`DPFeatures` is the DP-side bundle — φ-features plus one Case feature, valued
or not — and `satisfiesCaseFilter` is the predicate on it. The configural
alternative, on which case is read off the arrangement of nominals rather than
assigned by a head, is `Syntax/Case/Dependent.lean` ([marantz-1991],
[baker-2015]).

## Main definitions

* `DPFeatures`: a DP's φ-features together with its Case feature.
* `satisfiesCaseFilter`, `caseFilterHolds`: the Case Filter on one DP and on a
  derivation's DPs.
* `tAssignsNominative`, `vAssignsAccusative`, `dpNeedsCase`: the assigner and
  goal feature bundles.

## References

* [chomsky-2001]
* [woolford-2006]
-/
namespace Minimalist

open Features.Prominence

/-! ### Assigner feature bundles -/

/-- Nominative Case is assigned by T.
    T has [uCase:nom], assigns to closest DP in Spec-TP. -/
def tAssignsNominative : FeatureBundle :=
  .ofGramFeatures [.unvalued (.case .nom)]

/-- Accusative Case is assigned by v (transitive light verb).
    v has [uCase:acc], assigns to closest DP (object). -/
def vAssignsAccusative : FeatureBundle :=
  .ofGramFeatures [.unvalued (.case .acc)]

/-- DP needs Case (Case Filter).
    All DPs have [uCase], must be valued by Agree. The `.dat` value here
    is a placeholder — `featuresMatch` ignores values for unvalued probes,
    so any `Case` would work; `.dat` is conventional. -/
def dpNeedsCase : FeatureBundle :=
  .ofGramFeatures [.unvalued (.case .dat)]

/-! ### DP feature structures -/

/-- A DP's features (with unvalued Case). -/
structure DPFeatures where
  phi : List PhiFeature      -- Person, number, gender
  caseFeature : GramFeature  -- The Case feature (valued or unvalued)
  deriving Repr

/-- Create DP features with unvalued Case. The `.dat` value is a
    placeholder — see `dpNeedsCase` for the rationale. -/
def DPFeatures.withUnvaluedCase (phi : List PhiFeature) : DPFeatures :=
  ⟨phi, .unvalued (.case .dat)⟩

/-- Create DP features with valued Case. -/
def DPFeatures.withCase (phi : List PhiFeature) (c : Case) : DPFeatures :=
  ⟨phi, .valued (.case c)⟩

/-- A DP bears the case its valued Case feature carries; an unvalued
    Case feature (or a degenerate non-Case feature in the slot) is
    caseless. -/
instance : HasCase DPFeatures :=
  ⟨fun dp => match dp.caseFeature with
    | .valued (.case c) => some c
    | _ => none⟩

/-- Does a DP satisfy the Case Filter? — it bears a case
    (`HasCase.caseOf` is `some`). -/
def satisfiesCaseFilter (dp : DPFeatures) : Bool :=
  (HasCase.caseOf dp).isSome

/-- Convert DPFeatures to a FeatureBundle. -/
def DPFeatures.toBundle (dp : DPFeatures) : FeatureBundle :=
  .ofGramFeatures (dp.phi.map (λ p => .valued (.phi p)) ++ [dp.caseFeature])

/-! ### The Case Filter -/

/-- The Case Filter: a derivation converges only if all DPs have valued Case.
    This is stated as: for all DPs in the structure, their Case feature
    must be valued. -/
def caseFilterHolds (dps : List DPFeatures) : Bool :=
  dps.all satisfiesCaseFilter

/-- If Case Filter fails, there exists a DP without Case. -/
theorem case_filter_necessary (dps : List DPFeatures) :
    caseFilterHolds dps = false → ∃ dp ∈ dps, satisfiesCaseFilter dp = false := by
  intro h
  induction dps with
  | nil => contradiction
  | cons hd tl ih =>
    unfold caseFilterHolds at h; unfold List.all at h
    cases hhd : satisfiesCaseFilter hd with
    | false => exact ⟨hd, .head _, hhd⟩
    | true =>
      simp only [hhd, Bool.true_and] at h
      obtain ⟨dp, hdp, hsat⟩ := ih (by unfold caseFilterHolds; exact h)
      exact ⟨dp, .tail _ hdp, hsat⟩

/-- A well-formed derivation satisfies the Case Filter. -/
theorem case_filter_at_interfaces (dps : List DPFeatures)
    (hWF : caseFilterHolds dps = true) :
    ∀ dp ∈ dps, satisfiesCaseFilter dp = true := by
  intro dp hdp
  induction dps with
  | nil => contradiction
  | cons hd tl ih =>
    unfold caseFilterHolds at hWF; unfold List.all at hWF
    have h1 : satisfiesCaseFilter hd = true := by
      cases hhd : satisfiesCaseFilter hd <;> simp_all
    have h2 : caseFilterHolds tl = true := by
      unfold caseFilterHolds; cases htl : List.all tl satisfiesCaseFilter <;> simp_all
    cases hdp with
    | head => exact h1
    | tail _ hmem => exact ih h2 hmem

end Minimalist
