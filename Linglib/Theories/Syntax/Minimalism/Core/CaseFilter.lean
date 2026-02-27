import Linglib.Theories.Syntax.Minimalism.Core.Features

/-!
# The Case Filter

Every DP must receive Case. In Minimalist terms:
- Every DP has [uCase] (unvalued Case feature)
- [uCase] must be valued by Agree with a Case-assigning head
- Failure to value [uCase] causes the derivation to crash

Case assigners (Agree-based):
- T assigns nominative to its specifier (subject)
- v assigns accusative to its complement (object)
- P assigns oblique to its complement

For the competing dependent-case approach (Marantz 1991; Baker 2015),
see `DependentCase.lean`. For inherent/Voice-based case (Woolford 2006),
see `Voice.lean` and `Fragments.Mam.Agreement`.

## References

- Chomsky, N. (2001). Derivation by Phase.
- Marantz, A. (1991). Case and licensing.
- Baker, M. (2015). Case: Its Principles and Its Parameters.
-/

namespace Minimalism

open Core.Prominence

-- ============================================================================
-- § 1: Case Assignment Bundles (Agree-based)
-- ============================================================================

/-- Nominative Case is assigned by T.
    T has [uCase:nom], assigns to closest DP in Spec-TP. -/
def tAssignsNominative : FeatureBundle :=
  [.unvalued (.case .nom)]

/-- Accusative Case is assigned by v (transitive light verb).
    v has [uCase:acc], assigns to closest DP (object). -/
def vAssignsAccusative : FeatureBundle :=
  [.unvalued (.case .acc)]

/-- DP needs Case (Case Filter).
    All DPs have [uCase], must be valued by Agree. -/
def dpNeedsCase : FeatureBundle :=
  [.unvalued (.case .obl)]  -- unvalued, will be valued by T or v

-- ============================================================================
-- § 2: DP Feature Structures
-- ============================================================================

/-- A DP's features (with unvalued Case). -/
structure DPFeatures where
  phi : List PhiFeature      -- Person, number, gender
  caseFeature : GramFeature  -- The Case feature (valued or unvalued)
  deriving Repr

/-- Create DP features with unvalued Case. -/
def DPFeatures.withUnvaluedCase (phi : List PhiFeature) : DPFeatures :=
  ⟨phi, .unvalued (.case .obl)⟩

/-- Create DP features with valued Case. -/
def DPFeatures.withCase (phi : List PhiFeature) (c : CaseVal) : DPFeatures :=
  ⟨phi, .valued (.case c)⟩

/-- Does a DP satisfy the Case Filter? (has valued Case) -/
def satisfiesCaseFilter (dp : DPFeatures) : Bool :=
  dp.caseFeature.isValued

/-- Convert DPFeatures to a FeatureBundle. -/
def DPFeatures.toBundle (dp : DPFeatures) : FeatureBundle :=
  dp.phi.map (λ p => .valued (.phi p)) ++ [dp.caseFeature]

-- ============================================================================
-- § 3: Case Filter Predicate
-- ============================================================================

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

end Minimalism
