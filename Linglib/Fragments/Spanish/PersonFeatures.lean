import Linglib.Features.Person

/-!
# Person Feature Decomposition for Spanish Clitics
@cite{cysouw-2009} @cite{munoz-perez-2026}

Bridges @cite{cysouw-2009}'s `Category` to the person feature
decomposition used in Muñoz @cite{munoz-perez-2026}: [±PART], [±AUTHOR], [±SING].

Fission (the postsyntactic operation producing stylistic applicatives)
applies iff [+PART, +SING] — i.e., only to 1SG and 2SG. This is
derived from the feature geometry, not stipulated per person.

Person features ([±participant], [±author]) come from the canonical
Core decomposition `Category.toFeatures`; this module only adds
the Fission-specific combination with [±singular].

-/

namespace Fragments.Spanish.PersonFeatures

open Features.Person

-- ============================================================================
-- § 1: Fission Applicability
-- ============================================================================

/-- Fission applies iff [+PARTICIPANT, +SINGULAR].
    This derives the person restriction on stylistic applicatives:
    only 1SG and 2SG trigger Fission, not 3SG or any plural. -/
def IsFissionApplicable (p : Category) : Prop :=
  p.toFeatures.hasParticipant = true ∧ p.IsSingular

instance : DecidablePred IsFissionApplicable :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- § 2: Verification Theorems
-- ============================================================================

/-- Fission applies to 1SG. -/
theorem fission_1sg : IsFissionApplicable .s1 := by decide

/-- Fission applies to 2SG. -/
theorem fission_2sg : IsFissionApplicable .s2 := by decide

/-- Fission does NOT apply to 3SG (not a participant). -/
theorem fission_not_3sg : ¬ IsFissionApplicable .s3 := by decide

/-- Fission does NOT apply to group categories (not singular). -/
theorem fission_not_groups :
    ¬ IsFissionApplicable .minIncl ∧
    ¬ IsFissionApplicable .augIncl ∧
    ¬ IsFissionApplicable .excl ∧
    ¬ IsFissionApplicable .secondGrp ∧
    ¬ IsFissionApplicable .thirdGrp := by decide

/-- Exactly 2 of the 8 person categories trigger Fission. -/
theorem fission_count :
    (Category.all.filter (decide <| IsFissionApplicable ·)).length = 2 := by decide

end Fragments.Spanish.PersonFeatures
