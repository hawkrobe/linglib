import Linglib.Core.Person.Category

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

open Core.Person

-- ============================================================================
-- § 1: Fission Applicability
-- ============================================================================

/-- Fission applies iff [+PARTICIPANT, +SINGULAR].
    This derives the person restriction on stylistic applicatives:
    only 1SG and 2SG trigger Fission, not 3SG or any plural. -/
def fissionApplicable (p : Category) : Bool :=
  p.toFeatures.hasParticipant && p.isSingular

-- ============================================================================
-- § 2: Verification Theorems
-- ============================================================================

/-- Fission applies to 1SG. -/
theorem fission_1sg : fissionApplicable .s1 = true := rfl

/-- Fission applies to 2SG. -/
theorem fission_2sg : fissionApplicable .s2 = true := rfl

/-- Fission does NOT apply to 3SG (not a participant). -/
theorem fission_not_3sg : fissionApplicable .s3 = false := rfl

/-- Fission does NOT apply to group categories (not singular). -/
theorem fission_not_groups :
    fissionApplicable .minIncl = false ∧
    fissionApplicable .augIncl = false ∧
    fissionApplicable .excl = false ∧
    fissionApplicable .secondGrp = false ∧
    fissionApplicable .thirdGrp = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Exactly 2 of the 8 person categories trigger Fission. -/
theorem fission_count :
    (Category.all.filter fissionApplicable).length = 2 := by native_decide

end Fragments.Spanish.PersonFeatures
