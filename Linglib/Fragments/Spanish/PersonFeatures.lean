import Linglib.Core.PersonCategory

/-!
# Person Feature Decomposition for Spanish Clitics

Bridges Cysouw's (2009) `PersonCategory` to the person feature
decomposition used in Muñoz Pérez (2026): [±PART], [±AUTHOR], [±SING].

Fission (the postsyntactic operation producing stylistic applicatives)
applies iff [+PART, +SING] — i.e., only to 1SG and 2SG. This is
derived from the feature geometry, not stipulated per person.

## References

- Cysouw, M. (2009). The Paradigmatic Structure of Person Marking. OUP.
- Muñoz Pérez, C. (2026). Stylistic applicatives. *Glossa* 11(1).
-/

namespace Fragments.Spanish.PersonFeatures

open Core.PersonCategory

-- ============================================================================
-- § 1: Feature Decomposition
-- ============================================================================

/-- [+PARTICIPANT]: the referent includes a speech act participant. -/
def hasParticipant : PersonCategory → Bool
  | .s1 | .s2 => true    -- Speaker and addressee are participants
  | _ => false

/-- [+AUTHOR]: the referent includes the speaker. -/
def hasAuthor : PersonCategory → Bool
  | .s1 => true           -- Only the speaker is [+AUTHOR]
  | _ => false

-- ============================================================================
-- § 2: Fission Applicability
-- ============================================================================

/-- Fission applies iff [+PARTICIPANT, +SINGULAR].
    This derives the person restriction on stylistic applicatives:
    only 1SG and 2SG trigger Fission, not 3SG or any plural. -/
def fissionApplicable (p : PersonCategory) : Bool :=
  hasParticipant p && p.isSingular

-- ============================================================================
-- § 3: Verification Theorems
-- ============================================================================

/-- 1SG is [+PARTICIPANT]. -/
theorem s1_participant : hasParticipant .s1 = true := rfl

/-- 2SG is [+PARTICIPANT]. -/
theorem s2_participant : hasParticipant .s2 = true := rfl

/-- 3SG is [-PARTICIPANT]. -/
theorem s3_not_participant : hasParticipant .s3 = false := rfl

/-- Only 1SG is [+AUTHOR]. -/
theorem s1_author : hasAuthor .s1 = true := rfl
theorem s2_not_author : hasAuthor .s2 = false := rfl
theorem s3_not_author : hasAuthor .s3 = false := rfl

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
    (PersonCategory.all.filter fissionApplicable).length = 2 := by native_decide

end Fragments.Spanish.PersonFeatures
