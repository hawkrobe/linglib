import Linglib.Core.Prominence

/-!
# Person Feature Decomposition
@cite{cysouw-2009} @cite{siewierska-2004}

Framework-neutral decomposition of person into binary features:

- **[±participant]**: whether the referent includes a speech-act participant
  (speaker or addressee). 1st and 2nd person are [+participant]; 3rd person
  is [−participant].
- **[±author]**: whether the referent includes the speaker. 1st person is
  [+author]; 2nd and 3rd are [−author].

These features form a containment hierarchy: [+author] → [+participant].
An author (speaker) is necessarily a participant.

This decomposition is shared across theoretical frameworks:
- Minimalism: @cite{preminger-2014}, @cite{bejar-rezac-2009}
- Distributed Morphology: @cite{munoz-perez-2026} (Fission)
- Typology: @cite{cysouw-2009}, @cite{siewierska-2004}

The Minimalist-specific extension [±proximate]
(@cite{pancheva-zubizarreta-2018}) is added in
`Theories/Syntax/Minimalism/Core/PersonGeometry.lean`.

-/

namespace Core.Person

-- ============================================================================
-- § 1: Person Features
-- ============================================================================

/-- Binary person features: [±participant, ±author].

    These two features suffice for the three-way person distinction:
    - 1st person: [+participant, +author]
    - 2nd person: [+participant, −author]
    - 3rd person: [−participant, −author]

    The fourth combination [−participant, +author] is ill-formed:
    an author (speaker) is necessarily a speech-act participant. -/
structure Features where
  /-- [+participant]: referent includes a speech-act participant (1P or 2P). -/
  hasParticipant : Bool
  /-- [+author]: referent includes the speaker (1P only for singulars). -/
  hasAuthor : Bool
  deriving DecidableEq, BEq, Repr

/-- Well-formedness: [+author] → [+participant].
    An author (speaker) is necessarily a participant. -/
def Features.wellFormed (pf : Features) : Bool :=
  !pf.hasAuthor || pf.hasParticipant

-- ============================================================================
-- § 2: Canonical Person Feature Bundles
-- ============================================================================

/-- 1st person features: [+participant, +author]. -/
def first : Features := ⟨true, true⟩

/-- 2nd person features: [+participant, −author]. -/
def second : Features := ⟨true, false⟩

/-- 3rd person features: [−participant, −author]. -/
def third : Features := ⟨false, false⟩

-- ============================================================================
-- § 3: PersonLevel Bridge
-- ============================================================================

end Core.Person

namespace Core.Prominence

/-- Decompose `PersonLevel` into binary person features. -/
def PersonLevel.toFeatures : PersonLevel → Core.Person.Features
  | .first  => Core.Person.first
  | .second => Core.Person.second
  | .third  => Core.Person.third

end Core.Prominence

namespace Core.Person

open Core.Prominence

-- ============================================================================
-- § 4: Verification
-- ============================================================================

theorem first_wellFormed : first.wellFormed = true := rfl
theorem second_wellFormed : second.wellFormed = true := rfl
theorem third_wellFormed : third.wellFormed = true := rfl

/-- The ill-formed combination [−participant, +author] is the only
    combination that violates well-formedness. -/
theorem illFormed_only : (⟨false, true⟩ : Features).wellFormed = false := rfl

/-- There are exactly 3 well-formed feature combinations (= 3 persons). -/
theorem exactly_three_wellFormed :
    ([⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩].filter
      Features.wellFormed).length = 3 := by native_decide

/-- All person levels yield well-formed features. -/
theorem PersonLevel.toFeatures_wellFormed (p : PersonLevel) :
    p.toFeatures.wellFormed = true := by cases p <;> rfl

/-- PersonLevel.isSAP = Features.hasParticipant. -/
theorem PersonLevel.isSAP_eq_participant (p : PersonLevel) :
    p.isSAP = p.toFeatures.hasParticipant := by cases p <;> rfl

end Core.Person
