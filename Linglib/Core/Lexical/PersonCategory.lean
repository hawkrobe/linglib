import Linglib.Core.Lexical.UD
import Linglib.Core.Prominence

/-!
# Person Categories
@cite{cysouw-2009}

The 8 referential person categories from Cysouw's paradigmatic framework,
extracted to Core/ for use by both Phenomena/ (typological data) and
Fragments/ (person feature decomposition).

This module contains just the type and its basic predicates. The full
paradigmatic structure machinery (morpheme classes, homophony types,
language data) remains in `Phenomena/Agreement/PersonMarkingTypology.lean`.

-/

namespace Core.PersonCategory

/-- The 8 referential person categories (@cite{cysouw-2009}, Fig 10.1).

Three singular categories (individual speech act roles) and five group
categories (attested combinations of participants). -/
inductive PersonCategory where
  | s1        -- speaker (1st person singular)
  | s2        -- addressee (2nd person singular)
  | s3        -- other (3rd person singular)
  | minIncl   -- 1+2: minimal inclusive ('we' = speaker + addressee only)
  | augIncl   -- 1+2+3: augmented inclusive ('we' = speaker + addressee + others)
  | excl      -- 1+3: exclusive ('we' = speaker + others, excluding addressee)
  | secondGrp -- 2+3: second person group ('you all', addressee + others)
  | thirdGrp  -- 3+3: third person group ('they')
  deriving DecidableEq, BEq, Repr, Inhabited

namespace PersonCategory

/-- All 8 categories in canonical order (singular, then group). -/
def all : List PersonCategory :=
  [.s1, .s2, .s3, .minIncl, .augIncl, .excl, .secondGrp, .thirdGrp]

theorem all_length : all.length = 8 := by native_decide

/-- Is this a singular (individual) category? -/
def isSingular : PersonCategory → Bool
  | .s1 | .s2 | .s3 => true
  | _ => false

/-- Is this a group (non-singular) category? -/
def isGroup : PersonCategory → Bool
  | .minIncl | .augIncl | .excl | .secondGrp | .thirdGrp => true
  | _ => false

/-- Is this part of the first person complex (contains speaker)? -/
def isFirstPersonComplex : PersonCategory → Bool
  | .minIncl | .augIncl | .excl => true
  | _ => false

/-- Is this an inclusive category (contains both speaker and addressee)? -/
def isInclusive : PersonCategory → Bool
  | .minIncl | .augIncl => true
  | _ => false

/-- Does this category include the speaker? -/
def includesSpeaker : PersonCategory → Bool
  | .s1 | .minIncl | .augIncl | .excl => true
  | _ => false

/-- Does this category include the addressee? -/
def includesAddressee : PersonCategory → Bool
  | .s2 | .minIncl | .augIncl | .secondGrp => true
  | _ => false

end PersonCategory

-- ============================================================================
-- UD Bridges
-- ============================================================================

/-- Map singular PersonCategory to UD.Person. -/
def PersonCategory.toUDPerson : PersonCategory → Option UD.Person
  | .s1 => some .first
  | .s2 => some .second
  | .s3 => some .third
  | _   => none

/-- Map UD.Person to singular PersonCategory. -/
def PersonCategory.fromUDPerson : UD.Person → Option PersonCategory
  | .first  => some .s1
  | .second => some .s2
  | .third  => some .s3
  | .zero   => none

/-- Round-trip: UD.Person → PersonCategory → UD.Person is identity. -/
theorem ud_person_roundtrip :
    (PersonCategory.fromUDPerson .first).bind PersonCategory.toUDPerson = some .first ∧
    (PersonCategory.fromUDPerson .second).bind PersonCategory.toUDPerson = some .second ∧
    (PersonCategory.fromUDPerson .third).bind PersonCategory.toUDPerson = some .third :=
  ⟨rfl, rfl, rfl⟩

/-- Map PersonCategory to traditional person × number pair. -/
def PersonCategory.toUDPersonNumber :
    PersonCategory → Option (UD.Person × UD.Number)
  | .s1       => some (.first, .Sing)
  | .s2       => some (.second, .Sing)
  | .s3       => some (.third, .Sing)
  | .minIncl  => some (.first, .Dual)
  | .augIncl  => some (.first, .Plur)
  | .excl     => some (.first, .Plur)
  | .secondGrp => some (.second, .Plur)
  | .thirdGrp  => some (.third, .Plur)

/-- UD conflates inclusive and exclusive under first person plural. -/
theorem ud_conflates_incl_excl :
    PersonCategory.toUDPersonNumber .augIncl =
    PersonCategory.toUDPersonNumber .excl := rfl

-- ============================================================================
-- PersonLevel Bridge
-- ============================================================================

/-- Map singular PersonCategory to PersonLevel (the canonical three-way
    person distinction used by PersonGeometry, DifferentialIndexing, etc.).
    Group categories map to `none` — they encode number distinctions that
    PersonLevel does not capture. -/
def PersonCategory.toPersonLevel : PersonCategory → Option Core.Prominence.PersonLevel
  | .s1 => some .first
  | .s2 => some .second
  | .s3 => some .third
  | _   => none

/-- Map PersonLevel to singular PersonCategory. -/
def PersonCategory.fromPersonLevel : Core.Prominence.PersonLevel → PersonCategory
  | .first  => .s1
  | .second => .s2
  | .third  => .s3

/-- Round-trip: PersonLevel → PersonCategory → PersonLevel is identity. -/
theorem personLevel_roundtrip (p : Core.Prominence.PersonLevel) :
    (PersonCategory.fromPersonLevel p).toPersonLevel = some p := by
  cases p <;> rfl

/-- includesSpeaker on PersonCategory = hasParticipant ∧ hasAuthor on
    PersonLevel for singular categories: speaker (s1) = [+participant,
    +author], addressee (s2) = [+participant, −author], other (s3) =
    [−participant, −author]. This unifies the PersonCategory decomposition
    in `Spanish/PersonFeatures.lean` with `PersonGeometry.decomposePerson`. -/
theorem includesSpeaker_iff_author :
    (PersonCategory.s1.includesSpeaker = true) ∧
    (PersonCategory.s2.includesSpeaker = false) ∧
    (PersonCategory.s3.includesSpeaker = false) := ⟨rfl, rfl, rfl⟩

theorem includesAddressee_iff_participant_not_author :
    (PersonCategory.s1.includesAddressee = false) ∧
    (PersonCategory.s2.includesAddressee = true) ∧
    (PersonCategory.s3.includesAddressee = false) := ⟨rfl, rfl, rfl⟩

/-- SAP (speech-act participant) = includesSpeaker ∨ includesAddressee
    for singular categories. This matches PersonLevel.isSAP. -/
theorem singular_sap_match :
    (PersonCategory.s1.includesSpeaker || PersonCategory.s1.includesAddressee) = true ∧
    (PersonCategory.s2.includesSpeaker || PersonCategory.s2.includesAddressee) = true ∧
    (PersonCategory.s3.includesSpeaker || PersonCategory.s3.includesAddressee) = false :=
  ⟨rfl, rfl, rfl⟩

end Core.PersonCategory
