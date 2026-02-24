import Linglib.Core.UD

/-!
# Person Categories (Cysouw 2009)

The 8 referential person categories from Cysouw's paradigmatic framework,
extracted to Core/ for use by both Phenomena/ (typological data) and
Fragments/ (person feature decomposition).

This module contains just the type and its basic predicates. The full
paradigmatic structure machinery (morpheme classes, homophony types,
language data) remains in `Phenomena/Agreement/PersonMarkingTypology.lean`.

## References

- Cysouw, M. (2009). *The Paradigmatic Structure of Person Marking*. OUP.
-/

namespace Core.PersonCategory

/-- The 8 referential person categories (Cysouw 2009, Fig 10.1).

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

end Core.PersonCategory
