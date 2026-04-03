import Linglib.Core.Lexical.UD
import Linglib.Core.Prominence
import Linglib.Core.PrivativePair

/-!
# Person
@cite{cysouw-2009} @cite{siewierska-2004}

Two components of the person API:

**§ 1–4: Person Features** (@cite{cysouw-2009}, @cite{siewierska-2004}).
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

**§ 5–9: Person Categories** (@cite{cysouw-2009}). The 8 referential person
categories from Cysouw's paradigmatic framework. Three singular categories
(individual speech act roles) and five group categories (attested
combinations of participants).

The full paradigmatic structure machinery (morpheme classes, homophony types,
language data) remains in `Phenomena/Agreement/PersonMarkingTypology.lean`.

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
  deriving DecidableEq, Repr

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
-- § 4: Features Verification
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

-- ============================================================================
-- § 5: PhiFeatures Instance
-- ============================================================================

/-- Person features are a `PhiFeatures` instance:
    outer = hasParticipant, inner = hasAuthor.

    All shared properties (`no_four_way`, `specLevel`, `wellFormed`,
    `injective`) are inherited by construction. -/
instance : Core.PhiFeatures Features where
  toPair f := ⟨f.hasParticipant, f.hasAuthor⟩
  ofPair p := ⟨p.outer, p.inner⟩
  roundtrip := fun ⟨_, _⟩ => rfl

/-- The three canonical person values map to the three PrivativePair cells. -/
theorem first_is_maximal : PhiFeatures.toPair first = .maximal := rfl
theorem second_is_intermediate : PhiFeatures.toPair second = .intermediate := rfl
theorem third_is_minimal : PhiFeatures.toPair third = .minimal := rfl

/-- No 4-way singular person distinction (inherited from `PhiFeatures`). -/
theorem no_fourth_person :
    ∀ (a b c d : Features),
      a.wellFormed = true → b.wellFormed = true →
      c.wellFormed = true → d.wellFormed = true →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd =>
    Core.PhiFeatures.no_four_way a b c d ha hb hc hd

-- ============================================================================
-- § 6: Person Categories (Cysouw)
-- ============================================================================

/-- The 8 referential person categories (@cite{cysouw-2009}, Fig 10.1).

Three singular categories (individual speech act roles) and five group
categories (attested combinations of participants). -/
inductive Category where
  | s1        -- speaker (1st person singular)
  | s2        -- addressee (2nd person singular)
  | s3        -- other (3rd person singular)
  | minIncl   -- 1+2: minimal inclusive ('we' = speaker + addressee only)
  | augIncl   -- 1+2+3: augmented inclusive ('we' = speaker + addressee + others)
  | excl      -- 1+3: exclusive ('we' = speaker + others, excluding addressee)
  | secondGrp -- 2+3: second person group ('you all', addressee + others)
  | thirdGrp  -- 3+3: third person group ('they')
  deriving DecidableEq, Repr, Inhabited

namespace Category

/-- All 8 categories in canonical order (singular, then group). -/
def all : List Category :=
  [.s1, .s2, .s3, .minIncl, .augIncl, .excl, .secondGrp, .thirdGrp]

theorem all_length : all.length = 8 := by native_decide

/-- Is this a singular (individual) category? -/
def isSingular : Category → Bool
  | .s1 | .s2 | .s3 => true
  | _ => false

/-- Is this a group (non-singular) category? -/
def isGroup : Category → Bool
  | .minIncl | .augIncl | .excl | .secondGrp | .thirdGrp => true
  | _ => false

/-- Is this part of the first person complex (contains speaker)? -/
def isFirstPersonComplex : Category → Bool
  | .minIncl | .augIncl | .excl => true
  | _ => false

/-- Is this an inclusive category (contains both speaker and addressee)? -/
def isInclusive : Category → Bool
  | .minIncl | .augIncl => true
  | _ => false

/-- Does this category include the speaker? -/
def includesSpeaker : Category → Bool
  | .s1 | .minIncl | .augIncl | .excl => true
  | _ => false

/-- Does this category include the addressee? -/
def includesAddressee : Category → Bool
  | .s2 | .minIncl | .augIncl | .secondGrp => true
  | _ => false

end Category

-- ============================================================================
-- § 7: Category UD Bridges
-- ============================================================================

/-- Map singular Category to UD.Person. -/
def Category.toUDPerson : Category → Option UD.Person
  | .s1 => some .first
  | .s2 => some .second
  | .s3 => some .third
  | _   => none

/-- Map UD.Person to singular Category. -/
def Category.fromUDPerson : UD.Person → Option Category
  | .first  => some .s1
  | .second => some .s2
  | .third  => some .s3
  | .zero   => none

/-- Round-trip: UD.Person → Category → UD.Person is identity. -/
theorem ud_person_roundtrip :
    (Category.fromUDPerson .first).bind Category.toUDPerson = some .first ∧
    (Category.fromUDPerson .second).bind Category.toUDPerson = some .second ∧
    (Category.fromUDPerson .third).bind Category.toUDPerson = some .third :=
  ⟨rfl, rfl, rfl⟩

/-- Map Category to traditional person × number pair. -/
def Category.toUDPersonNumber :
    Category → Option (UD.Person × UD.Number)
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
    Category.toUDPersonNumber .augIncl =
    Category.toUDPersonNumber .excl := rfl

-- ============================================================================
-- § 8: Category ↔ Features Bridge
-- ============================================================================

/-- Decompose any Category into binary person features.

    - `hasAuthor` = `includesSpeaker`: the referent contains the speaker.
    - `hasParticipant` = `includesSpeaker ∨ includesAddressee`: the referent
      contains at least one speech-act participant.

    Features underdetermine group categories: `excl`, `minIncl`, and `augIncl`
    all map to `⟨true, true⟩`. The full `Category` type is needed for
    number and inclusivity distinctions. -/
def Category.toFeatures : Category → Features
  | .s1        => ⟨true, true⟩
  | .s2        => ⟨true, false⟩
  | .s3        => ⟨false, false⟩
  | .minIncl   => ⟨true, true⟩
  | .augIncl   => ⟨true, true⟩
  | .excl      => ⟨true, true⟩
  | .secondGrp => ⟨true, false⟩
  | .thirdGrp  => ⟨false, false⟩

/-- `hasAuthor` = `includesSpeaker` for all categories. -/
theorem toFeatures_author_eq_speaker (p : Category) :
    p.toFeatures.hasAuthor = p.includesSpeaker := by cases p <;> rfl

/-- `hasParticipant` = `includesSpeaker ∨ includesAddressee` for all categories. -/
theorem toFeatures_participant_eq_sap (p : Category) :
    p.toFeatures.hasParticipant = (p.includesSpeaker || p.includesAddressee) := by
  cases p <;> rfl

/-- All 8 categories yield well-formed features. -/
theorem toFeatures_wellFormed (p : Category) :
    p.toFeatures.wellFormed = true := by cases p <;> rfl

-- ============================================================================
-- § 9: Category ↔ PersonLevel Bridge
-- ============================================================================

/-- Map singular Category to PersonLevel (the canonical three-way
    person distinction used by PersonGeometry, DifferentialIndexing, etc.).
    Group categories map to `none` — they encode number distinctions that
    PersonLevel does not capture. -/
def Category.toPersonLevel : Category → Option Core.Prominence.PersonLevel
  | .s1 => some .first
  | .s2 => some .second
  | .s3 => some .third
  | _   => none

/-- Map PersonLevel to singular Category. -/
def Category.fromPersonLevel : Core.Prominence.PersonLevel → Category
  | .first  => .s1
  | .second => .s2
  | .third  => .s3

/-- Round-trip: PersonLevel → Category → PersonLevel is identity. -/
theorem personLevel_roundtrip (p : Core.Prominence.PersonLevel) :
    (Category.fromPersonLevel p).toPersonLevel = some p := by
  cases p <;> rfl

/-- includesSpeaker on Category = hasParticipant ∧ hasAuthor on
    PersonLevel for singular categories: speaker (s1) = [+participant,
    +author], addressee (s2) = [+participant, −author], other (s3) =
    [−participant, −author]. This unifies the Category decomposition
    in `Spanish/PersonFeatures.lean` with `PersonGeometry.decomposePerson`. -/
theorem includesSpeaker_iff_author :
    (Category.s1.includesSpeaker = true) ∧
    (Category.s2.includesSpeaker = false) ∧
    (Category.s3.includesSpeaker = false) := ⟨rfl, rfl, rfl⟩

theorem includesAddressee_iff_participant_not_author :
    (Category.s1.includesAddressee = false) ∧
    (Category.s2.includesAddressee = true) ∧
    (Category.s3.includesAddressee = false) := ⟨rfl, rfl, rfl⟩

/-- SAP (speech-act participant) = includesSpeaker ∨ includesAddressee
    for singular categories. This matches PersonLevel.isSAP. -/
theorem singular_sap_match :
    (Category.s1.includesSpeaker || Category.s1.includesAddressee) = true ∧
    (Category.s2.includesSpeaker || Category.s2.includesAddressee) = true ∧
    (Category.s3.includesSpeaker || Category.s3.includesAddressee) = false :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: Category Consistency
-- ============================================================================

/-- Singular categories: Category.toFeatures agrees with
    PersonLevel.toFeatures via the PersonLevel bridge. -/
theorem s1_features_match :
    Category.s1.toFeatures = Core.Prominence.PersonLevel.first.toFeatures := rfl
theorem s2_features_match :
    Category.s2.toFeatures = Core.Prominence.PersonLevel.second.toFeatures := rfl
theorem s3_features_match :
    Category.s3.toFeatures = Core.Prominence.PersonLevel.third.toFeatures := rfl

end Core.Person
