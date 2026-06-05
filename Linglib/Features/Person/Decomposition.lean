import Linglib.Data.UD.Basic
import Linglib.Features.Person.Basic
import Linglib.Features.Prominence
import Linglib.Features.ContainmentPair

/-!
# Person
[harley-ritter-2002] [adger-harbour-2008] [ackema-neeleman-2018]
[harbour-2016] [cysouw-2009] [siewierska-2004]

Two components of the person API:

**§ 1–4: Person Features** ([harley-ritter-2002]'s dependency organization,
in the bivalent presentation surveyed by [adger-harbour-2008]; with
[ackema-neeleman-2018]'s function-valued alternative). The typological
*category* inventory (§5+) is [cysouw-2009]'s, *derived* from these
features — not their source.
Decomposition of person into two bivalent features:
- **[±participant]**: whether the referent includes a speech-act participant
  (speaker or addressee). 1st and 2nd person are [+participant]; 3rd person
  is [−participant].
- **[±author]**: whether the referent includes the speaker. 1st person is
  [+author]; 2nd and 3rd are [−author].

These features form a containment hierarchy: [+author] → [+participant].
An author (speaker) is necessarily a participant. The hierarchy is carried
as the cooccurrence filter inherited from `Features.ContainmentPair` — the
descriptive convention of the feature-geometric tradition. [harbour-2016]
ch. 9 rejects the filter: in his calculus `+author(−participant(π))` is the
quadripartition *exclusive*, not ill-formed — see
`Features/ContainmentPair.lean` and `Studies/Harbour2016.lean`.

This decomposition is shared across theoretical frameworks:
- Minimalism: [preminger-2014], [bejar-rezac-2009]
- Distributed Morphology: [munoz-perez-2026] (Fission)
- Typology: [cysouw-2009], [siewierska-2004]

The Minimalist-specific extension [±proximate]
([pancheva-zubizarreta-2018]) is added in
`Syntax/Minimalist/Phi/Geometry.lean`.

The canonical analytical inventory (root `Person`) lives in
`Features/Person/Basic.lean`; this file is its feature decomposition
and referential-category layer.

**§ 5–9: Person Categories** ([cysouw-2009]). The 8 referential person
categories from Cysouw's paradigmatic framework. Three singular categories
(individual speech act roles) and five group categories (attested
combinations of participants).

The full paradigmatic structure machinery (morpheme classes, homophony types,
language data) remains in `Phenomena/Agreement/PersonMarkingTypology.lean`.

-/

open Features (ContainmentPair ContainmentPairLike)

namespace Person

-- ============================================================================
-- § 1: Person Features
-- ============================================================================

/-- Bivalent person features: [±participant, ±author].

    These two features suffice for the three-way person distinction:
    - 1st person: [+participant, +author]
    - 2nd person: [+participant, −author]
    - 3rd person: [−participant, −author]

    The fourth combination [−participant, +author] is cut by the
    containment filter (`WellFormed`): an author (speaker) is necessarily
    a speech-act participant. -/
structure Features where
  /-- [+participant]: referent includes a speech-act participant (1P or 2P). -/
  hasParticipant : Bool
  /-- [+author]: referent includes the speaker (1P only for singulars). -/
  hasAuthor : Bool
  deriving DecidableEq, Repr, Fintype

-- ============================================================================
-- § 2: Canonical Person Feature Bundles
-- ============================================================================

/-- 1st person features: [+participant, +author]. -/
def firstF : Features := ⟨true, true⟩

/-- 2nd person features: [+participant, −author]. -/
def secondF : Features := ⟨true, false⟩

/-- 3rd person features: [−participant, −author]. -/
def thirdF : Features := ⟨false, false⟩

-- ============================================================================
-- § 3: PersonLevel Bridge
-- ============================================================================

end Person

namespace Features.Prominence

/-- Decompose `PersonLevel` into binary person features. -/
def PersonLevel.toFeatures : PersonLevel → Person.Features
  | .first  => Person.firstF
  | .second => Person.secondF
  | .third  => Person.thirdF

/-- Convert `UD.Person` to `PersonLevel`. The UD `.zero` (impersonal)
    case has no `PersonLevel` analogue; everything else is direct. -/
def PersonLevel.ofUDPerson : UD.Person → Option PersonLevel
  | .first  => some .first
  | .second => some .second
  | .third  => some .third
  | .zero   => none

end Features.Prominence

namespace Person

open Features.Prominence

-- ============================================================================
-- § 4: ContainmentPair Presentation
-- ============================================================================

/-- The `[±participant, ±author]` decomposition is carrier-equivalent to
the containment pair: `outer` = participant, `inner` = author. One edge of
the φ-feature iso-web (`Features/PhiKernel.lean`). -/
def featuresEquiv : Features ≃ ContainmentPair where
  toFun f := ⟨f.hasParticipant, f.hasAuthor⟩
  invFun p := ⟨p.outer, p.inner⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

instance : ContainmentPairLike Features := .ofEquiv featuresEquiv

/-- The three canonical person values land on the three well-formed cells. -/
@[simp] theorem firstF_is_maximal :
    ContainmentPairLike.toPair firstF = .maximal := rfl
@[simp] theorem secondF_is_intermediate :
    ContainmentPairLike.toPair secondF = .intermediate := rfl
@[simp] theorem thirdF_is_minimal :
    ContainmentPairLike.toPair thirdF = .minimal := rfl

/-- Well-formedness: [+author] → [+participant] — an author is necessarily
    a participant. The geometry-tradition containment filter, inherited
    from `ContainmentPair.WellFormed` through the presentation. -/
abbrev Features.WellFormed (pf : Features) : Prop :=
  ContainmentPairLike.WellFormed pf

@[simp] theorem firstF_wellFormed : firstF.WellFormed := by decide
@[simp] theorem secondF_wellFormed : secondF.WellFormed := by decide
@[simp] theorem thirdF_wellFormed : thirdF.WellFormed := by decide

/-- The filtered combination [−participant, +author] is the only one that
    violates containment. -/
theorem illFormed_only : ¬ (⟨false, true⟩ : Features).WellFormed := by decide

/-- Exactly 3 well-formed feature combinations (= 3 persons) — the carrier
    count of the containment chain (`ContainmentPair.card_wellFormed`). -/
theorem card_wellFormed :
    Fintype.card {pf : Features // pf.WellFormed} = 3 := by decide

/-- All person levels yield well-formed features. -/
theorem PersonLevel.toFeatures_wellFormed (p : PersonLevel) :
    p.toFeatures.WellFormed := by cases p <;> decide

/-- PersonLevel.isSAP = Features.hasParticipant. -/
theorem PersonLevel.isSAP_eq_participant (p : PersonLevel) :
    p.isSAP = p.toFeatures.hasParticipant := by cases p <;> rfl

/-- No 4-way singular person distinction (inherited from
    `ContainmentPairLike.no_four_way`). -/
theorem no_fourth_person :
    ∀ (a b c d : Features),
      a.WellFormed → b.WellFormed → c.WellFormed → d.WellFormed →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd =>
    ContainmentPairLike.no_four_way a b c d ha hb hc hd

-- ============================================================================
-- § 6: Person Categories (Cysouw)
-- ============================================================================

/-- The 8 referential person categories ([cysouw-2009], Fig 10.1).

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

theorem all_length : all.length = 8 := by decide

/-- Is this a singular (individual) category? -/
def IsSingular (c : Category) : Prop :=
  c = .s1 ∨ c = .s2 ∨ c = .s3

instance : DecidablePred IsSingular := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Is this a group (non-singular) category? -/
def IsGroup (c : Category) : Prop :=
  c = .minIncl ∨ c = .augIncl ∨ c = .excl ∨ c = .secondGrp ∨ c = .thirdGrp

instance : DecidablePred IsGroup := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Is this part of the first person complex (contains speaker as part of a group)? -/
def IsFirstPersonComplex (c : Category) : Prop :=
  c = .minIncl ∨ c = .augIncl ∨ c = .excl

instance : DecidablePred IsFirstPersonComplex :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Is this an inclusive category (contains both speaker and addressee)? -/
def IsInclusive (c : Category) : Prop :=
  c = .minIncl ∨ c = .augIncl

instance : DecidablePred IsInclusive :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Does this category include the speaker? -/
def IncludesSpeaker (c : Category) : Prop :=
  c = .s1 ∨ c = .minIncl ∨ c = .augIncl ∨ c = .excl

instance : DecidablePred IncludesSpeaker :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Does this category include the addressee? -/
def IncludesAddressee (c : Category) : Prop :=
  c = .s2 ∨ c = .minIncl ∨ c = .augIncl ∨ c = .secondGrp

instance : DecidablePred IncludesAddressee :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

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

/-- The person coordinate of each referential category — the projection
    the canonical inventory recovers losslessly where UD cannot:
    `minIncl`/`augIncl` ↦ `firstInclusive`, `excl` ↦ `firstExclusive`.
    (The number coordinate is `toUDPersonNumber`'s second component; the
    full `Category ≃ compatible (Person × Number)` junction is the
    planned phase-2 theorem.) -/
def Category.person : Category → Person
  | .s1        => .first
  | .s2        => .second
  | .s3        => .third
  | .minIncl   => .firstInclusive
  | .augIncl   => .firstInclusive
  | .excl      => .firstExclusive
  | .secondGrp => .second
  | .thirdGrp  => .third

/-- The person projection tracks speaker inclusion. -/
theorem person_includesSpeaker_iff (c : Category) :
    c.person.IncludesSpeaker ↔ c.IncludesSpeaker := by
  cases c <;> simp [Category.person, Person.IncludesSpeaker,
    Category.IncludesSpeaker]

/-- Unlike UD realization, the person projection separates inclusive
    from exclusive. -/
theorem person_separates_clusivity :
    Category.augIncl.person ≠ Category.excl.person := by decide

-- ============================================================================
-- § 8: Category ↔ Features Bridge
-- ============================================================================

/-- Decompose any Category into binary person features (the framework-neutral
    Cysouw/Siewierska `[±participant, ±author]` decomposition).

    - `hasAuthor` = `includesSpeaker`: the referent contains the speaker.
    - `hasParticipant` = `includesSpeaker ∨ includesAddressee`: the referent
      contains at least one speech-act participant.

    Features underdetermine group categories: `excl`, `minIncl`, and `augIncl` all
    map to `⟨true, true⟩` — a genuine property of the descriptive two-feature system
    (the `Category` enum carries the clusivity distinction the features cannot). The
    theory-laden Harbour-*sign* decomposition that *does* distinguish the exclusive
    (`+author −participant`) lives in the theory layer
    (as `Studies.Harbour2016.signOf`, over `Syntax.Minimalist.Phi.Lattice` operators), not here. -/
def Category.toFeatures : Category → Features
  | .s1        => ⟨true, true⟩
  | .s2        => ⟨true, false⟩
  | .s3        => ⟨false, false⟩
  | .minIncl   => ⟨true, true⟩
  | .augIncl   => ⟨true, true⟩
  | .excl      => ⟨true, true⟩
  | .secondGrp => ⟨true, false⟩
  | .thirdGrp  => ⟨false, false⟩

/-- `hasAuthor` ↔ `IncludesSpeaker` for all categories. -/
theorem toFeatures_author_iff_speaker (p : Category) :
    p.toFeatures.hasAuthor = true ↔ p.IncludesSpeaker := by
  cases p <;> simp [Category.toFeatures, Category.IncludesSpeaker]

/-- `hasParticipant` ↔ `IncludesSpeaker ∨ IncludesAddressee` for all categories. -/
theorem toFeatures_participant_iff_sap (p : Category) :
    p.toFeatures.hasParticipant = true ↔ p.IncludesSpeaker ∨ p.IncludesAddressee := by
  cases p <;> simp [Category.toFeatures, Category.IncludesSpeaker, Category.IncludesAddressee]

/-- All 8 categories yield well-formed features. -/
theorem toFeatures_wellFormed (p : Category) :
    p.toFeatures.WellFormed := by cases p <;> decide

-- ============================================================================
-- § 9: Category ↔ PersonLevel Bridge
-- ============================================================================

/-- Map singular Category to PersonLevel (the canonical three-way
    person distinction used by Phi.Geometry, DifferentialIndexing, etc.).
    Group categories map to `none` — they encode number distinctions that
    PersonLevel does not capture. -/
def Category.toPersonLevel : Category → Option Features.Prominence.PersonLevel
  | .s1 => some .first
  | .s2 => some .second
  | .s3 => some .third
  | _   => none

/-- Map PersonLevel to singular Category. -/
def Category.fromPersonLevel : Features.Prominence.PersonLevel → Category
  | .first  => .s1
  | .second => .s2
  | .third  => .s3

/-- Round-trip: PersonLevel → Category → PersonLevel is identity. -/
theorem personLevel_roundtrip (p : Features.Prominence.PersonLevel) :
    (Category.fromPersonLevel p).toPersonLevel = some p := by
  cases p <;> rfl

/-- includesSpeaker on Category = hasParticipant ∧ hasAuthor on
    PersonLevel for singular categories: speaker (s1) = [+participant,
    +author], addressee (s2) = [+participant, −author], other (s3) =
    [−participant, −author]. This unifies the Category decomposition
    in `Spanish/PersonFeatures.lean` with `Phi.Geometry.decomposePerson`. -/
theorem includesSpeaker_iff_author :
    Category.s1.IncludesSpeaker ∧
    ¬ Category.s2.IncludesSpeaker ∧
    ¬ Category.s3.IncludesSpeaker := by decide

theorem includesAddressee_iff_participant_not_author :
    ¬ Category.s1.IncludesAddressee ∧
    Category.s2.IncludesAddressee ∧
    ¬ Category.s3.IncludesAddressee := by decide

/-- SAP (speech-act participant) = `IncludesSpeaker ∨ IncludesAddressee`
    for singular categories. This matches `PersonLevel.isSAP`. -/
theorem singular_sap_match :
    (Category.s1.IncludesSpeaker ∨ Category.s1.IncludesAddressee) ∧
    (Category.s2.IncludesSpeaker ∨ Category.s2.IncludesAddressee) ∧
    ¬ (Category.s3.IncludesSpeaker ∨ Category.s3.IncludesAddressee) := by decide

-- ============================================================================
-- § 10: Category Consistency
-- ============================================================================

/-- Singular categories: Category.toFeatures agrees with
    PersonLevel.toFeatures via the PersonLevel bridge. -/
theorem s1_features_match :
    Category.s1.toFeatures = Features.Prominence.PersonLevel.first.toFeatures := rfl
theorem s2_features_match :
    Category.s2.toFeatures = Features.Prominence.PersonLevel.second.toFeatures := rfl
theorem s3_features_match :
    Category.s3.toFeatures = Features.Prominence.PersonLevel.third.toFeatures := rfl

-- ============================================================================
-- § 11: Epistemic Authority ([bickel-nichols-2001])
-- ============================================================================

/-- Epistemic authority marking on verb agreement.
    [bickel-nichols-2001]

    Some languages (Akhvakh, Kathmandu Newari, Tibetan) mark whether the
    speaker has direct epistemic authority over the event. The morphological
    distinction cross-cuts person but correlates with it:
    - **conjunct**: speaker has authority (1st person declarative, 2nd
      person interrogative)
    - **disjunct**: speaker lacks authority (2nd/3rd declarative, 1st/3rd
      interrogative) -/
inductive EpistemicAuthority where
  | conjunct    -- speaker has epistemic authority over the event
  | disjunct    -- speaker lacks epistemic authority
  deriving DecidableEq, Repr

end Person
