import Linglib.Data.UD.Basic
import Linglib.Syntax.Person.Basic
import Linglib.Semantics.Reference.Prominence
import Linglib.Syntax.Agreement.ContainmentPair
import Linglib.Syntax.Number.Basic
import Linglib.Syntax.Person.Resolve
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

/-!
# Person
[harley-ritter-2002] [adger-harbour-2008] [ackema-neeleman-2018]
[harbour-2016] [cysouw-2003] [siewierska-2004]

Two components of the person API:

**§ 1–4: Person Features** ([harley-ritter-2002]'s dependency organization,
in the bivalent presentation surveyed by [adger-harbour-2008]; with
[ackema-neeleman-2018]'s function-valued alternative). The typological
*category* inventory (§5+) is [cysouw-2003]'s, *derived* from these
features — not their source.
Decomposition of person into two bivalent features:
- **[±participant]**: whether the referent includes a speech-act participant
  (speaker or addressee). 1st and 2nd person are [+participant]; 3rd person
  is [−participant].
- **[±author]**: whether the referent includes the speaker. 1st person is
  [+author]; 2nd and 3rd are [−author].

These features form a containment hierarchy: [+author] → [+participant].
An author (speaker) is necessarily a participant. The hierarchy is carried
as the cooccurrence filter inherited from `Agreement.ContainmentPair` — the
descriptive convention of the feature-geometric tradition. [harbour-2016]
ch. 9 rejects the filter: in his calculus `+author(−participant(π))` is the
quadripartition *exclusive*, not ill-formed — see
`Syntax/Agreement/ContainmentPair.lean` and `Studies/Harbour2016.lean`.

This decomposition is shared across theoretical frameworks:
- Minimalism: [preminger-2014], [bejar-rezac-2009]
- Distributed Morphology: [munoz-perez-2026] (Fission)
- Typology: [cysouw-2003], [siewierska-2004]

The Minimalist-specific extension [±proximate]
([pancheva-zubizarreta-2018]) is added in
`Syntax/Minimalist/Phi/Geometry.lean`.

The canonical analytical inventory (root `Person`) lives in
`Syntax/Person/Basic.lean`; this file is its feature decomposition
and referential-category layer.

**§ 5–9: Person Categories** ([cysouw-2003]). The 8 referential person
categories from Cysouw's paradigmatic framework, each a configuration of
the speech-act participants it contains (`Category.participants`) and of
the others it contains (`Category.otherCount`); the singular/group split,
speaker and addressee inclusion, the person projection and the feature
decomposition are all read off that configuration, and
`Category.toConfig_bijective` shows the eight are exactly the well-formed
configurations.

The paradigmatic structure of a person paradigm — the syncretism pattern over
these eight cells — is the subject of `Studies/Cysouw2003.lean`.

-/

open Agreement (ContainmentPair ContainmentPairLike)

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

/-- Decompose a person value into the binary features. The
    quadripartition cells share `firstF` (the two-feature system
    underdetermines clusivity — see `Category.toFeatures`); the
    impersonal `zero` has no featural decomposition. -/
def toFeatures : Person → Option Features
  | .first | .firstInclusive | .firstExclusive => some firstF
  | .second => some secondF
  | .third => some thirdF
  | .zero => none

-- ============================================================================
-- § 4: ContainmentPair Presentation
-- ============================================================================

/-- The `[±participant, ±author]` decomposition is carrier-equivalent to
the containment pair: `outer` = participant, `inner` = author. One edge of
the φ-feature iso-web (`phiKernelEquiv`, `Studies/Harbour2016.lean`). -/
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
theorem not_wellFormed_mk_false_true : ¬ (⟨false, true⟩ : Features).WellFormed := by decide

/-- Exactly 3 well-formed feature combinations (= 3 persons) — the carrier
    count of the containment chain (`ContainmentPair.card_wellFormed`). -/
theorem card_wellFormed :
    Fintype.card {pf : Features // pf.WellFormed} = 3 := by decide

/-- Every defined decomposition is well-formed. -/
theorem toFeatures_wellFormed (p : Person) :
    ∀ f, p.toFeatures = some f → f.WellFormed := by
  cases p <;> intro f hf <;>
    simp only [toFeatures, Option.some.injEq, reduceCtorEq] at hf <;>
    subst hf <;> decide

/-- `IsSAP` is featural participanthood. -/
theorem isSAP_iff_participant (p : Person) :
    ∀ f, p.toFeatures = some f →
      (p.IsSAP ↔ f.hasParticipant = true) := by
  cases p <;> intro f hf <;>
    simp only [toFeatures, Option.some.injEq, reduceCtorEq] at hf <;>
    subst hf <;> simp [IsSAP, firstF, secondF, thirdF]

/-- No 4-way singular person distinction (inherited from
    `ContainmentPairLike.no_four_way`). -/
theorem no_fourth_person :
    ∀ (a b c d : Features),
      a.WellFormed → b.WellFormed → c.WellFormed → d.WellFormed →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd =>
    ContainmentPairLike.no_four_way a b c d ha hb hc hd

/-! ### Person categories ([cysouw-2003]) -/

/-- The eight referential person categories ([cysouw-2003] ch. 3). A category is a
configuration of the speech-act participants a referent contains and of the others it
contains, none, one or several: the three singular participants and the five attested of the
seven logical groups of Table 3.1. The two dismissed groups, 1+1 (mass speaking) and 2+2 (an
audience with no one else, §3.4), are the configurations `Category.WellFormed` excludes, and
`Category.toConfig_bijective` shows the constructors are exactly the well-formed ones. -/
inductive Category where
  /-- The speaker alone, Cysouw's 1. -/
  | speaker
  /-- The addressee alone, Cysouw's 2. -/
  | addressee
  /-- A single other, Cysouw's 3. -/
  | other
  /-- The minimal inclusive, speaker and addressee only, Cysouw's 1+2. -/
  | speakerAddressee
  /-- The augmented inclusive, speaker and addressee with others, Cysouw's 1+2+3. -/
  | speakerAddresseeOthers
  /-- The exclusive, speaker with others but not the addressee, Cysouw's 1+3. -/
  | speakerOthers
  /-- The addressee with others, Cysouw's 2+3. -/
  | addresseeOthers
  /-- Several others, Cysouw's 3+3. -/
  | others
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Category

variable {c : Category}

/-- The speech-act participants a category contains. -/
def participants : Category → Finset Discourse.Role
  | speaker | speakerOthers => {.speaker}
  | addressee | addresseeOthers => {.addressee}
  | speakerAddressee | speakerAddresseeOthers => {.speaker, .addressee}
  | other | others => ∅

/-- The others a category contains: none, one, or several, several counting as two. -/
def otherCount : Category → Fin 3
  | speaker | addressee | speakerAddressee => 0
  | other | speakerOthers | addresseeOthers | speakerAddresseeOthers => 1
  | others => 2

/-- A configuration of participants and others is a category iff it is nonempty and has
    several others only on their own. The speaker and the addressee are unique individuals,
    so a group of speakers or of addressees does not arise, and a participant with one other
    or with several forms one group ([cysouw-2003] §3.4). -/
def WellFormed (x : Finset Discourse.Role × Fin 3) : Prop :=
  (x.1.Nonempty ∨ x.2 ≠ 0) ∧ (x.2 = 2 → x.1 = ∅)

instance : DecidablePred WellFormed := λ _ => by unfold WellFormed; infer_instance

/-- The configuration of a category. -/
def toConfig (c : Category) : {x // WellFormed x} :=
  ⟨(c.participants, c.otherCount), by cases c <;> decide +kernel⟩

/-- The categories are exactly the well-formed configurations. -/
theorem toConfig_bijective : Function.Bijective toConfig := ⟨by decide +kernel, by decide +kernel⟩

/-- All 8 categories in canonical order (singular, then group). -/
def all : List Category :=
  [.speaker, .addressee, .other, .speakerAddressee, .speakerAddresseeOthers, .speakerOthers,
    .addresseeOthers, .others]

/-- The members of a category, several others counting as two. -/
def card (c : Category) : ℕ := c.participants.card + c.otherCount

/-- A singular category has one member. -/
def IsSingular (c : Category) : Prop := c.card = 1

/-- A group category has several members. -/
def IsGroup (c : Category) : Prop := 2 ≤ c.card

/-- Does this category include the speaker? -/
def IncludesSpeaker (c : Category) : Prop := .speaker ∈ c.participants

/-- Does this category include the addressee? -/
def IncludesAddressee (c : Category) : Prop := .addressee ∈ c.participants

/-- The first person complex: the groups including the speaker. -/
def IsFirstPersonComplex (c : Category) : Prop := c.IncludesSpeaker ∧ c.IsGroup

/-- An inclusive category includes both the speaker and the addressee. -/
def IsInclusive (c : Category) : Prop := c.IncludesSpeaker ∧ c.IncludesAddressee

instance : DecidablePred IsSingular := λ _ => by unfold IsSingular; infer_instance
instance : DecidablePred IsGroup := λ _ => by unfold IsGroup; infer_instance
instance : DecidablePred IncludesSpeaker := λ _ => by unfold IncludesSpeaker; infer_instance
instance : DecidablePred IncludesAddressee := λ _ => by unfold IncludesAddressee; infer_instance
instance : DecidablePred IsFirstPersonComplex := λ _ => by
  unfold IsFirstPersonComplex; infer_instance
instance : DecidablePred IsInclusive := λ _ => by unfold IsInclusive; infer_instance

/-- A category is a group iff it is not singular. -/
theorem isGroup_iff_not_isSingular : c.IsGroup ↔ ¬ c.IsSingular := by
  revert c; decide +kernel

theorem IsInclusive.isFirstPersonComplex (h : c.IsInclusive) : c.IsFirstPersonComplex := by
  revert h; revert c; decide +kernel

theorem IsFirstPersonComplex.includesSpeaker (h : c.IsFirstPersonComplex) :
    c.IncludesSpeaker :=
  h.1

theorem IsInclusive.includesSpeaker (h : c.IsInclusive) : c.IncludesSpeaker := h.1

/-- The person of a category is the person of its participants, clusivity being a property
    of groups. -/
def person (c : Category) : Person :=
  if c.IsGroup then Person.ofParticipants c.participants
  else (Person.ofParticipants c.participants).coarsen

/-- The person projection tracks speaker inclusion. -/
theorem person_includesSpeaker_iff (c : Category) :
    c.person.IncludesSpeaker ↔ c.IncludesSpeaker := by
  cases c <;> decide +kernel

/-- Unlike UD realization, the person projection separates inclusive from exclusive. -/
theorem person_separates_clusivity :
    Category.speakerAddresseeOthers.person ≠ Category.speakerOthers.person := by decide +kernel

/-- The [cysouw-2003] categories a (person, number) coordinate pair can realize. Clusivity
    rides on the person value and the minimal/augmented coordinates give the minimal/augmented
    inclusives directly (Tagalog *kata* = `(firstInclusive, minimal)` ↦ `{speakerAddressee}`). A
    clusivity-unmarked non-singular first person is the syncretism
    `{speakerAddressee, speakerAddresseeOthers, speakerOthers}` (English *we*), general number is
    noncommittal between the singular and the group category (`(second, general)` ↦
    `{addressee, addresseeOthers}`), and a singular bearing clusivity or the impersonal person
    realizes nothing. -/
def ofPersonNumber : Person → Number → Finset Category
  | .first, .singular | .first, .minimal => {.speaker}
  | .first, .dual => {.speakerAddressee, .speakerOthers}
  | .first, .general => {.speaker, .speakerAddressee, .speakerAddresseeOthers, .speakerOthers}
  | .first, _ => {.speakerAddressee, .speakerAddresseeOthers, .speakerOthers}
  | .firstInclusive, .singular => ∅
  | .firstInclusive, .minimal | .firstInclusive, .dual => {.speakerAddressee}
  | .firstInclusive, .general => {.speakerAddressee, .speakerAddresseeOthers}
  | .firstInclusive, _ => {.speakerAddresseeOthers}
  | .firstExclusive, .singular => ∅
  | .firstExclusive, _ => {.speakerOthers}
  | .second, .singular | .second, .minimal => {.addressee}
  | .second, .general => {.addressee, .addresseeOthers}
  | .second, _ => {.addresseeOthers}
  | .third, .singular | .third, .minimal => {.other}
  | .third, .general => {.other, .others}
  | .third, _ => {.others}
  | .zero, _ => ∅

/-- `ofPersonNumber` inverts the person projection: every category is recovered from its
    coordinates at some number value. -/
theorem ofPersonNumber_person (c : Category) :
    ∃ n, ofPersonNumber c.person n = {c} := by
  cases c
  · exact ⟨.singular, rfl⟩
  · exact ⟨.singular, rfl⟩
  · exact ⟨.singular, rfl⟩
  · exact ⟨.minimal, rfl⟩
  · exact ⟨.augmented, rfl⟩
  · exact ⟨.plural, rfl⟩
  · exact ⟨.plural, rfl⟩
  · exact ⟨.plural, rfl⟩

/-! ### The person and number of a set of categories

A form that can denote several categories (the polite German *Sie*, addressee or addressees;
English *we*, any group containing the speaker) has a person and a number only up to the
values neutral between them: the clusivity-unmarked `first` and the noncommittal `general`. -/

/-- The person shared by a set of referential categories: the common value of `person` where
    there is one, `first` for categories differing only in clusivity, `none` for the empty set
    and for categories disagreeing on the speech-act roles they include. -/
def sharedPerson (s : Finset Category) : Option Person :=
  if s = ∅ then none
  else if ∀ c ∈ s, c.IncludesSpeaker then
    if ∀ c ∈ s, c.person = .firstInclusive then some .firstInclusive
    else if ∀ c ∈ s, c.person = .firstExclusive then some .firstExclusive
    else some .first
  else if ∀ c ∈ s, c.IncludesAddressee then some .second
  else if ∀ c ∈ s, ¬ c.IncludesSpeaker ∧ ¬ c.IncludesAddressee then some .third
  else none

/-- The number shared by a set of referential categories: singular or plural when the
    categories agree, `general` when they mix individuals and groups, `none` for the empty
    set. Cysouw's categories do not separate dual from plural, so the projection is at that
    granularity. -/
def sharedNumber (s : Finset Category) : Option Number :=
  if s = ∅ then none
  else if ∀ c ∈ s, c.IsSingular then some .singular
  else if ∀ c ∈ s, c.IsGroup then some .plural
  else some .general

/-- A single category shares its own person. -/
theorem sharedPerson_singleton (c : Category) : sharedPerson {c} = some c.person := by
  cases c <;> decide

/-- The categories a coordinate pair realizes share that person, wherever there are any. -/
theorem sharedPerson_ofPersonNumber (p : Person) (n : Number)
    (h : (ofPersonNumber p n).Nonempty) : sharedPerson (ofPersonNumber p n) = some p := by
  revert h; revert p n; decide

/-- The categories a coordinate pair realizes share the general number only at general
    number. -/
theorem sharedNumber_ofPersonNumber_eq_general (p : Person) (n : Number)
    (h : sharedNumber (ofPersonNumber p n) = some .general) : n = .general := by
  revert h; revert p n; decide

/-! ### The feature decomposition of a category -/

/-- The framework-neutral Cysouw/Siewierska `[±participant, ±author]` features of a category:
    whether it contains a speech-act participant and whether it contains the speaker. The
    features underdetermine the first person complex, whose three categories all map to
    `⟨true, true⟩`; the theory-laden Harbour-*sign* decomposition that distinguishes the
    exclusive (`+author −participant`) lives in `Studies.Harbour2016.signOf`. -/
def toFeatures (c : Category) : Features :=
  ⟨decide c.participants.Nonempty, decide c.IncludesSpeaker⟩

@[simp] theorem toFeatures_hasAuthor : c.toFeatures.hasAuthor = true ↔ c.IncludesSpeaker := by
  simp [toFeatures]

@[simp] theorem toFeatures_hasParticipant :
    c.toFeatures.hasParticipant = true ↔ c.IncludesSpeaker ∨ c.IncludesAddressee := by
  cases c <;> decide +kernel

/-- Every category yields well-formed features. -/
theorem toFeatures_wellFormed (c : Category) : c.toFeatures.WellFormed := by
  cases c <;> decide +kernel

end Category

-- ============================================================================
-- § 11: Epistemic Authority ([bickel-nichols-2007])
-- ============================================================================

/-- Epistemic authority marking on verb agreement.
    [bickel-nichols-2007]

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
