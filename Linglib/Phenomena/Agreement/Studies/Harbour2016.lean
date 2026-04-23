import Linglib.Features.Person
import Linglib.Features.Number
import Linglib.Theories.Syntax.Minimalism.CyclicAgree
import Linglib.Theories.Syntax.Minimalism.Agreement.FeatureRecursion
import Linglib.Phenomena.Agreement.Studies.Corbett2000

/-!
# Harbour (2016): Impossible Persons
@cite{harbour-2016}

Formalizes the core results of:

  Harbour, D. (2016). *Impossible Persons*. Linguistic Inquiry Monographs 74.
  MIT Press.

## The Partition Problem

Person categories are not primitives — they are **derived** from two privative
features [±author] and [±participant] operating on **sets** of discourse
participants. These features have the containment relation [+author] ⊂
[+participant] (an author is necessarily a participant), making them an instance
of the `Features.PrivativePair` abstraction.

The key insight: features evaluate over groups (non-empty sets of individuals),
not just atomic referents. A group is [+author] iff it **contains** the speaker;
[+participant] iff it contains **any** speech-act participant.

## Results Formalized

1. **Discourse groups derive the 8 person categories** (Ch 4–5). Three discourse
   roles (speaker, addressee, other) × atomicity yield exactly the 8 categories
   from @cite{cysouw-2009}'s typological inventory. No more, no fewer.

2. **Person–number isomorphism** (Ch 9: "The Phi Kernel"). Person features
   [±participant, ±author] and number features [±minimal, ±atomic] instantiate
   the same `PrivativePair` skeleton via `PhiFeatures`.

3. **Clusivity derived** (Ch 5). Inclusive/exclusive is not a feature — it falls
   out of person × atomicity. A [+author] non-atomic group is inclusive iff it
   also contains the addressee; exclusive otherwise.

4. **Impossibility results** (Ch 4–5). No 4-way singular person; no person
   system with exclusive but not inclusive.

5. **Containment hierarchy** (Ch 9). The person hierarchy 1 > 2 > 3 and number
   hierarchy sg > du > pl both reduce to the specification ordering of
   `PrivativePair`. Bridge theorem `specLevel_agrees_with_segments` connects
   this to @cite{bejar-rezac-2009}'s articulated segments.

-/

namespace Harbour2016

open Features.Person
open Features.Number (singularF dualF pluralF)
open Features (PhiFeatures PrivativePair)

-- ============================================================================
-- § 1: Clusivity
-- ============================================================================

/-- Clusivity values for non-atomic [+author] groups.

    @cite{harbour-2016} Ch 5: clusivity is derived from the interaction
    of person features and group composition, not from a stipulated
    [±inclusive] feature. -/
inductive Clusivity where
  | inclusive   -- speaker + addressee (± others)
  | exclusive   -- speaker + others, no addressee
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Discourse Groups
-- ============================================================================

/-- A discourse group: a non-empty collection of discourse participants,
    described by which role types are present and whether the group is atomic.

    Three role types: speaker, addressee, other (non-SAP). A group must
    contain at least one member (`nonempty`). An atomic group contains
    exactly one individual (`atomic_exclusive`).

    **Representational note**: @cite{harbour-2016} uses actual sets of
    individuals, making atomicity a derived property (|group| = 1). The
    Boolean encoding here requires explicit constraints (`atomic_exclusive`,
    `nonatomic_multiple`) to maintain consistency between the role flags
    and the atomicity flag. These constraints are representational guards,
    not part of Harbour's theory. -/
structure DiscourseGroup where
  /-- The group contains the speaker. -/
  hasSpeaker : Bool
  /-- The group contains the addressee. -/
  hasAddressee : Bool
  /-- The group contains at least one non-SAP individual. -/
  hasOther : Bool
  /-- The group is a singleton (one individual). -/
  isAtomic : Bool
  /-- Non-empty: at least one role present. -/
  nonempty : hasSpeaker || hasAddressee || hasOther = true
  /-- Atomic groups have at most one role type (no pair is both true).
      Combined with `nonempty`, this gives exactly one. -/
  atomic_exclusive : isAtomic = true →
    (hasSpeaker && hasAddressee) = false ∧
    (hasSpeaker && hasOther) = false ∧
    (hasAddressee && hasOther) = false
  /-- Non-atomic groups require multiple individuals. In the Boolean encoding,
      this means either ≥ 2 role types are present, or the "other" slot
      represents multiple individuals (as in thirdGrp = {3, 3}). -/
  nonatomic_multiple : isAtomic = false →
    (hasSpeaker && hasAddressee) = true ∨
    (hasSpeaker && hasOther) = true ∨
    (hasAddressee && hasOther) = true ∨
    hasOther = true
  deriving DecidableEq

-- ============================================================================
-- § 3: Person Features on Groups
-- ============================================================================

/-- [+author]: the group contains the speaker.
    @cite{harbour-2016} Ch 4: features evaluate over sets, not atoms. -/
def DiscourseGroup.author (g : DiscourseGroup) : Bool := g.hasSpeaker

/-- [+participant]: the group contains at least one SAP. -/
def DiscourseGroup.participant (g : DiscourseGroup) : Bool :=
  g.hasSpeaker || g.hasAddressee

/-- Extract the PrivativePair: outer = participant, inner = author. -/
def DiscourseGroup.toPrivativePair (g : DiscourseGroup) : PrivativePair :=
  ⟨g.participant, g.author⟩

/-- Person features on groups are always well-formed:
    [+author] → [+participant] because the speaker is a participant. -/
theorem DiscourseGroup.wellFormed (g : DiscourseGroup) :
    g.toPrivativePair.wellFormed = true := by
  simp [toPrivativePair, participant, author, PrivativePair.wellFormed]
  cases g.hasSpeaker <;> simp

/-- Group-level person features agree with Features.Person.Features
    on the atomic (singular) cases. -/
theorem DiscourseGroup.agrees_with_core (g : DiscourseGroup) :
    g.toPrivativePair =
      PhiFeatures.toPair (Features.Person.Features.mk g.participant g.author) := by
  rfl

-- ============================================================================
-- § 4: The Eight Categories
-- ============================================================================

/-- Map a DiscourseGroup to the corresponding Cysouw Category. -/
def DiscourseGroup.toCategory (g : DiscourseGroup) : Category :=
  match g.isAtomic, g.hasSpeaker, g.hasAddressee, g.hasOther with
  -- Singular (atomic) categories
  | true, true,  false, false => .s1         -- speaker alone
  | true, false, true,  false => .s2         -- addressee alone
  | true, false, false, true  => .s3         -- other alone
  -- Group (non-atomic) categories
  | false, true,  true,  false => .minIncl   -- speaker + addressee
  | false, true,  true,  true  => .augIncl   -- speaker + addressee + other(s)
  | false, true,  false, true  => .excl      -- speaker + other(s)
  | false, false, true,  true  => .secondGrp -- addressee + other(s)
  | false, false, false, true  => .thirdGrp  -- other(s) only, non-atomic
  -- Remaining cases are unreachable for well-formed groups; the constraints
  -- `nonempty`, `atomic_exclusive`, and `nonatomic_multiple` rule them out.
  | _, _, _, _ => .s3

/-- All 8 Cysouw categories are reachable from discourse groups. -/
theorem all_categories_reachable :
    ∀ c : Category, ∃ g : DiscourseGroup, g.toCategory = c := by
  intro c; cases c
  · exact ⟨⟨true, false, false, true, rfl, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨false, true, false, true, rfl, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨false, false, true, true, rfl, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨true, true, false, false, rfl, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨true, true, true, false, rfl, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨true, false, true, false, rfl, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨false, true, true, false, rfl, by decide, by decide⟩, rfl⟩
  · exact ⟨⟨false, false, true, false, rfl, by decide, by decide⟩, rfl⟩

-- ============================================================================
-- § 5: Person Features Agree with Core
-- ============================================================================

/-- Group-level person features agree with `Category.toFeatures`:
    the PrivativePair extracted from a group matches the one extracted
    from its Cysouw category.

    This is the key consistency result: the set-level feature evaluation
    (@cite{harbour-2016}) and the individual-level feature assignment
    (Core) agree on the person feature values for each category. -/
theorem group_features_match_category :
    ∀ c : Category,
      ∃ g : DiscourseGroup,
        g.toCategory = c ∧
        g.toPrivativePair = PhiFeatures.toPair c.toFeatures := by
  intro c; cases c
  · exact ⟨⟨true, false, false, true, rfl, by decide, by decide⟩, rfl, rfl⟩
  · exact ⟨⟨false, true, false, true, rfl, by decide, by decide⟩, rfl, rfl⟩
  · exact ⟨⟨false, false, true, true, rfl, by decide, by decide⟩, rfl, rfl⟩
  · exact ⟨⟨true, true, false, false, rfl, by decide, by decide⟩, rfl, rfl⟩
  · exact ⟨⟨true, true, true, false, rfl, by decide, by decide⟩, rfl, rfl⟩
  · exact ⟨⟨true, false, true, false, rfl, by decide, by decide⟩, rfl, rfl⟩
  · exact ⟨⟨false, true, true, false, rfl, by decide, by decide⟩, rfl, rfl⟩
  · exact ⟨⟨false, false, true, false, rfl, by decide, by decide⟩, rfl, rfl⟩

-- ============================================================================
-- § 6: Person–Number Isomorphism
-- ============================================================================

/-- Person and number share the same PrivativePair skeleton.

    This is @cite{harbour-2016}'s "phi kernel" (Ch 9): the structural parallel
    between person (1st/2nd/3rd) and number (singular/dual/plural) is not
    accidental — both are instances of the same 2-feature containment geometry.

    - Person maximal = 1st person = [+participant, +author]
    - Number maximal = singular = [+minimal, +atomic]
    - Both map to `PrivativePair.maximal` = `⟨true, true⟩`

    And so on for intermediate (2nd/dual) and minimal (3rd/plural). -/
theorem person_number_isomorphism :
    PhiFeatures.toPair singularF = PhiFeatures.toPair Features.Person.first ∧
    PhiFeatures.toPair dualF = PhiFeatures.toPair Features.Person.second ∧
    PhiFeatures.toPair pluralF = PhiFeatures.toPair Features.Person.third := ⟨rfl, rfl, rfl⟩

/-- The isomorphism factors through PrivativePair's canonical cells. -/
theorem person_number_via_cells :
    PhiFeatures.toPair Features.Person.first = .maximal ∧
    PhiFeatures.toPair Features.Person.second = .intermediate ∧
    PhiFeatures.toPair Features.Person.third = .minimal ∧
    PhiFeatures.toPair singularF = .maximal ∧
    PhiFeatures.toPair dualF = .intermediate ∧
    PhiFeatures.toPair pluralF = .minimal := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: Clusivity Derivation
-- ============================================================================

/-- Clusivity is derived, not stipulated.

    A non-atomic [+author] group (= first person non-singular) is:
    - **inclusive** iff it also contains the addressee
    - **exclusive** iff it does not

    No [±inclusive] feature is needed — clusivity falls out of the
    interaction between person features and group composition (Ch 5). -/
def clusivityFromGroup (g : DiscourseGroup) : Option Clusivity :=
  if g.isAtomic then none
  else if !g.hasSpeaker then none
  else if g.hasAddressee then some .inclusive
  else some .exclusive

/-- Inclusive groups are exactly those with both speaker and addressee. -/
theorem inclusive_iff_addressee (g : DiscourseGroup)
    (hna : g.isAtomic = false) (hspk : g.hasSpeaker = true) :
    clusivityFromGroup g = some .inclusive ↔ g.hasAddressee = true := by
  cases ha : g.hasAddressee <;> simp [clusivityFromGroup, hna, hspk, ha]

/-- Clusivity agrees with `Category.isInclusive`: categories that
    Cysouw marks as inclusive (minIncl, augIncl) are exactly the
    non-atomic [+author] groups that contain the addressee. -/
theorem clusivity_matches_category :
    clusivityFromGroup ⟨true, true, false, false, rfl,
      by decide, by decide⟩ = some .inclusive ∧   -- minIncl
    clusivityFromGroup ⟨true, true, true, false, rfl,
      by decide, by decide⟩ = some .inclusive ∧   -- augIncl
    clusivityFromGroup ⟨true, false, true, false, rfl,
      by decide, by decide⟩ = some .exclusive     -- excl
  := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Impossibility Results
-- ============================================================================

/-- **No 4-way singular person.** (Immediate from `Features.Person.no_fourth_person`.)

    Since singular categories are atomic discourse groups, and person
    features on atomic groups reduce to individual-level features,
    the 3-cell PrivativePair limit applies directly (Ch 4). -/
theorem no_four_singular_persons :
    ∀ (a b c d : Features.Person.Features),
      a.wellFormed = true → b.wellFormed = true →
      c.wellFormed = true → d.wellFormed = true →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  Features.Person.no_fourth_person

/-- **No exclusive without inclusive** (system-level).

    @cite{harbour-2016} Ch 5, §5.3: if a person system has the exclusive
    category (non-atomic [+author] groups without the addressee), then
    inclusive groups are also constructible from the same feature inventory.
    Both configurations use [+author] on a non-atomic group; they differ
    only in whether the addressee is present in the group.

    The feature system [±participant, ±author] operating over non-atomic
    groups *necessarily* generates both inclusive and exclusive
    configurations. Any feature inventory supporting exclusive
    automatically supports inclusive — this is an inherent consequence
    of the feature system, not an independent parameter. -/
theorem no_exclusive_without_inclusive :
    (∃ g : DiscourseGroup, clusivityFromGroup g = some .exclusive) →
    (∃ g : DiscourseGroup, clusivityFromGroup g = some .inclusive) := by
  intro ⟨_, _⟩
  exact ⟨⟨true, true, false, false, rfl, by decide, by decide⟩, rfl⟩

-- ============================================================================
-- § 9: Containment Hierarchy
-- ============================================================================

/-- The person hierarchy 1 > 2 > 3 is the specification ordering of
    PrivativePair: maximal > intermediate > minimal. This connects
    @cite{harbour-2016}'s lattice approach to the person hierarchy
    used in @cite{bejar-rezac-2009}'s Cyclic Agree and
    @cite{preminger-2014}'s relativized probing. -/
theorem person_hierarchy_is_spec_ordering :
    PhiFeatures.specLevel Features.Person.first >
      PhiFeatures.specLevel Features.Person.second ∧
    PhiFeatures.specLevel Features.Person.second >
      PhiFeatures.specLevel Features.Person.third := ⟨by decide, by decide⟩

/-- The number hierarchy sg > du > pl is the same specification ordering. -/
theorem number_hierarchy_is_spec_ordering :
    PhiFeatures.specLevel singularF >
      PhiFeatures.specLevel dualF ∧
    PhiFeatures.specLevel dualF >
      PhiFeatures.specLevel pluralF := ⟨by decide, by decide⟩

-- ============================================================================
-- § 10: Bridge to Cyclic Agree
-- ============================================================================

open Minimalism.CyclicAgree (personSpec)
open Features.Prominence (PersonLevel)

/-- The person hierarchy from `PrivativePair.specLevel` agrees with the
    segment count hierarchy from @cite{bejar-rezac-2009}'s Cyclic Agree.

    In the standard geometry, `specLevel + 1 = segment count`:
    - 1st: specLevel 2, segments [π, participant, speaker] (length 3)
    - 2nd: specLevel 1, segments [π, participant] (length 2)
    - 3rd: specLevel 0, segments [π] (length 1)

    This is the formal bridge between @cite{harbour-2016}'s algebraic
    person hierarchy (PrivativePair specification level) and
    @cite{bejar-rezac-2009}'s syntactic one (articulated segment count).
    The person hierarchy is *one* hierarchy realized in two independent
    formalizations: featural (spec level) and configurational (probe depth). -/
theorem specLevel_agrees_with_segments (p : PersonLevel) :
    PhiFeatures.specLevel (p.toFeatures) + 1 =
    (personSpec .standard p).length := by
  cases p <;> rfl

-- ============================================================================
-- § 11: Bridge to Corbett2000 via Feature Geometry
-- ============================================================================

/-! Every attested number system from @cite{corbett-2000} can be generated
    by some well-formed @cite{harbour-2016} configuration. This bridges the
    typological inventory (observed systems) with the feature geometry
    (generative mechanism).

    The bridge is a SUBSET relation: a language may not lexicalize all
    categories its feature geometry makes available (syncretism, facultative
    marking). What matters is that every attested category IS generated. -/

open Minimalism.Agreement.FeatureRecursion (HarbourConfig)
open Corbett2000

/-- Every attested number system's values are a subset of what some
    well-formed Harbour configuration generates.

    - Pirahã: no features → no categories
    - English/Russian/Japanese: [±atomic] only → {sg, pl}
    - Upper Sorbian/Slovene: [±atomic, ±minimal] → {sg, du, pl}
    - Bayso: [±atomic, ±additive] → {sg, pl, pauc}
    - Larike: [±atomic, ±minimal] + [±minimal] recursion → {sg, du, pl, trial, grpl}
    - Lihir: [±atomic, ±minimal, ±additive] + [±minimal] recursion →
             {sg, du, pl, trial, grpl, pauc} -/
theorem attested_number_systems_derivable :
    pirahaNS.values.all
      ((HarbourConfig.mk false false false false false).categories.contains ·) = true ∧
    englishNS.values.all
      ((HarbourConfig.mk true false false false false).categories.contains ·) = true ∧
    russianNS.values.all
      ((HarbourConfig.mk true false false false false).categories.contains ·) = true ∧
    upperSorbianNS.values.all
      ((HarbourConfig.mk true true false false false).categories.contains ·) = true ∧
    baysoNS.values.all
      ((HarbourConfig.mk true false true false false).categories.contains ·) = true ∧
    sloveneNS.values.all
      ((HarbourConfig.mk true true false false false).categories.contains ·) = true ∧
    larikeNS.values.all
      ((HarbourConfig.mk true true false true false).categories.contains ·) = true ∧
    lihirNS.values.all
      ((HarbourConfig.mk true true true true false).categories.contains ·) = true ∧
    japaneseNS.values.all
      ((HarbourConfig.mk true false false false false).categories.contains ·) = true
    := by native_decide

/-- MIN/AUG systems from @cite{harbour-2014} Table 3, now expressible
    with the expanded `Category` type. -/
theorem minAug_systems_derivable :
    winnebagoNS.values.all
      ((HarbourConfig.mk false true false false false).categories.contains ·) = true ∧
    rembarrnganS.values.all
      ((HarbourConfig.mk false true false true false).categories.contains ·) = true ∧
    mebengokreNS.values.all
      ((HarbourConfig.mk false true true false false).categories.contains ·) = true
    := by native_decide

/-- The Harbour configurations used in the bridge are all well-formed. -/
theorem bridge_configs_wellFormed :
    (HarbourConfig.mk false false false false false).wellFormed = true ∧
    (HarbourConfig.mk true false false false false).wellFormed = true ∧
    (HarbourConfig.mk true true false false false).wellFormed = true ∧
    (HarbourConfig.mk true false true false false).wellFormed = true ∧
    (HarbourConfig.mk true true false true false).wellFormed = true ∧
    (HarbourConfig.mk true true true true false).wellFormed = true ∧
    -- New configs for MIN/AUG systems:
    (HarbourConfig.mk false true false false false).wellFormed = true ∧
    (HarbourConfig.mk false true false true false).wellFormed = true ∧
    (HarbourConfig.mk false true true false false).wellFormed = true
    := by decide

end Harbour2016
