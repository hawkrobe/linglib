/-!
# Malayic Voice System: Voice/v Decomposition
@cite{erlewine-sommerlot-2025} @cite{nomoto-2015} @cite{nomoto-2021}

The verbal extended projection in Malayic languages involves two
functional heads above VP (@cite{nomoto-2015}, @cite{nomoto-2021}):

- **Voice** (higher): the phase head of the verbal domain. Always hosts
  exactly one nominal (DP) specifier. Realizes *me-*, *di-*, or ∅
  depending on adjacency to *v* and the flavor of *v*.

- ***v*** (lower): introduces the external argument in its specifier.
  Two flavors:
  - **v_ACT**: licenses the internal argument (theme) via c-command.
    Realizes as the homorganic nasal *N-*.
  - **v_PASS**: licenses its specifier (the external argument).
    Realizes as ∅.

The key insight of @cite{erlewine-sommerlot-2025} is that the active
prefix *meN-* in SI/SM reflects TWO affixes (*me-* on Voice + *N-* on
*v*), and that the behavior of object extraction constructions (so-called
"*meN*-deletion") follows from cyclic linearization when Voice is null.

## Cross-linguistic variation

The Malayic varieties differ only in their vocabulary items for Voice
and *v*, not in the underlying clause structure:

| Variety | Voice (active) | Voice (passive) | Voice (elsewhere) | v_ACT | v_PASS |
|---------|---------------|-----------------|-------------------|-------|--------|
| Desa    | me- / __ * v_ACT | di- / __ * v_PASS | ∅ | N- (always) | ∅ |
| SI/SM   | me- / __ * v_ACT | di- / __ * v_PASS | ∅ | N- / Voice * __ ; else ∅ | ∅ |
| Polite Madurese | N- / __ * v_ACT | e- / __ * v_PASS | ∅ | ∅ | ∅ |
| Familiar Madurese | N- / __ v_ACT·P | e- / __ v_PASS·P | (no elsewhere) | ∅ | ∅ |

`*` = linear adjacency required; `·P` = structural adjacency to vP.
-/

namespace Fragments.Malayic.VoiceSystem

-- ============================================================================
-- § 1: Head Flavors
-- ============================================================================

/-- The two flavors of the lower functional head *v*.
    @cite{erlewine-sommerlot-2025} (32b,c). -/
inductive LittleVFlavor where
  /-- Active: licenses internal argument via c-command.
      Realizes as homorganic nasal *N-*. -/
  | act
  /-- Passive: licenses its specifier (external argument, if present).
      Realizes as ∅. -/
  | pass
  deriving DecidableEq, BEq, Repr

/-- The four clause types in Malayic languages.
    @cite{erlewine-sommerlot-2025} (28), (29). -/
inductive ClauseType where
  /-- Active: agent = subject, *v* = v_ACT, Voice = *me-*/*N-*. -/
  | active
  /-- *di-* passive: theme = subject, *v* = v_PASS, Voice = *di-*. -/
  | diPassive
  /-- Bare passive: theme = subject, *v* = v_PASS, Voice = ∅,
      agent immediately preverbal. -/
  | barePassive
  /-- Object extraction: theme A'-extracted, *v* = v_ACT, Voice = ∅,
      agent immediately preverbal. -/
  | objectExtraction
  deriving DecidableEq, BEq, Repr

/-- The *v* flavor selected by each clause type. -/
def ClauseType.vFlavor : ClauseType → LittleVFlavor
  | .active          => .act
  | .diPassive        => .pass
  | .barePassive      => .pass
  | .objectExtraction => .act

-- ============================================================================
-- § 2: Vocabulary Items
-- ============================================================================

/-- A Malayic variety, characterized by its vocabulary items for Voice
    and *v*. Each variety is a function from clause type to the overt
    realizations of Voice and *v*. -/
structure MalayicVariety where
  name : String
  /-- Exponent of Voice in each clause type. `none` = null (pruned). -/
  voiceExponent : ClauseType → Option String
  /-- Exponent of *v* in each clause type. `none` = null. -/
  vExponent : ClauseType → Option String
  /-- Whether Voice has a null allomorph (∅ elsewhere).
      Determines availability of bare passive and object extraction. -/
  hasNullVoice : Bool

-- ============================================================================
-- § 3: Language-Specific Instantiations
-- ============================================================================

/-- Suak Mansi Desa voice system.
    @cite{erlewine-sommerlot-2025} (31)–(32).
    Key: *N-* and *meN-* are in free variation in active clauses;
    only *meN-* (= *me-* + *N-*) is blocked in object extraction. -/
def desa : MalayicVariety :=
  { name := "Desa"
  , voiceExponent := fun
      | .active          => some "me-"   -- optional; N- alone also possible
      | .diPassive        => some "di-"
      | .barePassive      => none         -- ∅ (elsewhere)
      | .objectExtraction => none         -- ∅ (forced by cyclic linearization)
  , vExponent := fun
      | .active          => some "N-"
      | .diPassive        => none
      | .barePassive      => none
      | .objectExtraction => some "N-"    -- N- survives; only me- blocked
  , hasNullVoice := true }

/-- Standard Indonesian / Standard Malay voice system.
    @cite{erlewine-sommerlot-2025} (48)–(49).
    Key: active verbs ALWAYS bear full *meN-* (no short *N-* variant).
    In object extraction, both *me-* and *N-* are lost. -/
def standardSISM : MalayicVariety :=
  { name := "SI/SM"
  , voiceExponent := fun
      | .active          => some "me-"
      | .diPassive        => some "di-"
      | .barePassive      => none
      | .objectExtraction => none
  , vExponent := fun
      | .active          => some "N-"    -- N- only when Voice adjacent
      | .diPassive        => none
      | .barePassive      => none
      | .objectExtraction => none         -- N- lost: Voice not adjacent
  , hasNullVoice := true }

/-- Polite-register Madurese.
    @cite{erlewine-sommerlot-2025} (81)–(82), based on @cite{jeoung-2017}.
    Three voices (like Desa/SI/SM) plus object extraction.
    Voice has a null elsewhere allomorph → bare passive and object
    extraction are available. -/
def politeMadurese : MalayicVariety :=
  { name := "Polite Madurese"
  , voiceExponent := fun
      | .active          => some "N-"    -- Voice = N- (not me-)
      | .diPassive        => some "e-"   -- Voice = e- (not di-)
      | .barePassive      => none
      | .objectExtraction => none
  , vExponent := fun _ => none            -- v always ∅ in Madurese
  , hasNullVoice := true }

/-- Familiar-register Madurese.
    @cite{erlewine-sommerlot-2025} (81), (83), based on @cite{jeoung-2017}.
    Only two voices (active, *e-* passive). Voice has NO null elsewhere
    allomorph → bare passive and object extraction are unavailable. -/
def familiarMadurese : MalayicVariety :=
  { name := "Familiar Madurese"
  , voiceExponent := fun
      | .active          => some "N-"
      | .diPassive        => some "e-"
      | .barePassive      => some "e-"    -- would be realized (structurally conditioned)
      | .objectExtraction => some "N-"    -- would be realized → crash
  , vExponent := fun _ => none
  , hasNullVoice := false }

-- ============================================================================
-- § 4: Predictions
-- ============================================================================

/-- Whether a clause type is grammatical in a given variety.
    Bare passives and object extraction require Voice to have a null
    allomorph. @cite{erlewine-sommerlot-2025} §4.3, §5.3. -/
def MalayicVariety.clauseAvailable (v : MalayicVariety) : ClauseType → Bool
  | .active          => true
  | .diPassive        => true
  | .barePassive      => v.hasNullVoice
  | .objectExtraction => v.hasNullVoice

-- ============================================================================
-- § 5: Verification
-- ============================================================================

/-- Desa has all four clause types. -/
theorem desa_all_four (ct : ClauseType) :
    desa.clauseAvailable ct = true := by cases ct <;> rfl

/-- SI/SM has all four clause types. -/
theorem sism_all_four (ct : ClauseType) :
    standardSISM.clauseAvailable ct = true := by cases ct <;> rfl

/-- Polite Madurese has all four clause types. -/
theorem polite_madurese_all_four (ct : ClauseType) :
    politeMadurese.clauseAvailable ct = true := by cases ct <;> rfl

/-- Familiar Madurese lacks bare passive and object extraction. -/
theorem familiar_madurese_no_bare_passive :
    familiarMadurese.clauseAvailable .barePassive = false := rfl
theorem familiar_madurese_no_object_extraction :
    familiarMadurese.clauseAvailable .objectExtraction = false := rfl
theorem familiar_madurese_has_active :
    familiarMadurese.clauseAvailable .active = true := rfl
theorem familiar_madurese_has_di_passive :
    familiarMadurese.clauseAvailable .diPassive = true := rfl

/-- The Madurese register contrast: the ONLY difference is whether Voice
    has a null allomorph. This single parameter accounts for the presence
    vs absence of bare passives and object extraction.
    @cite{erlewine-sommerlot-2025} §5.3. -/
theorem madurese_register_contrast :
    politeMadurese.hasNullVoice = true ∧
    familiarMadurese.hasNullVoice = false := ⟨rfl, rfl⟩

/-- In Desa object extraction, *v_ACT* still realizes as *N-*
    (only Voice/*me-* is blocked). In SI/SM, both are lost.
    This is the key Desa vs SI/SM contrast.
    @cite{erlewine-sommerlot-2025} §2.3, (25) vs (22). -/
theorem desa_keeps_n_in_extraction :
    desa.vExponent .objectExtraction = some "N-" := rfl
theorem sism_loses_n_in_extraction :
    standardSISM.vExponent .objectExtraction = none := rfl

/-- Object extraction always has v_ACT (not v_PASS). -/
theorem obj_extraction_uses_vACT :
    ClauseType.objectExtraction.vFlavor = .act := rfl

end Fragments.Malayic.VoiceSystem
