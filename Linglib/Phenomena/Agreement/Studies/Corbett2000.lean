import Linglib.Phenomena.Plurals.Typology
import Linglib.Phenomena.Agreement.Typology
import Linglib.Core.Lexical.UD

/-!
# Corbett (2000) — Number
@cite{corbett-2000}

Formalizes the core typological framework from:

  Corbett, G. G. (2000). *Number*. Cambridge Textbooks in Linguistics.
  Cambridge University Press.

## Core Contributions

1. **Number value inventory** (Ch 2): includes *general number* — a form outside
   the number system, non-committal as to cardinality (Bayso *lúban* 'lion(s)',
   Japanese *inu* 'dog(s)', Arabic collectives). Values are classified as
   **determinate** (fixed cardinality: singular=1, dual=2, trial=3) vs
   **indeterminate** (contextually variable: paucal, greater plural).

2. **Number system typology** (§2.3): implicational universals constrain which
   systems are possible — trial → dual → plural → singular.

3. **Animacy Hierarchy constraints** (Ch 3, @cite{smith-stark-1974}): the
   likelihood of number being distinguished decreases monotonically from
   speaker toward inanimate. Connects to `AnimacyRank` in `Core.Prominence`.

4. **The Agreement Hierarchy** (Ch 6, §6.2): for controllers permitting
   alternative agreement, semantic agreement increases monotonically along
   attributive < predicate < relative pronoun < personal pronoun.

5. **Controller–target mismatch** (§6.1): controller and target may have
   different number systems (Bayso: 4 controller values, 3 target forms).
-/

namespace Phenomena.Agreement.Studies.Corbett2000

-- ============================================================================
-- §1: Number Values (Ch 2)
-- ============================================================================

/-- Number values in Corbett's inventory.

    Two orthogonal classifications:
    - **System membership**: general is *outside* the number system; all others
      are within it.
    - **Determinacy**: values whose cardinality boundary is fixed (singular=1,
      dual=2, trial=3) vs those whose boundary varies by context (paucal ≈ 2–6,
      greater plural ≈ all/abundance). -/
inductive NumberValue where
  | general        -- non-committal, outside the number system
  | singular       -- exactly one
  | dual           -- exactly two
  | trial          -- exactly three
  | paucal         -- a few (indeterminate, ~2–6)
  | plural         -- more than one (residual)
  | greaterPaucal  -- indeterminate, larger than paucal
  | greaterPlural  -- abundance / totality (indeterminate)
  deriving DecidableEq, BEq, Repr

/-- A number value is determinate iff its cardinality boundary is fixed. -/
def NumberValue.isDeterminate : NumberValue → Bool
  | .singular | .dual | .trial => true
  | _ => false

/-- A number value participates in the number system (is not general). -/
def NumberValue.isInSystem : NumberValue → Bool
  | .general => false
  | _ => true

/-- Map Corbett's values to UD.Number (general has no UD equivalent). -/
def NumberValue.toUD : NumberValue → Option UD.Number
  | .general       => none
  | .singular      => some .Sing
  | .dual          => some .Dual
  | .trial         => some .Tri
  | .paucal        => some .Pauc
  | .plural        => some .Plur
  | .greaterPaucal => some .Grpa
  | .greaterPlural => some .Grpl

/-- Map UD.Number to Corbett's values (total). -/
def NumberValue.fromUD : UD.Number → NumberValue
  | .Sing  => .singular
  | .Plur  => .plural
  | .Dual  => .dual
  | .Tri   => .trial
  | .Pauc  => .paucal
  | .Grpa  => .greaterPaucal
  | .Grpl  => .greaterPlural
  | .Inv   => .plural     -- inverse encodes a number opposition
  | .Coll  => .general    -- collectives are non-committal to cardinality
  | .Count => .singular   -- count forms specify individuation

/-- Round-trip: fromUD ∘ toUD = id for all in-system values. -/
theorem roundtrip_fromUD_toUD :
    [NumberValue.singular, .dual, .trial, .paucal, .plural,
     .greaterPaucal, .greaterPlural].all
      (λ v => v.toUD.map NumberValue.fromUD == some v) = true := by native_decide

-- ============================================================================
-- §2: Number Systems (Ch 2, §2.3)
-- ============================================================================

/-- A number system specifies the values available in a language,
    which are obligatory vs facultative, and whether general number exists. -/
structure NumberSystem where
  name : String
  /-- Values available within the number system -/
  values : List NumberValue
  /-- Whether the language has general number (a form outside the system) -/
  hasGeneral : Bool := false
  /-- Values whose use is optional (facultative) -/
  facultative : List NumberValue := []
  deriving BEq

/-- Number of values in the system. -/
def NumberSystem.size (ns : NumberSystem) : Nat := ns.values.length

/-- Whether a value is obligatory (present and not facultative). -/
def NumberSystem.isObligatory (ns : NumberSystem) (v : NumberValue) : Bool :=
  ns.values.contains v && !(ns.facultative.contains v)

-- Language number systems

/-- English: obligatory sg–pl, no general number. -/
def englishNS : NumberSystem :=
  { name := "English", values := [.singular, .plural] }

/-- Russian: obligatory sg–pl, no general number. -/
def russianNS : NumberSystem :=
  { name := "Russian", values := [.singular, .plural] }

/-- Upper Sorbian: sg–dual–pl, all obligatory. -/
def upperSorbianNS : NumberSystem :=
  { name := "Upper Sorbian", values := [.singular, .dual, .plural] }

/-- Bayso (Cushitic): sg–paucal–pl within the system; general form *lúban*
    'lion(s)' exists outside it. Four controller values total. -/
def baysoNS : NumberSystem :=
  { name := "Bayso"
    values := [.singular, .paucal, .plural]
    hasGeneral := true }

/-- Slovene: sg–dual–pl, but the dual is facultative (plural substitutes). -/
def sloveneNS : NumberSystem :=
  { name := "Slovene"
    values := [.singular, .dual, .plural]
    facultative := [.dual] }

/-- Larike (Central Moluccan): sg–dual–trial–pl, dual and trial both
    facultative (plural can substitute for either). -/
def larikeNS : NumberSystem :=
  { name := "Larike"
    values := [.singular, .dual, .trial, .plural]
    facultative := [.dual, .trial] }

/-- Lihir (Oceanic): sg–dual–trial–paucal–pl, five values — the richest
    well-documented system. -/
def lihirNS : NumberSystem :=
  { name := "Lihir"
    values := [.singular, .dual, .trial, .paucal, .plural] }

/-- Japanese: sg–pl within the system, but general number exists
    (bare *inu* 'dog(s)' is non-committal). -/
def japaneseNS : NumberSystem :=
  { name := "Japanese"
    values := [.singular, .plural]
    hasGeneral := true }

/-- Pirahã (Mura): no number category at all. -/
def pirahaNS : NumberSystem :=
  { name := "Pirahã", values := [] }

def allNumberSystems : List NumberSystem :=
  [englishNS, russianNS, upperSorbianNS, baysoNS, sloveneNS,
   larikeNS, lihirNS, japaneseNS, pirahaNS]

-- Size checks
theorem english_two : englishNS.size = 2 := by native_decide
theorem upperSorbian_three : upperSorbianNS.size = 3 := by native_decide
theorem lihir_five : lihirNS.size = 5 := by native_decide
theorem piraha_zero : pirahaNS.size = 0 := by native_decide

-- General number
theorem bayso_has_general : baysoNS.hasGeneral = true := by native_decide
theorem japanese_has_general : japaneseNS.hasGeneral = true := by native_decide
theorem english_no_general : englishNS.hasGeneral = false := by native_decide

-- Facultative number
theorem slovene_dual_facultative :
    sloveneNS.facultative.contains .dual = true := by native_decide

theorem larike_both_facultative :
    larikeNS.facultative.contains .dual = true ∧
    larikeNS.facultative.contains .trial = true := by native_decide

-- Implicational universals (@cite{greenberg-1963}, Corbett §2.3.1)

/-- Trial implies dual: no language has trial without dual. -/
def NumberSystem.trialImpliesDual (ns : NumberSystem) : Bool :=
  !ns.values.contains .trial || ns.values.contains .dual

/-- Dual implies plural. -/
def NumberSystem.dualImpliesPlural (ns : NumberSystem) : Bool :=
  !ns.values.contains .dual || ns.values.contains .plural

/-- Plural implies singular (unless the system is empty = no number). -/
def NumberSystem.pluralImpliesSingular (ns : NumberSystem) : Bool :=
  !ns.values.contains .plural || ns.values.contains .singular ||
  ns.values.isEmpty

theorem all_trial_implies_dual :
    allNumberSystems.all (·.trialImpliesDual) = true := by native_decide

theorem all_dual_implies_plural :
    allNumberSystems.all (·.dualImpliesPlural) = true := by native_decide

theorem all_plural_implies_singular :
    allNumberSystems.all (·.pluralImpliesSingular) = true := by native_decide

-- ============================================================================
-- §3: Animacy Hierarchy and Number Marking (Ch 3)
-- ============================================================================

open Core.Prominence (AnimacyRank)

/-- Number marking status at a position on the Animacy Hierarchy. -/
inductive MarkingStatus where
  | obligatory  -- must mark number
  | optional    -- may mark number
  | absent      -- cannot mark number
  deriving DecidableEq, BEq, Repr

/-- Numeric ordering: higher = more marking. -/
def MarkingStatus.toNat : MarkingStatus → Nat
  | .obligatory => 2
  | .optional   => 1
  | .absent     => 0

/-- An animacy–number profile records marking status at each hierarchy
    position for a particular language. -/
structure AnimacyNumberProfile where
  name : String
  /-- Marking status at each position on the hierarchy. -/
  status : AnimacyRank → MarkingStatus

private def allRanks : List AnimacyRank :=
  [.speaker, .addressee, .thirdPerson, .kin, .human,
   .higherAnimal, .lowerAnimal, .discreteInanimate, .nondiscreteInanimate]

/-- **Constraint I** (Corbett Ch 3): the sg–pl distinction must affect a
    top segment of the hierarchy. If any position has obligatory marking,
    then the topmost position (speaker) does too. -/
def AnimacyNumberProfile.respectsConstraintI (p : AnimacyNumberProfile) : Bool :=
  !allRanks.any (λ r => (p.status r).toNat >= 2) ||
    (p.status .speaker).toNat >= 2

/-- **Constraint III** (Corbett Ch 3): as we move rightward along the
    hierarchy, the likelihood of number being distinguished decreases
    monotonically — no intervening increase. -/
def AnimacyNumberProfile.respectsConstraintIII (p : AnimacyNumberProfile) : Bool :=
  allRanks.all λ r1 =>
    allRanks.all λ r2 =>
      r1.toNat <= r2.toNat || (p.status r1).toNat >= (p.status r2).toNat

-- Language profiles

/-- English: obligatory everywhere (regular split at the bottom). -/
def englishAnimacy : AnimacyNumberProfile :=
  { name := "English", status := λ _ => .obligatory }

/-- Kannada (Dravidian): obligatory for humans, optional for non-human
    animates, absent for inanimates. -/
def kannadaAnimacy : AnimacyNumberProfile :=
  { name := "Kannada"
    status := λ
      | .speaker | .addressee | .thirdPerson | .kin | .human => .obligatory
      | .higherAnimal | .lowerAnimal => .optional
      | .discreteInanimate | .nondiscreteInanimate => .absent }

/-- Slave (Athabaskan): obligatory for humans and kin, absent below. -/
def slaveAnimacy : AnimacyNumberProfile :=
  { name := "Slave"
    status := λ
      | .speaker | .addressee | .thirdPerson | .kin | .human => .obligatory
      | _ => .absent }

def allAnimacyProfiles : List AnimacyNumberProfile :=
  [englishAnimacy, kannadaAnimacy, slaveAnimacy]

/-- Constraints I and III hold for all profiled languages. -/
theorem constraint_i_holds :
    allAnimacyProfiles.all (·.respectsConstraintI) = true := by native_decide

theorem constraint_iii_holds :
    allAnimacyProfiles.all (·.respectsConstraintIII) = true := by native_decide

-- ============================================================================
-- §4: The Agreement Hierarchy (Ch 6, §6.2)
-- ============================================================================

/-- Agreement target types, ordered by syntactic closeness to the controller.

    The ordering is Corbett's Agreement Hierarchy: attributive < predicate <
    relative pronoun < personal pronoun. As we move rightward, semantic
    agreement becomes more likely. -/
inductive AgreementTarget where
  | attributive      -- "this committee" / "*these committee"
  | predicate        -- "the committee has/have decided"
  | relativePronoun  -- "the committee, which/who..."
  | personalPronoun  -- "the committee... it/they"
  deriving DecidableEq, BEq, Repr

/-- Rank on the Agreement Hierarchy (higher = further right = more semantic). -/
def AgreementTarget.rank : AgreementTarget → Nat
  | .attributive     => 0
  | .predicate       => 1
  | .relativePronoun => 2
  | .personalPronoun => 3

/-- Whether agreement is determined by morphological form (syntactic)
    or by referential meaning (semantic). -/
inductive AgreementType where
  | syntactic  -- form-driven: *committee* is morphologically singular
  | semantic   -- meaning-driven: *committee* denotes a group of individuals
  deriving DecidableEq, BEq, Repr

/-- An agreement profile for a controller type records whether semantic
    agreement is available at each target position. -/
structure AgreementProfile where
  /-- Controller description -/
  controller : String
  /-- Whether semantic (meaning-driven) agreement is possible at each target -/
  semanticPossible : AgreementTarget → Bool

/-- The Agreement Hierarchy monotonicity constraint: once semantic agreement
    becomes possible at a target, it remains possible at all targets further
    right on the hierarchy. -/
def AgreementProfile.respectsHierarchy (p : AgreementProfile) : Bool :=
  let targets := [AgreementTarget.attributive, .predicate,
                   .relativePronoun, .personalPronoun]
  targets.all λ t1 =>
    targets.all λ t2 =>
      t1.rank >= t2.rank || !p.semanticPossible t1 || p.semanticPossible t2

-- Language data

/-- British English *committee*: syntactic only in attributive position;
    semantic agreement possible in predicate, relative pronoun, and
    personal pronoun. -/
def britishCommittee : AgreementProfile :=
  { controller := "committee (British English)"
    semanticPossible := λ
      | .attributive     => false  -- *these committee
      | .predicate       => true   -- the committee have decided
      | .relativePronoun => true   -- the committee, who have...
      | .personalPronoun => true } -- the committee... they

/-- American English *committee*: semantic agreement rare in predicate,
    but available in relative and personal pronoun. -/
def americanCommittee : AgreementProfile :=
  { controller := "committee (American English)"
    semanticPossible := λ
      | .attributive     => false
      | .predicate       => false  -- ?the committee have decided (rare in AmE)
      | .relativePronoun => true
      | .personalPronoun => true }

/-- Serbo-Croatian *deca* 'children': morphologically feminine singular,
    semantically plural. Semantic agreement available everywhere. -/
def serboCroatDeca : AgreementProfile :=
  { controller := "deca 'children' (Serbo-Croatian)"
    semanticPossible := λ _ => true }

def allAgreementProfiles : List AgreementProfile :=
  [britishCommittee, americanCommittee, serboCroatDeca]

/-- The Agreement Hierarchy is respected by all profiled controllers. -/
theorem agreement_hierarchy_holds :
    allAgreementProfiles.all (·.respectsHierarchy) = true := by native_decide

/-- Once semantic agreement reaches the personal pronoun (rightmost),
    it is necessarily available there for all our controllers. -/
theorem semantic_at_pronoun :
    allAgreementProfiles.all (·.semanticPossible .personalPronoun) = true := by
  native_decide

/-- No controller has semantic agreement only at the attributive position
    (the leftmost) without also having it further right — this would violate
    the monotonicity constraint. -/
theorem no_attributive_only_semantic :
    allAgreementProfiles.all (λ p =>
      !p.semanticPossible .attributive ||
       p.semanticPossible .personalPronoun) = true := by native_decide

-- ============================================================================
-- §5: Controller–Target Mismatch (Ch 6, §6.1)
-- ============================================================================

/-- Controller and target may operate with different number systems.
    The target system is typically a subset of the controller system. -/
structure ControllerTargetSystem where
  name : String
  controllerValues : List NumberValue
  targetValues : List NumberValue
  deriving BEq

/-- Whether controller and target systems differ in size. -/
def ControllerTargetSystem.hasMismatch (ct : ControllerTargetSystem) : Bool :=
  ct.controllerValues.length != ct.targetValues.length

/-- Bayso: 4 controller values (general, singular, paucal, plural),
    but only 3 target agreement forms. General and singular trigger the same
    agreement on the verb. -/
def baysoCT : ControllerTargetSystem :=
  { name := "Bayso"
    controllerValues := [.general, .singular, .paucal, .plural]
    targetValues := [.singular, .paucal, .plural] }

/-- Modern Hebrew: 3 controller values (sg, dual, pl), but only 2 target
    agreement values — dual and plural trigger the same verb agreement. -/
def hebrewCT : ControllerTargetSystem :=
  { name := "Modern Hebrew"
    controllerValues := [.singular, .dual, .plural]
    targetValues := [.singular, .plural] }

/-- English: 2 controller values, 2 target values (matched). -/
def englishCT : ControllerTargetSystem :=
  { name := "English"
    controllerValues := [.singular, .plural]
    targetValues := [.singular, .plural] }

theorem bayso_mismatch : baysoCT.hasMismatch = true := by native_decide
theorem hebrew_mismatch : hebrewCT.hasMismatch = true := by native_decide
theorem english_no_mismatch : englishCT.hasMismatch = false := by native_decide

-- ============================================================================
-- §6: Bridges to Existing Infrastructure
-- ============================================================================

/-- Bridge: AnimacyRank monotonicity constraint is consistent with the
    animacy hierarchy defined in `Core.Prominence`. The ranking used here
    agrees with the ranking there: speaker (8) > ... > nondiscrete (0). -/
theorem animacy_rank_ordering_consistent :
    AnimacyRank.speaker.toNat > AnimacyRank.human.toNat ∧
    AnimacyRank.human.toNat > AnimacyRank.higherAnimal.toNat ∧
    AnimacyRank.higherAnimal.toNat > AnimacyRank.discreteInanimate.toNat := by
  native_decide

/-- Bridge: English NumberSystem matches the PluralityProfile in
    `Plurals.Typology` — both record a 2-value obligatory system. -/
theorem english_matches_plurals_typology :
    englishNS.size = 2 ∧
    englishNS.hasGeneral = false ∧
    Phenomena.Plurals.Typology.english.occurrence =
      .allNounsAlwaysObligatory := by
  native_decide

/-- Bridge: Japanese general number in Corbett's analysis corresponds to
    the noNominalPlural/noPlural profile in `Plurals.Typology`. WALS and
    Corbett describe the same facts differently: WALS says "no nominal plural,"
    Corbett says "general number exists (form outside the system)." -/
theorem japanese_general_vs_wals :
    japaneseNS.hasGeneral = true ∧
    Phenomena.Plurals.Typology.japanese.coding = .noPlural := by
  native_decide

/-- Bridge: Bayso's general number explains its "no nominal plural"
    appearance — it's not that number is absent, but that the general form
    stands outside the number system. -/
theorem bayso_general_with_system :
    baysoNS.hasGeneral = true ∧
    baysoNS.size = 3 := by
  native_decide

-- ============================================================================
-- §7: Bridge to Cysouw NumberStage (Agreement.Typology)
-- ============================================================================

open Phenomena.Agreement.Typology (NumberStage)

/-- Map a Corbett NumberSystem to Cysouw's NumberStage hierarchy by
    counting the number of non-general values in the system.
    - 0–1 values → N1 (undifferentiated)
    - 2 values → N2 (basic sg/pl opposition)
    - 3 values (has dual or paucal) → N3
    - 4+ values → N4 -/
def NumberSystem.toNumberStage (ns : NumberSystem) : NumberStage :=
  match ns.size with
  | 0 | 1 => .N1
  | 2 => .N2
  | 3 => .N3
  | _ => .N4

theorem piraha_N1 : pirahaNS.toNumberStage = .N1 := by native_decide
theorem english_N2 : englishNS.toNumberStage = .N2 := by native_decide
theorem russian_N2 : russianNS.toNumberStage = .N2 := by native_decide
theorem japanese_N2 : japaneseNS.toNumberStage = .N2 := by native_decide
theorem upperSorbian_N3 : upperSorbianNS.toNumberStage = .N3 := by native_decide
theorem larike_N4 : larikeNS.toNumberStage = .N4 := by native_decide

/-- Corbett's implicational hierarchy (trial → dual → plural → singular) is
    consistent with Cysouw's N-stages: a system at stage Nₖ has exactly k
    number oppositions, matching `size` = k for k ≤ 4. -/
theorem numberStage_consistent_with_size :
    pirahaNS.size = 0 ∧ pirahaNS.toNumberStage = .N1 ∧
    englishNS.size = 2 ∧ englishNS.toNumberStage = .N2 ∧
    upperSorbianNS.size = 3 ∧ upperSorbianNS.toNumberStage = .N3 ∧
    larikeNS.size = 4 ∧ larikeNS.toNumberStage = .N4 := by
  native_decide

end Phenomena.Agreement.Studies.Corbett2000
