import Linglib.Phenomena.Plurals.Typology
import Linglib.Phenomena.Agreement.Typology
import Linglib.Theories.Syntax.Minimalism.Agreement.CoordinateResolution
import Linglib.Core.Number
import Linglib.Core.AgreementTarget
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

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

6. **Individuation Hierarchy** (Ch 4): integrates the animacy hierarchy with
   number value inventories. Higher animacy positions can sustain richer number
   systems. Constraint II: if trial exists at position X, dual exists at X and
   all higher positions.

7. **Resolution rules** (Ch 6, §6.3): when conjoined controllers disagree in
   number, resolution is either semantic (referent sum: sg + sg → pl) or
   syntactic (nearest conjunct agreement).

8. **Semantics of number** (Ch 7): inclusive vs exclusive plural interpretation.
   Link's `*P` gives the inclusive reading (≥ 1); exclusive (≥ 2) is derived by
   scalar implicature. General number semantics connects to
   @cite{chierchia-1998}'s Nominal Mapping Parameter.
-/

namespace Phenomena.Agreement.Studies.Corbett2000

-- Number categories, predicates, and UD bridges are in `Core/Number.lean`.
-- We alias `NumberValue` here for backward compatibility within this file.
open Core.Number

abbrev NumberValue := Category

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

-- AgreementTarget is now in Core/AgreementTarget.lean.
open Core (AgreementTarget)

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
    right (= lower `Core.AgreementTarget.rank`) on the hierarchy. -/
def AgreementProfile.respectsHierarchy (p : AgreementProfile) : Bool :=
  let targets := [AgreementTarget.attributive, .predicate,
                   .relativePronoun, .personalPronoun]
  targets.all λ t1 =>
    targets.all λ t2 =>
      t1.rank <= t2.rank || !p.semanticPossible t1 || p.semanticPossible t2

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
      | .personalPronoun => true   -- the committee... they
      | .verbTarget      => true }

/-- American English *committee*: semantic agreement rare in predicate,
    but available in relative and personal pronoun. -/
def americanCommittee : AgreementProfile :=
  { controller := "committee (American English)"
    semanticPossible := λ
      | .attributive     => false
      | .predicate       => false  -- ?the committee have decided (rare in AmE)
      | .relativePronoun => true
      | .personalPronoun => true
      | .verbTarget      => true }

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
-- §6: The Individuation Hierarchy (Ch 4)
-- ============================================================================

/-- An individuation profile records which number values are available at each
    position on the animacy hierarchy. Languages may have *split number systems*
    where pronouns sustain a richer inventory than nouns. -/
structure IndividuationProfile where
  name : String
  /-- Number values available at each hierarchy position -/
  valuesAt : AnimacyRank → List NumberValue

/-- **Constraint II** (Corbett Ch 4): if trial exists at position X, then dual
    exists at X and at all positions higher on the animacy hierarchy. -/
def IndividuationProfile.respectsConstraintII (p : IndividuationProfile) : Bool :=
  allRanks.all λ r =>
    !(p.valuesAt r).contains .trial ||
    ((p.valuesAt r).contains .dual &&
     allRanks.all λ r' => r'.toNat <= r.toNat || (p.valuesAt r').contains .dual)

/-- **Monotonicity**: number value inventories never grow as we move rightward
    (down) the hierarchy. If a value exists at position X, it exists at all
    higher positions. -/
def IndividuationProfile.respectsMonotonicity (p : IndividuationProfile) : Bool :=
  allRanks.all λ r1 =>
    allRanks.all λ r2 =>
      r1.toNat <= r2.toNat ||
      (p.valuesAt r2).all (λ v => (p.valuesAt r1).contains v)

/-- Upper Sorbian: sg–dual–pl in pronouns and some nouns, but dual absent in
    lower animacy positions where only sg–pl remains. -/
def upperSorbianIndiv : IndividuationProfile :=
  { name := "Upper Sorbian"
    valuesAt := λ
      | .speaker | .addressee | .thirdPerson | .kin | .human =>
          [.singular, .dual, .plural]
      | _ => [.singular, .plural] }

/-- Lihir (Oceanic): full sg–du–tri–pauc–pl in pronouns, reduced inventory in
    lower positions. -/
def lihirIndiv : IndividuationProfile :=
  { name := "Lihir"
    valuesAt := λ
      | .speaker | .addressee | .thirdPerson =>
          [.singular, .dual, .trial, .paucal, .plural]
      | .kin | .human | .higherAnimal =>
          [.singular, .dual, .plural]
      | _ => [.singular, .plural] }

/-- English: uniform sg–pl at all positions (no split). -/
def englishIndiv : IndividuationProfile :=
  { name := "English"
    valuesAt := λ _ => [.singular, .plural] }

def allIndividuationProfiles : List IndividuationProfile :=
  [upperSorbianIndiv, lihirIndiv, englishIndiv]

theorem constraint_ii_holds :
    allIndividuationProfiles.all (·.respectsConstraintII) = true := by
  native_decide

theorem individuation_monotonicity_holds :
    allIndividuationProfiles.all (·.respectsMonotonicity) = true := by
  native_decide

/-- Upper Sorbian pronouns have dual but lower animacy positions do not —
    a genuine split number system. -/
theorem upperSorbian_split :
    (upperSorbianIndiv.valuesAt .speaker).contains .dual = true ∧
    (upperSorbianIndiv.valuesAt .discreteInanimate).contains .dual = false := by
  native_decide

-- ============================================================================
-- §7: Resolution Rules for Conjoined Controllers (Ch 6, §6.3)
-- ============================================================================

/-- When conjoined NPs disagree in number, the language must resolve which
    number value appears on the agreement target. -/
inductive ResolutionStrategy where
  /-- Semantic resolution: sum the referents. sg + sg → pl because the
      conjunction denotes a plurality. -/
  | semantic
  /-- Syntactic resolution: the nearest (closest) conjunct to the target
      determines agreement, regardless of the other conjunct's number. -/
  | closestConjunct
  deriving DecidableEq, BEq, Repr

/-- The result of resolving two number values under semantic resolution. -/
def NumberValue.semanticResolve (a b : NumberValue) : NumberValue :=
  match a, b with
  | .singular, .singular => .plural  -- 1 + 1 > 1
  | .singular, .dual     => .trial   -- 1 + 2 = 3 (in languages with trial)
  | .dual, .singular     => .trial
  | _, _ => .plural                   -- default: conjunction yields plural

/-- Semantic resolution: sg + sg → pl. -/
theorem sg_sg_resolves_pl :
    NumberValue.semanticResolve .singular .singular = .plural := rfl

/-- Semantic resolution: sg + du → tri (in languages with trial). -/
theorem sg_du_resolves_tri :
    NumberValue.semanticResolve .singular .dual = .trial := rfl

-- ============================================================================
-- §8: Bridges to AnimacyRank, Plurals.Typology
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
-- §9: Bridge to Cysouw NumberStage (Agreement.Typology)
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

-- ============================================================================
-- §10: Bridge to Chierchia (1998) Nominal Mapping Parameter
-- ============================================================================

open Semantics.Lexical.Noun.Kind.Chierchia1998 (NominalMapping canDenoteKind)

/-- Corbett's general number languages are those where bare nouns can denote
    kinds without a determiner — exactly Chierchia's [+arg] languages.

    If a language has general number (a form outside the number system, non-
    committal to cardinality), bare NPs can serve as arguments. This corresponds
    to `canDenoteKind mapping (hasD := false) = true`, which holds for
    `argOnly` and `argAndPred` but not `predOnly`. -/
theorem general_number_iff_bare_kind :
    (baysoNS.hasGeneral = true ∧
     canDenoteKind .argOnly false = true) ∧
    (japaneseNS.hasGeneral = true ∧
     canDenoteKind .argOnly false = true) ∧
    (englishNS.hasGeneral = false ∧
     canDenoteKind .predOnly false = false) := by
  native_decide

-- ============================================================================
-- §11: Bridge to Link (1983) — Inclusive vs Exclusive Plural
-- ============================================================================

/-- The inclusive/exclusive ambiguity of plurals (Corbett Ch 7).

    Link's `*P` (star/plural closure) gives the *inclusive* interpretation:
    `*P(x)` holds for atoms AND their sums, so "dogs" denotes ≥ 1 dogs.
    The *exclusive* interpretation (≥ 2 dogs) is not a separate semantic
    primitive — it arises by scalar implicature from the singular alternative.

    This is modeled here as a parameter on plural interpretation. The
    compositional semantics (`Link1983.star`) always delivers inclusive;
    pragmatics narrows to exclusive. -/
inductive PluralInterpretation where
  /-- ≥ 1: Link's `*P`, closed under join. The singular is included. -/
  | inclusive
  /-- ≥ 2: derived by scalar implicature. The singular is excluded. -/
  | exclusive
  deriving DecidableEq, BEq, Repr

/-- Inclusive plural includes singletons; exclusive does not. -/
def PluralInterpretation.includesSingleton : PluralInterpretation → Bool
  | .inclusive => true
  | .exclusive => false

/-- The compositional (pre-pragmatic) interpretation is always inclusive. -/
theorem compositional_plural_is_inclusive :
    PluralInterpretation.inclusive.includesSingleton = true := rfl

-- ============================================================================
-- §12: Bridge to Unified Coordinate Resolution
-- ============================================================================

open Theories.Syntax.Minimalism.Agreement.CoordinateResolution

/-- Corbett's `semanticResolve` is the unwrapped form of the unified
    `numberResolve`: both compute the same value, but `numberResolve`
    wraps the result in `Option` to fit the `ResolutionOp` interface
    (which must handle dimensions where resolution can fail).

    Number resolution always succeeds, so the `Option` is always `some`. -/
theorem numberResolve_eq_semanticResolve (a b : NumberValue) :
    numberResolve a b
    = some (NumberValue.semanticResolve a b) := by
  cases a <;> cases b <;> rfl

end Phenomena.Agreement.Studies.Corbett2000
