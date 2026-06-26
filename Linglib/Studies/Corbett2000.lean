import Linglib.Fragments.English.Plurals
import Linglib.Fragments.Japanese.Plurals
import Linglib.Features.Number.Resolve
import Linglib.Syntax.Agreement.Basic
import Linglib.Semantics.Kinds.NominalMappingParameter

/-!
# Corbett (2000) — Number
[corbett-2000]

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

3. **Animacy Hierarchy constraints** (Ch 3, [smith-stark-1974]): the
   likelihood of number being distinguished decreases monotonically from
   speaker toward inanimate. Connects to `AnimacyRank` in `Features.Prominence`.

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
   [chierchia-1998]'s Nominal Mapping Parameter.
-/

namespace Corbett2000

-- The number value space, `Number.System`, `Number.Stage`, and the
-- implicational universals live in `Features/Number/Basic.lean`;
-- resolution in `Features/Number/Resolve.lean`. This file records the
-- book's language data and predictions over that substrate.

/-! ### Number Systems (Ch 2, §2.3) -/

-- Language number systems

/-- English: obligatory sg–pl, no general number. -/
def englishNS : Number.System :=
  { name := "English", values := [.singular, .plural] }

/-- Russian: obligatory sg–pl, no general number. -/
def russianNS : Number.System :=
  { name := "Russian", values := [.singular, .plural] }

/-- Upper Sorbian: sg–dual–pl, all obligatory. -/
def upperSorbianNS : Number.System :=
  { name := "Upper Sorbian", values := [.singular, .dual, .plural] }

/-- Bayso (Cushitic): sg–paucal–pl within the system; general form *lúban*
    'lion(s)' exists outside it. Four controller values total. -/
def baysoNS : Number.System :=
  { name := "Bayso"
    values := [.singular, .paucal, .plural]
    hasGeneral := true }

/-- Slovene: sg–dual–pl, but the dual is facultative (plural substitutes). -/
def sloveneNS : Number.System :=
  { name := "Slovene"
    values := [.singular, .dual, .plural]
    facultative := [.dual] }

/-- Larike (Central Moluccan): sg–dual–trial–pl, dual and trial both
    facultative (plural can substitute for either). -/
def larikeNS : Number.System :=
  { name := "Larike"
    values := [.singular, .dual, .trial, .plural]
    facultative := [.dual, .trial] }

/-- Lihir (Oceanic): sg–dual–trial–paucal–pl, five values — the richest
    well-documented system. -/
def lihirNS : Number.System :=
  { name := "Lihir"
    values := [.singular, .dual, .trial, .paucal, .plural] }

/-- Japanese: sg–pl within the system, but general number exists
    (bare *inu* 'dog(s)' is non-committal). -/
def japaneseNS : Number.System :=
  { name := "Japanese"
    values := [.singular, .plural]
    hasGeneral := true }

/-- Western Armenian (ISO `hyw`): singular–plural within the system, but
    general number exists for *singular indefinites* (bare *dəgha* "boy"
    can refer to one or more boys). Per [bale-khanjian-2014] eqs. 3
    and 9: ⟦dəgha⟧ contains both singular individuals and groups; only
    plural *dəgha-ner* is strictly ≥2. The general-number reading is
    *blocked* in definite contexts via syntactic-complexity competition
    with the same-complexity plural alternative — see
    `Studies/BaleKhanjian2014.lean`. Korean (Kim 2005)
    and Turkish (Bliss 2004) pattern alike per BK 2014 §2.3 and fn 14. -/
def westernArmenianNS : Number.System :=
  { name := "Western Armenian"
    values := [.singular, .plural]
    hasGeneral := true }

/-- Pirahã (Mura): no number category at all. -/
def pirahaNS : Number.System :=
  { name := "Pirahã", values := [] }

/-- Winnebago (Siouan): minimal–augmented, two values. {±minimal} only
    ([harbour-2014] Table 3). -/
def winnebagoNS : Number.System :=
  { name := "Winnebago", values := [.minimal, .augmented] }

/-- Rembarrnga (Australian): minimal–unit augmented–augmented, three values.
    {±minimal*} — feature recursion on [±minimal] without [±atomic]
    ([harbour-2014] Table 3). -/
def rembarrnganS : Number.System :=
  { name := "Rembarrnga"
    values := [.minimal, .unitAugmented, .augmented] }

/-- Mebengokre (Jê): minimal–paucal–plural, three values.
    {±additive, ±minimal} ([harbour-2014] Table 3). -/
def mebengokreNS : Number.System :=
  { name := "Mebengokre"
    values := [.minimal, .paucal, .plural] }

def allNumberSystems : List Number.System :=
  [englishNS, russianNS, upperSorbianNS, baysoNS, sloveneNS,
   larikeNS, lihirNS, japaneseNS, westernArmenianNS, pirahaNS,
   winnebagoNS, rembarrnganS, mebengokreNS]

-- Size checks
theorem english_two : englishNS.size = 2 := by decide
theorem upperSorbian_three : upperSorbianNS.size = 3 := by decide
theorem lihir_five : lihirNS.size = 5 := by decide
theorem piraha_zero : pirahaNS.size = 0 := by decide

-- General number
theorem bayso_has_general : baysoNS.hasGeneral = true := by decide
theorem japanese_has_general : japaneseNS.hasGeneral = true := by decide
theorem western_armenian_has_general :
    westernArmenianNS.hasGeneral = true := by decide
theorem english_no_general : englishNS.hasGeneral = false := by decide

-- Facultative number
theorem slovene_dual_facultative :
    .dual ∈ sloveneNS.facultative := by decide

theorem larike_both_facultative :
    .dual ∈ larikeNS.facultative ∧ .trial ∈ larikeNS.facultative := by decide

-- Implicational universals ([greenberg-1963], Corbett §2.3.1) — the
-- predicates live on `Number.System`; here they are checked on the data.

theorem all_trial_implies_dual :
    ∀ ns ∈ allNumberSystems, ns.TrialImpliesDual := by decide

theorem all_dual_implies_plural :
    ∀ ns ∈ allNumberSystems, ns.DualImpliesPlural := by decide

theorem all_plural_implies_singular_or_minimal :
    ∀ ns ∈ allNumberSystems, ns.PluralImpliesSingularOrMinimal := by decide

theorem all_augmented_implies_minimal :
    ∀ ns ∈ allNumberSystems, ns.AugmentedImpliesMinimal := by decide

theorem all_unitAug_implies_augmented :
    ∀ ns ∈ allNumberSystems, ns.UnitAugImpliesAugmented := by decide

/-- Every system the book records satisfies the *full* Table-1 universal
    set ([harbour-2014]) — all eleven implications, not only the five
    originally checked above. -/
theorem allNumberSystems_wellFormed :
    ∀ ns ∈ allNumberSystems, ns.WellFormed := by decide

/-! ### Animacy Hierarchy and Number Marking (Ch 3) -/

open Features.Prominence (AnimacyRank)

/-- Number marking status at a position on the Animacy Hierarchy. -/
inductive MarkingStatus where
  | obligatory  -- must mark number
  | optional    -- may mark number
  | absent      -- cannot mark number
  deriving DecidableEq, Repr

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
def AnimacyNumberProfile.RespectsConstraintI (p : AnimacyNumberProfile) : Prop :=
  (∃ r ∈ allRanks, (p.status r).toNat ≥ 2) → (p.status .speaker).toNat ≥ 2

/-- **Constraint III** (Corbett Ch 3): as we move rightward along the
    hierarchy, the likelihood of number being distinguished decreases
    monotonically — no intervening increase. -/
def AnimacyNumberProfile.RespectsConstraintIII (p : AnimacyNumberProfile) : Prop :=
  ∀ r1 ∈ allRanks, ∀ r2 ∈ allRanks,
    r1.toNat ≤ r2.toNat ∨ (p.status r1).toNat ≥ (p.status r2).toNat

instance (p : AnimacyNumberProfile) : Decidable p.RespectsConstraintI := by
  unfold AnimacyNumberProfile.RespectsConstraintI; infer_instance
instance (p : AnimacyNumberProfile) : Decidable p.RespectsConstraintIII := by
  unfold AnimacyNumberProfile.RespectsConstraintIII; infer_instance

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
    ∀ p ∈ allAnimacyProfiles, p.RespectsConstraintI := by decide

theorem constraint_iii_holds :
    ∀ p ∈ allAnimacyProfiles, p.RespectsConstraintIII := by decide

/-! ### The Agreement Hierarchy (Ch 6, §6.2) -/

open Agreement (AgreementTarget)

/-- Whether agreement is determined by morphological form (syntactic)
    or by referential meaning (semantic).

    Distinct from `Agreement.AgreementType` (grammatical vs. pronominal,
    [bickel-nichols-2001]), which is about whether the agreement
    marker has referential autonomy. This type is about what *controls*
    agreement — the formal features of the controller or its semantic
    content. -/
inductive AgreementControl where
  | syntactic  -- form-driven: *committee* is morphologically singular
  | semantic   -- meaning-driven: *committee* denotes a group of individuals
  deriving DecidableEq, Repr

/-- An agreement profile for a controller type records the targets where
    semantic (meaning-driven) agreement is available. -/
structure AgreementProfile where
  /-- Controller description -/
  controller : String
  /-- Targets where semantic (meaning-driven) agreement is possible. -/
  semanticTargets : List AgreementTarget

/-- The four positions of [corbett-1991]'s Agreement Hierarchy (`verb`
    is not one of them — see `Agreement.AgreementTarget`). -/
private def hierarchyPositions : List AgreementTarget :=
  [.attributive, .predicate, .relativePronoun, .personalPronoun]

/-- The Agreement Hierarchy monotonicity constraint: once semantic agreement
    becomes possible at a target, it remains possible at all targets further
    right (= lower `Agreement.AgreementTarget.rank`) on the hierarchy. -/
def AgreementProfile.RespectsHierarchy (p : AgreementProfile) : Prop :=
  ∀ t1 ∈ hierarchyPositions, ∀ t2 ∈ hierarchyPositions,
    t1.rank ≤ t2.rank ∨ t1 ∉ p.semanticTargets ∨ t2 ∈ p.semanticTargets

instance (p : AgreementProfile) : Decidable p.RespectsHierarchy := by
  unfold AgreementProfile.RespectsHierarchy; infer_instance

-- Language data

/-- British English *committee*: syntactic only in attributive position;
    semantic agreement possible in predicate, relative pronoun, and
    personal pronoun. -/
def britishCommittee : AgreementProfile :=
  -- *these committee (no); the committee have decided / who have... / they (yes)
  { controller := "committee (British English)"
    semanticTargets := [.predicate, .relativePronoun, .personalPronoun, .verb] }

/-- American English *committee*: semantic agreement rare in predicate,
    but available in relative and personal pronoun. -/
def americanCommittee : AgreementProfile :=
  -- ?the committee have decided (rare in AmE): no predicate/verb; pronouns yes
  { controller := "committee (American English)"
    semanticTargets := [.relativePronoun, .personalPronoun] }

/-- Serbo-Croatian *deca* 'children': morphologically feminine singular,
    semantically plural. Semantic agreement available everywhere. -/
def serboCroatDeca : AgreementProfile :=
  { controller := "deca 'children' (Serbo-Croatian)"
    semanticTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun, .verb] }

def allAgreementProfiles : List AgreementProfile :=
  [britishCommittee, americanCommittee, serboCroatDeca]

/-- The Agreement Hierarchy is respected by all profiled controllers. -/
theorem agreement_hierarchy_holds :
    ∀ p ∈ allAgreementProfiles, p.RespectsHierarchy := by decide

/-- Once semantic agreement reaches the personal pronoun (rightmost),
    it is necessarily available there for all our controllers. -/
theorem semantic_at_pronoun :
    ∀ p ∈ allAgreementProfiles, .personalPronoun ∈ p.semanticTargets := by decide

/-- No controller has semantic agreement only at the attributive position
    (the leftmost) without also having it further right — this would violate
    the monotonicity constraint. -/
theorem no_attributive_only_semantic :
    ∀ p ∈ allAgreementProfiles,
      .attributive ∈ p.semanticTargets → .personalPronoun ∈ p.semanticTargets := by
  decide

/-! ### Controller–Target Mismatch (Ch 6, §6.1) -/

/-- Controller and target may operate with different number systems.
    The target system is typically a subset of the controller system. -/
structure ControllerTargetSystem where
  name : String
  controllerValues : List Number
  targetValues : List Number
  /-- Number appearing when controller lacks specification (§6.1.2).
      Most languages default to singular; Tsez defaults to plural. -/
  defaultNumber : Number := .singular
  deriving DecidableEq

/-- Whether controller and target systems differ in size. -/
def ControllerTargetSystem.HasMismatch (ct : ControllerTargetSystem) : Prop :=
  ct.controllerValues.length ≠ ct.targetValues.length

instance (ct : ControllerTargetSystem) : Decidable ct.HasMismatch := by
  unfold ControllerTargetSystem.HasMismatch; infer_instance

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

theorem bayso_mismatch : baysoCT.HasMismatch := by decide
theorem hebrew_mismatch : hebrewCT.HasMismatch := by decide
theorem english_no_mismatch : ¬ englishCT.HasMismatch := by decide

/-! ### The Individuation Hierarchy (Ch 4) -/

/-- An individuation profile records which number values are available at each
    position on the animacy hierarchy. Languages may have *split number systems*
    where pronouns sustain a richer inventory than nouns. -/
structure IndividuationProfile where
  name : String
  /-- Number values available at each hierarchy position -/
  valuesAt : AnimacyRank → List Number
  /-- Minor number values: restricted to a closed class of nouns (e.g.,
      Hebrew dual for body-part nouns, Maltese dual). Constraints IV–VII
      govern the distribution of minor numbers. -/
  minorValues : List Number := []

/-- **Constraint II** (Corbett Ch 4): if trial exists at position X, then dual
    exists at X and at all positions higher on the animacy hierarchy. -/
def IndividuationProfile.RespectsConstraintII (p : IndividuationProfile) : Prop :=
  ∀ r ∈ allRanks, .trial ∈ p.valuesAt r →
    .dual ∈ p.valuesAt r ∧
    ∀ r' ∈ allRanks, r'.toNat ≤ r.toNat ∨ .dual ∈ p.valuesAt r'

/-- **Monotonicity**: number value inventories never grow as we move rightward
    (down) the hierarchy. If a value exists at position X, it exists at all
    higher positions. -/
def IndividuationProfile.RespectsMonotonicity (p : IndividuationProfile) : Prop :=
  ∀ r1 ∈ allRanks, ∀ r2 ∈ allRanks,
    r1.toNat ≤ r2.toNat ∨ ∀ v ∈ p.valuesAt r2, v ∈ p.valuesAt r1

instance (p : IndividuationProfile) : Decidable p.RespectsConstraintII := by
  unfold IndividuationProfile.RespectsConstraintII; infer_instance
instance (p : IndividuationProfile) : Decidable p.RespectsMonotonicity := by
  unfold IndividuationProfile.RespectsMonotonicity; infer_instance

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
    ∀ p ∈ allIndividuationProfiles, p.RespectsConstraintII := by decide

theorem individuation_monotonicity_holds :
    ∀ p ∈ allIndividuationProfiles, p.RespectsMonotonicity := by decide

/-- Upper Sorbian pronouns have dual but lower animacy positions do not —
    a genuine split number system. -/
theorem upperSorbian_split :
    .dual ∈ upperSorbianIndiv.valuesAt .speaker ∧
    .dual ∉ upperSorbianIndiv.valuesAt .discreteInanimate := by decide

/-! ### Resolution Rules for Conjoined Controllers (Ch 6, §6.3) -/

/-- When conjoined NPs disagree in number, the language must resolve which
    number value appears on the agreement target. -/
inductive ResolutionStrategy where
  /-- Semantic resolution: sum the referents. sg + sg → pl because the
      conjunction denotes a plurality. -/
  | semantic
  /-- Syntactic resolution: the nearest (closest) conjunct to the target
      determines agreement, regardless of the other conjunct's number. -/
  | closestConjunct
  deriving DecidableEq, Repr

/-- Semantic resolution in English ({sg, pl}): sg + sg → pl — the
    lattice-canonical dual coarsens to plural (`Number.System.resolve`,
    `Features/Number/Resolve.lean`). -/
theorem sg_sg_resolves_pl :
    englishNS.resolve .singular .singular = .plural := by decide

/-- In Upper Sorbian (which has dual), sg + sg resolves to dual: the
    lattice-canonical result survives uncoarsened ([corbett-2000] §6.3). -/
theorem sg_sg_resolves_du_with_dual :
    upperSorbianNS.resolve .singular .singular = .dual := by decide

/-- In languages without trial, sg + du resolves to pl. -/
theorem sg_du_resolves_pl_without_trial :
    englishNS.resolve .singular .dual = .plural := by decide

/-- In Larike (which has trial), sg + du keeps trial. -/
theorem sg_du_resolves_tri_with_trial :
    larikeNS.resolve .singular .dual = .trial := by decide

/-! ### Bridges to AnimacyRank, Fragment plurality profiles -/

/-- Bridge: AnimacyRank monotonicity constraint is consistent with the
    animacy hierarchy defined in `Features.Prominence`. The ranking used here
    agrees with the ranking there: speaker (8) > ... > nondiscrete (0). -/
theorem animacy_rank_ordering_consistent :
    AnimacyRank.speaker.toNat > AnimacyRank.human.toNat ∧
    AnimacyRank.human.toNat > AnimacyRank.higherAnimal.toNat ∧
    AnimacyRank.higherAnimal.toNat > AnimacyRank.discreteInanimate.toNat := by
  decide

/-- Bridge: English `Number.System` matches the English plurality profile in
    `English.Plurals` — both record a 2-value obligatory system. -/
theorem english_matches_plurals_typology :
    englishNS.size = 2 ∧
    englishNS.hasGeneral = false ∧
    English.pluralityProfile.occurrence =
      .allNounsAlwaysObligatory := by
  decide

/-- Bridge: Japanese general number in Corbett's analysis corresponds to the
    `noPlural` coding in `Japanese.Plurals`. WALS and Corbett
    describe the same facts differently: WALS says "no nominal plural,"
    Corbett says "general number exists (form outside the system)." -/
theorem japanese_general_vs_wals :
    japaneseNS.hasGeneral = true ∧
    Japanese.pluralityProfile.coding = .noPlural := by
  decide

/-- Bridge: Bayso's general number explains its "no nominal plural"
    appearance — it's not that number is absent, but that the general form
    stands outside the number system. -/
theorem bayso_general_with_system :
    baysoNS.hasGeneral = true ∧
    baysoNS.size = 3 := by
  decide

/-! ### Bridge to Cysouw `Number.Stage` -/

theorem piraha_N1 : pirahaNS.toStage = .N1 := by decide
theorem english_N2 : englishNS.toStage = .N2 := by decide
theorem russian_N2 : russianNS.toStage = .N2 := by decide
theorem japanese_N2 : japaneseNS.toStage = .N2 := by decide
theorem upperSorbian_N3 : upperSorbianNS.toStage = .N3 := by decide
theorem larike_N4 : larikeNS.toStage = .N4 := by decide

/-- Corbett's implicational hierarchy (trial → dual → plural → singular) is
    consistent with Cysouw's N-stages: a system at stage Nₖ has exactly k
    number oppositions, matching `size` = k for k ≤ 4. -/
theorem numberStage_consistent_with_size :
    pirahaNS.size = 0 ∧ pirahaNS.toStage = .N1 ∧
    englishNS.size = 2 ∧ englishNS.toStage = .N2 ∧
    upperSorbianNS.size = 3 ∧ upperSorbianNS.toStage = .N3 ∧
    larikeNS.size = 4 ∧ larikeNS.toStage = .N4 := by
  decide

/-! ### Bridge to Chierchia (1998) Nominal Mapping Parameter -/

open Semantics.Kinds.NMP (NominalMapping CanDenoteKind)

/-- Corbett's general number languages are those where bare nouns can denote
    kinds without a determiner — exactly Chierchia's [+arg] languages.

    If a language has general number (a form outside the number system, non-
    committal to cardinality), bare NPs can serve as arguments. This corresponds
    to `CanDenoteKind mapping (hasD := false)`, which holds for
    `argOnly` and `argAndPred` but not `predOnly`. -/
theorem general_number_iff_bare_kind :
    (baysoNS.hasGeneral = true ∧
     CanDenoteKind .argOnly False) ∧
    (japaneseNS.hasGeneral = true ∧
     CanDenoteKind .argOnly False) ∧
    (englishNS.hasGeneral = false ∧
     ¬ CanDenoteKind .predOnly False) :=
  ⟨⟨rfl, trivial⟩, ⟨rfl, trivial⟩, ⟨rfl, id⟩⟩

/-! ### Bridge to Link (1983) — Inclusive vs Exclusive Plural -/

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
  deriving DecidableEq, Repr

/-- Inclusive plural includes singletons; exclusive does not. -/
def PluralInterpretation.IncludesSingleton : PluralInterpretation → Prop
  | .inclusive => True
  | .exclusive => False

instance : DecidablePred PluralInterpretation.IncludesSingleton :=
  fun p => by cases p <;> unfold PluralInterpretation.IncludesSingleton <;> infer_instance

/-- The compositional (pre-pragmatic) interpretation is always inclusive. -/
theorem compositional_plural_is_inclusive :
    PluralInterpretation.inclusive.IncludesSingleton := trivial

/-! ### Minor Number Constraints IV–VII (Ch 4) -/

/-- **Constraint VII** ([corbett-2000] Ch 4): only dual and paucal can be
    minor numbers. Singular and plural cannot be minor — they are the core
    of any number system. -/
def IndividuationProfile.RespectsConstraintVII (p : IndividuationProfile) : Prop :=
  ∀ v ∈ p.minorValues, v = .dual ∨ v = .paucal

/-- **Constraint IV** ([corbett-2000] Ch 4): if a minor number exists
    at some animacy position, it must also exist at all higher positions.
    Minor numbers obey the same monotonicity as full number values. -/
def IndividuationProfile.RespectsConstraintIV (p : IndividuationProfile) : Prop :=
  ∀ v ∈ p.minorValues, ∀ r1 ∈ allRanks, ∀ r2 ∈ allRanks,
    r1.toNat ≤ r2.toNat ∨ v ∉ p.valuesAt r2 ∨ v ∈ p.valuesAt r1

instance (p : IndividuationProfile) : Decidable p.RespectsConstraintVII := by
  unfold IndividuationProfile.RespectsConstraintVII; infer_instance
instance (p : IndividuationProfile) : Decidable p.RespectsConstraintIV := by
  unfold IndividuationProfile.RespectsConstraintIV; infer_instance

/-- Modern Hebrew: minor dual restricted to body-part nouns and a few
    lexicalized time expressions. The dual is a closed class (Constraint V),
    found only among human/body-part nouns. -/
def hebrewIndiv : IndividuationProfile :=
  { name := "Modern Hebrew"
    valuesAt := λ
      | .speaker | .addressee | .thirdPerson | .kin | .human =>
          [.singular, .dual, .plural]
      | _ => [.singular, .plural]
    minorValues := [.dual] }

/-- Maltese: minor dual, also restricted to a small set of nouns (body
    parts and time expressions, e.g. *idejn* 'two hands'). -/
def malteseIndiv : IndividuationProfile :=
  { name := "Maltese"
    valuesAt := λ
      | .speaker | .addressee | .thirdPerson | .kin | .human =>
          [.singular, .dual, .plural]
      | _ => [.singular, .plural]
    minorValues := [.dual] }

def allIndividuationProfilesExtended : List IndividuationProfile :=
  [upperSorbianIndiv, lihirIndiv, englishIndiv, hebrewIndiv, malteseIndiv]

/-- Constraint VII holds for all profiles (only dual/paucal are minor). -/
theorem constraint_vii_holds :
    ∀ p ∈ allIndividuationProfilesExtended, p.RespectsConstraintVII := by decide

/-- Constraint IV holds for all profiles (minor number monotonicity). -/
theorem constraint_iv_holds :
    ∀ p ∈ allIndividuationProfilesExtended, p.RespectsConstraintIV := by decide

/-- Constraint II also holds for the extended profile set. -/
theorem constraint_ii_extended :
    ∀ p ∈ allIndividuationProfilesExtended, p.RespectsConstraintII := by decide

/-- Hebrew and Maltese duals are minor numbers. -/
theorem hebrew_minor_dual : hebrewIndiv.minorValues = [.dual] := rfl
theorem maltese_minor_dual : malteseIndiv.minorValues = [.dual] := rfl

/-- No language in our sample has minor singular or plural. -/
theorem no_minor_singular_or_plural :
    ∀ p ∈ allIndividuationProfilesExtended,
      .singular ∉ p.minorValues ∧ .plural ∉ p.minorValues := by decide

/-! ### Default Number (Ch 6, §6.1.2) -/

/-- Tsez (Northeast Caucasian): when the controller lacks a number
    specification, the default agreement target form is plural —
    opposite to most languages. -/
def tsezCT : ControllerTargetSystem :=
  { name := "Tsez"
    controllerValues := [.singular, .plural]
    targetValues := [.singular, .plural]
    defaultNumber := .plural }

/-- English defaults to singular. -/
theorem english_default_singular : englishCT.defaultNumber = .singular := rfl

/-- Tsez defaults to plural. -/
theorem tsez_default_plural : tsezCT.defaultNumber = .plural := rfl

/-- Default number is always in the target system. -/
theorem default_in_target_system :
    ∀ ct ∈ [englishCT, baysoCT, hebrewCT, tsezCT],
      ct.defaultNumber ∈ ct.targetValues := by decide

/-! ### Associative Plurals (Ch 5) -/

/-- Associative plural profile: "X and associates" constructions are
    constrained by animacy — they typically require human or animate
    controllers ([corbett-2000] Ch 5). -/
structure AssociativePluralProfile where
  name : String
  /-- Minimum animacy rank for associative plural use -/
  minAnimacy : AnimacyRank
  /-- Whether the associative marker is identical to the additive plural -/
  sameAsAdditive : Bool
  deriving DecidableEq

/-- Hungarian: associative -ék, dedicated form (not the additive plural),
    restricted to human referents. -/
def hungarianAssoc : AssociativePluralProfile :=
  { name := "Hungarian", minAnimacy := .human, sameAsAdditive := false }

/-- Japanese: associative -tachi, distinct from additive plural (none on
    common nouns), human-restricted. -/
def japaneseAssoc : AssociativePluralProfile :=
  { name := "Japanese", minAnimacy := .human, sameAsAdditive := false }

/-- Turkish: associative -ler (same as additive plural), available for
    human referents. -/
def turkishAssoc : AssociativePluralProfile :=
  { name := "Turkish", minAnimacy := .human, sameAsAdditive := true }

def allAssociativeProfiles : List AssociativePluralProfile :=
  [hungarianAssoc, japaneseAssoc, turkishAssoc]

/-- Associative plurals in our sample all require at least human animacy. -/
theorem associative_requires_human :
    ∀ p ∈ allAssociativeProfiles,
      p.minAnimacy.toNat ≥ AnimacyRank.human.toNat := by decide

/-- Bridge: Japanese has both associative plural (here) and general number
    (from the Number.System), reflecting the interaction between the two. -/
theorem japanese_associative_with_general :
    japaneseNS.hasGeneral = true ∧
    japaneseAssoc.sameAsAdditive = false := by
  decide

/-! ### Count/Mass × Number Interaction (Ch 7) -/

/-- Count/mass interaction with number systems ([corbett-2000] Ch 7).

    Mass nouns resist plural morphology; count nouns take it freely.
    The count/mass distinction interacts with the animacy hierarchy:
    higher animacy positions are more likely to be count (and thus
    support richer number distinctions). -/
structure CountMassNumberInteraction where
  name : String
  /-- Does the language require count nouns to inflect for number? -/
  countNounsInflect : Bool
  /-- Does the language allow mass nouns to inflect for number? -/
  massNounsInflect : Bool
  /-- Number system for count nouns -/
  countSystem : Number.System
  /-- Number system for mass nouns (often smaller or empty) -/
  massSystem : Number.System
  deriving DecidableEq

/-- English: count nouns inflect obligatorily, mass nouns do not
    (*furnitures, *informations). -/
def englishCountMass : CountMassNumberInteraction :=
  { name := "English"
    countNounsInflect := true
    massNounsInflect := false
    countSystem := englishNS
    massSystem := { name := "English (mass)", values := [.singular] } }

/-- Japanese: neither count nor mass nouns inflect for number (general
    number covers both). -/
def japaneseCountMass : CountMassNumberInteraction :=
  { name := "Japanese"
    countNounsInflect := false
    massNounsInflect := false
    countSystem := japaneseNS
    massSystem := japaneseNS }

def allCountMassInteractions : List CountMassNumberInteraction :=
  [englishCountMass, japaneseCountMass]

/-- Mass noun systems are never richer than count noun systems. -/
theorem mass_never_richer_than_count :
    ∀ cm ∈ allCountMassInteractions,
      cm.massSystem.size ≤ cm.countSystem.size := by decide

/-- In English, count nouns inflect but mass nouns do not. -/
theorem english_count_mass_asymmetry :
    englishCountMass.countNounsInflect = true ∧
    englishCountMass.massNounsInflect = false := by
  decide

/-- Bridge to Chierchia (1998): Japanese general number languages treat
    count and mass nouns identically — both get the same number system. -/
theorem japanese_count_mass_uniform :
    japaneseCountMass.countSystem = japaneseCountMass.massSystem := by
  decide

/-! ### Predicate Hierarchy Bridge -/

open Agreement (PredicateTarget)

/-- A predicate-hierarchy profile records the sub-positions (verb, participle,
    adjective, noun) where semantic agreement is possible for a controller —
    e.g. Russian honorific *vy*. -/
structure PredicateHierarchyProfile where
  name : String
  /-- Predicate sub-positions where semantic agreement is possible. -/
  semanticTargets : List PredicateTarget

/-- The four sub-positions of the Predicate Hierarchy. -/
private def predicatePositions : List PredicateTarget :=
  [.verb, .participle, .adjective, .noun]

/-- The Predicate Hierarchy ([comrie-1975]) monotonicity constraint:
    once semantic agreement becomes possible at a sub-position, it remains
    possible at all higher positions. -/
def PredicateHierarchyProfile.RespectsHierarchy (p : PredicateHierarchyProfile) : Prop :=
  ∀ t1 ∈ predicatePositions, ∀ t2 ∈ predicatePositions,
    t1.rank ≥ t2.rank ∨ t1 ∉ p.semanticTargets ∨ t2 ∈ p.semanticTargets

instance (p : PredicateHierarchyProfile) : Decidable p.RespectsHierarchy := by
  unfold PredicateHierarchyProfile.RespectsHierarchy; infer_instance

/-- Russian honorific *vy* 'you' (polite singular): grammatically plural but
    referring to one person, so semantic agreement = singular. Per
    [corbett-2000]'s Predicate Hierarchy data, the finite verb and
    participle keep syntactic (plural) agreement, while the long-form
    predicate adjective and the predicate noun take singular (semantic)
    agreement. -/
def russianHonorificVy : PredicateHierarchyProfile :=
  { name := "Russian honorific vy (Predicate Hierarchy)"
    semanticTargets := [.adjective, .noun] }

/-- The Russian honorific-*vy* profile respects Predicate Hierarchy
    monotonicity. -/
theorem russian_predicate_hierarchy_holds :
    russianHonorificVy.RespectsHierarchy := by decide

end Corbett2000
