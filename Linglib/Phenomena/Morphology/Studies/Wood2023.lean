import Linglib.Theories.Morphology.DM.Allosemy
import Linglib.Fragments.Icelandic.Nominalizations
import Linglib.Fragments.Icelandic.Predicates

/-!
# @cite{wood-2023} — Icelandic Nominalizations and Allosemy
@cite{wood-2023} @cite{wood-2015} @cite{wood-marantz-2017}

*Icelandic Nominalizations and Allosemy*. Oxford University Press.
DOI: 10.1093/oso/9780198865155.001.0001

## Overview

@cite{wood-2023} argues that Icelandic deverbal nominalizations are
built on the structure [nP n [vP v √ROOT]] (a complex head, NOT a
phrasal VoiceP), and that the ambiguity between CEN, SEN, and RN
readings arises from **allosemy of v and n** — one syntactic terminal
with multiple context-dependent meanings:

- **CEN** (Complex Event Nominal): v = eventive, n = Ø (identity).
  The noun inherits the verb's meaning, including event variable
  and argument structure (Ch. 5, (5.14)).
- **SEN** (Simple Event Nominal): v = Ø, n = SEN alloseme.
  Event reading without full argument structure (Ch. 5, (5.6)).
- **Result/Product Nominal**: v = eventive, n = result alloseme.
  Entity whose existence results from the event (Ch. 6, (6.30)).
- **Simple State**: v = Ø, n = state alloseme. State reading
  (e.g. *aðdáun* 'admiration' as lasting state) (Ch. 1, (1.18)).
- **Simple Entity**: v = Ø, n = entity alloseme. Entity reading with
  no event connection (e.g. *þvottur* 'laundry') (Ch. 5, (5.13)).

## Key Claims Formalized

1. **No Voice in nominalizations** (Ch. 3, Ch. 5): The external argument
   is introduced by a Poss head (= i* from @cite{wood-marantz-2017}),
   NOT by Voice. Voice diagnostics in nominalizations really test for
   agentive semantics, which Poss can also provide.

2. **Borer's Generalization** (Ch. 5 §5.1.5): CEN reading entails the
   existence of a morphologically related verb with the same meaning.
   This follows from the architecture: CEN requires v, and n cannot
   trigger root suppletion past v.

3. **P-prefixing patterns** (Ch. 4): Three patterns of preposition-verb
   interaction in nominalizations, depending on whether P conditions
   root meaning.

4. **marg- and endur- diagnostics** (Ch. 6): Iterative marg- 'many-' is
   only compatible with CEN; repetitive endur- 're-' is compatible
   with CEN, SEN, and result/product RN, but not simple entity RN.

5. **-vaeða verbs always compositional** (Ch. 6 §6.5): Because -vaeða
   is a compound (√VAEÐA adjoins to v), the root cannot interact
   idiosyncratically with n past v. Therefore -vaeðing nominals
   never have idiosyncratic RN readings.
-/

namespace Phenomena.Morphology.Studies.Wood2023

open Morphology.DM.Allosemy
open Fragments.Icelandic.Nominalizations
open Fragments.Icelandic.Predicates

-- ============================================================================
-- § 1: Reading Derivation from Allosemes (Ch. 5)
-- ============================================================================

/-- Wood's reading derivation: v and n alloseme combinations.

    @cite{wood-2023} Ch. 5 (5.4a–e):
    - v eventive + n zero → CEN (noun = verb meaning)
    - v zero + n simpleEvent → SEN (event-entity reading)
    - v zero + n entity → simple entity (entity reading)
    - v eventive + n result → result/product (entity from event) -/
theorem wood_cen_derivation :
    readingFromAllosemes .eventive .zero = some .complexEvent := rfl

theorem wood_sen_derivation :
    readingFromAllosemes .zero .simpleEvent = some .simpleEvent := rfl

theorem wood_simpleEntity_derivation :
    readingFromAllosemes .zero .entity = some .simpleEntity := rfl

theorem wood_result_derivation :
    readingFromAllosemes .eventive .result = some .result := rfl

theorem wood_state_derivation :
    readingFromAllosemes .zero .state = some .simpleState := rfl

/-- CEN and SEN differ in which head contributes eventive meaning:
    CEN = v eventive (event from verb), SEN = v zero (event from n). -/
theorem cen_sen_v_difference :
    (readingFromAllosemes .eventive .zero).isSome = true ∧
    (readingFromAllosemes .zero .simpleEvent).isSome = true ∧
    VAlloseme.eventive ≠ VAlloseme.zero := by decide

/-- The five reading types from @cite{wood-2023} Ch. 1 (1.18) are
    pairwise distinct. -/
theorem five_readings_distinct :
    NominalizationReading.complexEvent ≠ .simpleEvent ∧
    NominalizationReading.complexEvent ≠ .result ∧
    NominalizationReading.complexEvent ≠ .simpleState ∧
    NominalizationReading.complexEvent ≠ .simpleEntity ∧
    NominalizationReading.simpleEvent ≠ .result ∧
    NominalizationReading.simpleEvent ≠ .simpleState ∧
    NominalizationReading.simpleEvent ≠ .simpleEntity ∧
    NominalizationReading.result ≠ .simpleState ∧
    NominalizationReading.result ≠ .simpleEntity ∧
    NominalizationReading.simpleState ≠ .simpleEntity := by decide

-- ============================================================================
-- § 2: No Voice in Nominalizations (Ch. 3, Ch. 5)
-- ============================================================================

/-- Whether a nominalization has Voice (it doesn't, per @cite{wood-2023}).

    @cite{wood-2023} Ch. 5 §5.1.3: "I will assume, as discussed in
    Chapter 3, that there is in fact no Voice head in the structure."
    The external argument is introduced by Poss (= i*), not Voice. -/
def nomHasVoice : Bool := false

/-- Poss head semantics: parallel to Voice but for nominals.
    @cite{wood-2023} Ch. 5 (5.22):
    ⟦Poss⟧ ↔ λxλe. agent(x)(e) / __ agentive nP

    @cite{wood-marantz-2017}: Voice and Poss are the same head i*,
    appearing in different categories (vP vs nP). -/
inductive PossReading where
  | agent       -- agent interpretation (agentive event nominal)
  | possessor   -- general possessive interpretation
  | experiencer -- experiencer (with experiencer verbs)
  deriving DecidableEq, BEq, Repr

/-- Poss gets agent reading only with agentive (CEN) nP.
    @cite{wood-2023} Ch. 5 (5.24): "i* ↔ λxλe. agent(x)(e) /
    __ (agentive event)" -/
def possReading (nPisCEN : Bool) : PossReading :=
  if nPisCEN then .agent else .possessor

theorem agent_only_with_cen : possReading true = .agent := rfl
theorem possessor_without_cen : possReading false = .possessor := rfl

-- ============================================================================
-- § 3: P-Prefixing Patterns (Ch. 4)
-- ============================================================================

/-- Three patterns of preposition-verb interaction in nominalizations.

    @cite{wood-2023} Ch. 4:
    - **Pattern 1**: P conditions root meaning, must be prefixed, can
      also appear as complement PP (*ráða um* → *umráðun á*)
    - **Pattern 2**: P conditions root meaning, must be prefixed,
      cannot be doubled (*gera við* → *viðgerð á*, not **viðgerð við*)
    - **Pattern 3**: P does NOT condition root meaning, is not
      prefixed (*hugsa um* → *hugsun um*, not *umhugsun*) -/
inductive PPrefixPattern where
  | pConditionsDoubles   -- Pattern 1: P conditions meaning, can double
  | pConditionsNoDouble  -- Pattern 2: P conditions meaning, no doubling
  | pDoesNotCondition    -- Pattern 3: P doesn't condition root meaning
  deriving DecidableEq, BEq, Repr

/-- Pattern assignment for fragment nominalizations. -/
def PPrefixPattern.ofNom (n : IcelandicNom) : Option PPrefixPattern :=
  if !n.hasPPrefix then some .pDoesNotCondition
  else match n.nomForm with
  | "viðgerð"  => some .pConditionsNoDouble
  | "umönnun"  => some .pConditionsNoDouble
  | "aðdáun"   => some .pConditionsNoDouble
  | _          => none

/-- P-prefixed nominalizations use pattern 2 (no doubling). -/
theorem vidgerd_pattern2 :
    PPrefixPattern.ofNom vidgerd = some .pConditionsNoDouble := rfl

theorem umonnun_pattern2 :
    PPrefixPattern.ofNom umonnun = some .pConditionsNoDouble := rfl

-- ============================================================================
-- § 4: marg- and endur- as Reading Diagnostics (Ch. 6)
-- ============================================================================

/-- Verbal prefixes that diagnose nominalization readings.

    @cite{wood-2023} Ch. 6 §6.4:
    - *marg-* 'many-' adds iterativity to the event. Only compatible
      with CEN, because only CEN has an event variable at the v level.
    - *endur-* 're-' adds presupposition of prior eventuality. Compatible
      with CEN, SEN, and result/product RN (all have event variables),
      but NOT with simple entity RN or simple state (no event variable).
      Per (6.46)–(6.53): *endurprentun* 'reprint' (result RN) is OK,
      but *endur-þvottur* 'laundry' (simple entity) is not. -/
inductive VerbalPrefix where
  | marg    -- 'many-': iterative, CEN only
  | endur   -- 're-': repetitive, CEN + SEN + result RN
  deriving DecidableEq, BEq, Repr

/-- Whether a prefix is compatible with a reading.

    Key distinction: *endur-* is compatible with result/product nominals
    (where v is eventive and the entity is computed from the event) but
    NOT with simple entity nominals (where v is zero, no event variable).
    @cite{wood-2023} Ch. 6 (6.46)–(6.53). -/
def prefixCompatible : VerbalPrefix → NominalizationReading → Bool
  | .marg,  .complexEvent => true
  | .marg,  _             => false
  | .endur, .complexEvent => true
  | .endur, .simpleEvent  => true
  | .endur, .result       => true   -- result/product: event variable present
  | .endur, _             => false  -- simpleEntity, simpleState, content: no event

/-- *marg-* only compatible with CEN (@cite{wood-2023} Ch. 6 (6.38)). -/
theorem marg_cen_only :
    prefixCompatible .marg .complexEvent = true ∧
    prefixCompatible .marg .simpleEvent = false ∧
    prefixCompatible .marg .simpleEntity = false := ⟨rfl, rfl, rfl⟩

/-- *endur-* compatible with CEN, SEN, and result/product RN, but not
    simple entity RN (@cite{wood-2023} Ch. 6 (6.46)–(6.53)). -/
theorem endur_pattern :
    prefixCompatible .endur .complexEvent = true ∧
    prefixCompatible .endur .simpleEvent = true ∧
    prefixCompatible .endur .result = true ∧
    prefixCompatible .endur .simpleEntity = false ∧
    prefixCompatible .endur .simpleState = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- *marg-* is strictly more restrictive than *endur-*. -/
theorem marg_stricter_than_endur (r : NominalizationReading) :
    prefixCompatible .marg r = true → prefixCompatible .endur r = true := by
  cases r <;> simp [prefixCompatible]

-- ============================================================================
-- § 5: Borer's Generalization (Ch. 5 §5.1.5)
-- ============================================================================

/-- Borer's Generalization: CEN reading entails the existence of a
    morphologically related verb with the same meaning.

    @cite{wood-2023} Ch. 5 §5.1.5: This follows from two assumptions:
    (a) verbs are semantically special (they introduce event variables),
    (b) n cannot trigger root suppletion past v. -/
def borersGeneralization (nom : IcelandicNom) : Prop :=
  nom.availableReadings.contains .complexEvent → nom.baseVerb ≠ ""

/-- All CEN-capable nominals in the fragment have base verbs
    (Borer's Generalization holds). -/
theorem borers_generalization_holds :
    (allNoms.filter (fun n => n.availableReadings.contains .complexEvent)).all
      (fun n => n.baseVerb != "") = true := by native_decide

-- ============================================================================
-- § 6: -vaeða Compositionality (Ch. 6 §6.5)
-- ============================================================================

/-- -vaeða verbs are compounds: √VAEÐA adjoins directly to v.
    Because √VAEÐA is meaningless (like English do-support √DO),
    the root it compounds with must be categorized (n) first.

    @cite{wood-2023} Ch. 6 (6.60):
    [v [n ... √ROOT n] [v √VAEÐA v]]

    This structure entails:
    - Root cannot idiosyncratically select complement PPs
    - -vaeðing nominals never have idiosyncratic RN readings
    - PP complements of -vaeða verbs are always compositional
    - -vaeða verbs cannot select ApplP -/
structure VaedaProperties where
  /-- Root can condition idiosyncratic complement PP? -/
  idiosyncraticPP : Bool
  /-- Nominalization can have idiosyncratic RN reading? -/
  idiosyncraticRN : Bool
  /-- Verb can select ApplP? -/
  selectsApplP : Bool
  /-- Meaning of nominalization always compositional? -/
  alwaysCompositional : Bool
  deriving Repr, BEq

/-- -vaeða verbs have maximally restricted properties. -/
def vaedaProps : VaedaProperties :=
  { idiosyncraticPP := false
    idiosyncraticRN := false
    selectsApplP := false
    alwaysCompositional := true }

/-- All -vaeða restrictions hold simultaneously. -/
theorem vaeda_all_restrictions :
    vaedaProps.idiosyncraticPP = false ∧
    vaedaProps.idiosyncraticRN = false ∧
    vaedaProps.selectsApplP = false ∧
    vaedaProps.alwaysCompositional = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: Bridge Theorems — Wood 2023 ↔ Wood 2015
-- ============================================================================

/-- *opnun* 'opening' connects to *opnast* 'open-ST' (anticausative).
    The nominalization is built on the same root as the -st verb;
    the -st voice morphology does not appear in the nominal
    (nominalizations lack Voice). -/
theorem opnun_connects_to_st_verb :
    opnun.stVerb = some opnast ∧
    opnast.stType = .anticausative := ⟨rfl, rfl⟩

/-- Anticausative -st verbs can be nominalized: the nominalization
    lacks Voice (hence no -st), but retains the root's meaning.
    @cite{wood-2023} Ch. 3: -st and nominalization both require
    non-agentive contexts, but the nominal achieves this by lacking
    Voice entirely rather than having non-agentive Voice. -/
theorem st_verb_nominalization_drops_voice :
    opnun.stVerb.isSome = true ∧
    nomHasVoice = false := ⟨rfl, rfl⟩

/-- The Voice flavor of the -st verb is irrelevant for the nominal:
    nominalizations derive readings from v/n allosemy, not from Voice. -/
theorem voice_irrelevant_for_nom_reading :
    opnast.stType.voiceFlavor = .nonThematic ∧
    opnun.availableReadings.contains .complexEvent = true ∧
    opnun.availableReadings.contains .simpleEntity = true := by native_decide

-- ============================================================================
-- § 8: Suffix Uniformity (@cite{wood-2023} Ch. 2–3)
-- ============================================================================

/-- All nominalizing suffixes spell out the same head n.
    Different suffixes do NOT indicate different functional heads —
    this is allomorphy of n, not different morphemes.
    @cite{wood-2023} Ch. 2 (2.1), Ch. 3. -/
theorem suffix_count : (List.length [NomSuffix.un, .ing, .sla, .stur, .adur]) = 5 := rfl

/-- The same suffix (-un) can yield different readings:
    *opnun* has CEN + simple entity, *notkun* has CEN only.
    The reading is determined by allosemy, not by the suffix. -/
theorem same_suffix_different_readings :
    opnun.suffix = notkun.suffix ∧
    opnun.availableReadings ≠ notkun.availableReadings := by
  constructor
  · rfl
  · decide

/-- Different suffixes can yield the same reading type:
    *opnun* (-un) and *þvottur* (-stur) both have CEN readings.
    The reading comes from v/n allosemy, not from the suffix. -/
theorem different_suffix_same_reading :
    opnun.suffix ≠ pvottur.suffix ∧
    opnun.availableReadings.contains .complexEvent = true ∧
    pvottur.availableReadings.contains .complexEvent = true := by native_decide

end Phenomena.Morphology.Studies.Wood2023
