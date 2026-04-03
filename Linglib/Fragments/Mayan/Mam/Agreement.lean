import Linglib.Core.Case
import Linglib.Core.Prominence
import Linglib.Fragments.Mayan.Params

/-!
# Mam Agreement Fragment @cite{scott-2023}
@cite{deal-2024} @cite{woolford-1997} @cite{blake-1994}

Agreement morphology and pronoun realization data for San Juan Atitán (SJA)
Mam, a Mayan language with morphologically tripartite agreement alignment: S, A, and O each trigger distinct marking patterns
on the verb.

## The System

Mam has two agreement paradigms on the verb:
- **Set A** (ERG): prefixes on Voice cross-referencing the transitive agent
- **Set B** (ABS): preverbal markers on Infl cross-referencing the absolutive
  argument (intransitive S). In transitives, Infl's φ-probe is blocked by
  transitive VoiceP and default Set B (∅/tz'=)
  appears instead.

In the default construction, transitive *objects* are not cross-referenced
by either set — they co-occur with default Set B (tz'=) and require
full overt pronouns. However, some speakers accept agreeing Set B
for objects as a more formal variant (@cite{scott-2023}, ch. 3, ex. 156).

## Case Licensing

Case is NOT assigned via dependent case. Instead:
- **ERG**: inherent case from Voice
- **ACC**: structural case from Voice (object licensing; low-abs syntax)
- **ABS**: structural case from Infl (high-abs morphology; for intransitive S)

This gives a tripartite underlying Case system (ERG, ACC, ABS) despite
Mam having no independent case morphology on DPs — case is visible only
through agreement patterns.

## Argument Positions

| Position | Case | Agreement | Pronoun |
|----------|------|-----------|---------|
| A (transitive agent) | ERG (from Voice) | Set A | reduced/null |
| S (intransitive subj) | ABS (from Infl) | Set B | reduced/null |
| P (transitive patient) | ACC (from Voice) | default Set B | **overt** |

-/

namespace Fragments.Mayan.Mam

-- ============================================================================
-- § 1: Agreement Marker Paradigms (theory-neutral)
-- ============================================================================

/-- Set A (ERG) markers: prefixes/proclitics on the verb that
    cross-reference the transitive agent (@cite{scott-2023}, Table 2.8). -/
def setAMarkers : List (Core.Prominence.PersonLevel × Bool × String) :=
  [ (.first,  true,  "n-/w-")
  , (.second, true,  "t-")
  , (.third,  true,  "t-")
  , (.first,  false, "q-")
  , (.second, false, "ky-")
  , (.third,  false, "ky-") ]

/-- Set B (ABS) markers: preverbal markers on Infl that cross-reference
    the absolutive argument (@cite{scott-2023}, Table 3.5).
    The 2/3SG form tz'= is the **default** — it appears both for real
    agreement with a 2/3SG intransitive S and for default Set B in
    transitives when Infl's probe is blocked by VoiceP.
    1SG = chin, 2SG = tz'=, 3SG = tz'=, 1PL = qo, 2PL = chi, 3PL = chi. -/
def setBMarkers : List (Core.Prominence.PersonLevel × Bool × String) :=
  [ (.first,  true,  "chin")
  , (.second, true,  "tz'=")
  , (.third,  true,  "tz'=")
  , (.first,  false, "qo")
  , (.second, false, "chi")
  , (.third,  false, "chi") ]

/-- The default (Elsewhere) Set B marker. Surfaces in transitives when
    Infl's probe is blocked, and also for 2/3SG intransitive S. -/
def defaultSetB : String := "tz'="

/-- Look up a marker by person and number (true = singular). -/
def lookupMarker (markers : List (Core.Prominence.PersonLevel × Bool × String))
    (person : Core.Prominence.PersonLevel) (sg : Bool) : Option String :=
  markers.find? (λ ⟨p, n, _⟩ => p == person && n == sg) |>.map (·.2.2)

-- ============================================================================
-- § 2: Argument Positions and Agreement Status
-- ============================================================================

/-- Argument positions in a Mam clause (@cite{scott-2023}, ch. 3). -/
inductive MamArgPosition where
  | agent    -- A: transitive agent (external argument, Spec,VoiceP)
  | patient  -- P: transitive patient (internal argument, complement of V)
  | intranS  -- S: intransitive subject (sole argument, moves to Spec,TP)
  deriving DecidableEq, Repr

/-- The case each argument position receives.
    A gets ERG (inherent, from Voice), P gets ACC (structural, from Voice),
    S gets ABS (structural, from Infl). Three distinct underlying cases. -/
def MamArgPosition.case : MamArgPosition → Core.Case
  | .agent   => .erg
  | .patient => .acc
  | .intranS => .abs

/-- Is this argument position φ-Agreed-with by some probe?

    Agent: Voice probes for φ, finds agent in Spec,VoiceP → Set A
    Intransitive S: Infl probes for φ, finds S → Set B
    Patient: Infl's φ-probe has a disjunctive satisfaction condition
    [SAT: φ or Voice_TR]. In transitives, the
    probe encounters transitive Voice and stops — no φ-features are
    copied, and default Set B (the Elsewhere form) surfaces. -/
def MamArgPosition.isPhiAgreed : MamArgPosition → Bool
  | .agent   => true   -- φ-Agreed by Voice → Set A
  | .patient => false  -- NOT φ-Agreed: Infl probe blocked by Voice_TR
  | .intranS => true   -- φ-Agreed by Infl → Set B

-- ============================================================================
-- § 3: Pronoun Realization
-- ============================================================================

/-- Can a pronoun in this argument position undergo reduction?

    Scott's analysis (ch. 4, §4.4.3): first person pronouns in
    agreed-with positions are reduced via an impoverishment rule that
    deletes [±singular] in the context of [+author]^F (where F marks
    that the feature has been agreed with). This bleeds insertion of
    the pronominal base morphemes *qin* ([+author,+singular]) and *qo*
    ([+author,-singular]), leaving only the disagreement enclitic =i.

    Non-first person pronouns are NOT reduced — their subj/poss forms
    are identical to their independent forms (Table 4.25, p. 200).
    Whether actual reduction occurs depends on person (see
    `derivePronounForm`), but only agreed-with positions are eligible. -/
def MamArgPosition.canBeReduced (pos : MamArgPosition) : Bool :=
  pos.isPhiAgreed

/-- The three argument positions. -/
def mamArgPositions : List MamArgPosition :=
  [.agent, .patient, .intranS]

-- ============================================================================
-- § 4: Per-Position Verification
-- ============================================================================

/-- Agent gets ERG (inherent, from Voice). -/
theorem agent_case : MamArgPosition.agent.case = .erg := rfl

/-- Patient gets ACC (structural, from Voice). -/
theorem patient_case : MamArgPosition.patient.case = .acc := rfl

/-- Intransitive S gets ABS (structural, from Infl). -/
theorem intranS_case : MamArgPosition.intranS.case = .abs := rfl

/-- Three distinct underlying cases — morphologically tripartite. -/
theorem tripartite :
    MamArgPosition.agent.case ≠ MamArgPosition.patient.case ∧
    MamArgPosition.agent.case ≠ MamArgPosition.intranS.case ∧
    MamArgPosition.patient.case ≠ MamArgPosition.intranS.case := by
  exact ⟨by decide, by decide, by decide⟩

/-- Reduction eligibility correlates with φ-agreement: an argument
    position is eligible for pronoun reduction iff it triggers agreement
    on the verb. (Actual reduction further requires [+author]; see
    `derivePronounForm`.) -/
theorem reduction_eligible_iff_phi_agreed :
    mamArgPositions.all (λ pos => pos.canBeReduced == pos.isPhiAgreed) = true := by
  native_decide

-- ============================================================================
-- § 5: Case Inventory Validation (@cite{blake-1994})
-- ============================================================================

/-- Mam case inventory, derived from argument position case values. -/
def caseInventory : List Core.Case := [.erg, .acc, .abs]

/-- The inventory covers all argument positions. -/
theorem inventory_covers_positions :
    mamArgPositions.all (λ p => caseInventory.any (· == p.case)) = true := by
  native_decide

/-- Mam's {ERG, ACC, ABS} inventory is valid per Blake's case hierarchy
    (all are core cases at rank 6, trivially no gaps). -/
theorem inventory_valid : Core.validInventory caseInventory = true := by native_decide

-- ============================================================================
-- § 6: Pronoun Internal Structure (@cite{scott-2023}, ch. 4)
-- ============================================================================

/-- Person features relevant for pronoun reduction.

    Scott decomposes person into binary features following
    @cite{harbour-2016} (Table 4.3-4.4):
    - [±author]: distinguishes 1st from non-1st
    - [±participant]: distinguishes local (1st/2nd) from 3rd
    - [±singular]: number

    Agreement (Set A and Set B) copies only [±author] and [±singular]
    (Tables 4.7-4.8). It does NOT copy [±participant].

    The =i enclitic is the **disagreement enclitic** — it realizes
    *disagreeing* values of [±author] and [±participant] (ex. 59,
    adapting @cite{noyer-1992} / @cite{harbour-2016}):
    - 1SG/1PL.EXCL: [+author, -participant] → disagree → =i
    - 2SG/2PL: [-author, +participant] → disagree → =i
    - 1PL.INCL: [+author, +participant] → agree → no =i
    - 3SG/3PL: [-author, -participant] → agree → no =i -/
inductive PersonFeature where
  | person      -- person category (1st/2nd/3rd)
  | number      -- number category (sg/pl)
  | participant -- [±participant]: local (1st/2nd) vs non-local (3rd)
  deriving DecidableEq, Repr

/-- The pronominal base morpheme's features. -/
def baseFeatures : List PersonFeature := [.person, .number]

/-- The =i enclitic's feature: [participant]. -/
def encliticFeature : PersonFeature := .participant

/-- Features that agreement morphology copies (person and number only). -/
def agreedFeatures : List PersonFeature := [.person, .number]

/-- A feature is redundantly expressed by agreement iff agreement copies it. -/
def isRedundant (f : PersonFeature) : Bool :=
  agreedFeatures.any (· == f)

/-- A morpheme is deleted when ALL its features are redundantly expressed
    by agreement. -/
def allRedundant (feats : List PersonFeature) : Bool :=
  feats.all isRedundant

/-- The pronominal base is deleted: [person, number] are both copied by
    agreement, making the base fully redundant. -/
theorem base_is_redundant : allRedundant baseFeatures = true := by native_decide

/-- The =i enclitic survives: [participant] is NOT copied by agreement. -/
theorem enclitic_survives : isRedundant encliticFeature = false := by native_decide

/-- Pronoun realization after impoverishment (@cite{scott-2023}, §4.4.3).

    - `reduced`: 1st person agreed-with — impoverishment deletes
      [±singular] in the context of [+author]^F, bleeding insertion of
      pronominal base morphemes *qin*/*qo*. Only =i remains.
    - `full`: unreduced — the full independent pronoun form. This
      covers 2nd/3rd person subj/poss (which ARE identical to their
      independent forms, Table 4.25), as well as all object pronouns
      (which are not agreed-with and thus not eligible for reduction). -/
inductive PronounForm where
  | reduced -- 1st person agreed-with: base deleted, only =i remains
  | full    -- full independent pronoun (all other cases)
  deriving DecidableEq, Repr

/-- Is this person 1st (= [+author])? Only [+author] persons are
    eligible for the impoverishment rule (84) that deletes [±singular]
    and bleeds base morpheme insertion. -/
def isFirstPerson : Core.Prominence.PersonLevel → Bool
  | .first => true
  | _      => false

/-- Derive pronoun form from agreement status and person.

    The impoverishment rule (ex. 84/94) targets [+author] features
    that bear the F diacritic (indicating agreement has occurred):
    `[+/−singular] → ∅ / [+author]^F`

    This deletes [±singular] from 1st person agreed-with pronouns,
    bleeding insertion of *qin* ([+author,+singular]) and *qo*
    ([+author,−singular]). Only =i remains.

    For 2nd/3rd person, the rule does not apply (they are [-author]),
    so their subj/poss forms equal their independent forms (Table 4.25).
    For unagreed-with positions (objects), there is no F diacritic,
    so impoverishment does not apply regardless of person. -/
def derivePronounForm (pos : MamArgPosition) (person : Core.Prominence.PersonLevel) :
    PronounForm :=
  if pos.isPhiAgreed then
    if isFirstPerson person then .reduced
    else .full  -- 2nd/3rd: subj/poss = independent form (no reduction)
  else .full

/-- 1st person agent: reduced (base deleted, only =i remains). -/
theorem first_agent_reduced :
    derivePronounForm .agent .first = .reduced := rfl

/-- 3rd person agent: full independent form (impoverishment does not
    apply to [-author]). -/
theorem third_agent_full :
    derivePronounForm .agent .third = .full := rfl

/-- 2nd person agent: full independent form (=i IS the independent
    2SG pronoun, not a reduction). -/
theorem second_agent_full :
    derivePronounForm .agent .second = .full := rfl

/-- 1st person patient: full pronoun (no agreement → no F diacritic). -/
theorem first_patient_full :
    derivePronounForm .patient .first = .full := rfl

/-- 3rd person patient: full pronoun (no agreement → no F diacritic). -/
theorem third_patient_full :
    derivePronounForm .patient .third = .full := rfl

/-- 1st person intransitive S: reduced (Set B agreement triggers
    impoverishment, deleting base). -/
theorem first_intranS_reduced :
    derivePronounForm .intranS .first = .reduced := rfl

/-- 3rd person intransitive S: full independent form. -/
theorem third_intranS_full :
    derivePronounForm .intranS .third = .full := rfl

/-- Key asymmetry: for agreed-with positions, 1st person is reduced
    while 2nd/3rd retain full independent forms. This follows from the
    impoverishment rule targeting [+author] only. -/
theorem first_vs_nonfirst_asymmetry :
    (derivePronounForm .agent .first ≠ derivePronounForm .agent .third) ∧
    (derivePronounForm .intranS .first ≠ derivePronounForm .intranS .third) := by
  exact ⟨by decide, by decide⟩

/-- For unagreed-with positions, person is irrelevant: all get full pronouns. -/
theorem patient_person_irrelevant :
    derivePronounForm .patient .first = derivePronounForm .patient .third := rfl

-- ============================================================================
-- § 7: Mayan Absolutive Parameter
-- ============================================================================

/-- Mam is HIGH-ABS: Set B (absolutive) markers appear pre-stem on Infl,
    immediately following the aspect marker. Morpheme template:
    ASP-**ABS**-ERG-ROOT-SUFFIX (@cite{scott-2023}, §2.5.1). -/
def absPosition : Fragments.Mayan.ABSPosition := .high

/-- HIGH-ABS yields ABS=NOM case locus: Infl assigns case to the
    absolutive argument (@cite{scott-2023}, §3.3). -/
theorem mam_case_locus :
    Fragments.Mayan.toCaseLocus absPosition = .absNom := rfl

-- ============================================================================
-- § 8: Theory-Neutral Marker Lookup Verification
-- ============================================================================

/-- Set A 1SG marker. -/
theorem setA_1sg : lookupMarker setAMarkers .first true = some "n-/w-" := by native_decide

/-- Set A 3SG marker is "t-" (the default). -/
theorem setA_3sg : lookupMarker setAMarkers .third true = some "t-" := by native_decide

/-- Set B 1SG marker is "chin". -/
theorem setB_1sg : lookupMarker setBMarkers .first true = some "chin" := by native_decide

/-- Set B 3SG marker is the default "tz'=". -/
theorem setB_3sg : lookupMarker setBMarkers .third true = some defaultSetB := by native_decide

end Fragments.Mayan.Mam
