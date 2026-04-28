import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Params

/-!
# Mam Agreement Fragment @cite{scott-2023}
@cite{deal-2024} @cite{woolford-1997} @cite{blake-1994}

Agreement morphology and pronoun realization data for **San Juan Atitán
Mam (SJA Mam)**, the dialect analyzed in @cite{scott-2023}. Per Scott's
Chapter 3 (titled "Object licensing and agreement: SJA Mam is a
**tripartite high-abs language**"), SJA Mam exhibits morphologically
tripartite agreement alignment: S, A, and O each trigger distinct
marking patterns on the verb.

## Dialect-specificity and the analytical contrast

This fragment encodes Scott's analysis of SJA Mam specifically. Other
Mam dialects (notably Ixtahuacán Mam, the variety described in England
1983b and used by @cite{zavala-maldonado-2017} §4-5) have been
characterized as **ergative with a neutral pattern in aspectless
dependent clauses** — NOT tripartite. Per Zavala 2017 §4 (p. 237),
"Ch'orti' is the only Mayan language that exhibits three sets of
pronominal markers" — making Ch'orti' the canonical tripartite Mayan
language under that framing.

Scott's tripartite analysis of SJA Mam is an **analytical contribution**
that uses a high-abs / Voice Licensing / Ergative Extraction Constraint
framework (her ch. 3 §3.4) to argue for tripartite case (ERG, ACC, ABS)
even though Mam lacks independent DP case morphology. Per Scott §1.2.4
(Mam dialect variation, p. 11) and Table 1.2 (Mam dialect groups,
citing Simon 2019), Mam dialects vary substantially; the SJA Mam
analysis may not extend directly to Ixtahuacán Mam.

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

## Case Licensing (per Scott's analysis)

Case is NOT assigned via dependent case. Instead:
- **ERG**: inherent case from Voice
- **ACC**: structural case from Voice (object licensing; low-abs syntax)
- **ABS**: structural case from Infl (high-abs morphology; for intransitive S)

This gives a tripartite underlying Case system (ERG, ACC, ABS) despite
Mam having no independent case morphology on DPs — case is visible only
through agreement patterns. This tripartite analysis is dialect-specific
to SJA Mam per Scott; alternative analyses (for other Mam dialects or
under different theoretical frameworks) characterize Mam as ergative
with neutral patterns in dependent clauses (England 1983b;
@cite{zavala-maldonado-2017} §4-5).

## Argument Positions

| Position | Case | Agreement | Pronoun |
|----------|------|-----------|---------|
| A (transitive agent) | ERG (from Voice) | Set A | reduced/null |
| S (intransitive subj) | ABS (from Infl) | Set B | reduced/null |
| P (transitive patient) | ACC (from Voice) | default Set B | **overt** |

-/

namespace Fragments.Mayan.Mam

-- ============================================================================
-- § 1: Person-Number Inventory (theory-neutral cells)
-- ============================================================================

/-- Person-number combinations for Mam agreement paradigms.
    Six cells: three persons × two numbers. Mirrors the Kaqchikel
    `PersonNumber` structure for cross-Mayan helper compatibility. -/
inductive MamPersonNumber where
  | p1sg | p2sg | p3sg | p1pl | p2pl | p3pl
  deriving DecidableEq, Repr

/-- All six person-number values. -/
def mamPersonNumbers : List MamPersonNumber :=
  [.p1sg, .p2sg, .p3sg, .p1pl, .p2pl, .p3pl]

/-- Person value as `PersonLevel`. -/
def MamPersonNumber.person : MamPersonNumber → Features.Prominence.PersonLevel
  | .p1sg | .p1pl => .first
  | .p2sg | .p2pl => .second
  | .p3sg | .p3pl => .third

/-- Is this person-number [+plural]? -/
def MamPersonNumber.isPlural : MamPersonNumber → Bool
  | .p1pl | .p2pl | .p3pl => true
  | .p1sg | .p2sg | .p3sg => false

-- ============================================================================
-- § 2: Agreement Marker Paradigms (theory-neutral)
-- ============================================================================

/-- Set A (ERG) markers per cell: prefixes/proclitics on the verb that
    cross-reference the transitive agent (@cite{scott-2023}, Table 2.8).
    All six cells have distinct exponents (with t- syncretism for 2sg/3sg
    and ky- syncretism for 2pl/3pl). -/
def mamSetAExponent : MamPersonNumber → String
  | .p1sg => "n-/w-"
  | .p2sg => "t-"
  | .p3sg => "t-"
  | .p1pl => "q-"
  | .p2pl => "ky-"
  | .p3pl => "ky-"

/-- Set B (ABS) markers per cell (@cite{scott-2023}, Table 3.5).
    The 2/3SG form tz'= is the **default** — it appears both for real
    agreement with a 2/3SG intransitive S and for default Set B in
    transitives when Infl's probe is blocked by VoiceP.

    Per Scott's DM analysis, 2sg and 3sg are NOT specific entries; they
    surface via the Elsewhere fallback. The total function below
    returns "tz'=" for both, but downstream Vocabulary construction
    should treat them as derived from the Elsewhere entry. See
    `mamSetBSpecificCells` for the cells that have actual specific
    Vocabulary Items in the DM analysis. -/
def mamSetBExponent : MamPersonNumber → String
  | .p1sg => "chin"
  | .p2sg => "tz'="
  | .p3sg => "tz'="
  | .p1pl => "qo"
  | .p2pl => "chi"
  | .p3pl => "chi"

/-- The four Set B cells that have specific Vocabulary Items (per
    Scott's DM analysis). 2sg and 3sg are NOT included — they fall
    through to the Elsewhere entry. -/
def mamSetBSpecificCells : List MamPersonNumber :=
  [.p1sg, .p1pl, .p2pl, .p3pl]

/-- The default (Elsewhere) Set B marker. Surfaces in transitives when
    Infl's probe is blocked, and also for 2/3SG intransitive S. -/
def defaultSetB : String := "tz'="

-- ============================================================================
-- § 2: Argument Positions and Agreement Status (substrate-anchored)
-- ============================================================================

/-- Argument positions in a Mam clause (@cite{scott-2023} ch. 3).
    Aliased to the canonical `Features.Prominence.ArgumentRole`
    (S/A/P/R/T) so cross-Mayan and cross-framework code shares one
    inventory. Use the canonical constructor names `.A` / `.P` / `.S`
    directly. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- The case each argument position receives. Definitionally equal to
    `Fragments.Mayan.ergCaseMam`, which derives from
    `Alignment.tripartite.assignCase` in
    `Theories/Syntax/Case/Alignment.lean`: A → ERG (inherent from Voice),
    P → ACC (structural from Voice), S → ABS (structural from Infl).
    The three distinct cases are tripartite alignment per Scott's
    analysis (ch. 3 §3.4). -/
abbrev ArgPosition.case : ArgPosition → Core.Case :=
  Fragments.Mayan.ergCaseMam

/-- Does this argument position participate in φ-Agree?

    Agent: Voice probes for φ, finds agent in Spec,VoiceP → Set A
    Intransitive S: Infl probes for φ, finds S → Set B
    Patient: Infl's φ-probe has a disjunctive satisfaction condition
    [SAT: φ or Voice_TR]. In transitives, the
    probe encounters transitive Voice and stops — no φ-features are
    copied, and default Set B (the Elsewhere form) surfaces.
    Ditransitive R/T default to participating (not modeled). -/
def ArgPosition.IsPhiAgreed : ArgPosition → Prop
  | .A => True   -- φ-Agreed by Voice → Set A
  | .P => False  -- NOT φ-Agreed: Infl probe blocked by Voice_TR
  | .S | .R | .T => True   -- S φ-Agreed by Infl → Set B; R/T default

instance : DecidablePred ArgPosition.IsPhiAgreed := fun p => by
  cases p <;> unfold ArgPosition.IsPhiAgreed <;> infer_instance

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
def ArgPosition.CanBeReduced (pos : ArgPosition) : Prop :=
  pos.IsPhiAgreed

instance : DecidablePred ArgPosition.CanBeReduced := fun pos => by
  unfold ArgPosition.CanBeReduced; exact inferInstance

/-- The three monotransitive argument positions. -/
def mamArgPositions : List ArgPosition := [.A, .P, .S]

-- ============================================================================
-- § 4: Per-Position Verification
-- ============================================================================

/-- Agent gets ERG (inherent, from Voice). -/
theorem A_case : ArgPosition.case .A = .erg := rfl

/-- Patient gets ACC (structural, from Voice). -/
theorem P_case : ArgPosition.case .P = .acc := rfl

/-- Intransitive S gets ABS (structural, from Infl). -/
theorem S_case : ArgPosition.case .S = .abs := rfl

/-- Three distinct underlying cases — morphologically tripartite.
    Inherits from `Alignment.tripartite_distinguishes_all` via the
    substrate connection. -/
theorem tripartite_alignment :
    ArgPosition.case .A ≠ ArgPosition.case .P ∧
    ArgPosition.case .A ≠ ArgPosition.case .S ∧
    ArgPosition.case .P ≠ ArgPosition.case .S :=
  Alignment.tripartite_distinguishes_all

/-- Reduction eligibility ≡ φ-agreement: an argument position is
    eligible for pronoun reduction iff it triggers agreement on the
    verb. By `CanBeReduced := IsPhiAgreed`, this is reflexivity. -/
theorem reduction_eligible_iff_phi_agreed (pos : ArgPosition) :
    pos.CanBeReduced ↔ pos.IsPhiAgreed :=
  Iff.rfl

-- ============================================================================
-- § 5: Case Inventory Validation (@cite{blake-1994})
-- ============================================================================

/-- Mam case inventory, derived from argument position case values. -/
def caseInventory : Finset Core.Case := {.erg, .acc, .abs}

/-- The inventory covers all argument positions. -/
theorem inventory_covers_positions :
    ∀ p ∈ mamArgPositions, p.case ∈ caseInventory := by decide

-- Mam's {ERG, ACC, ABS} inventory is valid per Blake's case hierarchy
-- (all are core cases at rank 6, trivially no gaps).
example : Core.Case.IsValidInventory caseInventory := by decide

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
def isFirstPerson : Features.Prominence.PersonLevel → Prop
  | .first => True
  | _      => False

instance : DecidablePred isFirstPerson := fun p => by
  cases p <;> unfold isFirstPerson <;> infer_instance

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
def derivePronounForm (pos : ArgPosition) (person : Features.Prominence.PersonLevel) :
    PronounForm :=
  if pos.IsPhiAgreed then
    if isFirstPerson person then .reduced
    else .full  -- 2nd/3rd: subj/poss = independent form (no reduction)
  else .full

/-- 1st person agent: reduced (base deleted, only =i remains). -/
theorem first_A_reduced :
    derivePronounForm .A .first = .reduced := rfl

/-- 3rd person agent: full independent form (impoverishment does not
    apply to [-author]). -/
theorem third_A_full :
    derivePronounForm .A .third = .full := rfl

/-- 2nd person agent: full independent form (=i IS the independent
    2SG pronoun, not a reduction). -/
theorem second_A_full :
    derivePronounForm .A .second = .full := rfl

/-- 1st person patient: full pronoun (no agreement → no F diacritic). -/
theorem first_P_full :
    derivePronounForm .P .first = .full := rfl

/-- 3rd person patient: full pronoun (no agreement → no F diacritic). -/
theorem third_P_full :
    derivePronounForm .P .third = .full := rfl

/-- 1st person intransitive S: reduced (Set B agreement triggers
    impoverishment, deleting base). -/
theorem first_S_reduced :
    derivePronounForm .S .first = .reduced := rfl

/-- 3rd person intransitive S: full independent form. -/
theorem third_S_full :
    derivePronounForm .S .third = .full := rfl

/-- Key asymmetry: for agreed-with positions, 1st person is reduced
    while 2nd/3rd retain full independent forms. This follows from the
    impoverishment rule targeting [+author] only. -/
theorem first_vs_nonfirst_asymmetry :
    (derivePronounForm .A .first ≠ derivePronounForm .A .third) ∧
    (derivePronounForm .S .first ≠ derivePronounForm .S .third) := by
  exact ⟨by decide, by decide⟩

/-- For unagreed-with positions, person is irrelevant: all get full pronouns. -/
theorem patient_person_irrelevant :
    derivePronounForm .P .first = derivePronounForm .P .third := rfl

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
-- § 8: Theory-Neutral Marker Verification
-- ============================================================================

/-- Set A 1SG marker. -/
theorem setA_1sg : mamSetAExponent .p1sg = "n-/w-" := rfl

/-- Set A 3SG marker is "t-" (the default singular Set A — syncretic with 2SG). -/
theorem setA_3sg : mamSetAExponent .p3sg = "t-" := rfl

/-- Set B 1SG marker is "chin". -/
theorem setB_1sg : mamSetBExponent .p1sg = "chin" := rfl

/-- Set B 3SG marker is the default "tz'=". -/
theorem setB_3sg : mamSetBExponent .p3sg = defaultSetB := rfl

end Fragments.Mayan.Mam
