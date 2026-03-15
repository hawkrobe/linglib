import Linglib.Core.Prominence
import Linglib.Core.Lexical.DiathesisAlternation

/-!
# Valency Alternation Typology
@cite{creissels-2025}

A unified framework for describing valency alternations cross-linguistically,
following @cite{creissels-2025}'s framework for transitivity, valency, and
voice. This file provides the core vocabulary that subsumes both
@cite{levin-1993}'s English-specific diathesis alternations and
@cite{creissels-2025}'s cross-linguistic voice alternation typology.

## TR-roles

@cite{creissels-2025} §1.3.3 defines Transitivity-Related roles (A, P, S, X)
as *constructional* properties of nominal terms, not semantic roles. A is
"the nominal term whose coding matches the agent of a prototypical transitive
verb" — it's defined by coding (flagging, indexation, order), anchored to
semantic prototypes. These are already captured by `Prominence.ArgumentRole`
(S, A, P, R, T). This file adds X (oblique) as a `TRRole` that extends
`ArgumentRole` with the non-core case.

## Nucleativization and Denucleativization

The two fundamental operations on coding frames (§8.1.3):
- **Nucleativization**: a non-nuclear participant becomes a core term
  (A, P, or S) in the derived construction.
- **Denucleativization**: a core term of the initial construction
  becomes oblique or unexpressed in the derived construction.

All voice alternations are defined by specifying which participants are
nucleativized or denucleativized, and what TR-roles they acquire.

## Unification with Levin alternations

@cite{levin-1993}'s `DiathesisAlternation` captures English-specific
alternation patterns. Each maps to a `ValencyAlternation` that specifies
the structural effect. The key distinction: Levin alternations are often
*uncoded* (flexivalency — no verbal morphology marks the alternation),
while @cite{creissels-2025}'s voice alternations are *coded* (marked by
verbal morphology). The `marking` field captures this.
-/

namespace Core.Alternation

open Prominence (ArgumentRole)

-- ════════════════════════════════════════════════════
-- § 1. TR-Roles (@cite{creissels-2025} §1.3.3)
-- ════════════════════════════════════════════════════

/-- Transitivity-Related role including obliques.

    Extends `Prominence.ArgumentRole` (S, A, P, R, T) with X for obliques.
    @cite{creissels-2025} §1.3.3: "OBLIQUE NOMINAL TERMS (or simply OBLIQUES),
    symbolized as X, are defined as nominal terms of verbal clauses that do
    not meet the definition of either A, P, or S." -/
inductive TRRole where
  | S    -- sole core term of intransitive clause
  | A    -- agent-like core term of transitive clause
  | P    -- patient-like core term of transitive clause
  | X    -- oblique (non-core term)
  deriving DecidableEq, BEq, Repr

/-- Convert `ArgumentRole` to `TRRole`. R and T map to P (both are
    P-like in Creissels' binary core-term system). -/
def TRRole.ofArgumentRole : ArgumentRole → TRRole
  | .S => .S
  | .A => .A
  | .P => .P
  | .R => .P  -- recipients behave as P-like core terms
  | .T => .P  -- themes behave as P-like core terms

-- ════════════════════════════════════════════════════
-- § 2. Participant Fate in an Alternation
-- ════════════════════════════════════════════════════

/-- What happens to a participant's coding in a valency alternation.

    Each alternation is defined by specifying the fate of each participant
    in the initial construction. -/
inductive ParticipantFate where
  /-- Participant is nucleativized: becomes a core term in the derived
      construction. The `target` specifies which TR-role it acquires. -/
  | nucleativized (target : TRRole)
  /-- Participant is denucleativized: demoted from core term to oblique or
      unexpressed, but MAINTAINED IN PARTICIPANT STRUCTURE. The participant
      is still semantically present and may appear as an oblique phrase.
      @cite{creissels-2025} §8.3.2.1: "the referent of the initial A is
      denucleativized ... but is maintained in participant structure." -/
  | denucleativized
  /-- Participant is suppressed: REMOVED FROM PARTICIPANT STRUCTURE entirely.
      The participant has no syntactic realization in the derived construction
      and is not semantically implied.
      @cite{creissels-2025} §8.3.1.2: "Decausativization suppresses the
      referent of the initial A from participant structure." -/
  | suppressed
  /-- Participant's coding is maintained unchanged. -/
  | maintained
  /-- Two participants are cumulated into a single participant
      (reflexivization/reciprocalization). -/
  | cumulated
  /-- Not applicable (participant does not exist in initial construction). -/
  | na
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Alternation Marking
-- ════════════════════════════════════════════════════

/-- Whether and how a valency alternation is morphologically coded.

    @cite{creissels-2025} §1.1.3: voice = coded alternation; flexivalency
    = uncoded alternation. The distinction is fundamental to his framework:
    same structural alternation, different morphosyntactic status. -/
inductive AlternationMarking where
  /-- Coded by verbal morphology (affix, ablaut, tone, etc.) — this is
      VOICE in @cite{creissels-2025}'s terminology. -/
  | synthetic
  /-- Coded by an analytic construction (auxiliary + nonfinite form). -/
  | analytic
  /-- Coded by equipollent marking (both forms equally complex). -/
  | equipollent
  /-- Uncoded — no morphological marking (FLEXIVALENCY). -/
  | uncoded
  deriving DecidableEq, BEq, Repr

/-- Is this alternation an instance of voice (coded by verbal morphology)? -/
def AlternationMarking.isVoice : AlternationMarking → Bool
  | .synthetic | .analytic | .equipollent => true
  | .uncoded => false

-- ════════════════════════════════════════════════════
-- § 4. Valency Alternation
-- ════════════════════════════════════════════════════

/-- A valency alternation defined by its structural effect on participants.

    This is the unified type subsuming both @cite{levin-1993}'s English-specific
    diathesis alternations and @cite{creissels-2025}'s cross-linguistic voice
    alternation types. Each alternation specifies:
    - What happens to each participant of the initial construction
    - Whether a new participant is introduced
    - How (if at all) the alternation is morphologically marked -/
structure ValencyAlternation where
  /-- Descriptive name -/
  name : String
  /-- What happens to the initial A (if the initial construction is transitive) -/
  fateOfA : ParticipantFate
  /-- What happens to the initial P (if the initial construction is transitive) -/
  fateOfP : ParticipantFate
  /-- What happens to the initial S (if the initial construction is intransitive) -/
  fateOfS : ParticipantFate
  /-- Is a new participant introduced in the derived construction?
      If so, which TR-role does it receive? -/
  newParticipant : Option TRRole
  /-- Is the initial construction transitive, intransitive, or either? -/
  initialTransitive : Option Bool
  /-- Is the derived construction transitive? -/
  derivedTransitive : Option Bool
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § 5. Creissels' Voice Alternation Typology (§8.3)
-- ════════════════════════════════════════════════════

/-- Causativization (@cite{creissels-2025} §8.3.1.1): nucleativization of a
    causer in A role. Initial construction is intransitive; initial S becomes
    P in the derived transitive construction. -/
def causativization : ValencyAlternation :=
  { name := "causativization"
  , fateOfA := .na
  , fateOfP := .na
  , fateOfS := .maintained  -- S becomes P by the derived construction being transitive
  , newParticipant := some .A
  , initialTransitive := some false
  , derivedTransitive := some true }

/-- Decausativization (@cite{creissels-2025} §8.3.1.2): the initial A is
    SUPPRESSED FROM PARTICIPANT STRUCTURE; initial P becomes S of an
    intransitive construction. Called "anticausative" in most other
    frameworks; Creissels prefers "decausative" because the prefix *de-*
    transparently marks the removal of causation.

    The critical difference from passivization: in decausativization, A is
    entirely removed from participant structure (`.suppressed`), whereas in
    passivization, A is denucleativized but remains in participant structure
    (`.denucleativized`). -/
def decausativization : ValencyAlternation :=
  { name := "decausativization"
  , fateOfA := .suppressed
  , fateOfP := .maintained  -- P becomes S
  , fateOfS := .na
  , newParticipant := none
  , initialTransitive := some true
  , derivedTransitive := some false }

/-- Passivization (@cite{creissels-2025} §8.3.2.1): A is denucleativized
    (oblique or unexpressed) but maintained in participant structure.
    No participant is nucleativized. P becomes S.

    The key difference from decausativization: in passivization, the initial
    A is still semantically present (can appear as an oblique agent phrase).
    In decausativization, the initial A is removed from participant structure. -/
def passivization : ValencyAlternation :=
  { name := "passivization"
  , fateOfA := .denucleativized
  , fateOfP := .maintained  -- P becomes S
  , fateOfS := .na
  , newParticipant := none
  , initialTransitive := some true
  , derivedTransitive := some false }

/-- I-passivization (@cite{creissels-2025} §8.3.2.2): impersonal variant
    of passivization. A is denucleativized, but P's coding is unchanged —
    the derived construction is impersonal (no S). -/
def iPassivization : ValencyAlternation :=
  { name := "I-passivization"
  , fateOfA := .denucleativized
  , fateOfP := .maintained
  , fateOfS := .na
  , newParticipant := none
  , initialTransitive := some true
  , derivedTransitive := none }

/-- Antipassivization (@cite{creissels-2025} §8.3.2.3): P is denucleativized
    (oblique or unexpressed); A becomes S of an intransitive construction. -/
def antipassivization : ValencyAlternation :=
  { name := "antipassivization"
  , fateOfA := .maintained  -- A becomes S
  , fateOfP := .denucleativized
  , fateOfS := .na
  , newParticipant := none
  , initialTransitive := some true
  , derivedTransitive := some false }

/-- S-denucleativization (@cite{creissels-2025} §8.3.2.4): S of an
    intransitive construction is denucleativized, yielding an impersonal
    construction. -/
def sDenucleativization : ValencyAlternation :=
  { name := "S-denucleativization"
  , fateOfA := .na
  , fateOfP := .na
  , fateOfS := .denucleativized
  , newParticipant := none
  , initialTransitive := some false
  , derivedTransitive := none }

/-- Reflexivization (@cite{creissels-2025} §8.3.3): A and P are cumulated
    into S — a single participant fills both roles. -/
def reflexivization : ValencyAlternation :=
  { name := "reflexivization"
  , fateOfA := .cumulated
  , fateOfP := .cumulated
  , fateOfS := .na
  , newParticipant := none
  , initialTransitive := some true
  , derivedTransitive := some false }

/-- Reciprocalization (@cite{creissels-2025} §8.3.3): like reflexivization
    but with a group reading — participants mutually fill both roles. -/
def reciprocalization : ValencyAlternation :=
  { name := "reciprocalization"
  , fateOfA := .cumulated
  , fateOfP := .cumulated
  , fateOfS := .na
  , newParticipant := none
  , initialTransitive := some true
  , derivedTransitive := some false }

/-- P-applicativization (@cite{creissels-2025} §8.3.5, §14.1.1): a
    non-nuclear participant is nucleativized as P. The initial P may be
    denucleativized (demoted to oblique) or maintained in double-P
    constructions. -/
def pApplicativization : ValencyAlternation :=
  { name := "P-applicativization"
  , fateOfA := .maintained
  , fateOfP := .maintained  -- may be denucleativized in some languages
  , fateOfS := .na
  , newParticipant := some .P
  , initialTransitive := some true
  , derivedTransitive := some true }

/-- D-applicativization (@cite{creissels-2025} §14.1.3): a non-nuclear
    participant is nucleativized as a dative oblique (a special oblique
    type with core-term-like properties in many languages). -/
def dApplicativization : ValencyAlternation :=
  { name := "D-applicativization"
  , fateOfA := .maintained
  , fateOfP := .maintained
  , fateOfS := .na
  , newParticipant := some .X
  , initialTransitive := none
  , derivedTransitive := none }

/-- X-applicativization (@cite{creissels-2025} §14.1.4): a non-nuclear
    participant is nucleativized as an ordinary oblique. -/
def xApplicativization : ValencyAlternation :=
  { name := "X-applicativization"
  , fateOfA := .maintained
  , fateOfP := .maintained
  , fateOfS := .na
  , newParticipant := some .X
  , initialTransitive := none
  , derivedTransitive := none }

/-- A/S-nucleativization of obliques (@cite{creissels-2025} §8.3.4.1):
    an oblique participant (e.g., an instrument) takes over the A or S role
    in the derived construction. The nucleativized participant does NOT
    outrank the initial A/S in agentivity (distinguishing this from
    causativization).

    Example: Laalaa (Cangin) *Fetal-aa ap-ah-an paloom*
    'The gun will be used to kill antelopes' — instrument nucleativized as A. -/
def asNucleativizationOfObliques : ValencyAlternation :=
  { name := "A/S-nucleativization of obliques"
  , fateOfA := .maintained  -- initial A maintained (or .na if intransitive)
  , fateOfP := .maintained
  , fateOfS := .na
  , newParticipant := some .A  -- oblique promoted to A
  , initialTransitive := some true
  , derivedTransitive := some true }

/-- Concernativization (@cite{creissels-2025} §8.3.4.2): nucleativization
    of a concernee (external possessor / adversely affected party) into
    the A role. The initial construction may be transitive or intransitive.

    When initial is intransitive: S is maintained (becomes P-like), concernee
    becomes A, derived construction is transitive.
    When initial is transitive: A is maintained, P is maintained, concernee
    becomes an additional A-like participant.

    Example: Central Alaskan Yupik *Kit'-i-aqa kicaq*
    'I had the anchor sunk (me negatively affected)' — concernee as A. -/
def concernativization : ValencyAlternation :=
  { name := "concernativization"
  , fateOfA := .na
  , fateOfP := .na
  , fateOfS := .maintained  -- S maintained (becomes P in derived transitive)
  , newParticipant := some .A  -- concernee nucleativized as A
  , initialTransitive := some false  -- prototypical case is intransitive
  , derivedTransitive := some true }

/-- Portative derivation (@cite{creissels-2025} §8.3.7): converts a motion
    verb into a transitive 'A moves carrying P'. Distinguished from both
    causativization and applicativization. -/
def portativeDerivation : ValencyAlternation :=
  { name := "portative derivation"
  , fateOfA := .na
  , fateOfP := .na
  , fateOfS := .maintained  -- S of motion verb becomes A-like
  , newParticipant := some .P
  , initialTransitive := some false
  , derivedTransitive := some true }

-- ════════════════════════════════════════════════════
-- § 6. Alignment (@cite{creissels-2025} §1.3.4)
-- ════════════════════════════════════════════════════

/-- Alignment between core terms of transitive and intransitive clauses.

    @cite{creissels-2025} §1.3.4.2: the central typological parameter is
    whether S patterns with A (A-alignment, traditionally "accusative") or
    with P (P-alignment, traditionally "ergative"). Creissels avoids the
    traditional case-based labels because A-alignment can occur without
    accusative case, and P-alignment without ergative case. -/
inductive Alignment where
  /-- S is coded like A — traditionally "nominative-accusative" -/
  | A_alignment
  /-- S is coded like P — traditionally "absolutive-ergative" -/
  | P_alignment
  deriving DecidableEq, BEq, Repr

/-- The Obligatory Coding Principle (@cite{creissels-2025} §1.3.4.4):
    in most languages, every verb assigns a particular type of participant
    coding to one of its participants, and this type coincides with either
    A coding or P coding. A language that fully complies has either
    obligatory A-coding or obligatory P-coding.

    This is a reformulation of the accusative/ergative typology: obligatory
    A-coding = consistently accusative; obligatory P-coding = consistently
    ergative. -/
structure ObligatoryCodingProfile where
  language : String
  /-- Default alignment -/
  defaultAlignment : Alignment
  /-- Whether violations of the Obligatory Coding Principle exist -/
  violationsExist : Bool := false
  /-- Whether the language is split-S (different S classes align differently) -/
  splitS : Bool := false
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § 7. Voice Marker Polysemy (@cite{creissels-2025} §8.2)
-- ════════════════════════════════════════════════════

/-- A voice marker and the alternation types it can mark.

    @cite{creissels-2025} §8.2: cross-linguistically, voice markers are
    polysemous — the same morpheme may mark multiple voice alternation types.
    For example, Russian *-sja* marks reflexivization, reciprocalization,
    passivization, and antipassivization (§8.2, ex. 8). -/
structure VoiceMarkerProfile where
  /-- Language name -/
  language : String
  /-- Morpheme form -/
  marker : String
  /-- Which alternation types this marker can encode -/
  alternations : List ValencyAlternation
  deriving Repr, BEq

-- ════════════════════════════════════════════════════
-- § 8. Voice Alternation Distribution (@cite{creissels-2025} §8.3.8)
-- ════════════════════════════════════════════════════

/-- Cross-linguistic prevalence of voice alternation types.

    @cite{creissels-2025} §8.3.8, citing @cite{bahrt-2021}: distribution of
    synthetic voice marking across 222 languages from all genera. -/
structure VoiceDistribution where
  alternation : ValencyAlternation
  /-- Percentage of languages with synthetic marking for this alternation -/
  percentage : Float
  deriving Repr, BEq

/-- @cite{bahrt-2021} distribution data, cited in @cite{creissels-2025}
    §8.3.8. Percentages represent languages (out of 222) with synthetic
    marking for each voice alternation type. -/
def bahrt2021Distribution : List VoiceDistribution :=
  [ { alternation := causativization,       percentage := 73.9 }
  , { alternation := reciprocalization,     percentage := 60.4 }
  , { alternation := pApplicativization,    percentage := 45.9 }
  , { alternation := reflexivization,       percentage := 41.9 }
  , { alternation := decausativization,     percentage := 36.0 }
  , { alternation := passivization,         percentage := 36.0 }
  , { alternation := antipassivization,     percentage := 18.5 } ]

/-- Causativization is the most common voice alternation type
    cross-linguistically (@cite{bahrt-2021}). -/
theorem causativization_most_common :
    (bahrt2021Distribution.head?.map (·.alternation.name)) =
    some "causativization" := rfl

-- ════════════════════════════════════════════════════
-- § 9. Properties
-- ════════════════════════════════════════════════════

/-- Does this alternation involve nucleativization (adding a new core term)? -/
def ValencyAlternation.involvesNucleativization (va : ValencyAlternation) : Bool :=
  va.newParticipant.isSome

/-- Does this alternation involve denucleativization or suppression
    (removing a participant from core-term status)? -/
def ValencyAlternation.involvesDenucleativization (va : ValencyAlternation) : Bool :=
  va.fateOfA == .denucleativized || va.fateOfA == .suppressed ||
  va.fateOfP == .denucleativized || va.fateOfP == .suppressed ||
  va.fateOfS == .denucleativized || va.fateOfS == .suppressed

/-- Is this a valency-increasing alternation? -/
def ValencyAlternation.isValencyIncreasing (va : ValencyAlternation) : Bool :=
  va.involvesNucleativization && !va.involvesDenucleativization

/-- Is this a valency-decreasing alternation? -/
def ValencyAlternation.isValencyDecreasing (va : ValencyAlternation) : Bool :=
  va.involvesDenucleativization && !va.involvesNucleativization

/-- Does this alternation involve cumulation (reflexivization/reciprocalization)? -/
def ValencyAlternation.involvesCumulation (va : ValencyAlternation) : Bool :=
  va.fateOfA == .cumulated || va.fateOfP == .cumulated

-- ════════════════════════════════════════════════════
-- § 10. Property Theorems
-- ════════════════════════════════════════════════════

theorem causativization_increases :
    causativization.isValencyIncreasing = true := rfl

theorem decausativization_decreases :
    decausativization.isValencyDecreasing = true := rfl

theorem passivization_decreases :
    passivization.isValencyDecreasing = true := rfl

/-- The central distinction of @cite{creissels-2025} §8.3.2.1:
    passivization MAINTAINS A in participant structure (`.denucleativized`),
    while decausativization SUPPRESSES A from participant structure
    (`.suppressed`). These are structurally distinct operations. -/
theorem passivization_vs_decausativization :
    passivization.fateOfA = .denucleativized ∧
    decausativization.fateOfA = .suppressed :=
  ⟨rfl, rfl⟩

theorem antipassivization_decreases :
    antipassivization.isValencyDecreasing = true := rfl

theorem reflexivization_cumulates :
    reflexivization.involvesCumulation = true := rfl

theorem reciprocalization_cumulates :
    reciprocalization.involvesCumulation = true := rfl

theorem pApplicativization_increases :
    pApplicativization.isValencyIncreasing = true := rfl

/-- A/S-nucleativization of obliques is valency-increasing. -/
theorem as_nucleativization_increases :
    asNucleativizationOfObliques.isValencyIncreasing = true := rfl

/-- Portative derivation is valency-increasing, like causativization and
    applicativization, but cannot be reduced to either (§8.3.7). -/
theorem portative_increases :
    portativeDerivation.isValencyIncreasing = true := rfl

-- ════════════════════════════════════════════════════
-- § 11. Bridge: Levin DiathesisAlternation → ValencyAlternation
-- ════════════════════════════════════════════════════

/-- Map @cite{levin-1993}'s English-specific diathesis alternations to
    @cite{creissels-2025}'s cross-linguistic valency alternation types.

    Key insight: most Levin alternations are UNCODED (flexivalency) in
    English — the structural effect is the same as the corresponding coded
    voice alternation, but without morphological marking. For example,
    English *break* (tr)/*break* (intr) has the same structural effect as
    Tswana *-eχ* decausativization, but English uses no verbal morphology. -/
def toValencyAlternation : DiathesisAlternation → ValencyAlternation
  | .causativeInchoative => decausativization  -- the intransitive direction
  | .inducedAction => causativization  -- intransitive → transitive causative
  | .middle =>
    { name := "middle"
    , fateOfA := .denucleativized
    , fateOfP := .maintained
    , fateOfS := .na
    , newParticipant := none
    , initialTransitive := some true
    , derivedTransitive := some false }
  | .conative =>
    { name := "conative"
    , fateOfA := .maintained
    , fateOfP := .denucleativized
    , fateOfS := .na
    , newParticipant := none
    , initialTransitive := some true
    , derivedTransitive := some false }
  | .bodyPartPossessorAscension =>
    { name := "body-part possessor ascension"
    , fateOfA := .maintained
    , fateOfP := .maintained
    , fateOfS := .na
    , newParticipant := some .P  -- possessor promoted to P-like
    , initialTransitive := some true
    , derivedTransitive := some true }
  | .dative =>
    { name := "dative"
    , fateOfA := .maintained
    , fateOfP := .maintained
    , fateOfS := .na
    , newParticipant := none  -- no new participant; P↔X alternation
    , initialTransitive := some true
    , derivedTransitive := some true }
  | .benefactive =>
    { name := "benefactive"
    , fateOfA := .maintained
    , fateOfP := .maintained
    , fateOfS := .na
    , newParticipant := none  -- beneficiary alternates between PP and NP2
    , initialTransitive := some true
    , derivedTransitive := some true }
  | .locative =>
    { name := "locative"
    , fateOfA := .maintained
    , fateOfP := .maintained
    , fateOfS := .na
    , newParticipant := none  -- no new participant; P↔X alternation
    , initialTransitive := some true
    , derivedTransitive := some true }
  | .substanceSource =>
    { name := "substance/source"
    , fateOfA := .na
    , fateOfP := .maintained  -- substance alternates between S and P
    , fateOfS := .maintained
    , newParticipant := none
    , initialTransitive := none  -- both forms exist
    , derivedTransitive := none }
  | .materialProduct =>
    { name := "material/product"
    , fateOfA := .maintained
    , fateOfP := .maintained  -- material↔product alternate as direct object
    , fateOfS := .na
    , newParticipant := none
    , initialTransitive := some true
    , derivedTransitive := some true }
  | .unspecifiedObject =>
    { name := "unspecified object"
    , fateOfA := .maintained  -- A becomes S
    , fateOfP := .suppressed  -- object unexpressed
    , fateOfS := .na
    , newParticipant := none
    , initialTransitive := some true
    , derivedTransitive := some false }
  | .understoodBodyPartObject =>
    { name := "understood body-part object"
    , fateOfA := .maintained  -- A becomes S
    , fateOfP := .suppressed  -- body-part object unexpressed
    , fateOfS := .na
    , newParticipant := none
    , initialTransitive := some true
    , derivedTransitive := some false }
  | .understoodReflexiveObject =>
    { name := "understood reflexive object"
    , fateOfA := .cumulated   -- A and P collapse (self-directed)
    , fateOfP := .cumulated
    , fateOfS := .na
    , newParticipant := none
    , initialTransitive := some true
    , derivedTransitive := some false }
  | .understoodReciprocalObject =>
    { name := "understood reciprocal object"
    , fateOfA := .cumulated   -- A and P merged into plural S
    , fateOfP := .cumulated
    , fateOfS := .na
    , newParticipant := none
    , initialTransitive := some true
    , derivedTransitive := some false }
  | .swarm =>
    { name := "swarm"
    , fateOfA := .na
    , fateOfP := .na
    , fateOfS := .maintained  -- S maintained, locative becomes S
    , newParticipant := none
    , initialTransitive := some false
    , derivedTransitive := some false }
  | .totalTransformation =>
    { name := "total transformation"
    , fateOfA := .maintained
    , fateOfP := .maintained  -- P undergoes complete change
    , fateOfS := .na
    , newParticipant := none
    , initialTransitive := some true
    , derivedTransitive := some true }
  | .thereInsertion =>
    { name := "there-insertion"
    , fateOfA := .na
    , fateOfP := .na
    , fateOfS := .maintained  -- S moves to postverbal position
    , newParticipant := none
    , initialTransitive := some false
    , derivedTransitive := some false }
  | .locativeInversion =>
    { name := "locative inversion"
    , fateOfA := .na
    , fateOfP := .na
    , fateOfS := .maintained  -- S moves to postverbal position
    , newParticipant := none
    , initialTransitive := some false
    , derivedTransitive := some false }
  | .instrumentSubject =>
    { name := "instrument subject"
    , fateOfA := .denucleativized  -- agent optionally suppressed
    , fateOfP := .maintained
    , fateOfS := .na
    , newParticipant := some .A  -- instrument promoted to A
    , initialTransitive := some true
    , derivedTransitive := some true }
  | .verbalPassive => passivization  -- fundamental voice alternation
  | .prepositionalPassive =>
    { name := "prepositional passive"
    , fateOfA := .na
    , fateOfP := .na
    , fateOfS := .denucleativized  -- S demoted, oblique promoted
    , newParticipant := none
    , initialTransitive := some false
    , derivedTransitive := some false }
  | .cognateObject =>
    { name := "cognate object"
    , fateOfA := .na
    , fateOfP := .na
    , fateOfS := .maintained  -- S becomes A
    , newParticipant := some .P  -- cognate NP added
    , initialTransitive := some false
    , derivedTransitive := some true }
  | .wayConstruction =>
    { name := "way construction"
    , fateOfA := .na
    , fateOfP := .na
    , fateOfS := .maintained  -- S becomes A
    , newParticipant := some .P  -- reflexive possessive NP added
    , initialTransitive := some false
    , derivedTransitive := some true }
  | .resultative =>
    { name := "resultative"
    , fateOfA := .maintained
    , fateOfP := .maintained
    , fateOfS := .na
    , newParticipant := none
    , initialTransitive := some true
    , derivedTransitive := some true }
  | .directionalPhrase =>
    { name := "directional phrase"
    , fateOfA := .na
    , fateOfP := .na
    , fateOfS := .maintained  -- S maintained, directional PP added
    , newParticipant := none
    , initialTransitive := some false
    , derivedTransitive := some false }

/-- The causative/inchoative alternation maps to decausativization
    (viewed from the transitive direction, the intransitive variant removes
    the causer). -/
theorem causativeInchoative_is_decausativization :
    toValencyAlternation .causativeInchoative =
    decausativization := rfl

/-- The conative alternation is structurally an antipassivization:
    A is maintained, P is denucleativized (demoted to oblique with *at*). -/
theorem conative_is_antipassive_like :
    (toValencyAlternation .conative).involvesDenucleativization = true ∧
    (toValencyAlternation .conative).fateOfA = .maintained := ⟨rfl, rfl⟩

/-- Body-part possessor ascension is structurally a nucleativization
    (like applicativization): a possessor is promoted to core-term status. -/
theorem bppa_is_applicative_like :
    (toValencyAlternation .bodyPartPossessorAscension).involvesNucleativization = true := rfl

/-- The understood reciprocal object alternation involves cumulation,
    just like reflexivization and reciprocalization in @cite{creissels-2025}. -/
theorem understoodReciprocal_cumulates :
    (toValencyAlternation .understoodReciprocalObject).involvesCumulation = true := rfl

/-- The unspecified object alternation is valency-decreasing:
    P is suppressed (removed from participant structure). -/
theorem unspecifiedObject_decreases :
    (toValencyAlternation .unspecifiedObject).isValencyDecreasing = true := rfl

/-- The instrument subject alternation involves both nucleativization (instrument → A)
    and denucleativization (original A demoted), so it is neither strictly
    valency-increasing nor valency-decreasing — it is a restructuring. -/
theorem instrumentSubject_restructures :
    (toValencyAlternation .instrumentSubject).involvesNucleativization = true
    ∧ (toValencyAlternation .instrumentSubject).involvesDenucleativization = true
    ∧ (toValencyAlternation .instrumentSubject).isValencyIncreasing = false
    ∧ (toValencyAlternation .instrumentSubject).isValencyDecreasing = false := ⟨rfl, rfl, rfl, rfl⟩

/-- The induced action alternation maps to causativization:
    *Bill ran* → *Bill ran the horse* (intransitive S becomes P,
    new causer becomes A). -/
theorem inducedAction_is_causativization :
    toValencyAlternation .inducedAction = causativization := rfl

/-- The verbal passive maps to passivization. -/
theorem verbalPassive_is_passivization :
    toValencyAlternation .verbalPassive = passivization := rfl

/-- The understood reflexive object alternation involves cumulation,
    like reflexivization in @cite{creissels-2025}. -/
theorem understoodReflexive_cumulates :
    (toValencyAlternation .understoodReflexiveObject).involvesCumulation = true := rfl

/-- The cognate object alternation is valency-increasing:
    adds a P to an intransitive verb (*she laughed* → *she laughed a bitter laugh*). -/
theorem cognateObject_increases :
    (toValencyAlternation .cognateObject).isValencyIncreasing = true := rfl

/-- The way construction is valency-increasing:
    adds a possessive P (*she elbowed* → *she elbowed her way through*). -/
theorem wayConstruction_increases :
    (toValencyAlternation .wayConstruction).isValencyIncreasing = true := rfl

/-- The understood body-part object alternation is valency-decreasing:
    P is suppressed (*Bill waved his hand* → *Bill waved*). -/
theorem understoodBodyPartObject_decreases :
    (toValencyAlternation .understoodBodyPartObject).isValencyDecreasing = true := rfl

-- ════════════════════════════════════════════════════
-- § 12. Flexivalency / Ambitransitivity (@cite{creissels-2025} Ch 15)
-- ════════════════════════════════════════════════════

/-- Types of ambitransitivity (uncoded transitivity alternation).

    @cite{creissels-2025} §15.2: a verb is ambitransitive when it can
    appear in both transitive and intransitive constructions without
    morphological marking. The five subtypes differ in what happens to the
    participants. -/
inductive AmbitransitivityType where
  /-- S of intransitive = P of transitive. *The glass broke.* / *She broke the glass.*
      Traditionally "anticausative" or "unaccusative" ambitransitivity. -/
  | P_ambitransitivity
  /-- S of intransitive = A of transitive. *She ate.* / *She ate the cake.*
      Traditionally "unergative" ambitransitivity. -/
  | A_ambitransitivity
  /-- The intransitive is reflexive (A = P). *She washed.* = *She washed herself.* -/
  | reflexive
  /-- The intransitive is reciprocal (A = P, group). *They kissed.* -/
  | reciprocal
  /-- Ambiguous or underspecified. -/
  | unspecified
  deriving DecidableEq, BEq, Repr

/-- P-ambitransitivity corresponds to uncoded decausativization. -/
theorem p_ambi_is_uncoded_decausativization :
    decausativization.involvesDenucleativization = true := rfl

/-- A-ambitransitivity corresponds to uncoded antipassivization. -/
theorem a_ambi_is_uncoded_antipassivization :
    antipassivization.involvesDenucleativization = true := rfl

end Core.Alternation
