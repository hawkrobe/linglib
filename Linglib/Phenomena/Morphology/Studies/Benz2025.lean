import Linglib.Theories.Morphology.DM.Allosemy
import Linglib.Core.Empirical
import Linglib.Fragments.German.Predicates

/-!
# Benz (2025): Structure and Interpretation Across Categories
@cite{benz-2025}

*Structure and Interpretation Across Categories*.
PhD dissertation, University of Pennsylvania.

## Overview

This file formalizes three interconnected contributions from @cite{benz-2025}:

1. **Content nominalizations** (Ch. 3): German *-ung* nominalizations are
   systematically three-ways ambiguous (event/result/content), derived from
   allosemy of v and n in the structure [nP n [vP v [√Root]]].

2. **Co-occurrence restrictions** (Ch. 4): German preverbal elements
   (prefixes, particles, RSPs) show a striking co-occurrence paradigm
   explained by the conjunction of phrase-structural and interpretive
   constraints.

3. **Allosemy and locality** (Ch. 2, Ch. 4): RSPs are always interpreted
   transparently (outside v's locality domain), while prefixes and particles
   can receive non-transparent interpretations (inside v's complex head).

## Architecture

- `Theories.Morphology.DM.Allosemy`: general framework + v/n/Voice allosemy
- `Core.Empirical`: Acceptability type
-/

namespace Phenomena.Morphology.Studies.Benz2025

open Morphology.DM.Allosemy
open Core.Empirical
open Fragments.German.Predicates
open Semantics.Tense.Aspect.LexicalAspect (VendlerClass)

-- ════════════════════════════════════════════════════════════════════
-- Part I: Content Nominalizations (Ch. 3)
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────
-- § 1. German Nominalization Data
-- ────────────────────────────────────────────────────

/-- A German nominalization datum with reading and diagnostic properties. -/
structure NominalizationDatum where
  /-- The nominalized form. -/
  form : String
  /-- Base verb. -/
  baseVerb : String
  /-- Nominalizing suffix. -/
  suffix : String := "-ung"
  /-- The reading exhibited in this example. -/
  reading : NominalizationReading
  /-- Example sentence. -/
  sentence : String
  /-- Translation. -/
  translation : String
  /-- Accepts temporal modifiers? -/
  temporalModifiers : Bool
  /-- Can be pluralized? -/
  pluralizable : Bool
  /-- Takes CP complement? -/
  takesCPComplement : Bool
  deriving Repr, BEq

/-- *Beobachtung* ('observation') — the running example in Ch. 3.
    All three readings are available for this single form. -/
def beobachtung_CEN : NominalizationDatum :=
  { form := "Beobachtung"
  , baseVerb := "beobachten"
  , reading := .complexEvent
  , sentence := "Die Beobachtung der Delfine dauerte drei Stunden"
  , translation := "The observation of the dolphins lasted three hours"
  , temporalModifiers := true
  , pluralizable := false
  , takesCPComplement := false }

def beobachtung_RN : NominalizationDatum :=
  { form := "Beobachtung"
  , baseVerb := "beobachten"
  , reading := .simpleEntity
  , sentence := "Die Beobachtungen der Astronomin sind verloren"
  , translation := "The astronomer's observations are lost"
  , temporalModifiers := false
  , pluralizable := true
  , takesCPComplement := false }

def beobachtung_CCN : NominalizationDatum :=
  { form := "Beobachtung"
  , baseVerb := "beobachten"
  , reading := .content
  , sentence := "Seine Beobachtung, dass Planeten sich bewegen, veränderte die Wissenschaft"
  , translation := "His observation that planets move changed science"
  , temporalModifiers := false
  , pluralizable := true
  , takesCPComplement := true }

def allBeobachtungReadings : List NominalizationDatum :=
  [beobachtung_CEN, beobachtung_RN, beobachtung_CCN]

/-- All three readings are attested for *Beobachtung*. -/
theorem beobachtung_three_readings :
    (allBeobachtungReadings.any (·.reading == .complexEvent)) = true ∧
    (allBeobachtungReadings.any (·.reading == .simpleEntity)) = true ∧
    (allBeobachtungReadings.any (·.reading == .content)) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ────────────────────────────────────────────────────
-- § 2. Diagnostic Properties
-- ────────────────────────────────────────────────────

/-- CENs accept temporal modifiers. -/
theorem cen_temporal : beobachtung_CEN.temporalModifiers = true := rfl

/-- RNs are pluralizable. -/
theorem rn_plural : beobachtung_RN.pluralizable = true := rfl

/-- CCNs take CP complements. -/
theorem ccn_cp : beobachtung_CCN.takesCPComplement = true := rfl

/-- CENs resist pluralization (event readings are mass-like). -/
theorem cen_no_plural : beobachtung_CEN.pluralizable = false := rfl

/-- RNs lack temporal modifiers. -/
theorem rn_no_temporal : beobachtung_RN.temporalModifiers = false := rfl

-- ────────────────────────────────────────────────────
-- § 3. Allosemy Derivation
-- ────────────────────────────────────────────────────

/-- Map each reading to its alloseme pair. -/
def readingAllosemePair : NominalizationReading → VAlloseme × NAlloseme
  | .complexEvent => (.eventive, .sortal)
  | .simpleEvent  => (.zero,    .simpleEvent)
  | .result       => (.eventive, .result)
  | .simpleState  => (.zero,    .state)
  | .simpleEntity => (.zero,    .sortal)
  | .content      => (.eventive, .content)

/-- The alloseme pair correctly derives each reading. -/
theorem alloseme_derivation_CEN :
    readingFromAllosemes (.eventive) (.sortal) = some .complexEvent := rfl

theorem alloseme_derivation_RN :
    readingFromAllosemes (.zero) (.sortal) = some .simpleEntity := rfl

theorem alloseme_derivation_CCN :
    readingFromAllosemes (.eventive) (.content) = some .content := rfl

/-- Round-trip: each reading maps to allosemes that reconstruct it. -/
theorem alloseme_roundtrip (r : NominalizationReading) :
    let (v, n) := readingAllosemePair r
    readingFromAllosemes v n = some r := by
  cases r <;> rfl

/-- The impossible combination: zero v + content n yields no reading.
    Content requires an underlying event. -/
theorem zero_content_impossible :
    readingFromAllosemes .zero .content = none := rfl

/-- CEN and simple entity RN are "mirror images" of the division of
    semantic labor: in CEN, v does the work (introducing the event
    variable) while n merely nominalizes; in simple entity RN, v is null
    (zero) and the referential/object interpretation comes from the
    nominalization context. Both use the same n alloseme (sortal) —
    it's v that varies. -/
theorem cen_simpleEntity_mirror :
    (readingAllosemePair .complexEvent).1 = .eventive ∧
    (readingAllosemePair .simpleEntity).1 = .zero ∧
    (readingAllosemePair .complexEvent).2 = .sortal ∧
    (readingAllosemePair .simpleEntity).2 = .sortal := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════
-- Part II: Prefixes, Particles, and Resultatives (Ch. 4)
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────
-- § 4. German Preverbal Element Typology
-- ────────────────────────────────────────────────────

/-- The three types of German preverbal elements.

    Ch. 4: prefixes are inseparable and attach as heads;
    particles are separable and attach as phrases; RSPs are adjectival
    phrases that form complex predicates with the verb. -/
inductive PreverbalElement where
  | pfx  -- inseparable prefix (be-, ent-, er-, ge-, miss-, ver-, zer-)
  | prt  -- separable particle (ab-, an-, auf-, aus-, ein-, los-, nach-, vor-, zu-, ...)
  | rsp  -- resultative secondary predicate (platt, tot, kaputt, ...)
  deriving DecidableEq, BEq, Repr

/-- Syntactic status: head or phrase.

    §4.3.1: following Wurmbrand (1998) and Zeller (2001a),
    prefixes are heads (inseparable under V2 movement) while particles
    are phrases (obligatorily stranded under V2). RSPs are unambiguously
    phrasal (they can be modified: *total flach gehämmert*). -/
def PreverbalElement.isHead : PreverbalElement → Bool
  | .pfx => true
  | .prt => false
  | .rsp => false

/-- Does this element always specify a result state that conflicts with
    other delimiters?

    §4.1: prefixes and RSPs always contribute a
    (potentially conflicting) result state specification. Particles
    can have non-delimiting readings (directional, completive) that
    don't necessarily conflict — this is why PRT-pfx combinations
    like *aus-er-wählen* are interpretively acceptable. -/
def PreverbalElement.alwaysSpecifiesResult : PreverbalElement → Bool
  | .pfx => true
  | .prt => false
  | .rsp => true

-- ────────────────────────────────────────────────────
-- § 5. Prefix and Particle Inventory (Table 4)
-- ────────────────────────────────────────────────────

/-- German inseparable prefixes (closed class).

    Table 4. The prefix *ge-* is the rare
    non-participial prefix (as in *ge-bären*, *ge-denken*). -/
def inseparablePrefixes : List String :=
  ["be", "ent", "er", "ge", "miss", "ver", "zer"]

/-- German separable particles (open class, representative sample).

    Table 4. Elements like durch-, über-, um-
    are ambiguous between prefix and particle uses. -/
def separableParticles : List String :=
  ["ab", "an", "auf", "aus", "bei", "ein", "los", "nach", "vor", "zu"]

/-- Ambiguous preverbal elements: prefix or particle depending on verb. -/
def ambiguousElements : List String :=
  ["durch", "hinter", "über", "um", "unter", "wider"]

-- ────────────────────────────────────────────────────
-- § 6. Co-occurrence Restrictions (Table 3)
-- ────────────────────────────────────────────────────

/-- A co-occurrence pair: two preverbal elements in order (outer, inner),
    where the inner element is closer to the root. -/
structure CooccurrenceDatum where
  outer : PreverbalElement
  inner : PreverbalElement
  allowed : Bool
  /-- Structure (head/phrase) predicts this restriction? -/
  structurePredicts : Bool
  /-- Interpretation (delimitation) predicts this restriction? -/
  interpretationPredicts : Bool
  exampleStr : String
  deriving Repr, BEq

/-- The full co-occurrence paradigm from Table 3. -/
def cooccurrenceTable : List CooccurrenceDatum := [
  -- pfx-pfx: *ent-ver-trauen. Structure allows (two heads), but
  -- double delimitation blocks.
  { outer := .pfx, inner := .pfx
  , allowed := false
  , structurePredicts := true
  , interpretationPredicts := false
  , exampleStr := "*ent-ver-trauen (intended: stop trusting)" },
  -- pfx-PRT: *zer-ab-schneiden. Head cannot wrap phrase.
  { outer := .pfx, inner := .prt
  , allowed := false
  , structurePredicts := false
  , interpretationPredicts := true
  , exampleStr := "*zer-ab-schneiden (intended: cut off into strips)" },
  -- PRT-pfx: aus-er-wählen. THE productive combination.
  { outer := .prt, inner := .pfx
  , allowed := true
  , structurePredicts := true
  , interpretationPredicts := true
  , exampleStr := "aus-er-wählen (choose, cf. er-wählen 'pick')" },
  -- PRT-PRT: *rad-ein-fahren. Two phrases cannot stack.
  { outer := .prt, inner := .prt
  , allowed := false
  , structurePredicts := false
  , interpretationPredicts := true
  , exampleStr := "*rad-ein-fahren (intended: ride in on a bike)" },
  -- RSP-pfx: *arm be-raubt. Structure allows (phrase + head),
  -- but double delimitation blocks.
  { outer := .rsp, inner := .pfx
  , allowed := false
  , structurePredicts := true
  , interpretationPredicts := false
  , exampleStr := "*arm be-raubt (intended: robbed poor)" },
  -- RSP-PRT: *nass an-gespuckt. Two phrasal elements cannot stack.
  { outer := .rsp, inner := .prt
  , allowed := false
  , structurePredicts := false
  , interpretationPredicts := true
  , exampleStr := "*nass an-gespuckt (intended: spat at wet)" },
  -- RSP-RSP: *kaputt müde gearbeitet. Both factors block.
  { outer := .rsp, inner := .rsp
  , allowed := false
  , structurePredicts := false
  , interpretationPredicts := false
  , exampleStr := "*kaputt müde gearbeitet (intended: worked to exhaustion)" },
  -- pfx-RSP: head cannot wrap phrase, and double delimitation.
  { outer := .pfx, inner := .rsp
  , allowed := false
  , structurePredicts := false
  , interpretationPredicts := false
  , exampleStr := "*ver-platt-hämmern (blocked in all orders)" },
  -- PRT-RSP: two phrases cannot stack. PRT doesn't always delimit,
  -- so interpretation alone would allow it, but structure blocks.
  { outer := .prt, inner := .rsp
  , allowed := false
  , structurePredicts := false
  , interpretationPredicts := true
  , exampleStr := "*an-wach-küssen (intended: kiss awake at)" }
]

-- ────────────────────────────────────────────────────
-- § 7. Structural Prediction: Head/Phrase Compatibility
-- ────────────────────────────────────────────────────

/-- Structural compatibility: phrase can take headed complement; two heads
    can combine; head cannot wrap phrase; two phrases cannot stack.

    §4.3.1, §4.4. -/
def structurallyCompatible (outer inner : PreverbalElement) : Bool :=
  match outer.isHead, inner.isHead with
  | true,  true  => true   -- head + head
  | false, true  => true   -- phrase + head
  | true,  false => false  -- head cannot wrap phrase
  | false, false => false  -- phrases cannot stack

/-- The structural prediction matches Table 3's "Structure Predicts" column. -/
theorem structural_prediction_matches :
    cooccurrenceTable.map (λ d => structurallyCompatible d.outer d.inner) =
    cooccurrenceTable.map (λ d => d.structurePredicts) := by native_decide

-- ────────────────────────────────────────────────────
-- § 8. Interpretive Prediction: Result State Conflict
-- ────────────────────────────────────────────────────

/-- Two elements that both always specify a result state cannot co-occur,
    as a single event cannot be delimited twice with conflicting endpoints.

    §4.1: the interpretive constraint is about conflicting
    result state specifications. Particles escape this because they can
    have non-result (directional/completive) readings. -/
def interpretivelyCompatible (outer inner : PreverbalElement) : Bool :=
  !(outer.alwaysSpecifiesResult && inner.alwaysSpecifiesResult)

/-- The interpretive prediction matches Table 3's "Interpretation Predicts" column. -/
theorem interpretive_prediction_matches :
    cooccurrenceTable.map (λ d => interpretivelyCompatible d.outer d.inner) =
    cooccurrenceTable.map (λ d => d.interpretationPredicts) := by native_decide

-- ────────────────────────────────────────────────────
-- § 9. Combined Prediction
-- ────────────────────────────────────────────────────

/-- A combination is allowed iff both structurally compatible AND
    interpretively compatible (no conflicting result states).

    §4.4: both factors are needed; neither alone
    explains the full paradigm. -/
def predictedAllowed (outer inner : PreverbalElement) : Bool :=
  structurallyCompatible outer inner && interpretivelyCompatible outer inner

/-- The combined prediction matches Table 3's "Allowed" column. -/
theorem combined_prediction_matches :
    cooccurrenceTable.map (λ d => predictedAllowed d.outer d.inner) =
    cooccurrenceTable.map (λ d => d.allowed) := by native_decide

/-- PRT-pfx is the unique allowed combination. -/
theorem prt_pfx_uniquely_allowed :
    (cooccurrenceTable.filter (·.allowed)).length = 1 := by native_decide

-- ────────────────────────────────────────────────────
-- § 10. German Resultative Data (§4.2)
-- ────────────────────────────────────────────────────

/-- A German resultative datum with gloss and judgment. -/
structure GermanResultativeDatum where
  sentence : String
  gloss : String
  translation : String
  judgment : Acceptability
  verbClass : String
  deriving Repr, BEq

/-- German RSP data from §4.2.

    German allows obligatorily transitive, unaccusative, and inherently
    reflexive M predicates in resultatives — not just unergatives. -/
def germanRSPData : List GermanResultativeDatum := [
  { sentence := "Er hämmerte das Metall platt"
  , gloss := "he hammered the.ACC metal flat"
  , translation := "He hammered the metal flat"
  , judgment := .ok
  , verbClass := "transitive" },
  { sentence := "Er schießt seinen Gegner tot"
  , gloss := "he shoots his.ACC opponent dead"
  , translation := "He shoots his opponent dead"
  , judgment := .ok
  , verbClass := "transitive" },
  { sentence := "Hans hat den Stock kaputt gebrochen"
  , gloss := "Hans has the.ACC stick broken broken.PTCP"
  , translation := "Hans broke the stick"
  , judgment := .ok
  , verbClass := "obligatorily transitive" },
  { sentence := "Das Wasser fror fest"
  , gloss := "the.NOM water froze solid"
  , translation := "The water froze solid"
  , judgment := .ok
  , verbClass := "unaccusative" },
  { sentence := "Sie haben sich krank/tot geschämt"
  , gloss := "they have REFL sick/dead shamed.PTCP"
  , translation := "They were embarrassed sick/dead"
  , judgment := .ok
  , verbClass := "inherently reflexive" }
]

/-- German allows non-unergative M predicates in resultatives. -/
theorem german_allows_non_unergative_M :
    (germanRSPData.any (·.verbClass == "obligatorily transitive")) = true ∧
    (germanRSPData.any (·.verbClass == "unaccusative")) = true ∧
    (germanRSPData.any (·.verbClass == "inherently reflexive")) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ────────────────────────────────────────────────────
-- § 11. RSP Co-occurrence Restriction Data (§4.1)
-- ────────────────────────────────────────────────────

/-- RSPs are incompatible with prefixed verbs.
    Ch. 4: adding an RSP to a prefix verb is ungrammatical,
    but the same RSP with the simplex verb is fine. -/
def rsp_pfx_contrasts : List (GermanResultativeDatum × GermanResultativeDatum) := [
  ( { sentence := "*Sie haben uns arm be-raubt"
    , gloss := "they have us.ACC poor BE-robbed.PTCP"
    , translation := "They robbed us poor"
    , judgment := .unacceptable
    , verbClass := "prefix verb (be-)" },
    { sentence := "Sie haben uns arm geraubt"
    , gloss := "they have us.ACC poor robbed.PTCP"
    , translation := "They robbed us poor"
    , judgment := .ok
    , verbClass := "simplex verb" } ),
  ( { sentence := "*Sie haben ihn tot er-schossen"
    , gloss := "they have him.ACC dead ER-shot.PTCP"
    , translation := "They shot him dead"
    , judgment := .unacceptable
    , verbClass := "prefix verb (er-)" },
    { sentence := "Sie haben ihn tot geschossen"
    , gloss := "they have him.ACC dead shot.PTCP"
    , translation := "They shot him dead"
    , judgment := .ok
    , verbClass := "simplex verb" } ),
  ( { sentence := "*Hans hat den Stock kaputt zer-brochen"
    , gloss := "Hans has the.ACC stick broken ZER-broken.PTCP"
    , translation := "Hans broke the stick broken"
    , judgment := .unacceptable
    , verbClass := "prefix verb (zer-)" },
    { sentence := "Hans hat den Stock kaputt gebrochen"
    , gloss := "Hans has the.ACC stick broken.ADJ broken.PTCP"
    , translation := "Hans broke the stick broken"
    , judgment := .ok
    , verbClass := "simplex verb" } )
]

/-- Every RSP+pfx-verb contrast: pfx-verb ungrammatical, simplex OK. -/
theorem rsp_pfx_contrast_pattern :
    rsp_pfx_contrasts.all (fun (bad, good) =>
      bad.judgment == .unacceptable && good.judgment == .ok) = true := by
  native_decide

/-- RSPs are also incompatible with particles.
    Ch. 4: adding an RSP to a particle verb is ungrammatical,
    but the same RSP with the simplex verb is fine. -/
def rsp_prt_contrasts : List (GermanResultativeDatum × GermanResultativeDatum) := [
  ( { sentence := "*Sie hat den Tisch trocken ab-gewischt"
    , gloss := "she has the.ACC table dry AB-wiped.PTCP"
    , translation := "She wiped the table off dry"
    , judgment := .unacceptable
    , verbClass := "particle verb (ab-)" },
    { sentence := "Sie hat den Tisch trocken gewischt"
    , gloss := "she has the.ACC table dry wiped.PTCP"
    , translation := "She wiped the table dry"
    , judgment := .ok
    , verbClass := "simplex verb" } ),
  ( { sentence := "*Das Baby hat mich nass an-gespuckt"
    , gloss := "the baby has me.ACC wet AN-spit.PTCP"
    , translation := "The baby spat up on me and I was wet"
    , judgment := .unacceptable
    , verbClass := "particle verb (an-)" },
    { sentence := "Das Baby hat mich nass gespuckt"
    , gloss := "the baby has me.ACC wet spit.PTCP"
    , translation := "The baby spat up on me"
    , judgment := .ok
    , verbClass := "simplex verb" } )
]

/-- Every RSP+PRT-verb contrast: PRT-verb ungrammatical, simplex OK. -/
theorem rsp_prt_contrast_pattern :
    rsp_prt_contrasts.all (fun (bad, good) =>
      bad.judgment == .unacceptable && good.judgment == .ok) = true := by
  native_decide

-- ════════════════════════════════════════════════════════════════════
-- Part III: Allosemy and Locality (Ch. 2, Ch. 4)
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────
-- § 12. Interpretive Transparency
-- ────────────────────────────────────────────────────

/-- Claim 2: RSPs are always transparent (outside v's
    locality domain for allosemy); prefixes and particles can be opaque
    (inside the complex head). -/
inductive InterpretiveTransparency where
  | transparent
  | nonTransparent
  deriving DecidableEq, BEq, Repr

def typicalTransparency : PreverbalElement → InterpretiveTransparency
  | .rsp => .transparent
  | .pfx => .nonTransparent
  | .prt => .nonTransparent

theorem rsp_always_transparent :
    typicalTransparency .rsp = .transparent := rfl

-- ────────────────────────────────────────────────────
-- § 13. Means/End Event Decomposition (§4.2)
-- ────────────────────────────────────────────────────

/-! ### Complex predicate semantics

Following Williams (2015), adopted by §4.2:
resultatives are complex predicates with semantics:

    K(e₁, e₂, s) = Means(e₁, e₂) & End(e₁, s)

where e₁ is the complex event of change, e₂ is the means/manner
subevent, and s is the result state. The M predicate is the verb;
the R predicate is the RSP. This is NOT a causal relation — the
means event can be concurrent with the change.

The End Theme Postulate links the Theme of the complex event to the
end state: End(e₁, s) & Theme(e₁, x) |= Theme(s, x).

See also `Causative.Resultatives` for the complementary analysis
via causal dynamics, structural sufficiency, and CC-selection. -/

-- ────────────────────────────────────────────────────
-- § 14. Central Claims
-- ────────────────────────────────────────────────────

/-- **Claim 1**: Neither factor alone predicts the full co-occurrence paradigm.
    Structure alone is insufficient: some structurally OK combinations are
    blocked by interpretation (pfx-pfx, RSP-pfx).
    Interpretation alone is insufficient: some interpretively OK combinations
    are blocked by structure (pfx-PRT, PRT-PRT, RSP-PRT). -/
theorem claim1_two_factors :
    -- Structure alone is insufficient
    (cooccurrenceTable.any (λ d =>
      d.structurePredicts && !d.interpretationPredicts && !d.allowed)) = true ∧
    -- Interpretation alone is insufficient
    (cooccurrenceTable.any (λ d =>
      d.interpretationPredicts && !d.structurePredicts && !d.allowed)) = true := by
  constructor <;> native_decide

-- ════════════════════════════════════════════════════════════════════
-- Part IV: Prefixes in Nominalizations (Ch. 5)
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────
-- § 15. Nominalization Type Inventory
-- ────────────────────────────────────────────────────

/-- German nominalization types discussed in Ch. 5.

    - **ung**: *-ung* suffixation (*Beobachtung*, *Erzählung*). Requires
      the verb to project a full verbal shell including v; the entire
      vP is nominalized by n.
    - **ge_e**: *Ge-...-e* circumfixation (*Gerede*, *Gelaufe*). Directly
      nominalizes the root without a full verbal projection; the root
      must be able to stand without obligatory internal arguments.
    - **nomInfinitive**: Nominalized infinitive (*das Beobachten*,
      *das Erzählen*). The most permissive: the full verbal structure
      is preserved under nominalization. -/
inductive NominalizationType where
  | ung           -- -ung suffixation
  | ge_e          -- Ge-...-e circumfixation
  | nomInfinitive -- nominalized infinitive (das V-en)
  deriving DecidableEq, BEq, Repr

-- ────────────────────────────────────────────────────
-- § 16. PE Acceptability across Nominalization Types
-- ────────────────────────────────────────────────────

/-- Whether a preverbal element is acceptable in a given nominalization type.

    Ch. 5: the distribution of preverbal elements across
    nominalization types reveals complementary distribution between prefixes
    and RSPs:

    |             | pfx | prt | RSP |
    |-------------|-----|-----|-----|
    | -ung        |  ✓  |  ✓  |  ✗  |
    | Ge-...-e    |  ✗  |  ✓  |  ✓  |
    | nom. inf.   |  ✓  |  ✓  |  ✓  |

    - **-ung + RSP = ✗**: RSPs are phrasal and cannot be trapped inside the
      complex head that -ung nominalization creates. The RSP would need to
      be inside the vP that n selects, but as a phrase it cannot incorporate.
    - **Ge-...-e + pfx = ✗**: Ge-...-e directly nominalizes the root; it
      requires the root to be available without obligatory internal arguments.
      Prefixed verbs (where the prefix saturates argument structure) are
      incompatible because the prefix has already formed a complex head with
      the root, and the Ge-...-e circumfix cannot wrap around a complex head.
    - **Nom. inf.**: maximally permissive because the full verbal projection
      (including any preverbal element) is preserved under nominalization. -/
def peAcceptable : NominalizationType → PreverbalElement → Bool
  | .ung,           .pfx => true
  | .ung,           .prt => true
  | .ung,           .rsp => false
  | .ge_e,          .pfx => false
  | .ge_e,          .prt => true
  | .ge_e,          .rsp => true
  | .nomInfinitive, _    => true

-- ────────────────────────────────────────────────────
-- § 17. Complementary Distribution Theorems
-- ────────────────────────────────────────────────────

/-- Prefixes and RSPs show complementary distribution across -ung and Ge-...-e:
    pfx is accepted where RSP is rejected, and vice versa.

    Ch. 5: this complementarity follows from the structural
    difference between head-level (pfx) and phrase-level (RSP) preverbal
    elements, interacting with the different structural requirements of
    -ung (requires full vP) vs Ge-...-e (directly nominalizes root). -/
theorem pfx_rsp_complementary_ung_ge :
    peAcceptable .ung .pfx = true ∧ peAcceptable .ung .rsp = false ∧
    peAcceptable .ge_e .pfx = false ∧ peAcceptable .ge_e .rsp = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Particles are accepted in both -ung and Ge-...-e: they are structurally
    flexible enough to appear in both configurations. -/
theorem prt_accepted_in_both :
    peAcceptable .ung .prt = true ∧ peAcceptable .ge_e .prt = true := by
  exact ⟨rfl, rfl⟩

/-- Nominalized infinitives accept all three PE types. -/
theorem nom_inf_maximally_permissive (pe : PreverbalElement) :
    peAcceptable .nomInfinitive pe = true := by
  cases pe <;> rfl

/-- RSPs are blocked in -ung nominalizations — this connects to the
    co-occurrence restriction: RSPs as phrases cannot incorporate into
    the complex head structure that -ung creates. -/
theorem rsp_blocked_in_ung : peAcceptable .ung .rsp = false := rfl

/-- Prefixes are blocked in Ge-...-e nominalizations — the circumfix
    cannot wrap around a root that already has a prefix head. -/
theorem pfx_blocked_in_ge_e : peAcceptable .ge_e .pfx = false := rfl

/-- The head/phrase distinction predicts the -ung pattern:
    heads (pfx) are accepted, phrases (rsp) are not.
    Particles are the exception — separable but still accepted. -/
theorem ung_head_phrase_pattern :
    (peAcceptable .ung .pfx = PreverbalElement.pfx.isHead) ∧
    (peAcceptable .ung .rsp = PreverbalElement.rsp.isHead) := by
  exact ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════
-- Part V: Principled Derivation of the Co-occurrence Paradigm
-- ════════════════════════════════════════════════════════════════════

/-! ### Benz's core theoretical argument (Chs. 4–5)

central claim is that the 9-cell co-occurrence paradigm
(§6, Table 3) and the PE×nominalization distribution (§16, the table in
Ch. 5) are not stipulated — they follow from the conjunction of two
independently motivated principles:

1. **Lexical Integrity** (structural): a phrase cannot incorporate into a
   head. Only head+head or phrase+head are licit; head+phrase and
   phrase+phrase are not.

2. **Result State Uniqueness** (interpretive): an event can have at most
   one telos. Two elements that both obligatorily specify a result state
   cannot co-occur.

The types `SynLevel` and `ResultStateSpec` below formalize these two
dimensions abstractly. The compatibility functions `incorporationAllowed`
and `resultStatesCompatible` are defined purely over these abstract types,
with no reference to `PreverbalElement`. Only then do we classify each PE
into these dimensions and prove that the predicted paradigm matches. -/

-- ────────────────────────────────────────────────────
-- § 18. Abstract Structural Dimension: Syntactic Level
-- ────────────────────────────────────────────────────

/-- The syntactic level of a morphological element: head (X⁰) or phrase (XP).

    This distinction is standard in X-bar theory and is logically prior to
    the PE typology — it applies to any syntactic object, not just German
    preverbal elements. -/
inductive SynLevel where
  | head    -- X⁰: can incorporate into other heads
  | phrase  -- XP: cannot incorporate
  deriving DecidableEq, BEq, Repr

/-- **Lexical Integrity**: a head can take a head complement (head-adjunction
    / incorporation), and a phrase can take a head complement (normal
    complementation), but a head cannot take a phrase complement in a
    word-internal structure, and two phrases cannot form a word.

    This is a general principle of morphosyntactic structure, not specific
    to German preverbal elements. It follows from the ban on phrasal
    incorporation (§4.3.1, following Baker 1988). -/
def incorporationAllowed (outer inner : SynLevel) : Bool :=
  match outer, inner with
  | .head,   .head   => true   -- incorporation / head-adjunction
  | .phrase, .head   => true   -- normal complementation
  | .head,   .phrase => false  -- *phrasal incorporation
  | .phrase, .phrase => false  -- *phrase stacking inside a word

-- ────────────────────────────────────────────────────
-- § 19. Abstract Interpretive Dimension: Result State Specification
-- ────────────────────────────────────────────────────

/-- Whether an element obligatorily introduces a result state specification.

    This is a semantic property that applies to any predicate-modifying
    element — it is not specific to German PEs. An element that always
    specifies a result state will conflict with another such element
    because a single event has at most one telos. -/
inductive ResultStateSpec where
  | specifies  -- obligatorily introduces a result state
  | neutral    -- compatible with either (e.g. directional/completive readings)
  deriving DecidableEq, BEq, Repr

/-- **Result State Uniqueness**: two elements that both obligatorily specify
    a result state cannot co-occur, because a single event cannot be
    delimited by two conflicting endpoints.

    This is an instance of a general thematic uniqueness constraint: just as
    an event has at most one agent (Carlson 1998), it has at most one telos.
    The constraint is purely interpretive — it says nothing about syntax. -/
def resultStatesCompatible (a b : ResultStateSpec) : Bool :=
  match a, b with
  | .specifies, .specifies => false  -- conflicting result states
  | _, _ => true

-- ────────────────────────────────────────────────────
-- § 20. PE Classification into Abstract Dimensions
-- ────────────────────────────────────────────────────

/-- Classify each PE by its syntactic level.

    §4.3.1: prefixes are heads (inseparable under V2);
    particles and RSPs are phrases (stranded under V2, can be modified). -/
def PreverbalElement.synLevel : PreverbalElement → SynLevel
  | .pfx => .head
  | .prt => .phrase
  | .rsp => .phrase

/-- Classify each PE by its result state specification.

    §4.1: prefixes and RSPs obligatorily specify a result
    state. Particles are neutral — they can have non-delimiting readings
    (directional, completive) that do not introduce a result state. -/
def PreverbalElement.resultSpec : PreverbalElement → ResultStateSpec
  | .pfx => .specifies
  | .prt => .neutral
  | .rsp => .specifies

-- ────────────────────────────────────────────────────
-- § 21. Bridge: Abstract Classification Matches PE Booleans
-- ────────────────────────────────────────────────────

/-- The abstract `synLevel` classification is equivalent to `isHead`. -/
theorem synLevel_matches_isHead (pe : PreverbalElement) :
    (pe.synLevel == .head) = pe.isHead := by
  cases pe <;> rfl

/-- The abstract `resultSpec` classification is equivalent to
    `alwaysSpecifiesResult`. -/
theorem resultSpec_matches_alwaysSpecifies (pe : PreverbalElement) :
    (pe.resultSpec == .specifies) = pe.alwaysSpecifiesResult := by
  cases pe <;> rfl

-- ────────────────────────────────────────────────────
-- § 22. Blocking Derivations
-- ────────────────────────────────────────────────────

/-- A blocking derivation: a proof that a PE combination violates one of
    Benz's two independently motivated principles.

    Each constructor is a derivation rule whose premises are stated in terms
    of the abstract classification (`SynLevel`, `ResultStateSpec`), not
    PE-specific Booleans. A combination is blocked iff at least one
    derivation can be constructed.

    **`byLexicalIntegrity`** (§4.3.1, Baker 1988): only
    heads can occupy the inner (closer-to-root) position in a word-internal
    combination. A phrasal inner element cannot incorporate.

    **`byResultUniqueness`** (§4.1): an event has at most
    one telos. Two elements that both obligatorily specify a result state
    yield conflicting endpoints. -/
inductive Blocked : PreverbalElement → PreverbalElement → Prop where
  | byLexicalIntegrity {o i : PreverbalElement} :
      i.synLevel = .phrase → Blocked o i
  | byResultUniqueness {o i : PreverbalElement} :
      o.resultSpec = .specifies → i.resultSpec = .specifies → Blocked o i

/-- Boolean decomposition lemma: `predictedAllowed` factors into the
    conjunction of the two abstract compatibility functions. Used as a
    stepping stone in the soundness proof below. -/
theorem paradigm_from_principles (o i : PreverbalElement) :
    predictedAllowed o i =
      (incorporationAllowed o.synLevel i.synLevel &&
       resultStatesCompatible o.resultSpec i.resultSpec) := by
  cases o <;> cases i <;> rfl

-- ────────────────────────────────────────────────────
-- § 23. Characterization Theorem
-- ────────────────────────────────────────────────────

/-! The derivation system (`Blocked`) is both *sound* and *complete* with
respect to the empirical paradigm (`predictedAllowed`). Together with
`combined_prediction_matches` (§9), this means the two principles exactly
generate the data: every blocked cell has a derivation, every derivation
corresponds to a blocked cell, and the unique allowed cell (PRT-pfx) has
no derivation. -/

/-- **Soundness**: every blocking derivation corresponds to a genuinely
    blocked combination. The theory does not over-generate.

    - `byLexicalIntegrity`: a phrasal inner element makes `incorporationAllowed`
      return `false` regardless of the outer element's level.
    - `byResultUniqueness`: two result-specifying elements make
      `resultStatesCompatible` return `false` regardless of structure. -/
theorem blocked_sound {o i : PreverbalElement} (h : Blocked o i) :
    predictedAllowed o i = false := by
  rw [paradigm_from_principles]
  cases h with
  | byLexicalIntegrity hi =>
    have : incorporationAllowed o.synLevel i.synLevel = false := by
      rw [hi]; cases o <;> rfl
    simp [this]
  | byResultUniqueness ho hi =>
    have : resultStatesCompatible o.resultSpec i.resultSpec = false := by
      rw [ho, hi]; rfl
    simp [this]

/-- **Completeness**: every blocked combination has a blocking derivation.
    The two principles account for ALL restrictions — nothing is left
    unexplained.

    For each of the 8 blocked cells, an explicit derivation is constructed
    (6 by Lexical Integrity, 2 by Result State Uniqueness). For PRT-pfx,
    the hypothesis is contradictory. -/
theorem blocked_complete {o i : PreverbalElement}
    (h : predictedAllowed o i = false) : Blocked o i := by
  cases o <;> cases i <;>
    first
    | exact .byLexicalIntegrity rfl
    | exact .byResultUniqueness rfl rfl
    | simp [predictedAllowed, structurallyCompatible, interpretivelyCompatible,
            PreverbalElement.isHead, PreverbalElement.alwaysSpecifiesResult] at h

/-- **The allowed combination has no derivation.** PRT-pfx is allowed
    precisely because neither principle applies:
    - pfx is a head (not a phrase), so Lexical Integrity is satisfied
    - prt is result-neutral (not specifying), so Result Uniqueness is satisfied

    We examine each possible derivation and show its premises are
    contradicted by the PE classifications. -/
theorem prt_pfx_no_derivation : ¬ Blocked .prt .pfx := by
  intro h
  cases h with
  | byLexicalIntegrity hi => exact absurd hi (by decide)
  | byResultUniqueness ho _ => exact absurd ho (by decide)

-- ────────────────────────────────────────────────────
-- § 24. Both Derivation Rules Are Needed
-- ────────────────────────────────────────────────────

/-- pfx-pfx is blocked ONLY by Result State Uniqueness — Lexical Integrity
    cannot derive it (both are heads, so the inner is not phrasal). This
    shows the interpretive rule is not redundant. -/
theorem pfx_pfx_only_by_result :
    Blocked .pfx .pfx ∧ PreverbalElement.pfx.synLevel ≠ .phrase :=
  ⟨.byResultUniqueness rfl rfl, by decide⟩

/-- pfx-PRT is blocked ONLY by Lexical Integrity — Result State Uniqueness
    cannot derive it (PRT is result-neutral). This shows the structural
    rule is not redundant. -/
theorem pfx_prt_only_by_structure :
    Blocked .pfx .prt ∧ PreverbalElement.prt.resultSpec ≠ .specifies :=
  ⟨.byLexicalIntegrity rfl, by decide⟩

/-- Incorporation depends only on the inner element's level: the outer
    element's level is irrelevant. This is a derived property of the
    `incorporationAllowed` function, not stipulated. -/
theorem incorporation_only_depends_on_inner (outer inner : SynLevel) :
    incorporationAllowed outer inner = (inner == .head) := by
  cases outer <;> cases inner <;> rfl

-- ────────────────────────────────────────────────────
-- § 24. Ch. 5 Nominalization Distribution from Principles
-- ────────────────────────────────────────────────────

/-- **The nominalization theorem.** *-ung* acceptability (Ch. 5) follows from
    the same two abstract principles applied reflexively: a PE is acceptable
    in *-ung* iff it can incorporate with itself (headedness) OR its result
    state does not conflict with itself (neutrality).

    This connects Ch. 5 to Ch. 4: the PE×nominalization distribution is not
    an independent observation — it is a projection of the same two principles
    that generate the co-occurrence paradigm. -/
theorem ung_from_principles (pe : PreverbalElement) :
    peAcceptable .ung pe =
      (incorporationAllowed pe.synLevel pe.synLevel ||
       resultStatesCompatible pe.resultSpec pe.resultSpec) := by
  cases pe <;> rfl

/-- *Ge-...-e* acceptability reduces to a single abstract principle:
    a PE is acceptable in *Ge-...-e* iff it is a phrase (not a head).
    The circumfix directly nominalizes the root, so only non-head elements
    are compatible. -/
theorem ge_e_from_principles (pe : PreverbalElement) :
    peAcceptable .ge_e pe = (pe.synLevel == .phrase) := by
  cases pe <;> rfl

/-- The *-ung* / *Ge-...-e* mirror: for heads, the two nominalization types
    give opposite results. This follows from `ge_e_from_principles` and the
    fact that heads satisfy `incorporationAllowed` reflexively. -/
theorem ung_ge_e_mirror (pe : PreverbalElement) (h : pe.synLevel = .head) :
    peAcceptable .ung pe = true ∧ peAcceptable .ge_e pe = false := by
  cases pe <;> simp_all [PreverbalElement.synLevel, peAcceptable]

-- ────────────────────────────────────────────────────
-- § 25. End-to-End: Root Semantics → v Allosemy → Nominalization → PE
-- ────────────────────────────────────────────────────

/-! These theorems chain through four independently defined modules:
`RootTypology.lean` (root semantics) → `Allosemy.lean` (v alloseme
selection) → `Allosemy.lean` (nominalization reading) → `Benz2025.lean`
(PE distribution from abstract principles). No single module defines
the full path. -/

/-- End-to-end for result roots: a result root selects eventive v, yielding
    CEN in *-ung* nominalizations. *-ung* accepts heads (pfx) and rejects
    phrases that specify results (RSP) — both predictions derived from
    the abstract principles, not from the `peAcceptable` table. -/
theorem end_to_end_result_root :
    let v := VAlloseme.fromRootType .result
    v = .eventive ∧
    readingFromAllosemes v .sortal = some .complexEvent ∧
    -- PE distribution derived from principles, not table lookup
    incorporationAllowed (PreverbalElement.pfx).synLevel (PreverbalElement.pfx).synLevel = true ∧
    resultStatesCompatible (PreverbalElement.rsp).resultSpec (PreverbalElement.rsp).resultSpec = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Mirror chain for PC roots: zero v → simple entity reading → *Ge-...-e*,
    which accepts phrases (RSP) and rejects heads (pfx). -/
theorem end_to_end_pc_root :
    let v := VAlloseme.fromRootType .propertyConcept
    v = .zero ∧
    readingFromAllosemes v .sortal = some .simpleEntity ∧
    -- Ge-...-e distribution: phrase (RSP) accepted, head (pfx) rejected
    ((PreverbalElement.rsp).synLevel == .phrase) = true ∧
    ((PreverbalElement.pfx).synLevel == .phrase) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════
-- Part VI: Fragment Grounding
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────
-- § 21. -ung Nominalizability (Event Structure)
-- ────────────────────────────────────────────────────

/-- Whether a verb can undergo *-ung* nominalization, based on its
    Vendler class.

    Ch. 5, following Roßdeutscher & Kamp (2010):
    *-ung* requires complex change-of-state event structure. Only
    accomplishments and achievements (which contain a result state
    component) qualify. Activities and states do not. -/
def canUngNominalize : Option VendlerClass → Bool
  | some .accomplishment => true
  | some .achievement => true
  | _ => false

/-- Activity simplex verbs cannot form *-ung* nominalizations:
    **Hämmer-ung*, **Mal-ung*, **Küss-ung*. -/
theorem activity_no_ung :
    canUngNominalize haemmern.vendlerClass = false ∧
    canUngNominalize malen.vendlerClass = false ∧
    canUngNominalize kuessen.vendlerClass = false ∧
    canUngNominalize fuehren.vendlerClass = false ∧
    canUngNominalize rauben.vendlerClass = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Prefix/particle verbs with complex event structure CAN form
    *-ung* nominalizations: *Beobacht-ung*, *Einführ-ung*, *Verbind-ung*. -/
theorem complex_event_ung :
    canUngNominalize beobachten.vendlerClass = true ∧
    canUngNominalize einfuehren.vendlerClass = true ∧
    canUngNominalize verbinden.vendlerClass = true ∧
    canUngNominalize brechen.vendlerClass = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

-- ────────────────────────────────────────────────────
-- § 22. Fragment Entries Ground RSP Data
-- ────────────────────────────────────────────────────

/-- Transitivity derived from fragment fields (not from a raw string). -/
def isTransitiveVerb (v : GermanVerbEntry) : Bool :=
  v.complementType == .np && !v.unaccusative

/-- The verb classifications in the RSP data (§10, encoded as raw strings)
    are derivable from the fragment entries' typed fields. Changing
    *frieren*'s `unaccusative` field or *hämmern*'s `complementType` would
    break this theorem without touching the RSP data. -/
theorem rsp_data_grounded_in_fragments :
    isTransitiveVerb haemmern = true ∧
    isTransitiveVerb brechen = true ∧
    frieren.unaccusative = true ∧
    isTransitiveVerb frieren = false := ⟨rfl, rfl, rfl, rfl⟩

-- ────────────────────────────────────────────────────
-- § 23. Root Type → v Alloseme on Fragment Entries
-- ────────────────────────────────────────────────────

/-- *brechen* (result root) and *frieren* (PC root) yield opposite v
    allosemes. This connects three modules: the fragment entry's
    `rootType` (Predicates.lean), `VAlloseme.fromRootType` (Allosemy.lean),
    and `VAlloseme.introducesEvent` (Allosemy.lean). -/
theorem rootType_alloseme_divergence :
    brechen.rootType.map VAlloseme.fromRootType = some .eventive ∧
    frieren.rootType.map VAlloseme.fromRootType = some .zero ∧
    brechen.rootType.map (VAlloseme.fromRootType · |>.introducesEvent) = some true ∧
    frieren.rootType.map (VAlloseme.fromRootType · |>.introducesEvent) = some false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The allosemy-based CEN prediction and the event-structure-based *-ung*
    prediction agree for *brechen*: result root → eventive v → CEN reading
    → can -ung, and achievement vendlerClass → can -ung. Two independent
    paths to the same conclusion. -/
theorem brechen_two_paths :
    -- Path 1: rootType → VAlloseme → readingFromAllosemes → CEN
    brechen.rootType.bind (λ rt =>
      readingFromAllosemes (VAlloseme.fromRootType rt) .sortal)
      = some .complexEvent ∧
    -- Path 2: vendlerClass → canUngNominalize
    canUngNominalize brechen.vendlerClass = true := ⟨rfl, rfl⟩

/-- The two paths DISAGREE for *frieren*: the canonical PC root → zero
    v → RN (not CEN), yet the achievement vendlerClass → can -ung. This
    is not a bug — it captures key insight that allosemy
    means BOTH v allosemes are available for any verb. The canonical
    alloseme is a default, not a constraint. *Frieren* CAN have eventive v
    and thus CAN form a CEN, even though its canonical alloseme is zero. -/
theorem frieren_canonical_vs_possible :
    -- Canonical path: PC root → zero v → simple entity (no CEN)
    frieren.rootType.bind (λ rt =>
      readingFromAllosemes (VAlloseme.fromRootType rt) .sortal)
      = some .simpleEntity ∧
    -- But -ung is still possible (achievement vendlerClass)
    canUngNominalize frieren.vendlerClass = true ∧
    -- Because eventive v is always available (that's what allosemy means)
    readingFromAllosemes .eventive .sortal = some .complexEvent := ⟨rfl, rfl, rfl⟩

end Phenomena.Morphology.Studies.Benz2025
