import Linglib.Theories.Morphology.DM.Allosemy
import Linglib.Phenomena.Constructions.Studies.FillmoreKayOConnor1988

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
- `Phenomena.Constructions.Studies.FillmoreKayOConnor1988`: Judgment type
-/

namespace Phenomena.Morphology.Studies.Benz2025

open Morphology.DM.Allosemy
open Phenomena.Constructions.Studies.FillmoreKayOConnor1988 (Judgment)

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

/-- *Beobachtung* ('observation') — the running example in @cite{benz-2025} Ch. 3.
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
  , reading := .result
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
    (allBeobachtungReadings.any (·.reading == .result)) = true ∧
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
  | .result       => (.stative,  .sortal)
  | .content      => (.eventive, .content)

/-- The alloseme pair correctly derives each reading. -/
theorem alloseme_derivation_CEN :
    readingFromAllosemes (.eventive) (.sortal) = some .complexEvent := rfl

theorem alloseme_derivation_RN :
    readingFromAllosemes (.stative) (.sortal) = some .result := rfl

theorem alloseme_derivation_CCN :
    readingFromAllosemes (.eventive) (.content) = some .content := rfl

/-- Round-trip: each reading maps to allosemes that reconstruct it. -/
theorem alloseme_roundtrip (r : NominalizationReading) :
    let (v, n) := readingAllosemePair r
    readingFromAllosemes v n = some r := by
  cases r <;> rfl

/-- The impossible combination: stative v + content n yields no reading.
    Content requires an underlying event. -/
theorem stative_content_impossible :
    readingFromAllosemes .stative .content = none := rfl

/-- CEN and RN are "mirror images" of the division of semantic labor:
    in CEN, v does the work (introducing the event variable) while n merely
    nominalizes; in RN, v is null (stative) and the referential/object
    interpretation comes from the nominalization context. Both use the
    same n alloseme (sortal) — it's v that varies. -/
theorem cen_rn_mirror :
    (readingAllosemePair .complexEvent).1 = .eventive ∧
    (readingAllosemePair .result).1 = .stative ∧
    (readingAllosemePair .complexEvent).2 = .sortal ∧
    (readingAllosemePair .result).2 = .sortal := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════════
-- Part II: Prefixes, Particles, and Resultatives (Ch. 4)
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────
-- § 4. German Preverbal Element Typology
-- ────────────────────────────────────────────────────

/-- The three types of German preverbal elements.

    @cite{benz-2025} Ch. 4: prefixes are inseparable and attach as heads;
    particles are separable and attach as phrases; RSPs are adjectival
    phrases that form complex predicates with the verb. -/
inductive PreverbalElement where
  | pfx  -- inseparable prefix (be-, ent-, er-, ge-, miss-, ver-, zer-)
  | prt  -- separable particle (ab-, an-, auf-, aus-, ein-, los-, nach-, vor-, zu-, ...)
  | rsp  -- resultative secondary predicate (platt, tot, kaputt, ...)
  deriving DecidableEq, BEq, Repr

/-- Syntactic status: head or phrase.

    @cite{benz-2025} §4.3.1: following Wurmbrand (1998) and Zeller (2001a),
    prefixes are heads (inseparable under V2 movement) while particles
    are phrases (obligatorily stranded under V2). RSPs are unambiguously
    phrasal (they can be modified: *total flach gehämmert*). -/
def PreverbalElement.isHead : PreverbalElement → Bool
  | .pfx => true
  | .prt => false
  | .rsp => false

/-- Does this element always specify a result state that conflicts with
    other delimiters?

    @cite{benz-2025} §4.1: prefixes and RSPs always contribute a
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

    @cite{benz-2025} Table 4. The prefix *ge-* is the rare
    non-participial prefix (as in *ge-bären*, *ge-denken*). -/
def inseparablePrefixes : List String :=
  ["be", "ent", "er", "ge", "miss", "ver", "zer"]

/-- German separable particles (open class, representative sample).

    @cite{benz-2025} Table 4. Elements like durch-, über-, um-
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

/-- The full co-occurrence paradigm from @cite{benz-2025} Table 3. -/
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
  -- pfx/PRT + RSP: blocked by both factors.
  { outer := .pfx, inner := .rsp
  , allowed := false
  , structurePredicts := false
  , interpretationPredicts := false
  , exampleStr := "*ver-platt-hämmern (blocked in all orders)" }
]

-- ────────────────────────────────────────────────────
-- § 7. Structural Prediction: Head/Phrase Compatibility
-- ────────────────────────────────────────────────────

/-- Structural compatibility: phrase can take headed complement; two heads
    can combine; head cannot wrap phrase; two phrases cannot stack.

    @cite{benz-2025} §4.3.1, §4.4. -/
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

    @cite{benz-2025} §4.1: the interpretive constraint is about conflicting
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

    @cite{benz-2025} §4.4: both factors are needed; neither alone
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
  judgment : Judgment
  verbClass : String
  deriving Repr, BEq

/-- German RSP data from @cite{benz-2025} §4.2.

    German allows obligatorily transitive, unaccusative, and inherently
    reflexive M predicates in resultatives — not just unergatives. -/
def germanRSPData : List GermanResultativeDatum := [
  { sentence := "Er hämmerte das Metall platt"
  , gloss := "he hammered the.ACC metal flat"
  , translation := "He hammered the metal flat"
  , judgment := .grammatical
  , verbClass := "transitive" },
  { sentence := "Er schießt seinen Gegner tot"
  , gloss := "he shoots his.ACC opponent dead"
  , translation := "He shoots his opponent dead"
  , judgment := .grammatical
  , verbClass := "transitive" },
  { sentence := "Hans hat den Stock kaputt gebrochen"
  , gloss := "Hans has the.ACC stick broken broken.PTCP"
  , translation := "Hans broke the stick"
  , judgment := .grammatical
  , verbClass := "obligatorily transitive" },
  { sentence := "Das Wasser fror fest"
  , gloss := "the.NOM water froze solid"
  , translation := "The water froze solid"
  , judgment := .grammatical
  , verbClass := "unaccusative" },
  { sentence := "Sie haben sich krank/tot geschämt"
  , gloss := "they have REFL sick/dead shamed.PTCP"
  , translation := "They were embarrassed sick/dead"
  , judgment := .grammatical
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

/-- RSPs are incompatible with prefixed verbs. @cite{benz-2025} (87). -/
def rsp_pfx_contrasts : List (GermanResultativeDatum × GermanResultativeDatum) := [
  ( { sentence := "*Sie haben uns arm be-raubt"
    , gloss := "they have us.ACC poor BE-robbed.PTCP"
    , translation := "They robbed us poor"
    , judgment := .ungrammatical
    , verbClass := "prefix verb (be-)" },
    { sentence := "Sie haben uns arm geraubt"
    , gloss := "they have us.ACC poor robbed.PTCP"
    , translation := "They robbed us poor"
    , judgment := .grammatical
    , verbClass := "simplex verb" } ),
  ( { sentence := "*Sie haben ihn tot er-schossen"
    , gloss := "they have him.ACC dead ER-shot.PTCP"
    , translation := "They shot him dead"
    , judgment := .ungrammatical
    , verbClass := "prefix verb (er-)" },
    { sentence := "Sie haben ihn tot geschossen"
    , gloss := "they have him.ACC dead shot.PTCP"
    , translation := "They shot him dead"
    , judgment := .grammatical
    , verbClass := "simplex verb" } ),
  ( { sentence := "*Hans hat den Stock kaputt zer-brochen"
    , gloss := "Hans has the.ACC stick broken ZER-broken.PTCP"
    , translation := "Hans broke the stick broken"
    , judgment := .ungrammatical
    , verbClass := "prefix verb (zer-)" },
    { sentence := "Hans hat den Stock kaputt gebrochen"
    , gloss := "Hans has the.ACC stick broken.ADJ broken.PTCP"
    , translation := "Hans broke the stick broken"
    , judgment := .grammatical
    , verbClass := "simplex verb" } )
]

/-- Every RSP+pfx-verb contrast: pfx-verb ungrammatical, simplex OK. -/
theorem rsp_pfx_contrast_pattern :
    rsp_pfx_contrasts.all (fun (bad, good) =>
      bad.judgment == .ungrammatical && good.judgment == .grammatical) = true := by
  native_decide

/-- RSPs are also incompatible with particles. @cite{benz-2025} (88). -/
def rsp_prt_contrasts : List (GermanResultativeDatum × GermanResultativeDatum) := [
  ( { sentence := "*Sie hat den Tisch trocken ab-gewischt"
    , gloss := "she has the.ACC table dry AB-wiped.PTCP"
    , translation := "She wiped the table off dry"
    , judgment := .ungrammatical
    , verbClass := "particle verb (ab-)" },
    { sentence := "Sie hat den Tisch trocken gewischt"
    , gloss := "she has the.ACC table dry wiped.PTCP"
    , translation := "She wiped the table dry"
    , judgment := .grammatical
    , verbClass := "simplex verb" } ),
  ( { sentence := "*Das Baby hat mich nass an-gespuckt"
    , gloss := "the baby has me.ACC wet AN-spit.PTCP"
    , translation := "The baby spat up on me and I was wet"
    , judgment := .ungrammatical
    , verbClass := "particle verb (an-)" },
    { sentence := "Das Baby hat mich nass gespuckt"
    , gloss := "the baby has me.ACC wet spit.PTCP"
    , translation := "The baby spat up on me"
    , judgment := .grammatical
    , verbClass := "simplex verb" } )
]

/-- Every RSP+PRT-verb contrast: PRT-verb ungrammatical, simplex OK. -/
theorem rsp_prt_contrast_pattern :
    rsp_prt_contrasts.all (fun (bad, good) =>
      bad.judgment == .ungrammatical && good.judgment == .grammatical) = true := by
  native_decide

-- ════════════════════════════════════════════════════════════════════
-- Part III: Allosemy and Locality (Ch. 2, Ch. 4)
-- ════════════════════════════════════════════════════════════════════

-- ────────────────────────────────────────────────────
-- § 12. Interpretive Transparency
-- ────────────────────────────────────────────────────

/-- @cite{benz-2025} Claim 2: RSPs are always transparent (outside v's
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

Following Williams (2015), adopted by @cite{benz-2025} §4.2:
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

end Phenomena.Morphology.Studies.Benz2025
