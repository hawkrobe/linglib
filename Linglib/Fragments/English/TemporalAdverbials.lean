/-
# English Temporal Adverbial Fragment

Lexical entries for English temporal *in*-adverbials (TIAs) and related
temporal adverbials (*since*, *for*, *ago*), typed by the Theory layer.

## Architecture

Each `TIAEntry` records:
- Surface form and preposition
- Syntactic position (event-level vs perfect-level)
- Map function type (runtime τ vs identity id)
- Licensing requirements (telicity, polarity, perfect)

The Phenomena layer (`Phenomena/TemporalAdverbials/Rouillard2026.lean`)
imports these entries and proves that Theory predictions match empirical
acceptability judgments.

## References

- Rouillard, V. (2026). Maximal informativity accounts for the distribution
  of temporal *in*-adverbials. *L&P* 49:1--56.
- Dowty, D. (1979). Word Meaning and Montague Grammar.
- Krifka, M. (1989). Nominal reference, temporal constitution and
  quantification in event semantics.
- von Fintel, K. & Iatridou, S. (2019). Since since.
-/

import Linglib.Theories.Semantics.Lexical.Verb.Aspect

namespace Fragments.English.TemporalAdverbials

open TruthConditional.Verb.Aspect

-- ============================================================================
-- TIA Classification
-- ============================================================================

/-- Syntactic position of a temporal adverbial.
    Rouillard (2026) schemata (57), (61):
    - `eventLevel`: modifies VP (E-TIA reading)
    - `perfectLevel`: modifies AspP (G-TIA reading) -/
inductive AdverbialPosition where
  | eventLevel    -- VP-adjacent: measures event duration
  | perfectLevel  -- AspP-adjacent: measures gap (PTS) duration
  deriving DecidableEq, BEq, Repr

/-- Map function type: what does *in* relate to time?
    Rouillard (2026) eqs. (62)--(64), (70):
    - `runtime`: M = τ (temporal trace); used for E-TIAs
    - `identity`: M = id; used for G-TIAs (times map to themselves) -/
inductive MapFunction where
  | runtime   -- τ: events → times (E-TIA)
  | identity  -- id: times → times (G-TIA)
  deriving DecidableEq, BEq, Repr

/-- Temporal adverbial type.
    Rouillard (2026) terminology. -/
inductive TIAType where
  | eTIA  -- Event TIA: measures event durations
  | gTIA  -- Gap TIA: measures durations devoid of events
  deriving DecidableEq, BEq, Repr

/-- Aspect required by the adverbial's LF (E-perfect vs U-perfect).
    Rouillard (2026) Table 1. -/
inductive AspectReq where
  | perfective    -- PFV (E-perfect)
  | imperfective  -- IMPV (U-perfect)
  | either        -- no aspectual requirement
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Temporal Adverbial Entries
-- ============================================================================

/-- A lexical entry for a temporal *in*-adverbial or related adverbial.
    Theory-typed but theory-neutral: records structural properties without
    committing to a specific analysis of the perfect or aspect. -/
structure TIAEntry where
  /-- Surface preposition -/
  preposition : String
  /-- TIA type -/
  tiaType : TIAType
  /-- Syntactic position -/
  position : AdverbialPosition
  /-- Map function -/
  mapFunction : MapFunction
  /-- Requires telic VP? (for E-TIAs) -/
  requiresTelic : Bool
  /-- Requires negative polarity? (for G-TIAs) -/
  requiresNegative : Bool
  /-- Requires the perfect? -/
  requiresPerfect : Bool
  /-- Aspectual requirement -/
  aspectReq : AspectReq
  /-- Is this an NPI? -/
  isNPI : Bool
  deriving Repr, BEq

-- ============================================================================
-- The *in*-Adverbial Entries
-- ============================================================================

/-- *in* as E-TIA: "wrote a paper in three days".
    Rouillard (2026) eq. (62): ⟦in⟧ := λM λt λx. M(x) ⊑ t.
    Position: event-level (VP-adjacent).
    Map function: τ (runtime).
    Licensed when VP is telic. Not an NPI. -/
def inETIA : TIAEntry :=
  { preposition := "in"
    tiaType := .eTIA
    position := .eventLevel
    mapFunction := .runtime
    requiresTelic := true
    requiresNegative := false
    requiresPerfect := false
    aspectReq := .either
    isNPI := false }

/-- *in* as G-TIA: "hasn't been sick in three days".
    Rouillard (2026) eq. (70): ⟦id⟧ := id.
    Position: perfect-level (AspP-adjacent).
    Map function: id (times map to themselves).
    Licensed only under negation in the perfect. NPI. -/
def inGTIA : TIAEntry :=
  { preposition := "in"
    tiaType := .gTIA
    position := .perfectLevel
    mapFunction := .identity
    requiresTelic := false
    requiresNegative := true
    requiresPerfect := true
    aspectReq := .perfective
    isNPI := true }

-- ============================================================================
-- Related Temporal Adverbials (non-TIA)
-- ============================================================================

/-- Temporal adverbial type for non-TIA temporal expressions. -/
inductive TemporalAdvType where
  | since_   -- "since Monday": left-bounds PTS
  | for_     -- "for three days": event-level duration
  | ago      -- "three days ago": past reference
  | before_  -- "before Monday": upper bound on event time
  deriving DecidableEq, BEq, Repr

/-- A non-TIA temporal adverbial entry. -/
structure TemporalAdvEntry where
  /-- Surface form -/
  form : String
  /-- Adverbial type -/
  advType : TemporalAdvType
  /-- Specifies LB of PTS? (Iatridou et al. 2001 classification) -/
  specifiesLB : Bool
  /-- Requires the perfect? -/
  requiresPerfect : Bool
  /-- Is ambiguous between E- and U-perfect? -/
  perfectAmbiguity : Bool
  deriving Repr, BEq

/-- "since Monday": left-bounds the PTS.
    Durative adverbial (Iatridou et al. 2001): specifies LB.
    von Fintel & Iatridou (2019): not lexically ambiguous. -/
def since : TemporalAdvEntry :=
  { form := "since"
    advType := .since_
    specifiesLB := true
    requiresPerfect := true
    perfectAmbiguity := true }

/-- "for three days": event-level duration.
    Ambiguous between event-level (measures event) and perfect-level
    (measures PTS). Rouillard (2026) fn. 10. -/
def forAdv : TemporalAdvEntry :=
  { form := "for"
    advType := .for_
    specifiesLB := false
    requiresPerfect := false
    perfectAmbiguity := true }

/-- "three days ago": simple past reference. -/
def ago : TemporalAdvEntry :=
  { form := "ago"
    advType := .ago
    specifiesLB := false
    requiresPerfect := false
    perfectAmbiguity := false }

-- ============================================================================
-- Derived Properties
-- ============================================================================

/-- E-TIA vs G-TIA is determined by syntactic position.
    Rouillard (2026) schemata (61):
    (a) ASP [ VP E-TIA ]   (b) [ ASP VP ] G-TIA -/
def TIAEntry.isEventLevel (e : TIAEntry) : Bool :=
  e.position == .eventLevel

/-- Does this TIA type use the runtime function τ? -/
def TIAEntry.usesRuntime (e : TIAEntry) : Bool :=
  e.mapFunction == .runtime

/-- The Vendler class constraint for E-TIAs: telic VPs only. -/
def TIAEntry.vendlerConstraint (e : TIAEntry) : Option Telicity :=
  if e.requiresTelic then some .telic else none

-- ============================================================================
-- Lexicon
-- ============================================================================

/-- All TIA entries (both readings of *in*). -/
def allTIAs : List TIAEntry := [inETIA, inGTIA]

/-- All temporal adverbial entries. -/
def allTemporalAdvs : List TemporalAdvEntry := [since, forAdv, ago]

-- ============================================================================
-- Verification
-- ============================================================================

-- E-TIA and G-TIA have the same preposition but different positions
#guard inETIA.preposition == inGTIA.preposition
#guard inETIA.position != inGTIA.position

-- E-TIA uses runtime, G-TIA uses identity
#guard inETIA.usesRuntime
#guard !inGTIA.usesRuntime

-- Only G-TIA is an NPI
#guard !inETIA.isNPI
#guard inGTIA.isNPI

-- E-TIA requires telicity, G-TIA requires negation + perfect
#guard inETIA.requiresTelic && !inETIA.requiresNegative
#guard inGTIA.requiresNegative && inGTIA.requiresPerfect

-- Since specifies LB, for does not
#guard since.specifiesLB
#guard !forAdv.specifiesLB

end Fragments.English.TemporalAdverbials
