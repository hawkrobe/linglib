import Linglib.Features.Coordination
import Linglib.Data.WALS.Features.F56A
import Linglib.Data.WALS.Features.F63A
import Linglib.Data.WALS.Features.F64A

/-!
# Typology.Coordination
@cite{haspelmath-2007} @cite{stassen-2000} @cite{mitrovic-sauerland-2016}
@cite{dryer-haspelmath-2013} @cite{wals-2013}

Per-language typological substrate for coordination across three frameworks:

1. **@cite{haspelmath-2007} structural typology**: syndesis (asyndetic /
   monosyndetic / bisyndetic), coordinator position, structural patterns,
   and diachronic source (comitative vs additive focus particle).
2. **@cite{stassen-2000} AND/WITH typology**: derived from WALS Ch 63
   (lexical identity of "and" and "with").
3. **WALS Ch 56/63/64**: conjunction-quantifier relation, NP conjunction,
   nominal-vs-verbal conjunction.

Mirrors the `Linglib/Typology/{Possession,Negation,Question,Comparison}.lean`
substrate-extension pattern. Fragment-importable; cross-linguistic theorems
live in `Studies/Haspelmath2007.lean` (structural typology + 19-language
sample) and `Studies/Stassen2000.lean` (AND/WITH typology + 15-language
WALS sample).

## What lives here

- `Syndesis`, `CoordinatorPosition`, `CoordPattern`, `DiachronicSource`
  enums (@cite{haspelmath-2007}).
- `AndWithStatus` enum (@cite{stassen-2000}); derivation from WALS Ch 63.
- WALS aliases: `ConjQuantRelation`, `ConjComitativeRelation`,
  `NomVerbalConjRelation` for Chs 56/63/64.
- `SourcedEntry`, `ConjunctionSystem` structs (M&S framework).
- `CoordinationProfile` struct (WALS profile bundle).
- Helper predicates: `hasStrategy`, `muIsAdditive`, `hasSource`,
  `hasMonosyndetic`, `hasBisyndetic`, `muBoundness`.
- WALS aggregate sample-size + corpus-only generalisations (Ch 56/63/64).

## Theory-laden caveats

- `DiachronicSource` collapses Heine's full grammaticalization-source
  taxonomy to two main pathways relevant for coordination (comitative,
  focus particle); other pathways (e.g. coordinator from sequence
  adverbial) are conflated under `.other`.
- `AndWithStatus` is @cite{stassen-2000}'s binary classification; some
  authors (e.g. Mauri 2008) argue for a finer multi-way split.
-/

set_option autoImplicit false

namespace Typology.Coordination

open Features.Coordination

private abbrev ch56 := Data.WALS.F56A.allData
private abbrev ch63 := Data.WALS.F63A.allData
private abbrev ch64 := Data.WALS.F64A.allData

-- ============================================================================
-- §1. Haspelmath 2007 structural enums
-- ============================================================================

/-- Syndesis: presence and number of overt coordinators (Haspelmath §1). -/
inductive Syndesis where
  | asyndetic      -- A B (juxtaposition, no overt linker)
  | monosyndetic   -- A co-B (single coordinator)
  | bisyndetic     -- co-A co-B (two coordinators, one per coordinand)
  deriving DecidableEq, BEq, Repr

/-- Coordinator position relative to its coordinand (Haspelmath §1.2).

    @cite{haspelmath-2007} notes that **co-A B (prepositive on first
    coordinand only) is unattested** (cf. @cite{stassen-2000}, n=260). -/
inductive CoordinatorPosition where
  | prepositive    -- co precedes coordinand: "and A" / English "both X"
  | postpositive   -- co follows coordinand: "A-and" / Latin "X-que"
  deriving DecidableEq, BEq, Repr

/-- Structural pattern for binary coordination (Haspelmath (17)).

    Monosyndetic: 3 attested patterns (of 4 logically possible).
      A co-B (prepositive on 2nd: English "A and B")
      A-co B (postpositive on 1st: Tibetan "A-daŋ B")
      A B-co (postpositive on 2nd: Latin "A B-que")
      co-A B — UNATTESTED (@cite{haspelmath-2007})

    Bisyndetic: 4 attested patterns. -/
inductive CoordPattern where
  /-- A co-B: medial prepositive (English "A and B"). -/
  | a_co_b
  /-- A-co B: medial postpositive on 1st (Tibetan "A-daŋ B"). -/
  | a'co_b
  /-- A B-co: final postpositive (Latin "senatus populus-que"). -/
  | a_b'co
  /-- co-A co-B: prepositive bisyndetic (Yoruba "àtí A àtí B"). -/
  | co'a_co'b
  /-- A-co B-co: postpositive bisyndetic (Martuthunira "A-thurti B-thurti"). -/
  | a'co_b'co
  /-- A-co co-B: mixed bisyndetic (Homeric Greek "A-te kaì B"). -/
  | a'co_co'b
  /-- co-A B-co: mixed bisyndetic (Latin "et A B-que"). -/
  | co'a_b'co
  deriving DecidableEq, BEq, Repr

/-- Classify a pattern's syndesis. -/
def CoordPattern.syndesis : CoordPattern → Syndesis
  | .a_co_b | .a'co_b | .a_b'co => .monosyndetic
  | .co'a_co'b | .a'co_b'co | .a'co_co'b | .co'a_b'co => .bisyndetic

/-- Diachronic source of conjunction constructions (Haspelmath §5.1). -/
inductive DiachronicSource where
  | comitative      -- "with" → coordinator (gives A co-B or A-co B)
  | focusParticle   -- "also/too" → coordinator (gives A-co B-co)
  | other
  deriving DecidableEq, BEq, Repr

/-- Haspelmath's key insight connecting diachronic source to structural
    pattern. -/
def DiachronicSource.expectedPattern : DiachronicSource → Syndesis
  | .comitative    => .monosyndetic
  | .focusParticle => .bisyndetic
  | .other         => .monosyndetic  -- default

-- ============================================================================
-- §2. Stassen 2000 AND/WITH classification
-- ============================================================================

/-- @cite{stassen-2000} AND/WITH classification of languages.
    AND-languages have structurally distinct coordinate and comitative
    strategies. WITH-languages use comitative encoding as the only strategy
    for NP conjunction (lexical identity of "and" and "with"). -/
inductive AndWithStatus where
  | andLang   -- Coordinate and comitative are structurally distinct
  | withLang  -- Comitative marker = coordinator
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §3. WALS aliases (Chs 56/63/64)
-- ============================================================================

/-- WALS Ch 56: conjunction-quantifier relation. -/
abbrev ConjQuantRelation := Data.WALS.F56A.ConjunctionsAndUniversalQuantifiers

/-- WALS Ch 63: noun-phrase conjunction (and-vs-with). -/
abbrev ConjComitativeRelation := Data.WALS.F63A.NounPhraseConjunction

/-- WALS Ch 64: nominal-vs-verbal conjunction. -/
abbrev NomVerbalConjRelation := Data.WALS.F64A.NominalAndVerbalConjunction

/-- Derive AND/WITH status from the conjunction-comitative relation
    (@cite{stassen-2000}'s diagnostic). -/
def ConjComitativeRelation.toAndWithStatus :
    ConjComitativeRelation → AndWithStatus
  | .andDifferentFromWith => .andLang
  | .andIdenticalToWith   => .withLang

-- ============================================================================
-- §4. Per-language structs
-- ============================================================================

/-- A coordination entry annotated with its diachronic source.
    Wraps `CoordEntry` (from `Features.Coordination`) with typological
    metadata. For languages with Fragment files, `entry` references the
    Fragment entry directly — no data duplication. -/
structure SourcedEntry where
  /-- The coordination morpheme entry. -/
  entry : CoordEntry
  /-- Likely diachronic source, if known. -/
  source : Option DiachronicSource := none
  deriving Repr

/-- A language's conjunction system (M&S framework). -/
structure ConjunctionSystem where
  language : String
  /-- Available conjunction morphemes (sourced entries). -/
  morphemes : List SourcedEntry
  /-- Which conjunction strategies are available (M&S classification). -/
  strategies : List ConjunctionStrategy
  /-- Structural patterns attested (Haspelmath classification). -/
  patterns : List CoordPattern := []
  /-- ISO 639-3 code. -/
  iso : String := ""
  deriving Repr

/-- A language's coordination typology profile across WALS Chs 56, 63, 64. -/
structure CoordinationProfile where
  language : String
  iso : String := ""
  family : String := ""
  /-- Ch 56: conjunction-vs-universal-quantifier. -/
  conjQuant : Option ConjQuantRelation := none
  /-- Ch 63: "and" vs "with". -/
  conjComitative : Option ConjComitativeRelation := none
  /-- Ch 64: NP-vs-VP conjunction. -/
  nomVerbalConj : Option NomVerbalConjRelation := none
  walsNotes : String := ""
  deriving Repr

/-- Derive AND/WITH status for a coordination profile from its Ch 63 value. -/
def CoordinationProfile.andWithStatus (p : CoordinationProfile) :
    Option AndWithStatus :=
  p.conjComitative.map (·.toAndWithStatus)

-- ============================================================================
-- §5. Helper predicates
-- ============================================================================

/-- Does a language have a given strategy? -/
def ConjunctionSystem.hasStrategy (sys : ConjunctionSystem)
    (s : ConjunctionStrategy) : Bool :=
  sys.strategies.contains s

/-- Does a language have a MU morpheme that also serves as additive? -/
def ConjunctionSystem.muIsAdditive (sys : ConjunctionSystem) : Bool :=
  sys.morphemes.any fun m => m.entry.role == .mu && m.entry.alsoAdditive

/-- Does a language have a morpheme with a given diachronic source? -/
def ConjunctionSystem.hasSource (sys : ConjunctionSystem)
    (s : DiachronicSource) : Bool :=
  sys.morphemes.any fun m => m.source == some s

/-- Does a language have at least one monosyndetic pattern? -/
def ConjunctionSystem.hasMonosyndetic (sys : ConjunctionSystem) : Bool :=
  sys.patterns.any fun p => p.syndesis == .monosyndetic

/-- Does a language have at least one bisyndetic pattern? -/
def ConjunctionSystem.hasBisyndetic (sys : ConjunctionSystem) : Bool :=
  sys.patterns.any fun p => p.syndesis == .bisyndetic

/-- Get the boundness of a language's MU particle, if it has one. -/
def ConjunctionSystem.muBoundness (sys : ConjunctionSystem) : Option Boundness :=
  (sys.morphemes.find? fun m => m.entry.role == .mu).map (·.entry.boundness)


/-- F63A: "and" being different from "with" is the majority pattern (131 > 103). -/
theorem and_languages_majority :
    (ch63.filter (·.value == .andDifferentFromWith)).length >
    (ch63.filter (·.value == .andIdenticalToWith)).length := by native_decide

/-- F63A: languages where "and" = "with" form a substantial minority (103/234,
    44%) — comitative-to-coordinator grammaticalization is still transparent
    in many languages, but the AND-pattern dominates. -/
theorem comitative_source_substantial_minority :
    (ch63.filter (·.value == .andIdenticalToWith)).length * 2 < ch63.length ∧
    (ch63.filter (·.value == .andIdenticalToWith)).length * 3 > ch63.length := by
  exact ⟨by native_decide, by native_decide⟩

/-- F64A: identity of NP and VP conjunction is the majority pattern (161/301). -/
theorem nom_verbal_identity_is_majority :
    (ch64.filter (·.value == .identity)).length >
    (ch64.filter (·.value == .differentiation)).length ∧
    (ch64.filter (·.value == .identity)).length >
    (ch64.filter (·.value == .bothExpressedByJuxtaposition)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- F64A: juxtaposition for both NP and VP conjunction is rare (15/301 = 5%). -/
theorem juxtaposition_rare :
    (ch64.filter (·.value == .bothExpressedByJuxtaposition)).length * 20 <
    ch64.length := by native_decide

end Typology.Coordination
